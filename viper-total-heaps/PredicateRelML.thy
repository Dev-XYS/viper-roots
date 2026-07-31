theory PredicateRelML
  imports Boogie_Lang.HelperML ExprWfRelML TotalViperSimulation.ExhaleRel ViperBoogieHelperML CPGHelperML TotalViperSimulation.PredicateRel ExhaleRelML InhaleRelML KnownFoldedML FoldStmtRelKF
begin


subsection \<open>Unfold\<close>


ML \<open>

val Rmsg' = run_and_print_if_fail_2_tac'

(* Helpers for discharging \<^const>\<open>contains_no_heap_assignment_until\<close> and
   \<^const>\<open>program_point_restriction\<close> (\<open>fold_stmt_rel_kf\<close>'s trailing \<open>NoHeapAssignBetween\<close>/
   \<open>PPSyntacticRestriction\<close> premises), which are purely syntactic checks on the generated Boogie
   AST between the fold's known-folded-mask-update position and the rest of the method body.
   Bigblocks appear in the generated AST as opaque named constants (e.g. \<open>bigblock_15\<close>), so both
   need to repeatedly unfold whichever bigblock constant is currently blocking progress. *)

(* Recursively walks a \<^typ>\<open>bigblock \<times> cont\<close>/\<open>cont\<close>/\<open>bigblock list\<close>-shaped term, collecting the
   names of every opaque bigblock constant reachable without unfolding anything (i.e. everything
   visible in the term as it currently stands). Repeated calls (each preceded by unfolding the
   previously found names) reveal further nested names hidden inside \<^const>\<open>ParsedIf\<close> branches. *)
fun safe_resolve_tac msg ctxt thms i st =
  case Seq.pull ((resolve_tac ctxt thms i) st) of
    NONE => raise TERM (msg, [Thm.prop_of st])
  | some => Seq.make (fn () => some)

fun collect_bigblock_names (t : term) : string list =
  case t of
    Const (@{const_name Product_Type.Pair}, _) $ bb $ cont =>
      collect_bigblock_names bb @ collect_bigblock_names cont
  | Const (@{const_name KSeq}, _) $ bb $ cont =>
      collect_bigblock_names bb @ collect_bigblock_names cont
  | Const (@{const_name KEndBlock}, _) $ cont => collect_bigblock_names cont
  | Const (@{const_name KStop}, _) => []
  | Const (@{const_name BigBlock}, _) $ _ $ _ $ opt_if $ _ =>
      (case opt_if of
         Const (@{const_name Some}, _) $ (Const (@{const_name ParsedIf}, _) $ _ $ then_bbs $ else_bbs) =>
           collect_bigblock_list then_bbs @ collect_bigblock_list else_bbs
       | _ => [])
  | _ =>
      (case Term.head_of t of
         Const (name, _) => [name]
       | _ => [])
and collect_bigblock_list (t : term) : string list =
  case t of
    Const (@{const_name Nil}, _) => []
  | Const (@{const_name Cons}, _) $ x $ xs => collect_bigblock_names x @ collect_bigblock_list xs
  | _ => []

(* Extracts the \<open>(bigblock \<times> cont)\<close>-typed arguments from the current goal's conclusion, whichever
   of \<^const>\<open>contains_no_heap_assignment_until\<close> or \<^const>\<open>program_point_restriction\<close> it is. *)
fun program_points_in_goal (t : term) : term list =
  case Logic.strip_assums_concl t of
    @{term Trueprop} $ (Const (@{const_name contains_no_heap_assignment_until}, _) $ _ $ pp1 $ pp2) => [pp1, pp2]
  | @{term Trueprop} $ (Const (@{const_name program_point_restriction}, _) $ pp) => [pp]
  | _ => []

(* Unfolds every currently-visible opaque bigblock constant in the goal's program point(s) via its
   \<open>_def\<close> lemma (if one exists); a no-op if nothing (further) can be unfolded. *)
fun unfold_visible_bigblocks_tac ctxt = SUBGOAL (fn (t, i) =>
  let
    val names = maps collect_bigblock_names (program_points_in_goal t) |> distinct (op =)
    val thms = @{thms convert_list_to_cont.simps} @
               maps (fn name => Proof_Context.get_thms ctxt (name ^ "_def") handle ERROR _ => []) names
  in
    CHANGED (simp_only_tac thms ctxt i)
  end)

(* Repeatedly unfolds bigblocks (revealing further nested names each round) until no more progress
   can be made; bounded to avoid ever looping indefinitely on a malformed/cyclic AST. *)
fun unfold_all_bigblocks_tac ctxt = REPEAT_DETERM' (unfold_visible_bigblocks_tac ctxt)

(* Discharges \<^const>\<open>program_point_restriction \<gamma>\<close>: fully unfold every bigblock reachable from \<open>\<gamma>\<close>,
   then close via plain simp (\<^const>\<open>bigblock_restriction\<close>/\<^const>\<open>flatten_cont\<close> are plain \<open>fun\<close>s,
   so their equations are already default simp rules). *)
fun program_point_restriction_tac ctxt =
  (unfold_all_bigblocks_tac ctxt) THEN' (assm_full_simp_solved_tac ctxt)

(* Discharges \<^const>\<open>contains_no_heap_assignment_until hvar \<gamma>\<^sub>b \<gamma>\<close> by repeatedly applying the
   inductive definition's constructors (mirroring the worked example in
   \<open>BoogieSyntaxBasedProperties.thy\<close>): \<open>NoAssignReach\<close> once \<open>\<gamma>\<close> has been walked down to (syntactically
   equal to, after unfolding) \<open>\<gamma>\<^sub>b\<close>; \<open>NoAssignSimpleCmd\<close> to consume one command at a time (the
   "not an assignment to hvar, not a havoc" side condition is a simple syntactic fact about
   concrete variable indices, closed by simp); \<open>NoAssignIf\<close> to descend into both branches of an
   \<open>ParsedIf\<close>; \<open>NoAssignCont\<close> to move past an already-empty bigblock into the next one. Bigblocks
   are unfolded on demand (via \<open>unfold_visible_bigblocks_tac\<close>) whenever a rule's syntactic pattern
   would otherwise not match an opaque bigblock name. *)
(* Returns the name of the opaque constant blocking pattern-matching of a bigblock/cont term (i.e.
   the term is not already a raw \<^const>\<open>BigBlock\<close>/\<^const>\<open>KSeq\<close>/\<^const>\<open>KEndBlock\<close>/\<^const>\<open>KStop\<close>
   application), or \<open>NONE\<close> if it is already fully revealed at the top level. *)
fun blocking_name (already_head : term -> bool) (t : term) : string option =
  if already_head t then NONE
  else case Term.head_of t of
    Const (name, _) => SOME name
  | _ => NONE

fun is_bigblock_head (Const (@{const_name BigBlock}, _) $ _ $ _ $ _ $ _) = true
  | is_bigblock_head _ = false

fun is_cont_head (Const (@{const_name KSeq}, _) $ _ $ _) = true
  | is_cont_head (Const (@{const_name KEndBlock}, _) $ _) = true
  | is_cont_head (Const (@{const_name KStop}, _)) = true
  | is_cont_head _ = false

(* Unfolds exactly one opaque name (via its \<open>_def\<close> lemma, plus \<^const>\<open>convert_list_to_cont\<close>'s
   own equations, which the generalized \<open>NoAssignIf\<close> can introduce) across the whole goal. Applied
   lazily (only the single name currently blocking progress at the CURRENT walk position, never the
   whole remaining method body up front) to avoid inflating the goal with unrelated, not-yet-reached
   bigblocks -- unfolding everything reachable from the target program point eagerly (as an earlier
   version of this tactic did) makes the goal grow with the entire rest of the method and was the
   source of a severe slowdown. *)
fun unfold_one_name_tac ctxt (name : string) : int -> tactic =
  case Proof_Context.get_thms ctxt (name ^ "_def") handle ERROR _ => [] of
    [] => K no_tac
  | thms => (fn i => CHANGED (simp_only_tac (thms @ @{thms convert_list_to_cont.simps}) ctxt i))

(* Deterministically decides which of \<open>NoAssignReach\<close>/\<open>NoAssignSimpleCmd\<close>/\<open>NoAssignIf\<close>/
   \<open>NoAssignCont\<close> applies by inspecting the actual term shape of the goal's two program points,
   instead of letting \<open>resolve_tac\<close> search for a match (\<open>NoAssignReach\<close>'s conclusion has the same
   schematic variable \<open>\<gamma>\<^sub>b\<close> repeated twice, and blindly attempting it via unification against a
   large, growing goal term at every one of the (up to) ~100 recursion levels needed to walk the
   whole method body turned out to be a severe source of slowdown; a cheap structural check up
   front avoids invoking the unifier on alternatives that cannot possibly match). Whenever the
   current bigblock/cont is still hidden behind an opaque name, unfolds just that one name (via
   \<open>unfold_one_name_tac\<close>) instead of the whole reachable set. *)
fun dispatch_no_heap_assign_tac ctxt (pp2 : term) : int -> tactic =
  case pp2 of
    Const (@{const_name Product_Type.Pair}, _) $ bb $ cont =>
      if not (is_bigblock_head bb) then
        (case blocking_name is_bigblock_head bb of
           SOME name => unfold_one_name_tac ctxt name
         | NONE => (fn _ => raise TERM ("DEBUG dead end: pp2's bigblock is not headed by a constant", [pp2])))
      else
        let val Const (@{const_name BigBlock}, _) $ _ $ cs $ str $ _ = bb in
          case cs of
            Const (@{const_name Cons}, _) $ _ $ _ =>
              safe_resolve_tac "DEBUG NoAssignSimpleCmd did not unify" ctxt @{thms NoAssignSimpleCmd}
          | Const (@{const_name Nil}, _) =>
              (case str of
                 Const (@{const_name Some}, _) $ (Const (@{const_name ParsedIf}, _) $ _ $ _ $ _) =>
                   safe_resolve_tac "DEBUG NoAssignIf did not unify" ctxt @{thms NoAssignIf}
               | Const (@{const_name None}, _) =>
                   if not (is_cont_head cont) then
                     (case blocking_name is_cont_head cont of
                        SOME name => unfold_one_name_tac ctxt name
                      | NONE => (fn _ => raise TERM ("DEBUG dead end: pp2's cont is not headed by a constant", [pp2])))
                   else
                     (case cont of
                        Const (@{const_name KSeq}, _) $ _ $ _ =>
                          safe_resolve_tac "DEBUG NoAssignCont did not unify" ctxt @{thms NoAssignCont}
                      | _ => (fn _ => raise TERM ("DEBUG dead end: empty bigblock, str=None, cont is KStop/KEndBlock", [pp2])))
               | _ => (fn _ => raise TERM ("DEBUG dead end: empty bigblock, str neither Some(ParsedIf) nor None", [pp2, str])))
          | _ => (fn _ => raise TERM ("DEBUG dead end: cs neither Cons nor Nil", [pp2, cs]))
        end
  | _ => (fn _ => raise TERM ("DEBUG dead end: pp2 not a BigBlock pair", [pp2]))

fun no_heap_assignment_until_step_tac ctxt = SUBGOAL (fn (t, i) =>
  case program_points_in_goal t of
    [pp1, pp2] =>
      if pp1 aconv pp2 then safe_resolve_tac "DEBUG NoAssignReach did not unify" ctxt @{thms NoAssignReach} i
      else dispatch_no_heap_assign_tac ctxt pp2 i
  | _ => raise TERM ("DEBUG side-condition not closed by simp", [Logic.strip_assums_concl t]))

fun no_heap_assignment_until_tac ctxt : int -> tactic =
  no_heap_assignment_until_step_tac ctxt THEN_ALL_NEW
    (fn i => (assm_full_simp_solved_tac ctxt i) ORELSE (no_heap_assignment_until_tac ctxt i))


fun upd_exhale_pred_acc_in_unfold_tac ctxt (info: basic_stmt_rel_info) pred_name exp_rel_info =
  (Rmsg' "exh pred upd progress" (rewrite_rel_general_tac ctxt) ctxt) THEN'
  (Rmsg' "exh pred upd rule" (resolve_tac ctxt @{thms exhale_rel_pred_acc_upd_rel}) ctxt) THEN'
  (Rmsg' "exh pred upd StateRelIn" (simp_then_if_not_solved_blast_tac ctxt |> SOLVED') ctxt) THEN'
  (Rmsg' "exh pred upd TempPermNotInAux" (simp_then_if_not_solved_blast_tac ctxt |> SOLVED') ctxt) THEN'
  (Rmsg' "exh pred upd StateRelOut" (simp_then_if_not_solved_blast_tac ctxt |> SOLVED') ctxt) THEN'
  (Rmsg' "exh pred upd WfCons" (resolve_tac ctxt [#consistency_wf_thm info]) ctxt) THEN'
  (Rmsg' "exh pred upd WfTyRep" (resolve_tac ctxt [#wf_ty_repr_thm info]) ctxt) THEN'
  (Rmsg' "exh pred upd MaskVarDefSame" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "exh pred upd TyInterp" (resolve_tac ctxt [#type_interp_econtext info]) ctxt) THEN'
  (Rmsg' "exh pred upd NullConst" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "exh pred upd MaskVar" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "exh pred upd MaskUpdateWf" (resolve_tac ctxt [@{thm mask_update_wf_concrete} OF [#ctxt_wf_thm info, #wf_ty_repr_thm info]] THEN'
                                      assm_full_simp_solved_tac ctxt) ctxt) THEN'
  (Rmsg' "exh pred upd MaskReadWf" (resolve_tac ctxt [@{thm mask_read_wf_concrete} OF [#ctxt_wf_thm info, #wf_ty_repr_thm info]] THEN'
                                    assm_full_simp_solved_tac ctxt) ctxt) THEN'
  (Rmsg' "exh pred upd PredType" (assm_full_simp_solved_with_thms_tac [#ty_repr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "exh pred upd NewPermBpl" (simp_tac_with_thms @{thms update_mask_concrete_def} ctxt) ctxt) THEN'
  (Rmsg' "exh pred upd MaskUpdateBpl" (simp_tac_with_thms @{thms read_mask_concrete_def update_mask_concrete_def} ctxt THEN'
                                      assm_full_simp_solved_with_thms_tac [#ty_repr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "exh pred upd PlocBpl" (simp_tac_with_thms [] ctxt) ctxt) THEN'
  (Rmsg' "exh pred upd PlocRel" (prove_ploc_rel ctxt info pred_name exp_rel_info) ctxt) THEN'
  (Rmsg' "exh pred upd AbsInterpEq" (assm_full_simp_solved_with_thms_tac [#ty_repr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "exh pred upd ProgEq" (assm_full_simp_solved_with_thms_tac [#vpr_program_ctxt_eq_thm info] ctxt) ctxt) THEN'
  (Rmsg' "exh pred upd KFRelOff" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "exh pred upd ConsOn" (assm_full_simp_solved_with_thms_tac
                                  ([#tr_def_thm info] @ @{thms default_state_rel_options_def}) ctxt) ctxt)

fun atomic_exhale_pred_acc_in_unfold_tac ctxt (info: basic_stmt_rel_info) (no_def_checks_tac_opt: (Proof.context -> basic_stmt_rel_info -> int -> tactic) option) exh_pred_acc_hint =
    case exh_pred_acc_hint of
      PredAccExhHint (pred_name, exp_wf_rel_info, exp_rel_info, lookup_aux_var_ty_thm, lookup_aux_var_state_rel_thm, exp_rel_perm_access_thm) =>
        (Rmsg' "UnfoldExhPred 1" (resolve_tac ctxt @{thms unfold_exhale_pred_rel}) ctxt) THEN'
        (Rmsg' "UnfoldExhPred wf args list simp" (simp_only_tac @{thms append_Cons append_Nil} ctxt) ctxt) THEN'
        (Rmsg' "UnfoldExhPred wf subexpressions" (exps_wf_rel_tac info exp_wf_rel_info exp_rel_info ctxt no_def_checks_tac_opt 2) ctxt) THEN'
        (Rmsg' "UnfoldExhPred 2 propagate" (resolve_tac ctxt @{thms rel_propagate_pre_2}) ctxt) THEN'
        (Rmsg' "UnfoldExhPred 3 propagate" (resolve_tac ctxt @{thms red_ast_bpl_relI}) ctxt) THEN'
        (store_temporary_perm_pred_exh_tac ctxt info exp_rel_info lookup_aux_var_ty_thm) THEN'
        (prove_perm_non_negative_pred_exh_tac ctxt info lookup_aux_var_state_rel_thm) THEN'
        (prove_sufficient_perm_pred_tac ctxt info pred_name exp_rel_info lookup_aux_var_state_rel_thm exp_rel_perm_access_thm) THEN'
        (upd_exhale_pred_acc_in_unfold_tac ctxt info pred_name exp_rel_info)
    | _ => error("Unfold only supports PredAccExhHint")


fun kfm_upd_rel_unfold_tac ctxt (info: basic_stmt_rel_info) pred_name exp_rel_info =
  (Rmsg' "unfold kf upd rule" (resolve_tac ctxt @{thms unfold_knownfolded_upd_rel}) ctxt) THEN'
  (Rmsg' "unfold kf upd StateRelIn" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
  (Rmsg' "unfold kf upd StateRelOut" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
  (Rmsg' "unfold kf upd KFMPosOff" (assm_full_simp_solved_with_thms_tac
                                              ([#tr_def_thm info] @ @{thms default_state_rel_options_def}) ctxt) ctxt) THEN'
  (Rmsg' "unfold kf upd KFMOn" (assm_full_simp_solved_with_thms_tac
                                          ([#tr_def_thm info] @ @{thms default_state_rel_options_def}) ctxt) ctxt) THEN'
  (Rmsg' "unfold kf upd KFMRel" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
  (Rmsg' "unfold kf upd KFMNewOpt" (assm_full_simp_solved_with_thms_tac
                                              ([#tr_def_thm info] @ @{thms default_state_rel_options_def}) ctxt) ctxt) THEN'
  (Rmsg' "unfold kf upd HeapVarDefSame" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "unfold kf upd NullConst" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "unfold kf upd ZeroPMaskConst" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "unfold kf upd HeapVar" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "unfold kf upd FieldTranslation" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "unfold kf upd HeapUpdateWf" (resolve_tac ctxt [@{thm heap_update_wf_concrete} OF [#ctxt_wf_thm info, #wf_ty_repr_thm info]] THEN'
                                                assm_full_simp_solved_tac ctxt) ctxt) THEN'
  (Rmsg' "unfold kf upd KnownFoldedUpdBpl" (assm_full_simp_solved_with_thms_tac
                                                       [@{thm update_heap_concrete_def}, #ty_repr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "unfold kf upd PlocRel" (prove_ploc_sm_rel' ctxt info pred_name exp_rel_info) ctxt) THEN'
  (Rmsg' "unfold kf upd TyInterpEq" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
  (Rmsg' "unfold kf upd PredType" (assm_full_simp_solved_with_thms_tac [#ty_repr_def_thm info] ctxt) ctxt)

fun pred_unfold_tac ctxt pred_name (inhale_info: atomic_inhale_rel_hint inhale_rel_info) (exhale_info: atomic_exhale_rel_hint exhale_rel_info) (basic_info : basic_stmt_rel_info) atomic_exhale_hint inhale_hint =
  let val pred_data = lookup_predicate_data basic_info pred_name
      val exp_rel_info =
        case atomic_exhale_hint of
          PredAccExhHint (_, _, exp_rel_info, _, _, _) => exp_rel_info
        | _ => error("Unfold only supports PredAccExhHint")
  in
  (Rmsg' "unfold stmt rule" (resolve_tac ctxt @{thms unfold_stmt_rel}) ctxt) THEN'
  (Rmsg' "unfold stmt PredDecl" (assm_full_simp_solved_with_thms_tac [#vpr_program_ctxt_eq_thm basic_info, #predicate_lookup_thm pred_data] ctxt) ctxt) THEN'
  (Rmsg' "unfold stmt PredArgs" (assm_full_simp_solved_with_thms_tac (@{thms predicate_decl.defs}@[#predicate_args_thm pred_data]) ctxt) ctxt) THEN'
  (Rmsg' "unfold stmt PredBody" (assm_full_simp_solved_with_thms_tac (@{thms predicate_decl.defs}@[#predicate_body_thm pred_data]) ctxt) ctxt) THEN'
  (Rmsg' "unfold stmt CtxtPredWf" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "unfold stmt CtxtPredSF" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "unfold stmt WfCons" (resolve_tac ctxt [#consistency_wf_thm basic_info]) ctxt) THEN'
  (Rmsg' "unfold stmt StateRelImpliesIntCons" (assm_full_simp_solved_with_thms_tac [#tr_def_thm basic_info, @{thm default_state_rel_options_def}, @{thm state_rel_consistent}] ctxt) ctxt) THEN'

  (Rmsg' "unfold stmt StateRelImpliesExtCons 1" (resolve_tac ctxt @{thms extcons_fun_interp_irrelevant'}) ctxt) THEN'
  (Rmsg' "unfold stmt StateRelImpliesExtCons 2" (forward_tac ctxt @{thms state_rel_consistent}) ctxt) THEN'
  (Rmsg' "unfold stmt StateRelImpliesExtCons 3" (assm_full_simp_solved_with_thms_tac [@{thm default_state_rel_options_def}, #tr_def_thm basic_info] ctxt) ctxt) THEN'
  (Rmsg' "unfold stmt StateRelImpliesExtCons 4" (assm_full_simp_solved_with_thms_tac [#ty_repr_def_thm basic_info] ctxt) ctxt) THEN'

  (Rmsg' "unfold stmt StateRelImpliesKFRel" (fastforce_tac ctxt (#tr_def_thm basic_info :: @{thms state_rel_def state_rel0_def})) ctxt) THEN'

  (Rmsg' "unfold stmt StateRelWeakening" (eresolve_tac ctxt @{thms state_rel_kf_disable_consistency}) ctxt) THEN'

  (Rmsg' "unfold stmt ArgsRestriction" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "unfold stmt BodyNoUnfolding" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "unfold stmt PermSimp" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "unfold stmt PermPos" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'

  (Rmsg' "unfold stmt StepPermPos (always assert true)" (resolve_tac ctxt @{thms bpl_assert_true_is_skip}) ctxt) THEN'
  (Rmsg' "unfold stmt StepExhale" (atomic_exhale_pred_acc_in_unfold_tac ctxt basic_info (#no_def_checks_tac_opt exhale_info) atomic_exhale_hint) ctxt) THEN'
  (Rmsg' "unfold stmt simp synmult & subst" (asm_full_simp_tac ctxt) ctxt) THEN'
  (Rmsg' "unfold stmt StepInhale" (inhale_rel_tac ctxt inhale_info inhale_hint) ctxt) THEN'
  (Rmsg' "unfold stmt StepKFUpdate" (kfm_upd_rel_unfold_tac ctxt basic_info pred_name exp_rel_info) ctxt) THEN'
  (Rmsg' "unfold stmt NoHeapAssignBetween" (no_heap_assignment_until_tac ctxt |> SOLVED') ctxt) THEN'
  (Rmsg' "unfold stmt PPSyntacticRestriction" (program_point_restriction_tac ctxt |> SOLVED') ctxt)
  end

\<close>



subsection \<open>Fold\<close>


ML \<open>

fun normal_exhale_rel_tac ctxt (info: 'a exhale_rel_info) (hint: 'a normal_exhale_rel_complete_hint) =
  (Rmsg' "stmt rel exhale pre propagate" (resolve_tac ctxt @{thms exhale_rel_propagate_pre_no_inv_same_exh}) ctxt) THEN'
  (Rmsg' "stmt rel exhale propagate progress" (resolve_tac ctxt @{thms red_ast_bpl_rel_transitive} THEN' (progress_red_bpl_rel_tac ctxt)) ctxt) THEN'
  (Rmsg' "stmt rel exhale track well-def propagate" (resolve_tac ctxt @{thms red_ast_bpl_rel_transitive}) ctxt) THEN'
  (Rmsg' "stmt rel exhale track well-def" (resolve_tac ctxt @{thms red_ast_bpl_rel_to_state_rel} THEN'
          simp_then_if_not_solved_blast_tac ctxt) ctxt) THEN'
  (Rmsg' "setup well-def state exhale" ((#setup_well_def_state_tac hint) (#basic_info info) ctxt) ctxt) THEN'
  (* (SUBGOAL (fn (t,_) => raise TERM ("breakpoint", [t]))) THEN' *)
  exhale_rel_aux_tac ctxt info (#exhale_rel_hint hint)


fun inhale_rel_pred_acc_upd_rel_tac' ctxt (info: basic_stmt_rel_info) pred_name exp_rel_info =
  (Rmsg' "inh pred acc upd rule" (resolve_tac ctxt @{thms inhale_rel_pred_acc_upd_rel'}) ctxt) THEN'
  (Rmsg' "inh pred acc upd StateRelIn" (simp_then_if_not_solved_blast_tac ctxt) ctxt) THEN'
  (Rmsg' "inh pred acc upd StateRelOut" (simp_then_if_not_solved_blast_tac ctxt) ctxt) THEN'
  (Rmsg' "inh pred acc upd AuxDomTemp" (#aux_var_disj_tac info ctxt) ctxt) THEN'
  (Rmsg' "inh pred acc upd AuxDomMask" (#aux_var_disj_tac info ctxt) ctxt) THEN'
  (Rmsg' "inh pred acc upd WfTyRep" (resolve_tac ctxt [#wf_ty_repr_thm info]) ctxt) THEN'
  (Rmsg' "inh pred acc upd MaskVarDefDiff" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "inh pred acc upd TyInterp" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
  (Rmsg' "inh pred acc upd NullConst" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "inh pred acc upd MaskVar" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "inh pred acc upd MaskUpdateWf" (resolve_tac ctxt [ @{thm mask_update_wf_concrete} OF [#ctxt_wf_thm info, #wf_ty_repr_thm info]]) ctxt THEN'
                                          assm_full_simp_solved_tac ctxt) THEN'
  (Rmsg' "inh pred acc upd MaskReadWf" (resolve_tac ctxt [ @{thm mask_read_wf_concrete} OF [#ctxt_wf_thm info, #wf_ty_repr_thm info]]) ctxt THEN'
                                        assm_full_simp_solved_tac ctxt) THEN'
  (Rmsg' "inh pred acc upd PredType" (assm_full_simp_solved_with_thms_tac [#ty_repr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "inh pred acc upd 2" (assm_full_simp_solved_with_thms_tac [@{thm update_mask_concrete_def}, #ty_repr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "inh pred acc upd 3" (assm_full_simp_solved_with_thms_tac (#ty_repr_def_thm info::(@{thms update_mask_concrete_def read_mask_concrete_def})) ctxt) ctxt) THEN'
  (Rmsg' "inh pred acc upd PlocBpl" (simp_tac_with_thms [] ctxt) ctxt) THEN'
  (Rmsg' "inh pred acc upd PlocRel" (prove_ploc_rel' ctxt info pred_name exp_rel_info) ctxt) THEN'
  (Rmsg' "inh pred acc upd AbsInterpEq" (assm_full_simp_solved_with_thms_tac [#ty_repr_def_thm info, @{thm ty_repr_basic_def}] ctxt) ctxt) THEN'
  (Rmsg' "inh pred acc upd ProgEq" (simp_tac_with_thms [] ctxt) ctxt) THEN'
  (Rmsg' "inh pred acc upd KFPosOff" (assm_full_simp_solved_with_thms_tac
                                       ([#tr_def_thm info, #ty_repr_def_thm info] @
                                          @{thms default_state_rel_options_def}) ctxt) ctxt)


fun atomic_inhale_pred_acc_in_fold_tac ctxt (info: basic_stmt_rel_info) inh_pred_acc_hint =
  case inh_pred_acc_hint of
    PredicateAccInhHint (pred_name, exp_wf_rel_info, exp_rel_info, lookup_aux_var_ty_thm, lookup_aux_var_state_rel_thm) =>
      (Rmsg' "InhPred (fold) unfold current bigblock?" (rewrite_rel_general_tac ctxt) ctxt) THEN'
      (Rmsg' "InhPred (fold) propagate (store perm)" (resolve_tac ctxt @{thms rel_propagate_pre}) ctxt) THEN'
      (Rmsg' "InhPred (fold) red_ast_bpl_relI" (resolve_tac ctxt @{thms red_ast_bpl_relI}) ctxt) THEN'
      (store_temporary_inh_perm_tac ctxt info exp_rel_info lookup_aux_var_ty_thm) THEN'
      (Rmsg' "InhPred (fold) perm non-neg (always true)" (resolve_tac ctxt @{thms bpl_assert_true_is_skip}) ctxt) THEN'
      (true_implies_true_tac ctxt) THEN'
      (Rmsg' "InhPred (fold) propagate (reset state rel)" (resolve_tac ctxt @{thms rel_propagate_post_3}) ctxt) THEN'
      (inhale_rel_pred_acc_upd_rel_tac' ctxt (info: basic_stmt_rel_info) pred_name exp_rel_info) THEN'
      (exhale_revert_state_relation ctxt info)
  | _ => error("Fold only supports PredicateAccInhHint")


fun pred_fold_tac ctxt pred_name exp_wf_rel_info exp_rel_info (inhale_info: atomic_inhale_rel_hint inhale_rel_info) (exhale_info: atomic_exhale_rel_hint exhale_rel_info) (basic_info : basic_stmt_rel_info) exhale_hint atomic_inhale_hint (kfm_temp_var_lookup_thms : thm list) =
  let val pred_data = lookup_predicate_data basic_info pred_name in
  (Rmsg' "fold stmt propogate (good state)" (resolve_tac ctxt [@{thm stmt_rel_propagate_3}]) ctxt) THEN'

  (Rmsg' "fold stmt rule" (resolve_tac ctxt @{thms fold_stmt_rel_kf}) ctxt) THEN'

  (Rmsg' "fold stmt PredDecl" (assm_full_simp_solved_with_thms_tac [#vpr_program_ctxt_eq_thm basic_info, #predicate_lookup_thm pred_data] ctxt) ctxt) THEN'
  (Rmsg' "fold stmt PredArgs" (assm_full_simp_solved_with_thms_tac (@{thms predicate_decl.defs}@[#predicate_args_thm pred_data]) ctxt) ctxt) THEN'
  (Rmsg' "fold stmt PredBody" (assm_full_simp_solved_with_thms_tac (@{thms predicate_decl.defs}@[#predicate_body_thm pred_data]) ctxt) ctxt) THEN'
  (Rmsg' "fold stmt CtxtPredWf" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "fold stmt CtxtPredSF" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "fold stmt WfCons" (resolve_tac ctxt [#consistency_wf_thm basic_info]) ctxt) THEN'
  (Rmsg' "fold stmt StateRelImpliesIntCons" (assm_full_simp_solved_with_thms_tac [#tr_def_thm basic_info, @{thm default_state_rel_options_def}, @{thm state_rel_consistent}] ctxt) ctxt) THEN'

  (Rmsg' "fold stmt StateRelImpliesExtCons 1" (resolve_tac ctxt @{thms extcons_fun_interp_irrelevant'}) ctxt) THEN'
  (Rmsg' "fold stmt StateRelImpliesExtCons 2" (forward_tac ctxt @{thms state_rel_consistent}) ctxt) THEN'
  (Rmsg' "fold stmt StateRelImpliesExtCons 3" (assm_full_simp_solved_with_thms_tac [@{thm default_state_rel_options_def}, #tr_def_thm basic_info] ctxt) ctxt) THEN'
  (Rmsg' "fold stmt StateRelImpliesExtCons 4" (assm_full_simp_solved_with_thms_tac [#ty_repr_def_thm basic_info] ctxt) ctxt) THEN'

  (Rmsg' "fold stmt StateRelImpliesKFRel" (fastforce_tac ctxt (#tr_def_thm basic_info :: @{thms state_rel_def state_rel0_def default_state_rel_options_def})) ctxt) THEN'

  (Rmsg' "fold stmt StateRelWeakening" (eresolve_tac ctxt @{thms state_rel_kf_disable_consistency}) ctxt) THEN'

  (Rmsg' "fold stmt ArgsRestriction" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "fold stmt ArgsAreVarOrLit" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "fold stmt BodyNoUnfolding" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "fold stmt PermSimp" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "fold stmt PermPos" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'

  (Rmsg' "fold stmt wf args list simp" (simp_only_tac @{thms append_Cons append_Nil} ctxt) ctxt) THEN'
  (Rmsg' "fold stmt StepWfSubexp" (exps_wf_rel_tac basic_info exp_wf_rel_info exp_rel_info ctxt NONE 2) ctxt) THEN'
  (Rmsg' "fold stmt StepPermPos (always assert true)" (resolve_tac ctxt @{thms red_bpl_assert_true}) ctxt) THEN'
  (Rmsg' "fold stmt simp synmult" (simp_tac_with_thms [] ctxt) ctxt) THEN'

  (normal_exhale_rel_tac ctxt exhale_info exhale_hint) THEN'

  (Rmsg' "fold stmt StateRelStrengthening 1" (eresolve_tac ctxt @{thms turn_on_knownfolded_rel'}) ctxt) THEN'
  (Rmsg' "fold stmt StateRelStrengthening 2" (assm_full_simp_solved_with_thms_tac [#tr_def_thm basic_info] ctxt) ctxt) THEN'
  (Rmsg' "fold stmt StateRelStrengthening 3" (assm_full_simp_solved_with_thms_tac [#tr_def_thm basic_info, @{thm default_state_rel_options_def}] ctxt) ctxt) THEN'
  (Rmsg' "fold stmt StateRelStrengthening 4" (assm_full_simp_solved_with_thms_tac [#tr_def_thm basic_info, @{thm default_state_rel_options_def}] ctxt) ctxt) THEN'

  (atomic_inhale_pred_acc_in_fold_tac ctxt basic_info atomic_inhale_hint) THEN'

  (Rmsg' "fold stmt good state after inhale propagate 1" (resolve_tac ctxt @{thms rel_propagate_pre_3_only_state_rel}) ctxt) THEN'
  (Rmsg' "fold stmt good state after inhale progress 1" ((progress_assume_good_state_rel_tac ctxt (#ctxt_wf_thm basic_info) (#tr_def_thm basic_info))) ctxt) THEN'
  (Rmsg' "fold stmt good state after inhale propagate 2" (resolve_tac ctxt @{thms rel_propagate_pre_3_only_state_rel}) ctxt) THEN'
  (Rmsg' "fold stmt good state after inhale progress 2" ((progress_assume_good_state_rel_tac ctxt (#ctxt_wf_thm basic_info) (#tr_def_thm basic_info))) ctxt) THEN'

  (Rmsg' "fold stmt known-folded mask update" (kfm_upd_rel_tac ctxt basic_info pred_name exp_rel_info kfm_temp_var_lookup_thms) ctxt) THEN'

  (Rmsg' "fold stmt NoHeapAssignBetween" (no_heap_assignment_until_tac ctxt |> SOLVED') ctxt) THEN'
  (Rmsg' "fold stmt PPSyntacticRestriction" (program_point_restriction_tac ctxt |> SOLVED') ctxt) THEN'
  (Rmsg' "fold stmt good state final" ((progress_assume_good_state_rel_tac ctxt (#ctxt_wf_thm basic_info) (#tr_def_thm basic_info))) ctxt)
  end


fun exh_in_fold_no_def_checks_tac ctxt (info: basic_stmt_rel_info) : int -> tactic =
  (* (SUBGOAL (fn (t,_) => raise TERM ("breakpoint", [t]))) THEN' *)
  resolve_tac ctxt [ @{thm framing_subst_exprs_wf_rel} OF [ #consistency_down_mono_thm info ] ] THEN'
  blast_tac ctxt THEN'
  assm_full_simp_solved_tac ctxt THEN'
  assm_full_simp_solved_tac ctxt THEN'
  assm_full_simp_solved_tac ctxt

\<close>


end
