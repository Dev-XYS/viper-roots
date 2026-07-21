theory PredicateKfmUpdML
imports Boogie_Lang.HelperML ExprWfRelML TotalViperSimulation.ExhaleRel ViperBoogieHelperML CPGHelperML
        TotalViperSimulation.PredicateRel ExhaleRelML InhaleRelML
begin




text \<open>This theory is a working pad for the automation that discharges the known-folded permission
      mask update step of a \<^const>\<open>Fold\<close> statement (i.e. the \<open>StepKFUpdate\<close> premise of
      @{thm fold_stmt_rel}). Eventually this should be moved into the \<open>TotalViperSimulation\<close>
      session (e.g. next to @{thm fold_knownfolded_acc_upd_rel} in \<open>PredicateRel.thy\<close>) and the ML
      code should be moved into \<open>PredicateRelML.thy\<close>.

      All of @{thm fold_stmt_rel}'s \<open>StepKFUpdate\<close>, @{thm fold_knownfolded_acc_upd_rel},
      @{thm fold_knownfolded_star_upd_rel}, @{thm fold_knownfolded_imp_upd_rel} and
      @{thm fold_knownfolded_pred_upd_rel} now uniformly use \<^const>\<open>pred_kfm_sat_premise\<close> with a
      definedness state of \<open>None\<close> (there is no need to thread a \<open>Some \<omega>def\<close> witness through the
      recursion: the predicate arguments \<open>e_args_vpr\<close> are fixed for the whole known-folded-mask
      update, and \<open>None\<close> can simply be reused at every recursive call), so the tactic below only
      ever has to dispatch on the structure of the assertion, without any conversion between
      different shapes of the definedness-state argument.\<close>

subsection \<open>Tactic\<close>

ML \<open>

val Rmsg' = run_and_print_if_fail_2_tac'

(* Recursively searches a term for an application of \<^const>\<open>pred_kfm_sat_premise\<close> and, if found,
   returns its assertion argument (6th argument). *)
fun find_pred_kfm_sat_premise_assertion (t : term) : term option =
  case t of
    Const (@{const_name pred_kfm_sat_premise}, _) $ _ $ _ $ _ $ _ $ _ $ a $ _ => SOME a
  | t1 $ t2 =>
      (case find_pred_kfm_sat_premise_assertion t1 of
         SOME r => SOME r
       | NONE => find_pred_kfm_sat_premise_assertion t2)
  | Abs (_, _, body) => find_pred_kfm_sat_premise_assertion body
  | _ => NONE

(* Proves goals of the form \<open>\<And>\<omega>. ctxt_vpr, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p) \<and> p > 0\<close> where \<open>e\<close> is a
   closed (constant) permission expression built up from literals via arithmetic operators
   (this is the shape of the \<open>PermPosConstExpr\<close> premise of @{thm fold_knownfolded_acc_upd_rel} and
   @{thm fold_knownfolded_pred_upd_rel}). *)
(* TODO(generalize): this currently only handles a permission expression of the shape
   \<open>Binop (ELit _) bop (Binop (ELit _) bop' (ELit _))\<close> (i.e. exactly the nesting depth that
   arises from a \<open>1/1\<close> literal permission multiplied by the \<open>Fold\<close> statement's own permission
   amount, as in @{const fold_stmt_rel}'s \<open>syntactic_mult\<close>), by literally replaying the
   corresponding \<open>apply\<close> script. A generic version that recurses on arbitrary nesting via
   \<open>REPEAT_ALL_NEW (FIRST' [resolve_tac \<dots>, simp \<dots>])\<close> (or an explicit ML recursion using
   \<open>ORELSE\<close>) was tried but either left the \<open>eval_binop\<close> side-condition with an uninstantiated
   schematic permission value, or diverged; revisit this once there is a broader set of examples
   to test a generic solution against. *)
fun prove_vpr_const_perm_eval_tac ctxt =
  resolve_tac ctxt @{thms TotalExpressions.RedBinop} THEN'
  resolve_tac ctxt @{thms TotalExpressions.RedLit} THEN'
  resolve_tac ctxt @{thms TotalExpressions.RedBinop} THEN'
  resolve_tac ctxt @{thms TotalExpressions.RedLit} THEN'
  resolve_tac ctxt @{thms TotalExpressions.RedLit} THEN'
  assm_full_simp_solved_tac ctxt THEN'
  assm_full_simp_solved_tac ctxt THEN'
  assm_full_simp_solved_tac ctxt THEN'
  assm_full_simp_solved_tac ctxt

(* Discharges the assumptions of @{thm fold_knownfolded_acc_upd_rel} once the rule has been applied
   to a goal whose assertion is \<open>Atomic (Acc e_r_vpr f (PureExp e_p_vpr))\<close>. Mirrors the manual proof
   in relational_proof_foo.thy and the structure of upd_exhale_field_acc_tac in ExhaleRelML.thy. *)
fun upd_kfm_field_acc_tac ctxt (info: basic_stmt_rel_info) pred_name exp_rel_info =
  (Rmsg' "kfm upd field acc rule" (resolve_tac ctxt @{thms fold_knownfolded_acc_upd_rel}) ctxt) THEN'
  (Rmsg' "kfm upd field acc StateRelIn" (simp_then_if_not_solved_blast_tac ctxt |> SOLVED') ctxt) THEN'
  (Rmsg' "kfm upd field acc StateRelOut" (simp_then_if_not_solved_blast_tac ctxt |> SOLVED') ctxt) THEN'
  (Rmsg' "kfm upd field acc HeapVarDefSame" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "kfm upd field acc ExpSyntax" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
  (Rmsg' "kfm upd field acc TyInterpEq" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
  (Rmsg' "kfm upd field acc NullConst" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "kfm upd field acc HeapVar" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "kfm upd field acc PermPosConstExpr conjI" (resolve_tac ctxt @{thms conjI}) ctxt) THEN'
  (Rmsg' "kfm upd field acc PermPosConstExpr eval" (prove_vpr_const_perm_eval_tac ctxt |> SOLVED') ctxt) THEN'
  (Rmsg' "kfm upd field acc PermPosConstExpr pos" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
  (Rmsg' "kfm upd field acc HeapUpdateWf"
     (resolve_tac ctxt [@{thm heap_update_wf_concrete} OF [#ctxt_wf_thm info, #wf_ty_repr_thm info]] THEN'
      assm_full_simp_solved_tac ctxt) ctxt) THEN'
  (Rmsg' "kfm upd field acc HeapReadWf"
     (resolve_tac ctxt [@{thm heap_wf_concrete} OF [#ctxt_wf_thm info, #wf_ty_repr_thm info]] THEN'
      assm_full_simp_solved_tac ctxt) ctxt) THEN'
  (Rmsg' "kfm upd field acc PMaskUpdateWf"
     (resolve_tac ctxt [@{thm pmask_update_wf_concrete} OF [#ctxt_wf_thm info, #wf_ty_repr_thm info]] THEN'
      assm_full_simp_solved_tac ctxt) ctxt) THEN'
  (Rmsg' "kfm upd field acc KnownFoldedUpdBpl"
     (assm_full_simp_solved_with_thms_tac [@{thm update_heap_concrete_def}, #tr_def_thm info, #ty_repr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "kfm upd field acc KnownFoldedSetBpl"
     (assm_full_simp_solved_with_thms_tac [@{thm update_pmask_concrete_def}, #tr_def_thm info, #ty_repr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "kfm upd field acc KnownFoldedReadBpl"
     (assm_full_simp_solved_with_thms_tac [@{thm read_heap_concrete_def}, #tr_def_thm info, #ty_repr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "kfm upd field acc PredType" (assm_full_simp_solved_with_thms_tac [#ty_repr_def_thm info] ctxt) ctxt) THEN'
  (Rmsg' "kfm upd field acc PlocRel" (prove_ploc_sm_rel' ctxt info pred_name exp_rel_info) ctxt) THEN'
  (Rmsg' "kfm upd field acc RefExpRel" (exp_rel_tac exp_rel_info ctxt |> SOLVED') ctxt) THEN'
  (Rmsg' "kfm upd field acc FieldRelSingle" ((#field_rel_single_tac info) ctxt) ctxt)

(* Normalizes the assertion embedded in the goal (e.g. unfolds \<^const>\<open>substitute_args_assertion\<close>
   and \<^const>\<open>syntactic_mult\<close>, which wrap the predicate body as it comes out of @{thm fold_stmt_rel})
   without unfolding the (co-)domain of the known-folded mask itself, which would defeat the
   structural dispatch below. *)
fun kfm_upd_normalize_tac ctxt =
  asm_full_simp_tac
    (ctxt delsimps @{thms get_fnm_total_full.simps get_mh_nm.simps get_mp_nm.simps get_hh_total_full.simps})

(* Main entry point: discharges a goal of the shape
     \<open>rel_general (\<lambda>\<omega> ns. R \<omega> ns \<and> pred_kfm_sat_premise ctxt_vpr pid None e_args_vpr v_args_vpr A \<omega>)
                  R' (=) (\<lambda>_. False) P ctxt_bpl \<gamma> \<gamma>'\<close>
   by dispatching on the structure of the assertion \<open>A\<close> (\<open>Atomic (Acc \<dots>)\<close>, \<open>Star\<close>, \<open>Imp\<close>, or
   \<open>Atomic (AccPredicate \<dots>)\<close> for a nested folded predicate, which is not yet automated). *)
fun kfm_upd_rel_tac ctxt (info: basic_stmt_rel_info) pred_name exp_rel_info : int -> tactic =
  (Rmsg' "kfm upd normalize assertion" (kfm_upd_normalize_tac ctxt) ctxt) THEN'
  SUBGOAL (fn (t, i) =>
    case find_pred_kfm_sat_premise_assertion (Logic.strip_assums_concl t) of
      NONE => raise TERM ("kfm_upd_rel_tac: could not locate pred_kfm_sat_premise in goal", [t])
    | SOME a =>
        (case a of
           Const (@{const_name Star}, _) $ _ $ _ =>
             (Rmsg' "kfm upd Star rule" (resolve_tac ctxt @{thms fold_knownfolded_star_upd_rel'}) ctxt THEN'
              (Rmsg' "kfm upd Star CtxtPredWf" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
              (kfm_upd_rel_tac ctxt info pred_name exp_rel_info) THEN'
              (kfm_upd_rel_tac ctxt info pred_name exp_rel_info)) i
         | Const (@{const_name "assert.Imp"}, _) $ _ $ _ =>
             (Rmsg' "kfm upd Imp rule" (resolve_tac ctxt @{thms fold_knownfolded_imp_upd_rel}) ctxt THEN'
              (Rmsg' "kfm upd Imp StateRelIn" (simp_then_if_not_solved_blast_tac ctxt |> SOLVED') ctxt) THEN'
              (Rmsg' "kfm upd Imp StateRelOut" (simp_then_if_not_solved_blast_tac ctxt |> SOLVED') ctxt) THEN'
              (Rmsg' "kfm upd Imp HeapVarDefSame" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
              (Rmsg' "kfm upd Imp ExpSyntax" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
              (Rmsg' "kfm upd Imp TyInterpEq" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
              (Rmsg' "kfm upd Imp CondExpRel" (exp_rel_tac exp_rel_info ctxt |> SOLVED') ctxt) THEN'
              (kfm_upd_rel_tac ctxt info pred_name exp_rel_info)) i
         | Const (@{const_name Atomic}, _) $ (Const (@{const_name Acc}, _) $ _ $ _ $ _) =>
             upd_kfm_field_acc_tac ctxt info pred_name exp_rel_info i
         | Const (@{const_name Atomic}, _) $ (Const (@{const_name AccPredicate}, _) $ _ $ _ $ _) =>
             error ("kfm_upd_rel_tac: known-folded mask update for a nested folded predicate " ^
                    "access (AccPredicate) is not yet automated; see fold_knownfolded_pred_upd_rel " ^
                    "and the manual proof in relational_proof_foo.thy for how to discharge this case by hand")
         | _ => raise TERM ("kfm_upd_rel_tac: unsupported assertion structure for known-folded mask update", [a])))

\<close>

end
