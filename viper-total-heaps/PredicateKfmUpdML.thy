theory PredicateKfmUpdML
imports Boogie_Lang.HelperML ExprWfRelML TotalViperSimulation.ExhaleRel ViperBoogieHelperML CPGHelperML
        TotalViperSimulation.PredicateRel ExhaleRelML InhaleRelML
begin

text \<open>This theory is a working pad for the automation that discharges the known-folded permission
      mask update step of a \<^const>\<open>Fold\<close> statement (i.e. the \<open>StepKFUpdate\<close> premise of
      @{thm fold_stmt_rel}). Eventually this should be moved into the \<open>TotalViperSimulation\<close>
      session (e.g. next to @{thm fold_knownfolded_acc_upd_rel} in \<open>PredicateRel.thy\<close>) and the ML
      code should be moved into \<open>PredicateRelML.thy\<close>.\<close>

subsection \<open>Bridging lemma\<close>

text \<open>@{const pred_kfm_sat_premise} is stated for different shapes of the definedness state
      argument, depending on where in the recursive known-folded mask update proof one currently is:
        \<^item> \<open>None\<close>: used at the very top of the recursion (this is what \<^const>\<open>Fold\<close>'s statement rule,
          i.e. @{thm fold_stmt_rel}, requires) and for the left disjunct of a \<open>Star\<close> assertion
          (@{thm fold_knownfolded_star_upd_rel}).
        \<^item> \<open>Some \<omega>def\<close> for some fixed (schematic) \<open>\<omega>def\<close>: used everywhere once \<open>\<omega>def\<close> has been fixed
          once (e.g. @{thm fold_knownfolded_pred_upd_rel}).
        \<^item> \<open>\<exists>\<omega>def. \<dots> (Some \<omega>def) \<dots>\<close>: used for the right disjunct of a \<open>Star\<close> assertion and for the
          the right-hand side of an \<open>Imp\<close> assertion (@{thm fold_knownfolded_imp_upd_rel}), since in
          these cases no single \<open>\<omega>def\<close> can be fixed ahead of time (it depends on the concrete
          decomposition of the enclosing exhale).
      Converting an \<open>\<exists>\<omega>def. \<dots> (Some \<omega>def) \<dots>\<close> obligation into a fixed \<open>Some \<omega>def\<close> one (so that the
      dispatch on the assertion structure below can proceed uniformly) is always sound, and is done
      by the following lemma. Note that there is currently \<^emph>\<open>no\<close> way to convert a \<open>None\<close> obligation
      into a \<open>Some \<omega>def\<close>/\<open>\<exists>\<omega>def. \<dots>\<close> one: the natural candidate lemma for this
      (\<open>red_pure_exps_total ctxt None es \<omega> (Some vs) \<Longrightarrow> \<exists>\<omega>0. red_pure_exps_total ctxt (Some \<omega>0) es \<omega> (Some vs)\<close>),
      i.e. \<open>evals_with_None_exists_\<omega>def\<close> in \<open>TotalSemanticsProperties.thy\<close>, is only stated but not
      actually proved there (its proof ends in \<open>oops\<close>). As a result, the tactic below can only
      automate the known-folded mask update for a \<open>Star\<close> assertion when its \<^emph>\<open>left\<close> operand is
      atomic (\<open>Acc\<close> or \<open>AccPredicate\<close>) -- a compound (\<open>Star\<close>/\<open>Imp\<close>) left operand would need exactly
      this missing lemma.\<close>

lemma kfm_upd_rel_exists_some_intro:
  assumes StepSome: "\<And>\<omega>def. rel_general (\<lambda>\<omega> ns. R \<omega> ns \<and> pred_kfm_sat_premise ctxt_vpr pid (Some \<omega>def) e_args_vpr v_args_vpr A \<omega>)
                                R' (=) (\<lambda>_. False) P ctxt_bpl \<gamma> \<gamma>'"
    shows "rel_general (\<lambda>\<omega> ns. R \<omega> ns \<and> (\<exists>\<omega>def. pred_kfm_sat_premise ctxt_vpr pid (Some \<omega>def) e_args_vpr v_args_vpr A \<omega>))
                                R' (=) (\<lambda>_. False) P ctxt_bpl \<gamma> \<gamma>'"
proof (rule rel_intro_no_fail)
  fix \<omega> ns \<omega>'
  assume "R \<omega> ns \<and> (\<exists>\<omega>def. pred_kfm_sat_premise ctxt_vpr pid (Some \<omega>def) e_args_vpr v_args_vpr A \<omega>)" and "\<omega> = \<omega>'"
  then obtain \<omega>def where "R \<omega> ns" and "pred_kfm_sat_premise ctxt_vpr pid (Some \<omega>def) e_args_vpr v_args_vpr A \<omega>"
    by blast
  thus "\<exists>ns'. red_ast_bpl P ctxt_bpl (\<gamma>, Normal ns) (\<gamma>', Normal ns') \<and> R' \<omega>' ns'"
    using rel_success_elim[OF StepSome[of \<omega>def]] \<open>\<omega> = \<omega>'\<close>
    by blast
qed

subsection \<open>Tactic\<close>

ML \<open>

val Rmsg' = run_and_print_if_fail_2_tac'

(* Recursively searches a term for an application of \<^const>\<open>pred_kfm_sat_premise\<close> and, if found,
   returns its definedness-state argument (3rd argument) together with its assertion argument
   (6th argument). *)
fun find_pred_kfm_sat_premise_args (t : term) : (term * term) option =
  case t of
    Const (@{const_name pred_kfm_sat_premise}, _) $ _ $ _ $ wdef $ _ $ _ $ a $ _ => SOME (wdef, a)
  | t1 $ t2 =>
      (case find_pred_kfm_sat_premise_args t1 of
         SOME r => SOME r
       | NONE => find_pred_kfm_sat_premise_args t2)
  | Abs (_, _, body) => find_pred_kfm_sat_premise_args body
  | _ => NONE

(* Checks whether the term contains a subterm of the shape
   \<open>\<exists>\<omega>def. pred_kfm_sat_premise \<dots> (Some \<omega>def) \<dots>\<close>, i.e. an existential quantifier directly wrapping
   a \<^const>\<open>pred_kfm_sat_premise\<close> application (as opposed to one that is already resolved to a fixed
   \<open>\<omega>def\<close>). *)
fun contains_ex_wrapped_pred_kfm (t : term) : bool =
  case t of
    Const (@{const_name Ex}, _) $ Abs (_, _, body) =>
      (case find_pred_kfm_sat_premise_args body of
         SOME _ => true
       | NONE => contains_ex_wrapped_pred_kfm body)
  | t1 $ t2 => contains_ex_wrapped_pred_kfm t1 orelse contains_ex_wrapped_pred_kfm t2
  | Abs (_, _, body) => contains_ex_wrapped_pred_kfm body
  | _ => false

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
fun upd_kfm_field_acc_tac ctxt (info: basic_stmt_rel_info) exp_rel_info =
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
  (Rmsg' "kfm upd field acc PlocRel" (prove_ploc_sm_rel' ctxt info exp_rel_info) ctxt) THEN'
  (Rmsg' "kfm upd field acc RefExpRel" (exp_rel_tac exp_rel_info ctxt |> SOLVED') ctxt) THEN'
  (Rmsg' "kfm upd field acc FieldRelSingle" ((#field_rel_single_tac info) ctxt) ctxt)

(* Main entry point: discharges a goal of the shape
     \<open>rel_general (\<lambda>\<omega> ns. R \<omega> ns \<and> X) R' (=) (\<lambda>_. False) P ctxt_bpl \<gamma> \<gamma>'\<close>
   where \<open>X\<close> is one of the three shapes described above the bridging lemmas, by dispatching on the
   structure of the assertion embedded in \<open>X\<close> (\<open>Atomic (Acc \<dots>)\<close>, \<open>Star\<close>, \<open>Imp\<close>, or
   \<open>Atomic (AccPredicate \<dots>)\<close> for a nested folded predicate, which is not yet automated). *)
fun kfm_upd_atomic_tac ctxt (info: basic_stmt_rel_info) exp_rel_info a i =
  case a of
    Const (@{const_name Atomic}, _) $ (Const (@{const_name Acc}, _) $ _ $ _ $ _) =>
      upd_kfm_field_acc_tac ctxt info exp_rel_info i
  | Const (@{const_name Atomic}, _) $ (Const (@{const_name AccPredicate}, _) $ _ $ _ $ _) =>
      error ("kfm_upd_rel_tac: known-folded mask update for a nested folded predicate " ^
             "access (AccPredicate) is not yet automated; see fold_knownfolded_pred_upd_rel " ^
             "and the manual proof in relational_proof_foo.thy for how to discharge this case by hand")
  | _ => raise TERM ("kfm_upd_rel_tac: unsupported assertion structure for known-folded mask update", [a])

(* Normalizes the assertion embedded in the goal (e.g. unfolds \<^const>\<open>substitute_args_assertion\<close>
   and \<^const>\<open>syntactic_mult\<close>, which wrap the predicate body as it comes out of @{thm fold_stmt_rel})
   without unfolding the (co-)domain of the known-folded mask itself, which would defeat the
   structural dispatch below. *)
fun kfm_upd_normalize_tac ctxt =
  asm_full_simp_tac
    (ctxt delsimps @{thms get_fnm_total_full.simps get_mh_nm.simps get_mp_nm.simps get_hh_total_full.simps})

fun kfm_upd_rel_tac ctxt (info: basic_stmt_rel_info) exp_rel_info : int -> tactic =
  (Rmsg' "kfm upd normalize assertion" (kfm_upd_normalize_tac ctxt) ctxt) THEN'
  SUBGOAL (fn (t, i) =>
    let val concl = Logic.strip_assums_concl t in
      if contains_ex_wrapped_pred_kfm concl then
        (Rmsg' "kfm upd exists-some intro" (resolve_tac ctxt @{thms kfm_upd_rel_exists_some_intro}) ctxt THEN'
         kfm_upd_rel_tac ctxt info exp_rel_info) i
      else
        case find_pred_kfm_sat_premise_args concl of
          NONE => raise TERM ("kfm_upd_rel_tac: could not locate pred_kfm_sat_premise in goal", [t])
        | SOME (wdef, a) =>
            (case wdef of
               Const (@{const_name None}, _) =>
                 (* No proven lemma converts a \<open>None\<close> obligation into a \<open>Some \<omega>def\<close>-based one (see the
                    comment above kfm_upd_rel_exists_some_intro), so only the assertion shapes that are
                    themselves stated with \<open>None\<close> (the atomic ones) can be discharged here. *)
                 kfm_upd_atomic_tac ctxt info exp_rel_info a i
             | _ =>
                (case a of
                   Const (@{const_name Star}, _) $ _ $ _ =>
                     (Rmsg' "kfm upd Star rule" (resolve_tac ctxt @{thms fold_knownfolded_star_upd_rel}) ctxt THEN'
                      (Rmsg' "kfm upd Star CtxtPredWf" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
                      (kfm_upd_rel_tac ctxt info exp_rel_info) THEN'
                      (kfm_upd_rel_tac ctxt info exp_rel_info)) i
                 | Const (@{const_name "assert.Imp"}, _) $ _ $ _ =>
                     (Rmsg' "kfm upd Imp rule" (resolve_tac ctxt @{thms fold_knownfolded_imp_upd_rel}) ctxt THEN'
                      (Rmsg' "kfm upd Imp StateRelIn" (simp_then_if_not_solved_blast_tac ctxt |> SOLVED') ctxt) THEN'
                      (Rmsg' "kfm upd Imp StateRelOut" (simp_then_if_not_solved_blast_tac ctxt |> SOLVED') ctxt) THEN'
                      (Rmsg' "kfm upd Imp HeapVarDefSame" (assm_full_simp_solved_with_thms_tac [#tr_def_thm info] ctxt) ctxt) THEN'
                      (Rmsg' "kfm upd Imp ExpSyntax" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
                      (Rmsg' "kfm upd Imp TyInterpEq" (assm_full_simp_solved_tac ctxt) ctxt) THEN'
                      (Rmsg' "kfm upd Imp CondExpRel" (exp_rel_tac exp_rel_info ctxt |> SOLVED') ctxt) THEN'
                      (kfm_upd_rel_tac ctxt info exp_rel_info)) i
                 | _ => kfm_upd_atomic_tac ctxt info exp_rel_info a i))
    end)

\<close>

end
