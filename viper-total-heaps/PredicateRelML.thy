theory PredicateRelML
  imports Boogie_Lang.HelperML ExprWfRelML ExhaleRel ViperBoogieHelperML CPGHelperML PredicateRel ExhaleRelML InhaleRelML
begin


ML \<open>

val Rmsg' = run_and_print_if_fail_2_tac'

fun atomic_exhale_pred_acc_in_unfold_tac ctxt (info: basic_stmt_rel_info) (no_def_checks_tac_opt: (Proof.context -> basic_stmt_rel_info -> int -> tactic) option) exh_pred_acc_hint =
    case exh_pred_acc_hint of
      PredAccExhHint (exp_wf_rel_info, exp_rel_info, lookup_aux_var_ty_thm, lookup_aux_var_state_rel_thm, exp_rel_perm_access_thm) =>
        (* (SUBGOAL (fn (t,_) => raise TERM ("UnfoldExhField breakpoint", [t]))) THEN' *)
        (Rmsg' "UnfoldExhPred 1" (resolve_tac ctxt @{thms unfold_exhale_pred_rel}) ctxt) THEN'
          (Rmsg' "UnfoldExhPred wf args list simp" (simp_only_tac @{thms append_Cons append_Nil} ctxt) ctxt) THEN'
          (Rmsg' "UnfoldExhPred wf subexpressions" (exps_wf_rel_tac info exp_wf_rel_info exp_rel_info ctxt no_def_checks_tac_opt 2) ctxt) THEN'   
          (Rmsg' "UnfoldExhPred unfold current bigblock" (rewrite_rel_general_tac ctxt) ctxt) THEN'     
          (Rmsg' "UnfoldExhPred 2 propagate" (resolve_tac ctxt @{thms rel_propagate_pre_2}) ctxt) THEN'
          (Rmsg' "UnfoldExhPred 3 propagate" (resolve_tac ctxt @{thms red_ast_bpl_relI}) ctxt) THEN'
          (store_temporary_perm_pred_exh_tac ctxt info exp_rel_info lookup_aux_var_ty_thm) THEN'
          (prove_perm_non_negative_exh_tac ctxt info lookup_aux_var_state_rel_thm) THEN'
          (prove_sufficient_perm_tac ctxt info exp_rel_info lookup_aux_var_state_rel_thm exp_rel_perm_access_thm) THEN'
          (upd_exhale_field_acc_tac ctxt info exp_rel_info)
    | _ => error("only support PredAccExhHint")

fun pred_unfold_tac ctxt (inhale_info: atomic_inhale_rel_hint inhale_rel_info) (exhale_info: atomic_exhale_rel_hint exhale_rel_info) (basic_info : basic_stmt_rel_info) atomic_exhale_hint inhale_hint =
  (SUBGOAL (fn (t,_) => raise TERM ("Unfold breakpoint", [t]))) THEN'
  (Rmsg' "Unfold Start" (resolve_tac ctxt @{thms unfold_stmt_rel}) ctxt) THEN'
  (Rmsg' "Unfold PredDecl Lookup" (assm_full_simp_solved_with_thms_tac [#vpr_prog_def_thm basic_info] ctxt) ctxt) THEN'
  (Rmsg' "Unfold PredBody Lookup" (assm_full_simp_solved_with_thms_tac [#vpr_prog_def_thm basic_info, @{thm predicate_decl.defs(1)}] ctxt) ctxt) THEN'
  (atomic_exhale_pred_acc_in_unfold_tac ctxt basic_info (#no_def_checks_tac_opt exhale_info) atomic_exhale_hint) THEN'
  (SUBGOAL (fn (t,_) => raise TERM ("Unfold breakpoint", [t])))

\<close>


end
