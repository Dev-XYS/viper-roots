theory PredicateRelML
  imports Boogie_Lang.HelperML ExprWfRelML ExhaleRel ViperBoogieHelperML CPGHelperML PredicateRel ExhaleRelML InhaleRelML
begin


subsection \<open>Unfold\<close>


ML \<open>

val Rmsg' = run_and_print_if_fail_2_tac'

fun atomic_exhale_pred_acc_in_unfold_tac ctxt (info: basic_stmt_rel_info) (no_def_checks_tac_opt: (Proof.context -> basic_stmt_rel_info -> int -> tactic) option) exh_pred_acc_hint =
    case exh_pred_acc_hint of
      PredAccExhHint (exp_wf_rel_info, exp_rel_info, lookup_aux_var_ty_thm, lookup_aux_var_state_rel_thm, exp_rel_perm_access_thm) =>
        (Rmsg' "UnfoldExhPred 1" (resolve_tac ctxt @{thms unfold_exhale_pred_rel}) ctxt) THEN'
        (Rmsg' "UnfoldExhPred wf args list simp" (simp_only_tac @{thms append_Cons append_Nil} ctxt) ctxt) THEN'
        (Rmsg' "UnfoldExhPred wf subexpressions" (exps_wf_rel_tac info exp_wf_rel_info exp_rel_info ctxt no_def_checks_tac_opt 2) ctxt) THEN'
        (Rmsg' "UnfoldExhPred 2 propagate" (resolve_tac ctxt @{thms rel_propagate_pre_2}) ctxt) THEN'
        (Rmsg' "UnfoldExhPred 3 propagate" (resolve_tac ctxt @{thms red_ast_bpl_relI}) ctxt) THEN'
        (store_temporary_perm_pred_exh_tac ctxt info exp_rel_info lookup_aux_var_ty_thm) THEN'
        (prove_perm_non_negative_pred_exh_tac ctxt info lookup_aux_var_state_rel_thm) THEN'
        (prove_sufficient_perm_pred_tac ctxt info exp_rel_info lookup_aux_var_state_rel_thm exp_rel_perm_access_thm) THEN'
        (upd_exhale_pred_acc_tac ctxt info exp_rel_info)
    | _ => error("Unfold only supports PredAccExhHint")


fun pred_unfold_tac ctxt (inhale_info: atomic_inhale_rel_hint inhale_rel_info) (exhale_info: atomic_exhale_rel_hint exhale_rel_info) (basic_info : basic_stmt_rel_info) atomic_exhale_hint inhale_hint =
  (Rmsg' "unfold stmt rule" (resolve_tac ctxt @{thms unfold_stmt_rel}) ctxt) THEN'
  (Rmsg' "unfold stmt PredDecl" (assm_full_simp_solved_with_thms_tac [#vpr_prog_def_thm basic_info] ctxt) ctxt) THEN'
  (Rmsg' "unfold stmt PredArgs" (assm_full_simp_solved_with_thms_tac @{thms predicate_decl.defs} ctxt) ctxt) THEN'
  (Rmsg' "unfold stmt PredBody" (assm_full_simp_solved_with_thms_tac @{thms predicate_decl.defs} ctxt) ctxt) THEN'
  (Rmsg' "unfold stmt CtxtPredWf" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "unfold stmt CtxtPredSF" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "unfold stmt WfCons" (resolve_tac ctxt [#consistency_wf_thm basic_info]) ctxt) THEN'
  (Rmsg' "unfold stmt StateRelImpliesIntCons" (assm_full_simp_solved_with_thms_tac [#tr_def_thm basic_info, @{thm default_state_rel_options_def}, @{thm state_rel_consistent}] ctxt) ctxt) THEN'

  (Rmsg' "unfold stmt StateRelImpliesExtCons 1" (resolve_tac ctxt @{thms extcons_fun_interp_irrelevant'}) ctxt) THEN'
  (Rmsg' "unfold stmt StateRelImpliesExtCons 2" (forward_tac ctxt @{thms state_rel_consistent}) ctxt) THEN'
  (Rmsg' "unfold stmt StateRelImpliesExtCons 3" (assm_full_simp_solved_with_thms_tac [@{thm default_state_rel_options_def}, #tr_def_thm basic_info] ctxt) ctxt) THEN'
  (Rmsg' "unfold stmt StateRelImpliesExtCons 4" (assm_full_simp_solved_with_thms_tac [#ty_repr_def_thm basic_info] ctxt) ctxt) THEN'

  (Rmsg' "unfold stmt StateRelImpliesKFRel" (fastforce_tac ctxt @{thms state_rel_def state_rel0_def}) ctxt) THEN'

  (Rmsg' "unfold stmt StateRelWeakening" (eresolve_tac ctxt @{thms state_rel_kf_disable_consistency}) ctxt) THEN'

  (Rmsg' "unfold stmt ArgsRestriction" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "unfold stmt BodyNoUnfolding" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "unfold stmt PermSimp" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "unfold stmt PermPos" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'

  (Rmsg' "unfold stmt StepPermPos (always assert true)" (resolve_tac ctxt @{thms bpl_assert_true_is_skip}) ctxt) THEN'
  (Rmsg' "unfold stmt StepExhale" (atomic_exhale_pred_acc_in_unfold_tac ctxt basic_info (#no_def_checks_tac_opt exhale_info) atomic_exhale_hint) ctxt) THEN'
  (Rmsg' "unfold stmt simp synmult & subst" (asm_full_simp_tac ctxt) ctxt) THEN'
  (Rmsg' "unfold stmt StepInhale" (inhale_rel_tac ctxt inhale_info inhale_hint) ctxt) THEN'
  (SUBGOAL (fn (t,_) => raise TERM ("breakpoint working", [t])))

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


fun inhale_rel_pred_acc_upd_rel_tac' ctxt (info: basic_stmt_rel_info) exp_rel_info =
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
  (Rmsg' "inh pred acc upd PlocRel" (prove_ploc_rel' ctxt info exp_rel_info) ctxt) THEN'
  (Rmsg' "inh pred acc upd AbsInterpEq" (assm_full_simp_solved_with_thms_tac [#ty_repr_def_thm info, @{thm ty_repr_basic_def}] ctxt) ctxt) THEN'
  (Rmsg' "inh pred acc upd ProgEq" (simp_tac_with_thms [] ctxt) ctxt)


fun atomic_inhale_pred_acc_in_fold_tac ctxt (info: basic_stmt_rel_info) inh_pred_acc_hint =
  case inh_pred_acc_hint of
    PredicateAccInhHint (exp_wf_rel_info, exp_rel_info, lookup_aux_var_ty_thm, lookup_aux_var_state_rel_thm) =>
      (Rmsg' "InhPred (fold) unfold current bigblock?" (rewrite_rel_general_tac ctxt) ctxt) THEN'
      (Rmsg' "InhPred (fold) propagate (store perm)" (resolve_tac ctxt @{thms rel_propagate_pre}) ctxt) THEN'
      (Rmsg' "InhPred (fold) red_ast_bpl_relI" (resolve_tac ctxt @{thms red_ast_bpl_relI}) ctxt) THEN'
      (store_temporary_inh_perm_tac ctxt info exp_rel_info lookup_aux_var_ty_thm) THEN'
      (Rmsg' "InhPred (fold) perm non-neg (always true)" (resolve_tac ctxt @{thms bpl_assert_true_is_skip}) ctxt) THEN'
      (true_implies_true_tac ctxt) THEN'
      (Rmsg' "InhPred (fold) propagate (reset state rel)" (resolve_tac ctxt @{thms rel_propagate_post_3}) ctxt) THEN'
      (inhale_rel_pred_acc_upd_rel_tac' ctxt (info: basic_stmt_rel_info) exp_rel_info) THEN'
      (exhale_revert_state_relation ctxt info)
  | _ => error("Fold only supports PredicateAccInhHint")


fun pred_fold_tac ctxt exp_wf_rel_info exp_rel_info (inhale_info: atomic_inhale_rel_hint inhale_rel_info) (exhale_info: atomic_exhale_rel_hint exhale_rel_info) (basic_info : basic_stmt_rel_info) exhale_hint atomic_inhale_hint =
  (Rmsg' "fold stmt rule" (resolve_tac ctxt @{thms fold_stmt_rel}) ctxt) THEN'

  (Rmsg' "fold stmt PredDecl" (assm_full_simp_solved_with_thms_tac [#vpr_prog_def_thm basic_info] ctxt) ctxt) THEN'
  (Rmsg' "fold stmt PredArgs" (assm_full_simp_solved_with_thms_tac @{thms predicate_decl.defs} ctxt) ctxt) THEN'
  (Rmsg' "fold stmt PredBody" (assm_full_simp_solved_with_thms_tac @{thms predicate_decl.defs} ctxt) ctxt) THEN'
  (Rmsg' "fold stmt CtxtPredWf" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "fold stmt CtxtPredSF" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "fold stmt WfCons" (resolve_tac ctxt [#consistency_wf_thm basic_info]) ctxt) THEN'
  (Rmsg' "fold stmt StateRelImpliesIntCons" (assm_full_simp_solved_with_thms_tac [#tr_def_thm basic_info, @{thm default_state_rel_options_def}, @{thm state_rel_consistent}] ctxt) ctxt) THEN'

  (Rmsg' "fold stmt StateRelImpliesExtCons 1" (resolve_tac ctxt @{thms extcons_fun_interp_irrelevant'}) ctxt) THEN'
  (Rmsg' "fold stmt StateRelImpliesExtCons 2" (forward_tac ctxt @{thms state_rel_consistent}) ctxt) THEN'
  (Rmsg' "fold stmt StateRelImpliesExtCons 3" (assm_full_simp_solved_with_thms_tac [@{thm default_state_rel_options_def}, #tr_def_thm basic_info] ctxt) ctxt) THEN'
  (Rmsg' "fold stmt StateRelImpliesExtCons 4" (assm_full_simp_solved_with_thms_tac [#ty_repr_def_thm basic_info] ctxt) ctxt) THEN'

  (Rmsg' "fold stmt ArgsRestriction" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "fold stmt BodyNoUnfolding" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "fold stmt PermSimp" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "fold stmt PermPos" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'

  (Rmsg' "fold stmt wf args list simp" (simp_only_tac @{thms append_Cons append_Nil} ctxt) ctxt) THEN'
  (Rmsg' "fold stmt StepWfSubexp" (exps_wf_rel_tac basic_info exp_wf_rel_info exp_rel_info ctxt NONE 2) ctxt) THEN'
  (Rmsg' "fold stmt StepPermPos (always assert true)" (resolve_tac ctxt @{thms red_bpl_assert_true}) ctxt) THEN'
  (Rmsg' "fold stmt simp synmult" (simp_tac_with_thms [] ctxt) ctxt) THEN'

  (* (Rmsg' "fold stmt propagate state reset" (resolve_tac ctxt @{thms exhale_rel_propagate_post}) ctxt) THEN' *)
  (normal_exhale_rel_tac ctxt exhale_info exhale_hint) THEN'
  (* (Rmsg' "fold stmt state reset after exhale" (exhale_revert_state_relation ctxt basic_info) ctxt) THEN' *)

  (atomic_inhale_pred_acc_in_fold_tac ctxt basic_info atomic_inhale_hint) THEN'

  (Rmsg' "fold stmt good state after inhale propagate 1" (resolve_tac ctxt @{thms rel_propagate_pre_3_only_state_rel}) ctxt) THEN'
  (Rmsg' "fold stmt good state after inhale progress 1" ((progress_assume_good_state_rel_tac ctxt (#ctxt_wf_thm basic_info) (#tr_def_thm basic_info))) ctxt) THEN'
  (Rmsg' "fold stmt good state after inhale propagate 2" (resolve_tac ctxt @{thms rel_propagate_pre_3_only_state_rel}) ctxt) THEN'
  (Rmsg' "fold stmt good state after inhale progress 2" ((progress_assume_good_state_rel_tac ctxt (#ctxt_wf_thm basic_info) (#tr_def_thm basic_info))) ctxt) THEN'

  (SUBGOAL (fn (t,_) => raise TERM ("breakpoint head", [t]))) THEN'

  (Rmsg' "fold stmt test1" (resolve_tac ctxt @{thms rel_general_success_refl}) ctxt) THEN'
  (Rmsg' "fold stmt test2" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) THEN'
  (Rmsg' "fold stmt test3" (assm_full_simp_solved_with_thms_tac [] ctxt) ctxt) (* THEN'

  (Rmsg' "Progress Good State" ((progress_assume_good_state_rel_tac ctxt (#ctxt_wf_thm basic_info) (#tr_def_thm basic_info)) ORELSE' (progress_red_bpl_rel_tac ctxt)) ctxt)
  THEN' (SUBGOAL (fn (t,_) => raise TERM ("breakpoint head", [t]))) *)


fun exh_in_fold_no_def_checks_tac ctxt (info: basic_stmt_rel_info) : int -> tactic =
  (* (SUBGOAL (fn (t,_) => raise TERM ("breakpoint", [t]))) THEN' *)
  resolve_tac ctxt [ @{thm framing_subst_exprs_wf_rel} OF [ #consistency_down_mono_thm info ] ] THEN'
  blast_tac ctxt THEN'
  assm_full_simp_solved_tac ctxt THEN'
  assm_full_simp_solved_tac ctxt THEN'
  assm_full_simp_solved_tac ctxt

\<close>


end
