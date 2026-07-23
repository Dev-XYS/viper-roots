theory PredExhaleAssmsHelper
imports TotalViperSimulation.ExhaleRel
begin

text \<open>Controlled projection out of \<^const>\<open>exhale_pred_acc_rel_assms\<close>'s third conjunct, mirroring
      \<open>exhale_pred_acc_rel_assms_args_eval\<close> (\<open>Simulation/ExhaleRel.thy\<close>) for the first conjunct.
      Used by \<open>prove_ploc_reduce\<close> (\<open>CPGHelperML.thy\<close>) to discharge \<open>exp_result_predicate_loc\<close>'s
      \<open>ArgsWellTy\<close> premise via a plain \<open>resolve_tac\<close> against a fixed theorem instead of
      \<open>fastforce\<close>/\<open>blast\<close> searching over the unfolded conjunction/disjunction soup at
      tactic-execution time.\<close>

lemma exhale_pred_acc_rel_assms_ty_correct:
  assumes "exhale_pred_acc_rel_assms ctxt pred_id e_args e_p v_args v_p \<omega>0 \<omega>"
  shows "pred_ty_correct_premise ctxt pred_id v_args"
  using assms
  unfolding exhale_pred_acc_rel_assms_def
  by (elim conjE)

end
