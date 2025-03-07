theory TotalConsistencyInst
  imports TotalSemantics TotalIntConsPreservation TotalExtConsPreservation
begin


subsection \<open>Internal Consistency Wellfoundness\<close>

lemma mono_prop_downward_ord_consistent_internal_total_full:
  shows "mono_prop_downward_ord consistent_internal_total_full"
  sorry


lemma wf_total_consistency_internal:
  assumes "ctxt_wf_pred ctxt"
      and "ctxt_pred_self_framing ctxt"
    shows "wf_total_consistency ctxt consistent_internal_total_full consistent_internal_total"
  unfolding wf_total_consistency_def
  apply (intro conjI)
           apply (rule intcons_mono_prop_downward)
          apply (simp add: intcons_empty is_empty_total_full_def)
  using intcons_preserved_by_red_stmt
         apply blast
        apply (simp add: intcons_preserved_by_update_store)
  using consistent_internal_total_full_def
       apply blast
  using extcons_preserved_by_red_stmt
      apply blast
  subgoal
    unfolding consistent_internal_total_def consistent_internal_def wf_mask_simple_def
    by (metis get_mh_total.simps mh_le_nm_loc_sum order_trans)
  using unfold_preserves_internal_consistency_total
    apply blast
  by fact+


end
