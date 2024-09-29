theory TotalConsistencyInst
  imports TotalSemantics TotalInternalConsistency
begin


subsection \<open>Internal Consistency Wellfoundness\<close>

lemma wf_total_consistency_internal: "wf_total_consistency ctxt consistent_internal_total_full consistent_internal_total"
  sorry


subsection \<open>Internal consistency subsumes valid heap mask\<close>

lemma intcons_implies_valid_heap_mask:
  assumes "consistent_internal_total \<phi>"
  shows "valid_heap_mask (get_mh_total \<phi>)"
  sorry


end
