theory TotalConsistencyInst
  imports TotalSemantics TotalIntConsPreservation
begin


subsection \<open>Internal Consistency Wellfoundness\<close>

lemma wf_total_consistency_internal: "wf_total_consistency ctxt consistent_internal_total_full consistent_internal_total"
  unfolding wf_total_consistency_def
  apply (intro conjI)
  sorry


end
