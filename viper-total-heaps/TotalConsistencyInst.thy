theory TotalConsistencyInst
  imports TotalSemantics TotalIntConsPreservation
begin


subsection \<open>Internal Consistency Wellfoundness\<close>

lemma wf_total_consistency_internal: "wf_total_consistency ctxt consistent_internal_total_full consistent_internal_total"
  unfolding wf_total_consistency_def
  apply (intro conjI)
      apply (rule intcons_mono_prop_downward)
     apply (simp add: intcons_empty is_empty_total_full_def)
  using intcons_preserved_by_red_stmt
    apply blast
   apply (simp add: intcons_preserved_by_update_store)
  using consistent_internal_total_full_def
  by blast


end
