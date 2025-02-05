theory TotalConsistencyProperties
  imports TotalSemantics TotalInternalConsistency TotalSemanticsProperties TotalFraming
begin


subsection \<open>Exhale statement preserves external consistency.\<close>

lemma exhale_preserves_hh:
  assumes "red_exhale ctxt R \<omega> A \<omega> (RNormal \<omega>')"
  shows "get_hh_total_full \<omega> = get_hh_total_full \<omega>'"
  sorry


end
