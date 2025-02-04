theory TotalIntConsPreservation
  imports TotalInternalConsistency TotalSemantics
begin


lemma intcons_preserved_by_red_stmt:
  assumes "consistent_internal (get_nm_total_full \<omega>)"
      and "red_stmt_total ctxt StateCons \<Lambda> stmt \<omega> (RNormal \<omega>')"
    shows "consistent_internal (get_nm_total_full \<omega>')"
  sorry

end
