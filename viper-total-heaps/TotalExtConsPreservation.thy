theory TotalExtConsPreservation
  imports TotalExtConsProps
begin


lemma extcons_preserved_by_mh_change:
  assumes "consistent_external ctxt \<phi>"
  shows "consistent_external ctxt (upd_mh_total \<phi> mh')"
  sorry

lemma extcons_preserved_by_inhale_acc:
  assumes "consistent_external ctxt (get_total_full \<omega>)"
      and "\<omega>' \<in> inhale_perm_single StateCons \<omega> lh p_opt"
    shows "consistent_external ctxt (get_total_full \<omega>')"
  sorry

lemma extcons_preserved_by_red_stmt:
  assumes "consistent_external ctxt (get_total_full \<omega>)"
      and "red_stmt_total ctxt R \<Lambda> stmt \<omega> (RNormal \<omega>')"
    shows "consistent_external ctxt (get_total_full \<omega>')"
  sorry

end
