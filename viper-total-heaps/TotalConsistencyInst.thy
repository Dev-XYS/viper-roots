theory TotalConsistencyInst
  imports TotalSemantics TotalIntConsPreservation TotalExtConsPreservation
begin


subsection \<open>Internal Consistency Wellfoundness\<close>

lemma mono_prop_downward_ord_consistent_internal_total_full:
  shows "mono_prop_downward_ord consistent_internal_total_full"
  unfolding mono_prop_downward_ord_def
proof standard+
  fix \<omega>\<^sub>1 \<omega>\<^sub>2 :: "('a,'b) full_total_state_scheme"
  assume *: "\<omega>\<^sub>1 \<le> \<omega>\<^sub>2 \<and> consistent_internal_total_full \<omega>\<^sub>2"
  note le = this[THEN conjunct1, unfolded less_eq_full_total_state_ext_def]
  show "consistent_internal_total_full \<omega>\<^sub>1"
    unfolding consistent_internal_total_full_def
    apply (intro conjI)
     apply (meson * consistent_internal_total_full_def intcons_total_mono_prop_downward le mono_prop_downward_def total_state_greater_equiv)
    by (metis (mono_tags, opaque_lifting) * consistent_internal_total_full_def domD domI intcons_total_mono_prop_downward le mono_prop_downward_def total_state_greater_equiv)
qed


lemma wf_total_consistency_internal:
  assumes "ctxt_pred_syn_wf ctxt"
      and "ctxt_pred_self_framing_sat ctxt"
    shows "wf_total_consistency ctxt consistent_internal_total_full consistent_internal_total"
  unfolding wf_total_consistency_def
  apply (intro conjI)
           apply (rule intcons_total_full_mono_prop_downward)
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
