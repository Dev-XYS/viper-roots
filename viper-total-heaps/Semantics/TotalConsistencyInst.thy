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


lemma rm_from_lpm_preserved_intcons:
  assumes ctxt_wf: "ctxt_pred_syn_wf ctxt"
      and extcons: "consistent_external ctxt (get_total_full \<omega>)"
      and "p \<le> get_mp_total_full \<omega> lp"
    shows "consistent_external ctxt (get_total_full (rm_from_lpm_total_full \<omega> lp p))"
  apply standard
  apply (rename_tac pid vs q nm')
  apply (case_tac "(pid,vs) = lp")
   defer
  using extcons[unfolded consistent_external.simps]
   apply simp
proof -
  fix pid vs q' nm'
  assume lpm': "Some (q',nm') = get_fnm_total (get_total_full (rm_from_lpm_total_full \<omega> lp p)) (pid,vs)"
     and "(pid, vs) = lp"
  then obtain q nm where lpm: "Some (q,nm) = get_fnm_total (get_total_full \<omega>) (pid,vs)"
    apply simp
    by (metis (no_types, opaque_lifting) lpm' get_fnm_total.simps get_fnm_total_full.simps rm_from_lpm_total_full_inverse)
  hence extcons_ploc: "consistent_external_wrt_ploc ctxt (get_total_full \<omega>\<lparr> get_nm_total := nm \<rparr>) (pid,vs) (Rep_posreal q)"
    using extcons[unfolded consistent_external.simps]
    by auto
  show "consistent_external_wrt_ploc ctxt
          (get_total_full (rm_from_lpm_total_full \<omega> lp p)\<lparr>get_nm_total := nm'\<rparr>) (pid,vs) (Rep_posreal q')"
  proof (cases "p \<ge> Rep_posreal q")
    case True
    hence "get_fnm_total (get_total_full (rm_from_lpm_total_full \<omega> lp p)) (pid,vs) = None"
      apply (cases "get_fnm_total_full \<omega> lp"; simp)
      using \<open>(pid, vs) = lp\<close> lpm
      by fastforce+
    then show ?thesis
      using lpm'
      by auto
  next
    case False
    have "nm' = (1 - p / Rep_posreal q) *\<^sub>s nm"
      using lpm lpm'
      apply (cases "get_fnm_total_full \<omega> lp"; simp)
       apply (simp add: \<open>(pid, vs) = lp\<close>)
      by (metis Some_Some_ifD \<open>(pid, vs) = lp\<close> fstI option.inject sndI)
    have "q' = Abs_posreal (Rep_posreal q - p)"
      using lpm lpm'
      apply (cases "get_fnm_total_full \<omega> lp"; simp)
       apply (simp add: \<open>(pid, vs) = lp\<close>)
      by (metis Some_Some_ifD \<open>(pid, vs) = lp\<close> fstI option.inject sndI)
    have "(1 - p / Rep_posreal q) * Rep_posreal q = Rep_posreal q - p / Rep_posreal q * Rep_posreal q"
      using False
      apply (simp add: preal_to_real)
      by (metis comm_monoid_mult_class.mult_1 divide_le_eq_1_pos eq_divide_eq left_diff_distrib less_eq_real_def linorder_le_cases prat_non_negative)
    hence *: "(1 - p / Rep_posreal q) * Rep_posreal q =
             Rep_posreal (Abs_posreal (Rep_posreal q - p))"
      apply (simp add: preal_to_real)
      using False PosReal.ppos.rep_eq gr_0_is_ppos less_eq_preal.rep_eq minus_preal.rep_eq posreal_to_preal(8) prat_non_negative
      by auto

    show ?thesis
      using fraction_consistent_external(1)[OF ctxt_wf extcons_ploc, of "1 - p / Rep_posreal q"]
      apply simp
      unfolding \<open>nm' = _\<close> \<open>q' = _\<close>
      using *
      by fastforce
  qed
qed


lemma wf_total_consistency_internal:
  assumes "ctxt_pred_syn_wf ctxt"
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
     apply (metis mono_prop_downward_ord_consistent_internal_total_full mono_prop_downward_ord_def rm_from_lpm_total_full_smaller)
  using assms(1) rm_from_lpm_preserved_intcons
  by blast


end
