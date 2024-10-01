theory TotalInternalConsistency
  imports NestedMaskProperties TotalFoldUnfold
begin


subsection \<open>New Internal Consistency\<close>

definition consistent_internal :: "'a nested_mask \<Rightarrow> bool" where
  "consistent_internal nm \<equiv> \<forall>loc. \<exists>s. s \<le> 1 \<and> nm_loc_sum loc nm s"


lemma shift_up_preserves_loc_sum:
  assumes "shift_up pred_id vs q nm nm'"
      and "nm_loc_sum loc nm s"
    shows "nm_loc_sum loc nm' s"
proof -
  from assms(1) obtain mh mp fnm pnm_opt p mp' fnm' nm'_sub where
    nm: "nm = NM mh mp fnm" and
    pnm_opt: "pnm_opt = fnm (pred_id,vs)" and
    "p = mp (pred_id,vs)" and
    "q \<le> p" and
    "q \<noteq> 0" and
    "mp' = mp( (pred_id,vs) := p - q )" and
    fnm': "fnm' = fnm( (pred_id,vs) := if p = q then None else ((p - q) / p) *\<^sub>s pnm_opt )" and
    nm_sub: "nm'_sub = NM mh mp' fnm'" and
    nm': "Some nm' = Some nm'_sub + (q / p) *\<^sub>s pnm_opt"
    by (blast elim: shift_up.cases)
  show ?thesis
  proof (cases pnm_opt)
    case None
    then show ?thesis
      by (smt (verit, ccfv_threshold) \<open>\<And>thesis. (\<And>mh mp fnm pnm_opt p mp' fnm' nm'_sub. \<lbrakk>nm = NM mh mp fnm; pnm_opt = fnm (pred_id, vs); p = mp (pred_id, vs); q \<le> p; q \<noteq> pos_perm_class.pnone; mp' = mp((pred_id, vs) := p - q); fnm' = fnm ((pred_id, vs) := if p = q then None else ((p - q) / p) *\<^sub>s pnm_opt); nm'_sub = NM mh mp' fnm'; Some nm' = Some nm'_sub + (q / p) *\<^sub>s pnm_opt\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> assms(2) fun_upd_triv get_fnm_nm.simps group_cancel.rule0 nm nm_loc_sum_mp_irrelevant option.map(1) option.sel pnm_opt scale_option_def zero_option_def)
  next
    case (Some pnm)
    from assms(2) obtain pf where
      pf: "pf has_sumA (s - mh loc) \<and>
           (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf ploc)) (pf ploc = 0) (fnm ploc))"
      using nm nm_loc_sum.simps by blast
    then obtain ps where pnm_sum: "nm_loc_sum loc pnm ps"
      by (metis option_fold.simps(1) pnm_opt Some)
    with pf have "s - mh loc \<ge> ps"
      by (metis all_pos has_sumA_nonneg_ge_one_preal nm_loc_sum_unique option_fold.simps(1) pnm_opt Some)
    hence "s \<ge> ps"
      by (metis assms(2) nm nm_loc_sum.simps order.trans psub_smaller)
  
    \<comment> \<open>sum of \<^term>\<open>nm_sub\<close>\<close>
    from pnm_sum have "option_fold (\<lambda>nm. nm_loc_sum loc nm (ps * ((p - q) / p))) (ps * ((p - q) / p) = 0) (fnm' (pred_id,vs))"
      apply (cases "fnm' (pred_id,vs)")
       apply simp_all
       apply (simp add: Some fnm' scale_option_def)
       apply (metis None_eq_map_option_iff PosReal.field_divide_inverse Some cancel_comm_monoid_add_class.diff_cancel lambda_zero mult_zero_right option.distinct(1) scale_option_def)
      apply (simp add: fnm' Some scale_option_def)
      using nm_loc_sum_mult
      by (metis Some option.distinct(1) option.sel option.simps(9) scale_option_def)
    moreover have "option_fold (\<lambda>nm. nm_loc_sum loc nm ps) (ps = 0) (fnm (pred_id,vs))"
      by (metis option_fold.simps(1) pnm_opt Some pnm_sum)
    moreover have "fnm' = fnm( (pred_id, vs) := fnm' (pred_id, vs) )"
      by (simp add: fnm')
    ultimately have nm_sub_sum: "nm_loc_sum loc nm'_sub (s - ps + ps * ((p - q) / p))"
      using nm_loc_sum_change_sum[of loc mh mp fnm s ps "(pred_id,vs)" "ps * ((p - q) / p)" "fnm' (pred_id,vs)" mp'] nm assms(2) fnm' nm_sub
      by argo
  
    \<comment> \<open>sum of q/p of pnm\<close>
    have pnm_frac_sum: "nm_loc_sum loc ((q / p) *\<^sub>s pnm) (ps * (q / p))"
      using nm_loc_sum_mult pnm_sum
      by blast
  
    \<comment> \<open>sum of nm'\<close>
    have "s - ps + ps * ((p - q) / p) + ps * (q / p) = s"
      by (metis PosReal.field_divide_inverse PosReal.field_inverse \<open>ps \<le> s\<close> \<open>q \<le> p\<close> \<open>q \<noteq> pos_perm_class.pnone\<close> add.assoc add_cancel_right_left distrib_left greater_minus_plus mult.commute mult.right_neutral padd_pos)

    thus "nm_loc_sum loc nm' s"
      using pnm_frac_sum nm_sub_sum nm'[simplified scale_option_def Some]
      by (metis combine_options_simps(3) nm_loc_sum_add option.sel option.simps(9) plus_option_def)
  qed
qed


subsubsection \<open>Unfold preserves internal consistency\<close>

lemma shift_up_preserves_internal_consistency:
  assumes "shift_up pred_id vs q nm nm'"
      and "consistent_internal nm"
    shows "consistent_internal nm'"
  by (meson assms(1) assms(2) consistent_internal_def shift_up_preserves_loc_sum)

lemma unfold_preserves_internal_consistency:
  assumes "unfold_rel ctxt pid vs q \<phi> \<phi>'"
      and "consistent_internal (get_nm_total \<phi>)"
    shows "consistent_internal (get_nm_total \<phi>')"
  by (meson assms(1) assms(2) shift_up_preserves_internal_consistency unfold_rel.simps)


subsubsection \<open>Fold preserves internal consistency\<close>

lemma fold_rel_preserves_loc_sum:
  assumes "fold_rel ctxt pred_id vs p \<omega> (RNormal \<omega>')"
      and "nm_loc_sum loc (get_nm_total_full \<omega>) s"
    shows "nm_loc_sum loc (get_nm_total_full \<omega>') s"
proof -
  obtain pred_decl pred_body \<omega>0 R \<omega>1 nm_exh where
    "ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl" and
    "ViperLang.predicate_decl.body pred_decl = Some pred_body" and
    "p \<noteq> 0" and
    \<omega>0: "\<omega>0 = \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty, get_total_full = get_total_full \<omega> \<rparr>" and
    exh: "red_exhale ctxt R \<omega>0 (syntactic_mult (Rep_preal p) pred_body) \<omega>0 (RNormal \<omega>1)" and
    nm_sub: "nm_exh = nested_mask_subtract (get_nm_total_full \<omega>0) (get_nm_total_full \<omega>1)" and
    \<omega>': "\<omega>' = \<lparr> get_store_total = get_store_total \<omega>,
                get_trace_total = get_trace_total \<omega>,
                get_total_full = add_to_nm_loc_total
                  (inc_mp_loc_total (get_total_full \<omega>1) (pred_id,vs) p)
                  (pred_id,vs) nm_exh
              \<rparr>"
    using assms(1)
    by (auto elim: FoldRelNormal_case)

  define nm0 where "nm0 = get_nm_total_full \<omega>0"
  define nm1 where "nm1 = get_nm_total_full \<omega>1"
  define nm' where "nm' = get_nm_total_full \<omega>'"

  have "nm0 = get_nm_total_full \<omega>"
    by (simp add: \<omega>0 nm0_def)
  hence "nm_loc_sum loc nm0 s"
    using assms(2) by blast

  have "nm0 = nm1 + nm_exh"
    using exhale_fraction[OF exh] nested_mask_sub_add[OF nm_sub] exhale_smaller[OF exh]
    apply simp
    by (metis TotalStateUtil.get_nm_total_full.simps get_fnm_nm.elims get_nm_loc_nm.simps nm0_def nm1_def)
  moreover obtain s1 s_exh where
    "nm_loc_sum loc nm1 s1" and
    "nm_loc_sum loc nm_exh s_exh"
    sorry
  ultimately have "s = s1 + s_exh"
    by (metis \<open>nm0 = get_nm_total_full \<omega>\<close> assms(2) nm_loc_sum_add nm_loc_sum_unique)

  have "nm_loc_sum loc (get_nm_total (inc_mp_loc_total (get_total_full \<omega>1) (pred_id,vs) p)) s1"
    apply simp
    using \<open>nm_loc_sum loc nm1 s1\<close> nm1_def nm_loc_sum.elims(2) by fastforce
  hence "nm_loc_sum loc (get_nm_total_full \<omega>') (s1 + s_exh)"
    by (simp add: \<open>nm_loc_sum loc nm_exh s_exh\<close> nm_loc_sum_add_to_sub \<omega>')

  thus ?thesis
    using \<open>s = s1 + s_exh\<close> by blast
qed


lemma fold_rel_preserves_internal_consistency:
  assumes "fold_rel ctxt pred_id vs p \<omega> (RNormal \<omega>')"
      and "consistent_internal (get_nm_total_full \<omega>)"
    shows "consistent_internal (get_nm_total_full \<omega>')"
  by (metis assms(1) assms(2) consistent_internal_def fold_rel_preserves_loc_sum)


subsection \<open>Full permission in direct mask\<close>

lemma mh_1_sub_0:
  assumes "consistent_internal nm"
      and "get_mh_nm nm loc = 1"
      and "get_fnm_nm nm ploc = Some nm'"
    shows "nm_loc_sum loc nm' 0"
  sorry


subsection \<open>Internal Consistency on Total States\<close>

definition consistent_internal_total where
  "consistent_internal_total \<phi> \<equiv> consistent_internal (get_nm_total \<phi>)"

lemma unfold_preserves_internal_consistency_total:
  assumes "unfold_rel ctxt pid vs q \<phi> \<phi>'"
      and "consistent_internal_total \<phi>"
    shows "consistent_internal_total \<phi>'"
  using unfold_preserves_internal_consistency assms(1) assms(2) consistent_internal_total_def
  by blast


subsection \<open>Internal Consistency on Full Total States\<close>

definition consistent_internal_total_full where
  "consistent_internal_total_full \<omega> \<equiv>
     consistent_internal_total (get_total_full \<omega>) \<and>
     (\<forall>lbl \<phi>. get_trace_total \<omega> lbl = Some \<phi> \<longrightarrow> consistent_internal_total \<phi>)"


end
