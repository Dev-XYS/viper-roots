theory TotalInternalConsistency
  imports TotalFoldUnfold NestedMaskProperties TotalStateProperties
begin


subsection \<open>New Internal Consistency\<close>

definition consistent_internal :: "'a nested_mask \<Rightarrow> bool" where
  "consistent_internal nm \<equiv> \<forall>loc. \<exists>s. s \<le> 1 \<and> nm_loc_sum loc nm s"


lemma shift_up_preserves_loc_sum:
  assumes "shift_up pid vs q nm nm'"
      and "nm_loc_sum loc nm s"
    shows "nm_loc_sum loc nm' s"
proof (cases "q > 0")
  case True
  from assms(1) obtain mh fnm p\<^sub>p pnm p fnm' nm'_sub where
    "mh = get_mh_nm nm" and
    "fnm = get_fnm_nm nm" and
    lpm: "Some (p\<^sub>p, pnm) = fnm (pid,vs)" and
    "p = pos2p p\<^sub>p" and
    "q \<le> p" and
    fnm': "fnm' = fnm( (pid,vs) := if p = q then None else Some (p2pos (p - q), ((p - q) / p) *\<^sub>s pnm) )" and
    "nm'_sub = NM mh fnm'" and
    "nm' = nm'_sub + (q / p) *\<^sub>s pnm"
    using True pperm_pgt_pnone
    by (fastforce elim: shift_up.cases)

  from iffD1[OF nm_loc_sum'.simps
      subst[OF nm_get_eq[of nm],
        of "\<lambda>nm. nm_loc_sum' loc nm (Rep_preal s)",
        OF assms(2)[simplified]]]
  obtain pf where
    pf_sum: "pf has_sumA (Rep_preal s - Rep_preal (mh loc))" and
    pf_each: "\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf lp)) (pf lp = 0) (fnm lp)"
    using \<open>fnm = _\<close> \<open>mh = _\<close>
    by blast

  define pf' where "pf' = pf( (pid,vs) :=  Rep_preal ((p - q) / p) * pf (pid,vs) )"

  have pf'_sum: "pf' has_sumA (Rep_preal s - Rep_preal (mh loc) - Rep_preal (q / p) * pf (pid,vs))"
    apply (rule subst[where ?P="\<lambda>s. pf' has_sumA s"])
     defer
    using has_sumA_change_one_real[OF pf_sum, of "(pid,vs)" "Rep_preal ((p - q) / p) * pf (pid,vs)", simplified pf'_def[symmetric]]
     apply simp
    apply (simp add: preal_to_real iffD1[OF less_eq_preal.rep_eq \<open>q \<le> p\<close>])
    apply (subgoal_tac "Rep_preal p \<noteq> 0")
     apply (metis (no_types, opaque_lifting) cancel_ab_semigroup_add_class.diff_right_commute cancel_comm_monoid_add_class.diff_cancel left_diff_distrib' nonzero_mult_div_cancel_left times_divide_eq_right verit_minus_simplify(3))
    using \<open>p = pos2p p\<^sub>p\<close> pos2p_gt_0 pperm_pgt_pnone preal_to_real(10) zero_preal.rep_eq
    by fastforce

  have pf'_each: "\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf' lp)) (pf' lp = 0) (fnm' lp)"
  proof
    fix lp
    show "option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf' lp)) (pf' lp = 0) (fnm' lp)"
    proof (cases "lp = (pid,vs)")
      case True
      then show ?thesis
        apply (simp add: pf'_def fnm')
        apply (intro conjI)
         apply (simp add: divide_preal.rep_eq zero_preal.rep_eq)
        by (metis lpm mult.commute nm_loc_sum'_mult option_fold.simps(1) pf_each snd_conv)
    next
      case False
      then show ?thesis
        apply (simp add: pf'_def fnm')
        using pf_each
        by blast
    qed
  qed

  have "nm_loc_sum' loc nm'_sub (Rep_preal s - Rep_preal (q / p) * pf (pid,vs))"
  proof -
    have "\<And>x. pf x \<ge> 0"
      by (smt (verit) has_Some_iff nm_loc_sum'_nonneg pf_each)
    hence "\<And>x. pf' x \<ge> 0"
      by (simp add: pf'_def prat_non_negative)
    hence "Rep_preal s - Rep_preal (mh loc) - Rep_preal (q / p) * pf (pid,vs) \<ge> 0"
      using has_sum_nonneg pf'_sum
      by blast
    thus ?thesis
      unfolding \<open>nm'_sub = _\<close> nm_loc_sum'.simps
      apply (intro conjI)
       defer
       apply (rule exI[of _ pf'])
      using pf'_each pf'_sum
      by argo+
  qed

  moreover have "nm_loc_sum' loc ((q / p) *\<^sub>s pnm) (Rep_preal (q / p) * pf (pid,vs))"
    by (metis lpm mult.commute nm_loc_sum'_mult option_fold.simps(1) pf_each snd_conv)

  ultimately show ?thesis
    using \<open>nm' = _\<close> nm_loc_sum'_add
    by fastforce
next
  case False
  then show ?thesis
    using assms shift_up_case
    by blast
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

lemma exhale_0_state_same:
  assumes "red_exhale ctxt R \<omega>0 (syntactic_mult 0 pred_body) \<omega> (RNormal \<omega>')"
  shows "\<omega>' = \<omega>"
  sorry

lemma fold_rel_preserves_loc_sum:
  assumes "fold_rel ctxt pred_id vs p \<omega> (RNormal \<omega>')"
      and "nm_loc_sum loc (get_nm_total_full \<omega>) s"
    shows "nm_loc_sum loc (get_nm_total_full \<omega>') s"
proof -
  obtain pred_decl pred_body \<omega>0 \<omega>1 \<omega>1' nm_exh where
    "ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl" and
    "ViperLang.predicate_decl.body pred_decl = Some pred_body" and
    \<omega>0: "\<omega>0 = \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty, get_total_full = get_total_full \<omega> \<rparr>" and
    exh: "red_exhale ctxt (\<lambda>_. True) \<omega>0 (syntactic_mult (Rep_preal p) pred_body) \<omega>0 (RNormal \<omega>1')" and
    \<omega>1: "\<omega>1 = \<omega>\<lparr> get_total_full := get_total_full \<omega>1' \<rparr>" and
    nm_sub: "get_nm_total_full \<omega>1 + nm_exh = get_nm_total_full \<omega>0" and
    \<omega>': "\<omega>' = add_to_lpm_total_full \<omega>1 (pred_id,vs) (if p = 0 then None else Some (p2pos p, nm_exh))"
    using assms(1)
    by (auto elim: FoldRelNormal_case)

  define nm0 where "nm0 = get_nm_total_full \<omega>0"
  define nm1 where "nm1 = get_nm_total_full \<omega>1"
  define nm' where "nm' = get_nm_total_full \<omega>'"

  have "nm0 = get_nm_total_full \<omega>"
    by (simp add: \<omega>0 nm0_def)
  hence "nm_loc_sum loc nm0 s"
    using assms(2) by blast

  moreover have "nm0 = nm1 + nm_exh"
    using nm0_def nm1_def nm_sub
    by presburger
  moreover obtain s1 s_exh where
    nm1_sum: "nm_loc_sum loc nm1 s1" and
    nm_exh_sum: "nm_loc_sum loc nm_exh s_exh"
    using nm_loc_sum_smaller[OF \<open>nm_loc_sum loc nm0 s\<close>] nm_sum_is_bigger
    by (metis add.commute calculation(2))
  ultimately have "s = s1 + s_exh"
    using nm_loc_sum_add nm_loc_sum_unique
    by (metis nm_loc_sum.elims(2) Rep_preal_inject[symmetric])

  have "nm_loc_sum loc (get_nm_total_full \<omega>') (s1 + s_exh)"
    apply (simp only: \<omega>' \<omega>1)
    apply (cases "p = 0")
    using \<open>nm_loc_sum loc nm0 s\<close> \<open>s = s1 + s_exh\<close> exh exhale_0_state_same nm0_def zero_preal.rep_eq
     apply fastforce
    apply (simp del: add_to_lpm_nm.simps)
    apply (subgoal_tac "get_nm_total_full \<omega>1' = nm1")
    using nm1_sum nm_exh_sum nm_loc_sum_add_to_lpm
     apply fastforce
    by (simp add: nm1_def \<omega>1)

  thus ?thesis
    using \<open>s = s1 + s_exh\<close>
    by blast
qed


lemma fold_rel_preserves_internal_consistency:
  assumes "fold_rel ctxt pred_id vs p \<omega> (RNormal \<omega>')"
      and "consistent_internal (get_nm_total_full \<omega>)"
    shows "consistent_internal (get_nm_total_full \<omega>')"
  by (metis assms(1) assms(2) consistent_internal_def fold_rel_preserves_loc_sum)


subsection \<open>Full permission in direct mask\<close>

(*
lemma mh_1_sub_0:
  assumes "consistent_internal nm"
      and "get_mh_nm nm loc = 1"
      and "get_fnm_nm nm ploc = Some nm'"
    shows "nm_loc_sum loc nm' 0"
  sorry
*)


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
