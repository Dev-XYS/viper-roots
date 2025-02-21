theory TotalInternalConsistency
  imports TotalFoldUnfold NestedMaskProperties TotalStateProperties TotalSemantics
begin


subsection \<open>New Internal Consistency\<close>

definition consistent_internal :: "'a nested_mask \<Rightarrow> bool" where
  "consistent_internal nm \<equiv> \<forall>loc. \<exists>s. s \<le> 1 \<and> nm_loc_sum loc nm s"


subsection \<open>Internal Consistency on Total States\<close>

definition consistent_internal_total where
  "consistent_internal_total \<phi> \<equiv> consistent_internal (get_nm_total \<phi>)"


subsection \<open>Internal Consistency on Full Total States\<close>

definition consistent_internal_total_full where
  "consistent_internal_total_full \<omega> \<equiv>
     consistent_internal_total (get_total_full \<omega>) \<and>
     (\<forall>lbl \<phi>. get_trace_total \<omega> lbl = Some \<phi> \<longrightarrow> consistent_internal_total \<phi>)"


subsection \<open>Well-formed state consistency\<close>

\<comment> \<open>Putting these here is really sub-optimal. Previously, these definitions lie in \<^file>\<open>TotalSemantics.thy\<close>.
    The reason to put it here is that only internal consistency (or simply consistency in the following
    definition) parameterized and external consistency is not, and the well-formedness of internal
    consistency requires external consistency.\<close>

text \<open>Many of the theorems are parametrized by the state consistency. Many of the theorems require
certain properties on the state consistency. The following well-formedness definition captures
these properties.\<close>

definition wf_total_consistency
  where "wf_total_consistency ctxt R Rt \<equiv>
               mono_prop_downward R \<and>
               (\<forall>\<omega>. is_empty_total_full \<omega> \<longrightarrow> Rt (get_total_full \<omega>)) \<and>
               (\<forall>\<omega> \<omega>' \<Lambda> stmt. R \<omega> \<longrightarrow> red_stmt_total ctxt R \<Lambda> stmt \<omega> (RNormal \<omega>') \<longrightarrow> R \<omega>') \<and>
               \<comment>\<open>The following statement ensures that states in the body of a scope preserve consistency.\<close>
               (\<forall>\<omega> v. R \<omega> \<longrightarrow> R (shift_and_add_state_total \<omega> v)) \<and>
               (\<forall>\<omega>. R \<omega> \<longleftrightarrow> (Rt (get_total_full \<omega>) \<and> (\<forall>lbl \<phi>. get_trace_total \<omega> lbl = Some \<phi> \<longrightarrow> Rt \<phi>))) \<and>
               (\<forall>\<omega> \<omega>' \<Lambda> stmt. consistent_external ctxt (get_total_full \<omega>) \<longrightarrow> R \<omega> \<longrightarrow>
                              ctxt_wf_pred ctxt \<longrightarrow> ctxt_pred_self_framing ctxt \<longrightarrow>
                              red_stmt_total ctxt R \<Lambda> stmt \<omega> (RNormal \<omega>') \<longrightarrow>
                              consistent_external ctxt (get_total_full \<omega>'))"

lemma total_consistencyI:
  assumes "wf_total_consistency ctxt R Rt"
      and "Rt (get_total_full \<omega>)"
      and "\<And> lbl \<phi>. get_trace_total \<omega> lbl = Some \<phi> \<Longrightarrow> Rt \<phi>"
    shows "R \<omega>"
  using assms
  unfolding wf_total_consistency_def
  by blast

lemma wf_total_consistency_trivial: "wf_total_consistency ctxt (\<lambda>_.True) (\<lambda>_.True)"
  unfolding wf_total_consistency_def mono_prop_downward_def
  oops  \<comment> \<open>Does not hold any more.\<close>

lemma total_consistency_red_stmt_preserve:
  assumes "wf_total_consistency ctxt R Rt"
      and "R \<omega>"
      and "red_stmt_total ctxt R \<Lambda> stmt \<omega> (RNormal \<omega>')"
    shows "R \<omega>'"
  using assms
  unfolding wf_total_consistency_def
  by blast

lemma total_consistency_store_update:
  assumes "wf_total_consistency ctxt R Rt"
      and "R \<omega>"
      and "get_total_full \<omega>' = get_total_full \<omega>"
      and "get_trace_total \<omega>' = get_trace_total \<omega>"
    shows "R \<omega>'"
  using assms
  unfolding wf_total_consistency_def
  by metis

lemma total_consistency_store_update_2:
  assumes "wf_total_consistency ctxt R Rt"
      and "R \<omega>"
    shows "R (\<omega> \<lparr> get_store_total := \<sigma> \<rparr>)"
  using assms total_consistency_store_update
  by fastforce

lemma total_consistency_trace_update:
  assumes "wf_total_consistency ctxt R Rt"
      and "R \<omega>"
      and "get_store_total \<omega>' = get_store_total \<omega>"
      and "get_total_full \<omega>' = get_total_full \<omega>"
      and "\<And> lbl \<phi>. get_trace_total \<omega>' lbl = Some \<phi> \<Longrightarrow> Rt \<phi>"
    shows "R \<omega>'"
  using assms
  unfolding wf_total_consistency_def
  by simp

lemma total_consistency_trace_update_2:
  assumes "wf_total_consistency ctxt R Rt"
      and "R \<omega>"
      and "\<And> lbl \<phi>. t lbl = Some \<phi> \<Longrightarrow> Rt \<phi>"
    shows "R (\<omega> \<lparr> get_trace_total := t \<rparr>)"
  using assms
  unfolding wf_total_consistency_def
  by simp

lemma wf_total_consistency_trace_mono_downwardD:
  assumes "wf_total_consistency ctxt R Rt"
  shows "mono_prop_downward R"
  using assms
  unfolding wf_total_consistency_def
  by blast

lemma total_consistency_red_stmt_extcons_preserve:
  assumes "wf_total_consistency ctxt R Rt"
      and "consistent_external ctxt (get_total_full \<omega>)"
      and "ctxt_wf_pred ctxt"
      and "ctxt_pred_self_framing ctxt"
      and "R \<omega>"
      and "red_stmt_total ctxt R \<Lambda> stmt \<omega> (RNormal \<omega>')"
    shows "consistent_external ctxt (get_total_full \<omega>')"
  using assms
  unfolding wf_total_consistency_def
  by blast


subsection \<open>Unfold preserves internal consistency\<close>

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
    "p = Rep_posreal p\<^sub>p" and
    "q \<le> p" and
    fnm': "fnm' = fnm( (pid,vs) := if p = q then None else Some (Abs_posreal (p - q), ((p - q) / p) *\<^sub>s pnm) )" and
    "nm'_sub = NM mh fnm'" and
    "nm' = nm'_sub + (q / p) *\<^sub>s pnm"
    using True pperm_pgt_pnone
    by (auto elim: shift_up.cases)

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
    by (metis Rep_preal_inverse True \<open>q \<le> p\<close> linorder_not_less zero_preal_def)

  have pf'_each: "\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf' lp)) (pf' lp = 0) (fnm' lp)"
  proof
    fix lp
    show "option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf' lp)) (pf' lp = 0) (fnm' lp)"
    proof (cases "lp = (pid,vs)")
      case True
      then show ?thesis
        apply (simp add: pf'_def fnm')
        apply (intro conjI)
         apply (simp add: divide_preal.rep_eq minus_preal.rep_eq)
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

lemma unfold_preserves_internal_consistency_total:
  assumes "unfold_rel ctxt pid vs q \<phi> \<phi>'"
      and "consistent_internal_total \<phi>"
    shows "consistent_internal_total \<phi>'"
  using unfold_preserves_internal_consistency assms(1) assms(2) consistent_internal_total_def
  by blast


subsection \<open>Fold preserves internal consistency\<close>

lemma exhale_0_state_same:
  assumes "red_exhale ctxt R \<omega>0 (syntactic_mult 0 A) \<omega> (RNormal \<omega>')"
  shows "\<omega>' = \<omega>"
  using assms
proof (induction A arbitrary: \<omega> \<omega>')
  case IH: (Atomic atm)
  show ?case
  proof (cases atm)
    case (Pure e)
    show ?thesis
      using red_exhale.cases[OF IH[simplified Pure, simplified], simplified]
      by (metis exh_if_total.elims result_total.distinct(5) result_total.inject)
  next
    case (Acc e_r f perm)
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      obtain mh v_r v_p a where
        "mh = get_mh_total_full \<omega>" and
        "ctxt, (Some \<omega>0) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef v_r)" and
        v_p: "ctxt, (Some \<omega>0) \<turnstile> \<langle>Binop (ELit NoPerm) Mult e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
        "a = the_address v_r" and
        "RNormal \<omega>' = exh_if_total (v_p \<ge> 0 \<and> (if v_r = Null then v_p = 0 else mh (a,f) \<ge> Abs_preal v_p))
                                   (if v_r = Null then \<omega> else dec_mh_loc_total_full \<omega> (a,f) (Abs_preal v_p))"
        using IH[simplified Acc PureExp, simplified]
        by (auto elim: red_exhale.cases)
      hence "v_p = 0"
        using RedBinop_case[OF v_p, simplified]
        by (metis (no_types, lifting) RedLit_case binop_result.inject eval_binop_perm_mult_constant extended_val.inject mult_not_zero val.inject(3) val_of_lit.simps(3))
      moreover have "dec_mh_loc_total_full \<omega> (a,f) (Abs_preal v_p) = \<omega>"
        apply (simp add: \<open>v_p = 0\<close>)
        apply (rule full_total_state.equality)
           apply simp_all
        apply (rule total_state.equality)
          apply simp_all
        apply (rule nested_mask_equality)
         apply standard
         apply (simp_all add: zero_preal.abs_eq[symmetric])
        using all_pos greater_minus_plus
        by fastforce
      then show ?thesis
        using exh_if_total.elims[OF \<open>RNormal \<omega>' = _\<close>[symmetric], simplified]
        by metis
    next
      case Wildcard
      obtain mh v_r v_p a where
        "mh = get_mh_total_full \<omega>" and
        "ctxt, (Some \<omega>0) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef v_r)" and
        "ctxt, (Some \<omega>0) \<turnstile> \<langle>ELit NoPerm; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
        "a = the_address v_r" and
        "RNormal \<omega>' = exh_if_total (v_p \<ge> 0 \<and> (if v_r = Null then v_p = 0 else mh (a,f) \<ge> Abs_preal v_p))
                                   (if v_r = Null then \<omega> else dec_mh_loc_total_full \<omega> (a,f) (Abs_preal v_p))"
        using IH[simplified Acc Wildcard, simplified]
        by (auto elim: red_exhale.cases)
      hence "v_p = 0"
        by (auto elim: RedLit_case)
      moreover have "dec_mh_loc_total_full \<omega> (a,f) (Abs_preal v_p) = \<omega>"
        apply (simp add: \<open>v_p = 0\<close>)
        apply (rule full_total_state.equality)
           apply simp_all
        apply (rule total_state.equality)
          apply simp_all
        apply (rule nested_mask_equality)
         apply standard
         apply (simp_all add: zero_preal.abs_eq[symmetric])
        using all_pos greater_minus_plus
        by fastforce
      ultimately show ?thesis
        using exh_if_total.elims[OF \<open>RNormal \<omega>' = _\<close>[symmetric], simplified]
        by metis
    qed
  next
    case (AccPredicate pid e_args perm)
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      obtain mp v_args v_p where
        "mp = get_mp_total_full \<omega>" and
        "red_pure_exps_total ctxt (Some \<omega>0) e_args \<omega> (Some v_args)" and
        v_p: "ctxt, (Some \<omega>0) \<turnstile> \<langle>Binop (ELit NoPerm) Mult e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
        "RNormal \<omega>' = exh_if_total (v_p \<ge> 0 \<and> mp (pid,v_args) \<ge> Abs_preal v_p)
                                   (exhale_pred \<omega> (pid,v_args) (Abs_preal v_p))"
        using IH[simplified AccPredicate PureExp, simplified]
        by (auto elim: red_exhale.cases)
      hence "v_p = 0"
        using RedBinop_case[OF v_p, simplified]
        by (metis (no_types, lifting) RedLit_case binop_result.inject eval_binop_perm_mult_constant extended_val.inject mult_not_zero val.inject(3) val_of_lit.simps(3))
      moreover have "exhale_pred \<omega> (pid,v_args) (Abs_preal v_p) = \<omega>"
        apply (simp add: \<open>v_p = 0\<close> exhale_pred_def)
        apply (rule full_total_state.equality)
           apply simp_all
        apply (rule total_state.equality)
          apply simp_all
        apply (rule nested_mask_equality)
         apply standard
         apply simp
        apply standard
        apply simp
        apply (subgoal_tac "\<And>x. Rep_posreal x \<le> Abs_preal 0 = False")
         apply standard+
         apply simp
         apply (smt (verit, del_insts) Rep_posreal_inverse Rep_preal_inverse add.commute add_0 all_pos div_0 divide_preal.rep_eq fst_conv greater_minus_plus not_None_eq option_fold.simps(1) option_fold.simps(2) preal_semimodule_class.scale_one snd_conv surj_pair zero_preal.rep_eq)
        using Rep_posreal linorder_not_less zero_preal_def
        by auto
      then show ?thesis
        using exh_if_total.elims[OF \<open>RNormal \<omega>' = _\<close>[symmetric], simplified]
        by metis
    next
      case Wildcard
      obtain mp v_args v_p where
        "mp = get_mp_total_full \<omega>" and
        "red_pure_exps_total ctxt (Some \<omega>0) e_args \<omega> (Some v_args)" and
        v_p: "ctxt, (Some \<omega>0) \<turnstile> \<langle>ELit NoPerm; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
        "RNormal \<omega>' = exh_if_total (v_p \<ge> 0 \<and> mp (pid,v_args) \<ge> Abs_preal v_p)
                                   (exhale_pred \<omega> (pid,v_args) (Abs_preal v_p))"
        using IH[simplified AccPredicate Wildcard, simplified]
        by (auto elim: red_exhale.cases)
      hence "v_p = 0"
        by (auto elim: RedLit_case)
      moreover have "exhale_pred \<omega> (pid,v_args) (Abs_preal v_p) = \<omega>"
        apply (simp add: \<open>v_p = 0\<close> exhale_pred_def)
        apply (rule full_total_state.equality)
           apply simp_all
        apply (rule total_state.equality)
          apply simp_all
        apply (rule nested_mask_equality)
         apply standard
         apply simp
        apply standard
        apply (subgoal_tac "\<And>x. Rep_posreal x \<le> Abs_preal 0 = False")
         apply simp
         apply (smt (verit, del_insts) Rep_posreal_inverse Rep_preal_inverse add.commute add_0 all_pos div_0 divide_preal.rep_eq fst_conv greater_minus_plus not_None_eq option_fold.simps(1) option_fold.simps(2) preal_semimodule_class.scale_one snd_conv surj_pair zero_preal.rep_eq)
        using Rep_posreal linorder_not_less zero_preal_def
        by auto
      ultimately show ?thesis
        using exh_if_total.elims[OF \<open>RNormal \<omega>' = _\<close>[symmetric], simplified]
        by metis
    qed
  qed
qed (simp, blast elim: red_exhale.cases)+


lemma fold_rel_preserves_loc_sum:
  assumes "fold_rel ctxt pred_id vs p \<omega> (RNormal \<omega>')"
      and "nm_loc_sum loc (get_nm_total_full \<omega>) s"
    shows "nm_loc_sum loc (get_nm_total_full \<omega>') s"
proof -
  obtain pred_decl pred_body \<omega>0 \<omega>1 \<omega>1' nm_exh where
    "ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl" and
    "ViperLang.predicate_decl.body pred_decl = Some pred_body" and
    "vals_well_typed (absval_interp_total ctxt) vs (predicate_decl.args pred_decl)" and
    \<omega>0: "\<omega>0 = \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty, get_total_full = get_total_full \<omega> \<rparr>" and
    exh: "red_exhale ctxt (\<lambda>_. True) \<omega>0 (syntactic_mult (Rep_preal p) pred_body) \<omega>0 (RNormal \<omega>1')" and
    \<omega>1: "\<omega>1 = \<omega>\<lparr> get_total_full := get_total_full \<omega>1' \<rparr>" and
    nm_sub: "get_nm_total_full \<omega>1 + nm_exh = get_nm_total_full \<omega>0" and
    \<omega>': "\<omega>' = add_to_lpm_total_full \<omega>1 (pred_id,vs) (if p = 0 then None else Some (Abs_posreal p, nm_exh))"
    apply (rule FoldRelNormal_case[OF assms(1)])
    by simp

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


lemma fold_rel_preserved_trace:
  assumes "fold_rel ctxt pred_id vs p \<omega> (RNormal \<omega>')"
  shows "get_trace_total \<omega> = get_trace_total \<omega>'"
  using assms
  by (fastforce elim: fold_rel.cases)


lemma intcons_preserved_by_fold_rel:
  assumes "fold_rel ctxt pred_id vs p \<omega> (RNormal \<omega>')"
      and "consistent_internal_total_full \<omega>"
    shows "consistent_internal_total_full \<omega>'"
  by (metis assms(1) assms(2) consistent_internal_total_def consistent_internal_total_full_def fold_rel_preserved_trace fold_rel_preserves_internal_consistency get_nm_total_full.simps)


subsection \<open>Some Basic Properties\<close>

lemma intcons_mono_prop_downward:
  shows "mono_prop_downward consistent_internal_total_full"
  unfolding mono_prop_downward_def
proof standard+
  fix \<omega>\<^sub>1 \<omega>\<^sub>2 :: "('a,'b) full_total_state_scheme"
  assume *: "\<omega>\<^sub>2 \<succeq> \<omega>\<^sub>1 \<and> consistent_internal_total_full \<omega>\<^sub>2"
  then obtain \<omega>' where "Some \<omega>\<^sub>2 = \<omega>\<^sub>1 \<oplus> \<omega>'"
    by (metis greater_def)
  have diff: "get_nm_total_full \<omega>\<^sub>1 + get_nm_total_full \<omega>' = get_nm_total_full \<omega>\<^sub>2"
    using Some_Some_ifD[OF \<open>Some \<omega>\<^sub>2 = _\<close>[unfolded plus_full_total_state_ext_def]]
    unfolding defined_def not_None_eq
    by (metis Some_Some_ifD \<open>Some \<omega>\<^sub>2 = \<omega>\<^sub>1 \<oplus> \<omega>'\<close> get_nm_total_full.simps option.sel plus_Some_full_total_state_total_state plus_total_state_ext_def total_state.select_convs(2) total_state.surjective total_state.update_convs(2))
  hence "get_nm_total_full \<omega>\<^sub>1 \<le> get_nm_total_full \<omega>\<^sub>2"
    by (metis nm_sum_is_bigger)
  thus "consistent_internal_total_full \<omega>\<^sub>1"
    unfolding consistent_internal_total_full_def
    apply (intro conjI)
     defer
     apply (metis * consistent_internal_total_full_def full_total_state_greater_only_mask_changed)
    unfolding consistent_internal_total_def consistent_internal_def
    by (metis * consistent_internal_def consistent_internal_total_def consistent_internal_total_full_def dual_order.trans get_nm_total_full.simps nm_loc_sum_smaller)
qed


lemma intcons_empty:
  assumes "is_empty_total \<phi>"
  shows "consistent_internal_total \<phi>"
  unfolding consistent_internal_total_def consistent_internal_def
  apply (intro allI)
  apply (rule exI[of _ 0])
  unfolding assms[unfolded is_empty_total_def] zero_nested_mask_def
  apply (intro conjI)
   apply (simp add: all_pos)
  apply (simp add: zero_mask_def)
  apply (rule exI[of _ "\<lambda>_. 0"])
  by force


subsection \<open>Full permission in direct mask\<close>

lemma mh_1_nested_0:
  assumes "consistent_internal nm"
      and "get_mh_nm nm loc = 1"
      and "get_fnm_nm nm lp = Some lpm"
    shows "nm_loc_sum loc (snd lpm) 0"
proof -
  obtain s where s: "s \<le> 1 \<and> nm_loc_sum loc nm s"
    using assms(1) consistent_internal_def
    by blast
  obtain mh fnm where "nm = NM mh fnm"
    using nm_get_eq
    by blast
  hence "mh loc = 1"
    using assms(2)
    by force

  from s[unfolded \<open>nm = _\<close>, simplified] obtain pf where
    *: "Rep_preal (mh loc) \<le> Rep_preal s" and
    pf: "(pf has_sumA (Rep_preal s - Rep_preal (mh loc)) \<and>
           (\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf lp)) (pf lp = 0) (fnm lp)))"
    by fast+

  have "s = 1"
    using *[unfolded \<open>mh loc = 1\<close>] conjunct1[OF s]
    by (simp add: Rep_preal_inject less_eq_preal.rep_eq)

  with pf have pf0: "pf has_sumA 0"
    using \<open>mh loc = pos_perm_class.pwrite\<close>
    by force

  have "pf lp = 0"
    using nm_loc_sum'_nonneg has_sumA_nonneg_ge_one_real[OF pf0]
    by (smt (verit, best) has_Some_iff pf)

  thus ?thesis
    by (metis \<open>nm = _\<close> assms(3) get_fnm_nm.simps nm_loc_sum.simps option_fold.simps(1) pf zero_preal.rep_eq)
qed


end
