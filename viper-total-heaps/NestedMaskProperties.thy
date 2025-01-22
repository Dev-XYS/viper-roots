section \<open>Permission of a Heap Location Inside a Nested Mask Using Infinite Sum\<close>

theory NestedMaskProperties
  imports HOL.Groups_Big "HOL-Analysis.Infinite_Sum"
          TotalMaskUtil TotalStateUtil
begin


subsection \<open>Definitions\<close>

abbreviation has_sumA :: "('a \<Rightarrow> 'b :: {comm_monoid_add, topological_space}) \<Rightarrow> 'b \<Rightarrow> bool" (infixr "has'_sumA" 46) where
  "(f has_sumA S) \<equiv> (f has_sum S) UNIV"


function (sequential) nm_loc_sum :: "heap_loc \<Rightarrow> 'a nested_mask \<Rightarrow> preal \<Rightarrow> bool" where
  "nm_loc_sum loc (NM mh fnm) p =
     (mh loc \<le> p \<and>
      (\<exists>pf. pf has_sumA (p - mh loc) \<and>
            (\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum loc (snd lpm) (pf lp)) (pf lp = 0) (fnm lp))))"
  by (pat_completeness) auto
termination
  apply (relation "{} <*lex*> nested_mask_rel <*lex*> {}")
  using wf_nested_mask_rel
   apply blast
  by fastforce

lemma nm_loc_sumI:
  assumes "mh loc \<le> p \<and>
           (\<exists>pf. pf has_sumA (p - mh loc) \<and>
                 (\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum loc (snd lpm) (pf lp)) (pf lp = 0) (fnm lp)))"
  shows "nm_loc_sum loc (NM mh fnm) p"
  using assms
  by auto


fun nm_loc_sum_option :: "heap_loc \<Rightarrow> 'a nested_mask option \<Rightarrow> preal \<Rightarrow> bool" where
  "nm_loc_sum_option loc nm_opt p = option_fold (\<lambda>nm. nm_loc_sum loc nm p) (p = 0) nm_opt"


subsection \<open>Properties of Addition\<close>

lemma nm_loc_sum_add:
  assumes "nm_loc_sum loc nm\<^sub>1 p"
      and "nm_loc_sum loc nm\<^sub>2 q"
    shows "nm_loc_sum loc (nm\<^sub>1 + nm\<^sub>2) (p + q)"
  using assms
proof (induct arbitrary: p q rule: nested_mask_merge.induct[of _ nm\<^sub>1 nm\<^sub>2])
  case IH: (1 mh\<^sub>1 fnm\<^sub>1 mh\<^sub>2 fnm\<^sub>2)
  from IH have "mh\<^sub>1 loc \<le> p" and "mh\<^sub>2 loc \<le> q"
    by (metis get_mh_nm.simps nm_loc_sum.elims(1))+
  from IH(2) obtain pf\<^sub>1 where pf\<^sub>1: "pf\<^sub>1 has_sumA (p - mh\<^sub>1 loc) \<and>
      (\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum loc (snd lpm) (pf\<^sub>1 lp)) (pf\<^sub>1 lp = 0) (fnm\<^sub>1 lp))"
    by (metis nm_loc_sum.simps)
  from IH(3) obtain pf\<^sub>2 where pf\<^sub>2: "pf\<^sub>2 has_sumA (q - mh\<^sub>2 loc) \<and>
      (\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum loc (snd lpm) (pf\<^sub>2 lp)) (pf\<^sub>2 lp = 0) (fnm\<^sub>2 lp))"
    by (metis nm_loc_sum.simps)

  define pf where "pf = (\<lambda>x. pf\<^sub>1 x + pf\<^sub>2 x)"
  hence has_sum: "pf has_sumA ((p - mh\<^sub>1 loc) + (q - mh\<^sub>2 loc))"
    using has_sum_add[of pf\<^sub>1 UNIV "p - mh\<^sub>1 loc" pf\<^sub>2 "q - mh\<^sub>2 loc"] pf\<^sub>1 pf\<^sub>2
    by blast

  show ?case
    apply (simp add: plus_nested_mask_def del: split_paired_All)
    apply (intro conjI)
     apply (simp add: PosReal.padd_mono \<open>mh\<^sub>1 loc \<le> p\<close> \<open>mh\<^sub>2 loc \<le> q\<close> add_masks_def)
    apply (rule exI[of _ pf])
    apply (intro conjI)
     apply (simp add: add_masks_def)
     apply (subgoal_tac "p - mh\<^sub>1 loc + (q - mh\<^sub>2 loc) = p + q - (mh\<^sub>1 loc + mh\<^sub>2 loc)")
    using has_sum
      apply argo
     apply (simp add: preal_to_real)
    using \<open>mh\<^sub>1 loc \<le> p\<close> \<open>mh\<^sub>2 loc \<le> q\<close> less_eq_preal.rep_eq
     apply blast
    apply (simp only: plus_nested_mask_def[symmetric])
  proof standard
    fix lp
    show "option_fold (\<lambda>lpm. nm_loc_sum loc (snd lpm) (pf lp))
                        (pf lp = pos_perm_class.pnone)
                        ((fnm\<^sub>1 +\<lparr> \<lambda>lpm\<^sub>1 lpm\<^sub>2. (fst lpm\<^sub>1 + fst lpm\<^sub>2, snd lpm\<^sub>1 + snd lpm\<^sub>2) \<rparr>+ fnm\<^sub>2) lp)"
      apply (cases "fnm\<^sub>1 lp"; cases "fnm\<^sub>2 lp")
         apply (simp_all add: option_fold_def pfun_comb_def)
         apply (metis (mono_tags) add_0 option_fold.simps(2) pf\<^sub>1 pf\<^sub>2 pf_def)
        apply (metis (mono_tags, lifting) add_0 option_fold.simps(1) option_fold.simps(2) pf\<^sub>1 pf\<^sub>2 pf_def)
      apply (metis (mono_tags, lifting) add.right_neutral option_fold.simps(1) option_fold.simps(2) pf\<^sub>1 pf\<^sub>2 pf_def)
      by (metis (no_types, lifting) IH.hyps is_none_code(2) option.sel option_fold.simps(1) pf\<^sub>1 pf\<^sub>2 pf_def range_eqI)
  qed
qed


subsection \<open>Properties of Multiplication\<close>

lemma nm_loc_sum_mult:
    fixes frac :: preal
  assumes "nm_loc_sum loc nm p"
    shows "nm_loc_sum loc (frac *\<^sub>s nm) (p * frac)"
  using assms(1)
proof (induct nm arbitrary: p)
  case IH: (NM mh fnm)
  from IH(2) obtain pf where
    "mh loc \<le> p" and
    pf: "pf has_sumA (p - mh loc) \<and> (\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum loc (snd lpm) (pf lp)) (pf lp = 0) (fnm lp))"
    by (blast elim: nm_loc_sum.elims)

  define pf' where "pf' = (\<lambda>x. pf x * frac)"
  hence has_sum: "pf' has_sumA (frac * (p - mh loc))"
    using has_sum_cmult_right[of pf "UNIV" "p - mh loc" frac] pf pf'_def
    by (simp add: mult.commute)

  show ?case
    apply (simp add: scale_nested_mask_def del: split_paired_All)
    apply (intro conjI)
     apply (simp add: mul_mask_def preal_to_real)
    using PosReal.pmult_comm \<open>mh loc \<le> p\<close> less_eq_preal.rep_eq mult_left_mono prat_non_negative times_preal.rep_eq
     apply fastforce
    apply (rule exI[of _ pf'])
    apply (intro conjI)
     apply (simp add: mul_mask_def)
     apply (subgoal_tac "p * frac - frac * mh loc = frac * (p - mh loc)")
    using has_sum
      apply force
     apply (simp add: PosReal.pmult_comm right_diff_distrib')
    apply (simp only: scale_nested_mask_def[symmetric])
  proof standard
    fix lp
    show "(frac = pos_perm_class.pnone \<longrightarrow> pf' lp = pos_perm_class.pnone) \<and>
          (frac \<noteq> pos_perm_class.pnone \<longrightarrow>
             option_fold (\<lambda>lpm. nm_loc_sum loc (snd lpm) (pf' lp))
                         (pf' lp = pos_perm_class.pnone)
                         (map_option (\<lambda>lpm. (fst lpm * Abs_posreal (Rep_preal frac), frac *\<^sub>s snd lpm))
                         (fnm lp)))"
      apply (cases "fnm lp")
       apply (simp_all)
       apply (metis (mono_tags, lifting) mult_zero_left option_fold.simps(2) pf pf'_def)
      apply (intro conjI)
       apply (simp_all add: pf'_def)
      by (metis IH.hyps option.set_intros option_fold.simps(1) pf rangeI snds.intros)
  qed
qed


\<comment> \<open>Nested mask summation - uniqueness\<close>

lemma nm_loc_sum_unique:
  assumes "nm_loc_sum loc nm p"
      and "nm_loc_sum loc nm q"
    shows "p = q"
  using assms
proof (induct nm arbitrary: p q)
  case (NM mh mp fnm)
  obtain pf\<^sub>1 pf\<^sub>2 where
    pf\<^sub>1: "pf\<^sub>1 has_sumA (p - mh loc) \<and>
          (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf\<^sub>1 ploc)) (pf\<^sub>1 ploc = 0) (fnm ploc))" and
    pf\<^sub>2: "pf\<^sub>2 has_sumA (q - mh loc) \<and>
          (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf\<^sub>2 ploc)) (pf\<^sub>2 ploc = 0) (fnm ploc))"
    using NM.prems by auto
  have "pf\<^sub>1 = pf\<^sub>2"
  proof
    fix ploc
    show "pf\<^sub>1 ploc = pf\<^sub>2 ploc"
    proof (cases "fnm ploc")
      case None
      then show ?thesis
        by (metis (full_types) pf\<^sub>1 pf\<^sub>2 option_fold.simps(2))
    next
      case (Some a)
      then show ?thesis
        by (metis NM.hyps option.set_intros option_fold.simps(1) pf\<^sub>1 pf\<^sub>2 range_eqI)
    qed
  qed
  thus ?case
    by (metis NM.prems(1) NM.prems(2) infsumI nm_loc_sum.simps pf\<^sub>1 pf\<^sub>2 greater_minus_plus)
qed


\<comment> \<open>\<^const>\<open>has_sumA\<close>: conversion between real and preal\<close>

lemma has_sumA_Rep_preal:
  fixes f :: "'a \<Rightarrow> preal"
  assumes "f has_sumA S"
  shows "(\<lambda>x. Rep_preal (f x)) has_sumA (Rep_preal S)"
  apply (simp_all add: has_sum_def tendsto_def)
  sorry


\<comment> \<open>\<^const>\<open>has_sumA\<close>: sum greater than one\<close>

lemma has_sumA_nonneg_ge_one_real:
    fixes f :: "'a \<Rightarrow> real"
  assumes "f has_sumA S"
      and "\<And>x. f x \<ge> 0"
    shows "S \<ge> f a"
proof -
  have "f has_sumA (SUP F\<in>{F. finite F \<and> F \<subseteq> UNIV}. (sum f F))"
    by (metis (no_types, lifting) Collect_cong assms(1) assms(2) has_sum_nonneg_SUPREMUM_real summable_on_def)
  moreover have "(SUP F\<in>{F. finite F \<and> F \<subseteq> UNIV}. (sum f F)) \<ge> sum f {a}"
    by (smt (verit, best) top_greatest assms(2) Collect_mono_iff calculation empty_def finite.emptyI finite.insertI finite_sum_le_has_sum insert_Collect)
  moreover have "sum f {a} = f a" by auto
  ultimately show ?thesis
    by (metis assms(1) infsumI)
qed


lemma has_sumA_nonneg_ge_one_ennreal:
    fixes f :: "'a \<Rightarrow> ennreal"
  assumes "f has_sumA S"
    shows "S \<ge> f a"
proof -
  have "f has_sumA (SUP F\<in>{F. finite F \<and> F \<subseteq> UNIV}. (sum f F))"
    by (metis (full_types) nonneg_has_sum_complete zero_le)
  moreover have "(SUP F\<in>{F. finite F \<and> F \<subseteq> UNIV}. (sum f F)) \<ge> sum f {a}"
    by (metis (mono_tags, lifting) SUP_upper finite.emptyI finite_insert mem_Collect_eq subset_UNIV)
  moreover have "sum f {a} = f a" by auto
  ultimately show ?thesis
    using assms infsumI by metis
qed


lemma has_sumA_nonneg_ge_one_preal:
    fixes f :: "'a \<Rightarrow> preal"
  assumes "f has_sumA S"
      and "\<And>x. f x \<ge> 0"
    shows "S \<ge> f a"
proof -
  define f' where "f' = (\<lambda>x. Rep_preal (f x))"
  with assms(1) have "f' has_sumA (Rep_preal S)"
    using has_sumA_Rep_preal by blast
  thus ?thesis
    by (metis f'_def has_sumA_nonneg_ge_one_real less_eq_preal.rep_eq prat_non_negative)
qed


lemma has_sumA_nonneg_change_one_preal:
    fixes f :: "'a \<Rightarrow> preal"
  assumes "f has_sumA S"
  shows "f( a := v ) has_sumA (S - f a + v)"
  sorry


\<comment> \<open>Nested mask summation - replacing one sub-mask\<close>

(* lemma nm_loc_sum_change_sum_None:
  assumes "nm_loc_sum loc (NM mh mp fnm) p"
      and "option_fold (\<lambda>nm. nm_loc_sum loc nm q) (q = 0) (fnm ploc)"
    shows "nm_loc_sum loc (NM mh mp (fnm( ploc := None ))) (p - q)"
proof (cases "fnm ploc")
  case None
  then show ?thesis
    by (smt (verit) Rep_preal_inverse assms(1) assms(2) fun_upd_triv less_eq_preal.rep_eq minus_preal.abs_eq option_fold.simps(2) psub_smaller zero_preal.rep_eq)
next
  case (Some nm)
  from assms(1) obtain pf where pf_split:
    "mh loc \<le> p \<and>
     (pf has_sumA (p - mh loc) \<and>
      (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf ploc)) (pf ploc = 0) (fnm ploc)))"
    by auto
  define pf' where "pf' = pf( ploc := 0 )"
  have pf'_split:
    "mh loc \<le> p - q \<and>
     (pf' has_sumA (p - q - mh loc) \<and>
      (\<forall>l. option_fold (\<lambda>m. nm_loc_sum loc m (pf' l)) (pf' l = 0) ((fnm( ploc := None )) l)))"
  proof (standard; standard?)
    have "pf ploc = q"
      by (metis Some assms(2) nm_loc_sum_unique option_fold.simps(1) pf_split)
    with pf_split have "p - mh loc \<ge> q"
      using has_sumA_nonneg_ge_one_preal
      by (metis all_pos)
    thus "mh loc \<le> p - q"
      using less_eq_preal.rep_eq minus_preal.rep_eq pf_split by auto
    have "pf' has_sumA (p - mh loc - q)"
      using pf_split pf'_def \<open>pf ploc = q\<close>
      by (metis add.right_neutral has_sumA_nonneg_change_one_preal)
    moreover have "p - mh loc - q = p - q - mh loc"
      by (smt (verit, best) \<open>mh loc \<le> p - q\<close> \<open>q \<le> p - mh loc\<close> dual_order.trans minus_preal.abs_eq minus_preal.rep_eq pf_split psub_smaller)
    ultimately show "pf' has_sumA (p - q - mh loc)" by simp
  next
    show "\<forall>l. option_fold (\<lambda>m. nm_loc_sum loc m (pf' l)) (pf' l = 0) ((fnm(ploc := None)) l)"
      using pf'_def pf_split by auto
  qed
  show ?thesis
    apply simp using pf'_split
    using pf_split pf'_def by auto
qed *)


lemma nm_loc_sum_change_sum:
  assumes "nm_loc_sum loc (NM mh mp fnm) p"
      and "option_fold (\<lambda>nm. nm_loc_sum loc nm q) (q = 0) (fnm ploc)"
      and "option_fold (\<lambda>nm. nm_loc_sum loc nm r) (r = 0) nm'"
    shows "nm_loc_sum loc (NM mh mp' (fnm( ploc := nm' ))) (p - q + r)"
proof -
  from assms(1) obtain pf where pf_split:
    "mh loc \<le> p \<and>
     (pf has_sumA (p - mh loc) \<and>
      (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf ploc)) (pf ploc = 0) (fnm ploc)))"
    by auto
  define pf' where "pf' = pf( ploc := r )"

  have "pf ploc = q"
    apply (cases "fnm ploc")
    apply (metis (full_types) assms(2) option_fold.simps(2) pf_split)
    by (metis assms(2) nm_loc_sum_unique option_fold.simps(1) pf_split)

  \<comment> \<open>part 1\<close>
  have "mh loc \<le> p - q + r"
  proof -
    have "mh loc \<le> p - q"
      by (smt (verit, ccfv_SIG) \<open>pf ploc = q\<close> all_pos has_sumA_nonneg_ge_one_preal less_eq_preal.rep_eq minus_preal.rep_eq pf_split)
    thus "mh loc \<le> p - q + r"
      by (meson order_trans padd_pgte)
  qed

  \<comment> \<open>part 2\<close>
  moreover have "pf' has_sumA (p - q + r - mh loc)"
  proof -
    have "pf' has_sumA (p - mh loc - q + r)"
      by (metis \<open>pf ploc = q\<close> has_sumA_nonneg_change_one_preal pf'_def pf_split)
    moreover have "p - mh loc - q + r = p - q + r - mh loc"
      by (smt (verit, ccfv_SIG) Rep_preal_inject \<open>mh loc \<le> p - q + r\<close> \<open>pf ploc = q\<close> all_pos dual_order.trans has_sumA_nonneg_ge_one_preal minus_preal.rep_eq pf_split plus_preal.rep_eq psub_smaller)
    ultimately show "pf' has_sumA (p - q + r - mh loc)"
      by simp
  qed

  \<comment> \<open>part 3\<close>
  moreover have "\<forall>pl. option_fold (\<lambda>m. nm_loc_sum loc m (pf' pl)) (pf' pl = 0) ((fnm( ploc := nm' )) pl)"
    using assms(3) pf'_def pf_split by fastforce

  ultimately show ?thesis
    using nm_loc_sumI
    by blast
qed


\<comment> \<open>The sum of one sub-mask is smaller than the entire sum.\<close>

lemma nm_loc_sum_sub_le:
  assumes "nm_loc_sum loc (NM mh mp fnm) p"
      and "nm_loc_sum_option loc (fnm ploc) q"
    shows "q \<le> p"
proof (cases "fnm ploc")
  case None
  then show ?thesis
    using all_pos assms(2) by auto
next
  case (Some nm)
  with assms(2) show ?thesis
    apply simp
    by (smt (verit, best) Rep_preal_inverse assms(1) assms(2) fun_upd_triv greater_minus_plus minus_preal.rep_eq nm_loc_sum_change_sum nm_loc_sum_option.elims(2) nm_loc_sum_unique order_le_less)
qed


\<comment> \<open>Adding to a sub-mask\<close>

lemma nm_loc_sum_add_to_sub':
  assumes "nm_loc_sum loc (NM mh mp fnm) p"
      and "nm_loc_sum_option loc nm' q"
    shows "nm_loc_sum loc (NM mh mp' (fnm( ploc := fnm ploc + nm' ))) (p + q)"
proof -
  obtain s_sub where "option_fold (\<lambda>nm. nm_loc_sum loc nm s_sub) (s_sub = 0) (fnm ploc)"
    using assms(1) nm_loc_sum.simps by blast
  moreover have "s_sub \<le> p"
    by (metis assms(1) calculation nm_loc_sum_option.elims(1) nm_loc_sum_sub_le)
  moreover have "option_fold (\<lambda>nm. nm_loc_sum loc nm (s_sub + q)) (s_sub + q = 0) (fnm ploc + nm')"
    apply (cases "fnm ploc"; cases nm'; simp)
    using assms(2) calculation(1)
       apply (simp add: plus_option_def)
      apply (metis (mono_tags) add_0 assms(2) calculation(1) nm_loc_sum_option.elims(2) option_fold.simps(2) zero_option_def)
     apply (metis (mono_tags) add.right_neutral assms(2) calculation(1) nm_loc_sum_option.simps option_fold.simps(2) zero_option_def)
    by (metis assms(2) calculation(1) combine_options_simps(3) nm_loc_sum_add nm_loc_sum_option.elims(2) option_fold.simps(1) plus_option_def)
  ultimately have "nm_loc_sum loc (NM mh mp' (fnm( ploc := fnm ploc + nm' ))) (p - s_sub + (s_sub + q))"
    using assms(1) nm_loc_sum_change_sum by blast
  thus ?thesis
    by (metis \<open>s_sub \<le> p\<close> greater_minus_plus group_cancel.add1)
qed

lemma nm_loc_sum_add_to_sub:
  assumes "nm_loc_sum loc nm s"
      and "nm_loc_sum loc nm' s'"
    shows "nm_loc_sum loc (add_to_nm_loc_nm nm ploc nm') (s + s')"
  using assms nm_loc_sum_add_to_sub'[where nm'="Some nm'"]
  by (cases nm) (auto simp del: nm_loc_sum.simps)


\<comment> \<open>Sum does not depend on predicate mask\<close>

lemma nm_loc_sum_mp_irrelevant:
  assumes "nm_loc_sum loc (NM mh mp fnm) s"
  shows "nm_loc_sum loc (NM mh mp' fnm) s"
  using assms by force


\<comment> \<open>Nested mask subtraction\<close>

lemma nested_mask_sub_add:
  assumes "nm_diff = nested_mask_subtract nm1 nm2"
      and "\<And>x. get_mh_nm nm1 x \<ge> get_mh_nm nm2 x"
      and "\<And>x. get_mp_nm nm1 x \<ge> get_mp_nm nm2 x"
      and "\<And>x. \<exists>frac. get_nm_loc_nm nm2 x = frac *\<^sub>s get_nm_loc_nm nm1 x"
    shows "nm2 + nm_diff = nm1"
  sorry


subsection \<open>Zero Permission Location\<close>

lemma sum_0_implies_mh_zero:
  assumes "nm_loc_sum loc nm 0"
    shows "get_mh_nm nm loc = 0"
  by (metis assms get_mh_nm.simps leD nm_loc_sum.elims(2) preal_not_0_gt_0)

lemma sum_0_implies_sub_zero:
  assumes "nm_loc_sum loc nm 0"
      and "Some nm' = get_fnm_nm nm ploc"
    shows "nm_loc_sum loc nm' 0"
  sorry


subsection \<open>Sum of a smaller state\<close>

lemma nm_loc_sum_smaller:
  assumes "nm_loc_sum loc nm s"
      and "nm' \<le> nm"
    shows "\<exists>s'. nm_loc_sum loc nm' s"
  sorry

lemma nm_sum_is_bigger:
  fixes nm1 nm2 nm :: "'a nested_mask"
  assumes "nm = nm1 + nm2"
  shows "nm1 \<le> nm"
  sorry


end
