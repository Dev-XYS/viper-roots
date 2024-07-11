theory NestedMaskProperties
  imports TotalSemanticsCore HOL.Groups_Big "HOL-Analysis.Infinite_Sum"
begin


fun domain :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set" where
  "domain f = {x . True}"

abbreviation has_sumA (infixr "has'_sumA" 46) where
  "(f has_sumA S) \<equiv> (f has_sum S) (domain f)"

function (sequential) nm_loc_sum :: "heap_loc \<Rightarrow> 'a nested_mask \<Rightarrow> preal \<Rightarrow> bool" where
  "nm_loc_sum loc (NM mh mp fnm) p =
     (mh loc \<le> p \<and>
      (\<exists>pf. pf has_sumA (p - mh loc) \<and>
            (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf ploc)) (pf ploc = 0) (fnm ploc))))"
  by (pat_completeness) auto
termination
  apply (relation "{} <*lex*> nested_mask_rel <*lex*> {}")
  using wf_nested_mask_rel
   apply blast
  by (metis (mono_tags, lifting) in_lex_prod mem_Collect_eq)

lemma nm_loc_sumI:
  assumes "mh loc \<le> p \<and>
           (\<exists>pf. pf has_sumA (p - mh loc) \<and>
                 (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf ploc)) (pf ploc = 0) (fnm ploc)))"
  shows "nm_loc_sum loc (NM mh mp fnm) p"
  using assms by auto


\<comment> \<open>Nested mask summation - addition\<close>

lemma nm_loc_sum_add:
  assumes "nm_loc_sum loc nm\<^sub>1 p"
      and "nm_loc_sum loc nm\<^sub>2 q"
    shows "nm_loc_sum loc (nested_mask_merge nm\<^sub>1 nm\<^sub>2) (p + q)"
  using assms
proof (induct arbitrary: p q rule: nested_mask_merge.induct[of _ nm\<^sub>1 nm\<^sub>2])
  case IH: (1 mh\<^sub>1 mp\<^sub>1 fnm\<^sub>1 mh\<^sub>2 mp\<^sub>2 fnm\<^sub>2)
  show ?case
  proof -
    from IH have "mh\<^sub>1 loc \<le> p" and "mh\<^sub>2 loc \<le> q"
      by (metis get_mh_nm.simps nm_loc_sum.elims(1))+
    from IH(2) obtain pf\<^sub>1 where pf\<^sub>1: "pf\<^sub>1 has_sumA (p - mh\<^sub>1 loc) \<and>
      (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf\<^sub>1 ploc)) (pf\<^sub>1 ploc = 0) (fnm\<^sub>1 ploc))"
      by (metis nm_loc_sum.simps)
    from IH(3) obtain pf\<^sub>2 where pf\<^sub>2: "pf\<^sub>2 has_sumA (q - mh\<^sub>2 loc) \<and>
      (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf\<^sub>2 ploc)) (pf\<^sub>2 ploc = 0) (fnm\<^sub>2 ploc))"
      by (metis nm_loc_sum.simps)
    define pf where "pf = (pf\<^sub>1 +\<lbrakk>(+)\<rbrakk>+ pf\<^sub>2)"
    hence "domain pf = domain pf\<^sub>1" and "domain pf = domain pf\<^sub>2" by auto+
    hence has_sum: "pf has_sumA ((p - mh\<^sub>1 loc) + (q - mh\<^sub>2 loc))"
      using has_sum_add[of pf\<^sub>1 "domain pf" "p - mh\<^sub>1 loc" pf\<^sub>2 "q - mh\<^sub>2 loc"] fun_comb_def
      by (metis (no_types, lifting) pf\<^sub>1 pf\<^sub>2 has_sum_cong pf_def)
    define fnm where "fnm = (fnm\<^sub>1 +\<lparr>nested_mask_merge\<rparr>+ fnm\<^sub>2)"
    have all_sub: "\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf ploc)) (pf ploc = 0) (fnm ploc)"
    proof
      fix ploc
      show "option_fold (\<lambda>m. nm_loc_sum loc m (pf ploc)) (pf ploc = 0) (fnm ploc)"
      proof (cases "fnm\<^sub>1 ploc")
        case c1N: None
        show ?thesis
        proof (cases "fnm\<^sub>2 ploc")
          case c2N: None
          show ?thesis
            apply (simp del: nm_loc_sum.simps add: fnm_def pfun_comb_def combine_options_def option_fold_def)
            apply (simp del: nm_loc_sum.simps add: c1N c2N)
            by (metis (full_types) add_0 c1N c2N fun_comb_def option_fold.simps(2) pf\<^sub>1 pf\<^sub>2 pf_def)
        next
          case c2S: (Some a)
          show ?thesis
            apply (simp del: nm_loc_sum.simps add: fnm_def pfun_comb_def combine_options_def option_fold_def)
            apply (simp del: nm_loc_sum.simps add: c1N c2S)
            by (metis (mono_tags, lifting) add_0 c1N c2S fun_comb_def option_fold.simps(1) option_fold.simps(2) pf\<^sub>1 pf\<^sub>2 pf_def)
        qed
      next
        case c1S: (Some a)
        show ?thesis
        proof (cases "fnm\<^sub>2 ploc")
          case c2N: None
          show ?thesis
            apply (simp del: nm_loc_sum.simps add: fnm_def pfun_comb_def combine_options_def option_fold_def)
            apply (simp del: nm_loc_sum.simps add: c1S c2N)
            by (metis (mono_tags, lifting) add.right_neutral c1S c2N fun_comb_def option_fold.simps(1) option_fold.simps(2) pf\<^sub>1 pf\<^sub>2 pf_def)
        next
          case c2S: (Some a)
          show ?thesis
            apply (simp del: nm_loc_sum.simps add: fnm_def pfun_comb_def combine_options_def option_fold_def)
            apply (simp del: nm_loc_sum.simps add: c1S c2S)
            by (metis (mono_tags, lifting) IH.hyps c1S c2S fun_comb_def option_fold.simps(1) pf\<^sub>1 pf\<^sub>2 pf_def)
        qed
      qed
    qed
    define mh where "mh = field_mask_merge mh\<^sub>1 mh\<^sub>2"
    define mp where "mp = predicate_mask_merge mp\<^sub>1 mp\<^sub>2"
    have "mh loc \<le> p + q"
      by (simp add: PosReal.padd_mono \<open>mh\<^sub>1 loc \<le> p\<close> \<open>mh\<^sub>2 loc \<le> q\<close> fun_comb_def mh_def)
    moreover from has_sum all_sub have
      "\<exists>pf. pf has_sumA ((p - mh\<^sub>1 loc) + (q - mh\<^sub>2 loc)) \<and>
            (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf ploc)) (pf ploc = 0) (fnm ploc))"
      by metis
    moreover have "mh loc = mh\<^sub>1 loc + mh\<^sub>2 loc"
      by (simp add: fun_comb_def mh_def)
    have "p + q \<ge> mh\<^sub>1 loc + mh\<^sub>2 loc"
      using PosReal.padd_mono \<open>mh\<^sub>1 loc \<le> p\<close> \<open>mh\<^sub>2 loc \<le> q\<close> by presburger
    moreover hence "(p - mh\<^sub>1 loc) + (q - mh\<^sub>2 loc) = (p + q) - (mh\<^sub>1 loc + mh\<^sub>2 loc)"
      using \<open>mh\<^sub>1 loc \<le> p\<close> \<open>mh\<^sub>2 loc \<le> q\<close> Rep_preal_inject minus_preal.rep_eq plus_preal.rep_eq
      by fastforce
    moreover have "nested_mask_merge (NM mh\<^sub>1 mp\<^sub>1 fnm\<^sub>1) (NM mh\<^sub>2 mp\<^sub>2 fnm\<^sub>2) = NM mh mp fnm"
      by (simp add: fnm_def mh_def mp_def)
    ultimately show "nm_loc_sum loc (nested_mask_merge (NM mh\<^sub>1 mp\<^sub>1 fnm\<^sub>1) (NM mh\<^sub>2 mp\<^sub>2 fnm\<^sub>2)) (p + q)"
      by (simp add: \<open>mh loc = PosReal.padd (mh\<^sub>1 loc) (mh\<^sub>2 loc)\<close>)
  qed
qed


\<comment> \<open>Nested mask summation - multiplication\<close>

lemma nm_loc_sum_mult:
    fixes frac :: preal
  assumes "frac > 0"
      and "nm_loc_sum loc nm p"
    shows "nm_loc_sum loc (nested_mask_multiply nm frac) (p * frac)"
  using assms(2)
proof (induct arbitrary: p rule: nested_mask_multiply.induct[of _ nm p])
  case IH: (1 mh mp fnm p)
  define mh' where "mh' = field_mask_multiply mh frac"
  define mp' where "mp' = predicate_mask_multiply mp frac"
  define fnm' where "fnm' = (map_option (\<lambda>nm. nested_mask_multiply nm frac)) \<circ> fnm"
  have "mh' loc \<le> p * frac"
    apply (simp add: mh'_def)
    using IH(2)
    by (simp add: less_eq_preal.rep_eq mult.commute mult_left_mono prat_non_negative times_preal.rep_eq)
  from IH(2) obtain pf where pf: "pf has_sumA (p - mh loc) \<and>
      (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf ploc)) (pf ploc = 0) (fnm ploc))"
    using nm_loc_sum.simps by blast
  define pf' where "pf' = ((*) frac) \<circ> pf"
  moreover hence "domain pf' = domain pf" by simp
  moreover have "frac * p - mh' loc = frac * p - frac * mh loc"
    by (simp add: mh'_def)
  moreover hence "frac * p - mh' loc = frac * (p - mh loc)"
    by (smt (verit, ccfv_threshold) IH.prems PosReal.pmult_comm Rep_preal_inverse \<open>mh' loc \<le> PosReal.pmult p frac\<close> comp_apply field_mask_multiply.simps mh'_def minus_preal.rep_eq nm_loc_sum.simps right_diff_distrib times_preal.rep_eq)
  ultimately have "pf' has_sumA (frac * p - mh' loc)"
    using has_sum_cmult_right[of pf "domain pf" "p - mh loc" frac] pf pf'_def
    by (metis (no_types, lifting) comp_apply has_sum_cong)
  moreover have "(\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf' ploc)) (pf' ploc = 0) (fnm' ploc))"
  proof
    fix ploc
    show "option_fold (\<lambda>m. nm_loc_sum loc m (pf' ploc)) (pf' ploc = PosReal.pnone) (fnm' ploc)"
    proof (cases "fnm ploc")
      case None
      then show ?thesis
        by (metis (mono_tags, lifting) comp_apply fnm'_def mult_zero_right option.simps(8) option_fold.simps(2) pf pf'_def)
    next
      case (Some nm)
      hence "fnm' ploc = Some (nested_mask_multiply nm frac)"
        using fnm'_def by simp
      then show ?thesis
        apply simp
        using IH(1)[of "fnm ploc" nm]
        by (metis Some comp_apply mult.commute option_fold.simps(1) pf pf'_def rangeI)
    qed
  qed
  ultimately show ?case
    using PosReal.pmult_comm \<open>mh' loc \<le> PosReal.pmult p frac\<close> fnm'_def mh'_def by auto
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
    by (metis NM.prems(1) NM.prems(2) Rep_preal_inverse diff_diff_eq2 diff_left_imp_eq infsumI minus_preal.rep_eq nm_loc_sum.simps pf\<^sub>1 pf\<^sub>2)
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
  have "f has_sumA (SUP F\<in>{F. finite F \<and> F \<subseteq> domain f}. (sum f F))"
    by (metis (no_types, lifting) Collect_cong assms(1) assms(2) has_sum_imp_summable has_sum_nonneg_SUPREMUM_real)
  moreover have "(SUP F\<in>{F. finite F \<and> F \<subseteq> domain f}. (sum f F)) \<ge> sum f {a}"
    using assms(2)
    by (smt (verit, del_insts) Collect_mono_iff calculation domain.elims empty_def finite.emptyI finite.insertI finite_sum_le_has_sum insert_Collect)
  moreover have "sum f {a} = f a" by auto
  ultimately show ?thesis
    using assms(1) has_sum_unique by auto
qed


lemma has_sumA_nonneg_ge_one_ennreal:
    fixes f :: "'a \<Rightarrow> ennreal"
  assumes "f has_sumA S"
    shows "S \<ge> f a"
proof -
  have "f has_sumA (SUP F\<in>{F. finite F \<and> F \<subseteq> domain f}. (sum f F))"
    by (metis (full_types) nonneg_has_sum_complete zero_le)
  moreover have "(SUP F\<in>{F. finite F \<and> F \<subseteq> domain f}. (sum f F)) \<ge> sum f {a}"
    by (metis (no_types, lifting) SUP_upper domain.elims empty_subsetI insert_subset mem_Collect_eq sum.infinite zero_le)
  moreover have "sum f {a} = f a" by auto
  ultimately show ?thesis
    using assms has_sum_unique by auto
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


\<comment> \<open>Lemmas on SUP\<close>

(* lemma SUP_including_one:
    fixes f :: "'a \<Rightarrow> real"
  assumes "SUP F\<in>{F. finite F \<and> F \<subseteq> D}. (sum f F) = S"
      and "a \<in> D"
      and "\<And>x. x \<in> D \<Longrightarrow> f x \<ge> 0"
    shows "SUP F\<in>{F. finite F \<and> F \<subseteq> D \<and> a \<in> F}. (sum f F) = S"
proof -
  from assms(1) have "SUP F\<in>{F. finite F \<and> F \<subseteq> D}. (sum f F) =
                      CONST Sup ((\<lambda>F. sum f F) ` {F. finite F \<and> F \<subseteq> D})"
  from assms(1) have "S = (LEAST z. \<forall>F. finite F \<and> F \<subseteq> D \<longrightarrow> sum f F \<le> z)" *)


\<comment> \<open>\<^const>\<open>has_sumA\<close>: sum excluding one\<close>

(* lemma has_sum_nonneg_exclude_one_real':
    fixes f :: "'a \<Rightarrow> real"
  assumes "(f has_sum S) (A - {a})"
      and "a \<in> A"
    shows "(f( a := 0 ) has_sum S) A"
  sorry


lemma has_sumA_nonneg_exclude_one_real:
    fixes f :: "'a \<Rightarrow> real"
  assumes "f has_sumA S"
      and "\<And>x. f x \<ge> 0"
    shows "f( a := 0 ) has_sumA (S - f a)"
proof -
  have "f has_sumA (SUP F\<in>{F. finite F \<and> F \<subseteq> domain f}. (sum f F))"
    by (metis (no_types, lifting) Collect_cong assms(1) assms(2) has_sum_imp_summable has_sum_nonneg_SUPREMUM_real)
  have "\<And>F. finite F \<Longrightarrow> F \<subseteq> domain f \<Longrightarrow> a \<in> F \<Longrightarrow> sum f F = sum (f( a := 0 )) F + f a"
  proof -
    fix F
    assume "finite F" and "F \<subseteq> domain f" and "a \<in> F"
    hence "sum f F - f a = sum f (F - {a})" using sum_diff1[of F f a]
      by presburger
    moreover have "sum (f(a := 0)) F = (f(a := 0)) a + sum (f(a := 0)) (F - {a})"
      by (meson \<open>a \<in> F\<close> \<open>finite F\<close> sum.remove)
    moreover hence "sum (f(a := 0)) F = sum f (F - {a})" by auto
    ultimately show "sum f F = sum (f(a := 0)) F + f a"
      by linarith
  qed
  have "\<And>F. finite F \<and> F \<subseteq> domain f \<Longrightarrow> \<exists>F'. finite F' \<and> F' \<subseteq> domain f \<and> a \<in> F' \<and> sum f F' \<ge> sum f F"
    sorry
  have "(SUP F\<in>{F. finite F \<and> F \<subseteq> domain f \<and> a \<in> F}. (sum f F)) =
        (SUP F\<in>{F. finite F \<and> F \<subseteq> domain f}. (sum f F))" sorry
  have "f has_sumA (SUP F\<in>{F. finite F \<and> F \<subseteq> domain f \<and> a \<in> F}. (sum f F))" sorry
  show ?thesis sorry
qed *)


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
    apply (metis assms(2) option_fold.simps(2) pf_split)
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


end
