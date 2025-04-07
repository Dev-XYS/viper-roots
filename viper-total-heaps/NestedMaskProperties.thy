section \<open>Permission of a Heap Location Inside a Nested Mask Using Infinite Sum\<close>

theory NestedMaskProperties
  imports HOL.Groups_Big "HOL-Analysis.Infinite_Sum"
          TotalMaskUtil TotalStateUtil
begin


subsection \<open>Definitions\<close>

abbreviation has_sumA :: "('a \<Rightarrow> 'b :: {comm_monoid_add, topological_space}) \<Rightarrow> 'b \<Rightarrow> bool" (infixr "has'_sumA" 46) where
  "(f has_sumA S) \<equiv> (f has_sum S) UNIV"


function (sequential) nm_loc_sum' :: "heap_loc \<Rightarrow> 'a nested_mask \<Rightarrow> real \<Rightarrow> bool" where
  "nm_loc_sum' loc (NM mh fnm) p =
     (Rep_preal (mh loc) \<le> p \<and>
      (\<exists>pf. pf has_sumA (p - Rep_preal (mh loc)) \<and>
            (\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf lp)) (pf lp = 0) (fnm lp))))"
  by (pat_completeness) auto
termination
  apply (relation "{} <*lex*> nested_mask_rel <*lex*> {}")
  using wf_nested_mask_rel
   apply blast
  by fastforce

fun nm_loc_sum :: "heap_loc \<Rightarrow> 'a nested_mask \<Rightarrow> preal \<Rightarrow> bool" where
  "nm_loc_sum loc nm p = nm_loc_sum' loc nm (Rep_preal p)"

lemma nm_loc_sum'I:
  assumes "Rep_preal (mh loc) \<le> p \<and>
           (\<exists>pf. pf has_sumA (p - Rep_preal (mh loc)) \<and>
                 (\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf lp)) (pf lp = 0) (fnm lp)))"
  shows "nm_loc_sum' loc (NM mh fnm) p"
  using assms
  by auto


fun nm_loc_sum_option :: "heap_loc \<Rightarrow> 'a nested_mask option \<Rightarrow> preal \<Rightarrow> bool" where
  "nm_loc_sum_option loc nm_opt p = option_fold (\<lambda>nm. nm_loc_sum loc nm p) (p = 0) nm_opt"


subsection \<open>Sum is Non-Negative\<close>

lemma nm_loc_sum'_nonneg:
  assumes "nm_loc_sum' loc nm p"
  shows "p \<ge> 0"
  by (meson assms nm_loc_sum'.elims(2) order_trans prat_non_negative)


subsection \<open>Properties of Addition\<close>

lemma nm_loc_sum'_add:
  assumes "nm_loc_sum' loc nm\<^sub>1 p"
      and "nm_loc_sum' loc nm\<^sub>2 q"
    shows "nm_loc_sum' loc (nm\<^sub>1 + nm\<^sub>2) (p + q)"
  using assms
proof (induct arbitrary: p q rule: nested_mask_merge.induct[of _ nm\<^sub>1 nm\<^sub>2])
  case IH: (1 mh\<^sub>1 fnm\<^sub>1 mh\<^sub>2 fnm\<^sub>2)
  from IH have "Rep_preal (mh\<^sub>1 loc) \<le> p" and "Rep_preal (mh\<^sub>2 loc) \<le> q"
    by (metis get_mh_nm.simps nm_loc_sum'.elims(1))+
  from IH(2) obtain pf\<^sub>1 where pf\<^sub>1: "pf\<^sub>1 has_sumA (p - Rep_preal (mh\<^sub>1 loc)) \<and>
      (\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf\<^sub>1 lp)) (pf\<^sub>1 lp = 0) (fnm\<^sub>1 lp))"
    by (metis nm_loc_sum'.simps)
  from IH(3) obtain pf\<^sub>2 where pf\<^sub>2: "pf\<^sub>2 has_sumA (q - Rep_preal (mh\<^sub>2 loc)) \<and>
      (\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf\<^sub>2 lp)) (pf\<^sub>2 lp = 0) (fnm\<^sub>2 lp))"
    by (metis nm_loc_sum'.simps)

  define pf where "pf = (\<lambda>x. pf\<^sub>1 x + pf\<^sub>2 x)"
  hence has_sum: "pf has_sumA ((p - Rep_preal (mh\<^sub>1 loc)) + (q - Rep_preal (mh\<^sub>2 loc)))"
    using has_sum_add[of pf\<^sub>1 UNIV "p - Rep_preal (mh\<^sub>1 loc)" pf\<^sub>2 "q - Rep_preal (mh\<^sub>2 loc)"] pf\<^sub>1 pf\<^sub>2
    by blast    

  show ?case
    apply (simp add: plus_nested_mask_def del: split_paired_All)
    apply (intro conjI)
     apply (simp add: \<open>Rep_preal (mh\<^sub>1 loc) \<le> p\<close> \<open>Rep_preal (mh\<^sub>2 loc) \<le> q\<close> add_masks_def add_mono plus_preal.rep_eq)
    apply (rule exI[of _ pf])
    apply (intro conjI)
     apply (simp add: add_masks_def)
     apply (subgoal_tac "p - Rep_preal (mh\<^sub>1 loc) + (q - Rep_preal (mh\<^sub>2 loc)) =
                         p + q - (Rep_preal (mh\<^sub>1 loc) + Rep_preal (mh\<^sub>2 loc))")
    using has_sum plus_preal.rep_eq
      apply presburger
     apply (simp add: preal_to_real)
    apply (simp only: plus_nested_mask_def[symmetric])
  proof standard
    fix lp
    show "option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf lp))
                        (pf lp = 0)
                        ((fnm\<^sub>1 +\<lparr> \<lambda>lpm\<^sub>1 lpm\<^sub>2. (fst lpm\<^sub>1 + fst lpm\<^sub>2, snd lpm\<^sub>1 + snd lpm\<^sub>2) \<rparr>+ fnm\<^sub>2) lp)"
      apply (cases "fnm\<^sub>1 lp"; cases "fnm\<^sub>2 lp")
         apply (simp_all add: option_fold_def pfun_comb_def)
         apply (metis (mono_tags) add_0 option_fold.simps(2) pf\<^sub>1 pf\<^sub>2 pf_def)
        apply (metis (mono_tags, lifting) add_0 option_fold.simps(1) option_fold.simps(2) pf\<^sub>1 pf\<^sub>2 pf_def)
      apply (metis (mono_tags, lifting) add.right_neutral option_fold.simps(1) option_fold.simps(2) pf\<^sub>1 pf\<^sub>2 pf_def)
      by (metis (no_types, lifting) IH.hyps is_none_code(2) option.sel option_fold.simps(1) pf\<^sub>1 pf\<^sub>2 pf_def range_eqI)
  qed
qed

lemma nm_loc_sum_add:
  assumes "nm_loc_sum loc nm\<^sub>1 p"
      and "nm_loc_sum loc nm\<^sub>2 q"
    shows "nm_loc_sum loc (nm\<^sub>1 + nm\<^sub>2) (p + q)"
  by (metis assms nm_loc_sum'_add nm_loc_sum.elims(2) nm_loc_sum.elims(3) plus_preal.rep_eq)


subsection \<open>Properties of Multiplication\<close>

lemma nm_loc_sum'_mult:
    fixes frac :: preal
  assumes "nm_loc_sum' loc nm p"
    shows "nm_loc_sum' loc (frac *\<^sub>s nm) (p * Rep_preal frac)"
  using assms(1)
proof (induct nm arbitrary: p)
  case IH: (NM mh fnm)
  from IH(2) obtain pf where
    "Rep_preal (mh loc) \<le> p" and
    pf: "pf has_sumA (p - Rep_preal (mh loc)) \<and> (\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf lp)) (pf lp = 0) (fnm lp))"
    by (blast elim: nm_loc_sum'.elims)

  define pf' where "pf' = (\<lambda>x. pf x * Rep_preal frac)"
  hence has_sum: "pf' has_sumA (Rep_preal frac * (p - Rep_preal (mh loc)))"
    using has_sum_cmult_right[of pf "UNIV" "p - Rep_preal (mh loc)" "Rep_preal frac"] pf pf'_def
    by (simp add: mult.commute)

  show ?case
    apply (simp add: scale_nested_mask_def del: split_paired_All)
    apply (intro conjI)
     apply (simp add: mul_mask_def preal_to_real)
    using PosReal.pmult_comm \<open>Rep_preal (mh loc) \<le> p\<close> less_eq_preal.rep_eq mult_left_mono prat_non_negative times_preal.rep_eq
     apply (metis mult.commute)
    apply (rule exI[of _ pf'])
    apply (intro conjI)
     apply (simp add: mul_mask_def)
     apply (subgoal_tac "p * Rep_preal frac - Rep_preal frac * Rep_preal (mh loc) = Rep_preal frac * (p - Rep_preal (mh loc))")
    using has_sum times_preal.rep_eq
      apply presburger
     apply (simp add: PosReal.pmult_comm right_diff_distrib')
    apply (simp only: scale_nested_mask_def[symmetric])
  proof standard
    fix lp
    show "(frac = 0 \<longrightarrow> pf' lp = 0) \<and>
          (frac \<noteq> 0 \<longrightarrow>
             option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf' lp))
                         (pf' lp = 0)
                         (map_option (\<lambda>lpm. (fst lpm * Abs_posreal frac, frac *\<^sub>s snd lpm))
                         (fnm lp)))"
      apply (cases "fnm lp")
       apply (simp_all)
       apply (metis (mono_tags, lifting) mult_zero_left option_fold.simps(2) pf pf'_def)
      apply (intro conjI)
       apply (simp_all add: pf'_def zero_preal.rep_eq)
      by (metis IH.hyps option.set_intros option_fold.simps(1) pf rangeI snds.intros)
  qed
qed

lemma nm_loc_sum_mult:
    fixes frac :: preal
  assumes "nm_loc_sum loc nm p"
    shows "nm_loc_sum loc (frac *\<^sub>s nm) (p * frac)"
  by (metis assms nm_loc_sum'_mult nm_loc_sum.elims(1) times_preal.rep_eq)


subsection \<open>Uniqueness\<close>

lemma nm_loc_sum'_unique:
  assumes "nm_loc_sum' loc nm p"
      and "nm_loc_sum' loc nm q"
    shows "p = q"
  using assms
proof (induct nm arbitrary: p q)
  case (NM mh fnm)
  obtain pf\<^sub>1 pf\<^sub>2 where
    pf\<^sub>1: "pf\<^sub>1 has_sumA (p - Rep_preal (mh loc)) \<and>
          (\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf\<^sub>1 lp)) (pf\<^sub>1 lp = 0) (fnm lp))" and
    pf\<^sub>2: "pf\<^sub>2 has_sumA (q - Rep_preal (mh loc)) \<and>
          (\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf\<^sub>2 lp)) (pf\<^sub>2 lp = 0) (fnm lp))"
    using NM.prems
    by auto
  have "pf\<^sub>1 = pf\<^sub>2"
  proof
    fix lp
    show "pf\<^sub>1 lp = pf\<^sub>2 lp"
    proof (cases "fnm lp")
      case None
      then show ?thesis
        by (metis (mono_tags, lifting) option_fold.simps(2) pf\<^sub>1 pf\<^sub>2)
    next
      case (Some a)
      then show ?thesis
        by (metis NM.hyps option.set_intros option_fold.simps(1) pf\<^sub>1 pf\<^sub>2 range_eqI snds.intros)
    qed
  qed
  thus ?case
    using has_sum_unique pf\<^sub>1 pf\<^sub>2
    by fastforce
qed


lemma nm_loc_sum_unique:
  assumes "nm_loc_sum loc nm p"
      and "nm_loc_sum loc nm q"
    shows "p = q"
  using assms
  unfolding nm_loc_sum.simps
  by (simp add: nm_loc_sum'_unique Rep_preal_inject[symmetric])


subsection \<open>\<^const>\<open>has_sumA\<close>: sum greater than one\<close>

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

lemma nm_loc_sum'_submask_le:
  assumes "nm_loc_sum' loc (NM mh fnm) p"
      and "option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) q) (q = 0) (fnm lp)"
    shows "q \<le> p"
proof (cases "fnm lp")
  case None
  then show ?thesis
    by (metis (full_types) assms nm_loc_sum'_nonneg option_fold.simps(2))
next
  case (Some lpm)
  obtain pf where pf: "pf has_sumA p - Rep_preal (mh loc) \<and>
                       (\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf lp)) (pf lp = 0) (fnm lp))"
    using assms(1)
    by (blast elim: nm_loc_sum'.elims)
  hence "pf lp = q"
    by (metis Some assms(2) nm_loc_sum'_unique option_fold.simps(1))
  have "\<And>x. pf x \<ge> 0"
    by (smt (verit) has_Some_iff nm_loc_sum'_nonneg pf)
  moreover have "q \<le> p - Rep_preal (mh loc)"
    using has_sumA_nonneg_ge_one_real[OF conjunct1[OF pf]] \<open>pf lp = q\<close> calculation
    by blast
  ultimately show ?thesis
    by (smt (verit, del_insts) prat_non_negative)
qed

lemma nm_loc_sum_submask_le:
  assumes "nm_loc_sum loc (NM mh fnm) p"
      and "option_fold (\<lambda>lpm. nm_loc_sum loc (snd lpm) q) (q = 0) (fnm lp)"
    shows "q \<le> p"
  by (smt (verit) all_pos assms(1) assms(2) has_Some_iff less_eq_preal.rep_eq nm_loc_sum'_submask_le nm_loc_sum.elims(2) option_fold.simps(1))


subsection \<open>Change One Sub-Mask\<close>

lemma has_sumA_change_one_real:
    fixes f :: "'a \<Rightarrow> real"
  assumes "f has_sumA S"
    shows "f( a := v ) has_sumA (S - f a + v)"
proof -
  define d where "d = (\<lambda>x. if x = a then v - f a else 0)"
  hence "f( a := v ) = (\<lambda>x. f x + d x)"
    by auto
  moreover have "d has_sumA (v - f a)"
  proof -
    have "(d has_sum (v - f a)) {a}"
      by (metis d_def empty_iff has_sum_empty has_sum_insert verit_sum_simplify)
    moreover have "(d has_sum 0) (UNIV - {a})"
      apply (subgoal_tac "\<And>x. x \<in> (UNIV - {a}) \<Longrightarrow> d x = 0")
      using has_sum_0
       apply blast
      by (simp add: d_def)
    ultimately show ?thesis
      by (metis (mono_tags, lifting) Diff_UNIV Diff_iff d_def has_sum_cong_neutral insertCI)
  qed
  moreover have "(\<lambda>x. f x + d x) has_sumA (S - f a + v)"
  proof -
    have "(\<lambda>x. f x + d x) has_sumA S + (v - f a)"
      using assms calculation(2) has_sum_add
      by blast
    then show ?thesis
      by argo
  qed
  ultimately show ?thesis
    by argo
qed


lemma nm_loc_sum'_change_sum:
  assumes "nm_loc_sum' loc (NM mh fnm) p"
      and "option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) q) (q = 0) (fnm lp)"
      and "option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) r) (r = 0) lpm'"
    shows "nm_loc_sum' loc (NM mh (fnm( lp := lpm' ))) (p - q + r)"
proof -
  from assms(1) obtain pf where pf_split:
    "Rep_preal (mh loc) \<le> p \<and>
     (pf has_sumA (p - Rep_preal (mh loc)) \<and>
      (\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf lp)) (pf lp = 0) (fnm lp)))"
    by auto
  define pf' where "pf' = pf( lp := r )"

  have "pf lp = q"
    apply (cases "fnm lp")
    apply (metis (mono_tags) assms(2) option_fold.simps(2) pf_split)
    by (metis assms(2) nm_loc_sum'_unique option_fold.simps(1) pf_split)

  \<comment> \<open>part 1\<close>
  have "Rep_preal (mh loc) \<le> p - q + r"
  proof -
    have "\<And>x. pf x \<ge> 0"
      by (metis (mono_tags, lifting) le_numeral_extra(3) nm_loc_sum'_nonneg not_None_eq option_fold.simps(1) option_fold.simps(2) pf_split)
    moreover have "p - Rep_preal (mh loc) \<ge> q"
      using has_sumA_nonneg_ge_one_real[OF conjunct1[OF conjunct2[OF pf_split]]] \<open>\<And>x. 0 \<le> pf x\<close> \<open>pf lp = q\<close>
      by blast
    ultimately have "Rep_preal (mh loc) \<le> p - q"
      by argo
    moreover have "r \<ge> 0"
      by (metis (mono_tags, lifting) assms(3) dual_order.refl nm_loc_sum'_nonneg not_None_eq option_fold.simps(1) option_fold.simps(2))
    ultimately show ?thesis
      by force
  qed

  \<comment> \<open>part 2\<close>
  moreover have "pf' has_sumA (p - q + r - Rep_preal (mh loc))"
  proof -
    have "pf' has_sumA (p - Rep_preal (mh loc) - q + r)"
      by (metis \<open>pf lp = q\<close> has_sumA_change_one_real pf'_def pf_split)
    moreover have "p - Rep_preal (mh loc) - q + r = p - q + r - Rep_preal (mh loc)"
      by argo
    ultimately show "pf' has_sumA (p - q + r - Rep_preal (mh loc))"
      by simp
  qed

  \<comment> \<open>part 3\<close>
  moreover have "\<forall>l. option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf' l)) (pf' l = 0) ((fnm( lp := lpm' )) l)"
    using assms(3) pf'_def pf_split by fastforce

  ultimately show ?thesis
    using nm_loc_sum'I
    by blast
qed

lemma nm_loc_sum_change_sum:
  assumes "nm_loc_sum loc (NM mh fnm) p"
      and "option_fold (\<lambda>lpm. nm_loc_sum loc (snd lpm) q) (q = 0) (fnm lp)"
      and "option_fold (\<lambda>lpm. nm_loc_sum loc (snd lpm) r) (r = 0) lpm'"
    shows "nm_loc_sum loc (NM mh (fnm( lp := lpm' ))) (p - q + r)"
proof -
  have 1: "(q = 0) = (Rep_preal q = 0)"
    by (metis Rep_preal_inverse zero_preal.rep_eq)
  have 2: "(r = 0) = (Rep_preal r = 0)"
    by (metis Rep_preal_inverse zero_preal.rep_eq)
  have 3: "p \<ge> q"
    using assms(1) assms(2) nm_loc_sum_submask_le
    by blast
  show ?thesis using
    nm_loc_sum'_change_sum[OF assms(1)[simplified nm_loc_sum.simps]
                              assms(2)[simplified nm_loc_sum.simps 1]
                              assms(3)[simplified nm_loc_sum.simps 2]]
    unfolding nm_loc_sum.simps
    using 3 minus_preal.rep_eq plus_preal.rep_eq
    by presburger
qed


subsection \<open>Adding to a Sub-Mask\<close>

(*
lemma nm_loc_sum_add_to_sub':
  assumes "nm_loc_sum loc (NM mh fnm) p"
      and "nm_loc_sum_option loc nm' q"
    shows "nm_loc_sum loc (NM mh (fnm( ploc := fnm ploc + nm' ))) (p + q)"
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
*)

lemma nm_loc_sum'_add_to_lpm:
  assumes "nm_loc_sum' loc nm s"
      and "nm_loc_sum' loc nm' s'"
    shows "nm_loc_sum' loc (add_to_lpm_nm nm lp (Some (p, nm'))) (s + s')"
proof -
  define mh where "mh = get_mh_nm nm"
  define fnm where "fnm = get_fnm_nm nm"
  have "nm = NM mh fnm"
    by (simp add: fnm_def mh_def nm_get_eq)
  with assms(1) have nm_sum: "nm_loc_sum' loc (NM mh fnm) s"
    by fast

  from iffD1[OF nm_loc_sum'.simps nm_sum] obtain pf where
    "Rep_preal (mh loc) \<le> s" and
    "pf has_sumA (s - Rep_preal (mh loc))" and
    pf: "\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf lp)) (pf lp = 0) (fnm lp)"
    by blast

  have lpm_origin_sum: "option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf lp)) (pf lp = 0) (fnm lp)"
  using pf
  by blast

  have lpm_addend_sum: "option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) s') (s' = 0) (Some (p, nm'))"
    by (simp add: assms(2))

  show ?thesis
  proof (cases "fnm lp")
    case None
    hence new_nm: "add_to_lpm_nm nm lp (Some (p, nm')) = NM mh (fnm( lp := Some (p, nm') ))"
      by (simp add: \<open>nm = _\<close>)
    have *: "s + s' = s - 0 + s'"
      by auto
    show ?thesis
      apply (subst new_nm)
      apply (subst *)
      apply (rule nm_loc_sum'_change_sum)
        apply (rule nm_sum)
       apply (simp add: None)
      by (rule lpm_addend_sum)
  next
    case (Some lpm)
    hence new_nm: "add_to_lpm_nm nm lp (Some (p, nm')) = NM mh (fnm( lp := Some (fst lpm + p, snd lpm + nm') ))"
      by (simp add: \<open>nm = _\<close>)
    have *: "s + s' = s - pf lp + (pf lp + s')"
      by auto
    have **: "option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf lp + s')) (pf lp + s' = 0) (Some (fst lpm + p, snd lpm + nm'))"
      apply simp
      using Some assms(2) lpm_origin_sum nm_loc_sum'_add
      by fastforce
    show ?thesis
      apply (subst new_nm)
      apply (subst *)
      apply (rule nm_loc_sum'_change_sum)
        apply (rule nm_sum)
       apply (rule lpm_origin_sum)
      by (rule **)
  qed
qed

lemma nm_loc_sum_add_to_lpm:
  assumes "nm_loc_sum loc nm s"
      and "nm_loc_sum loc nm' s'"
    shows "nm_loc_sum loc (add_to_lpm_nm nm lp (Some (p, nm'))) (s + s')"
  by (metis assms nm_loc_sum'_add_to_lpm nm_loc_sum.elims(2) nm_loc_sum.elims(3) plus_preal.rep_eq)


subsection \<open>Zero/Non-Zero Permission Location\<close>

lemma sum_0_implies_mh_zero:
  assumes "nm_loc_sum loc nm 0"
    shows "get_mh_nm nm loc = 0"
  by (metis assms less_eq_preal.rep_eq nm_get_eq nm_loc_sum'.simps nm_loc_sum.simps padd_pos preal_gte_padd)


subsection \<open>Sub-Mask Smaller\<close>

lemma sub_mask_smaller:
  assumes "nm_loc_sum loc nm s"
      and "Some (p,nm') = get_fnm_nm nm lp"
    shows "\<exists>s'. s' \<le> s \<and> nm_loc_sum loc nm' s'"
proof -
  obtain mh fnm pf where
    "nm = NM mh fnm" and
    "pf has_sumA (Rep_preal s - Rep_preal (mh loc)) \<and>
     (\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf lp)) (pf lp = 0) (fnm lp))"
    by (metis assms(1) nm_loc_sum'.elims(2) nm_loc_sum.simps)
  show ?thesis
    apply (rule exI[of _ "Abs_preal (pf lp)"])
    by (smt (verit, ccfv_threshold) \<open>nm = NM mh fnm\<close> \<open>pf has_sumA Rep_preal s - Rep_preal (mh loc) \<and> (\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf lp)) (pf lp = 0) (fnm lp))\<close> assms(2) get_fnm_nm.simps has_Some_iff has_sumA_nonneg_ge_one_real less_eq_preal.rep_eq mem_Collect_eq nm_loc_sum'_nonneg nm_loc_sum.elims(3) option_fold.simps(1) prat_non_negative Abs_preal_inverse snd_conv)
qed


subsection \<open>Sum of a smaller state\<close>

lemma has_sumA_nonneg_smaller:
    fixes S :: real
  assumes "f has_sumA S"
      and "\<And>x. g x \<ge> 0"
      and "\<And>x. g x \<le> f x"
    shows "\<exists>S'. g has_sumA S' \<and> S' \<le> S"
proof -
  from assms(1) have "f abs_summable_on UNIV"
    using summable_on_def summable_on_iff_abs_summable_on_real
    by blast
  hence "g abs_summable_on UNIV"
    by (metis assms(2) assms(3) summable_on_comparison_test summable_on_iff_abs_summable_on_real)
  moreover have "\<And>x. g x = norm (g x)"
    by (simp add: assms(2))
  ultimately show ?thesis
    by (metis assms has_sum_mono summable_on_comparison_test summable_on_def)
qed


lemma nm_loc_sum_smaller:
  assumes "nm_loc_sum loc nm s"
      and "nm' \<le> nm"
    shows "\<exists>s'. s' \<le> s \<and> nm_loc_sum loc nm' s'"
  using assms
proof (induction nm arbitrary: nm' s)
  case IH: (NM mh fnm)
  obtain mh' fnm' where "nm' = NM mh' fnm'"
    using nm_get_eq
    by blast

  from IH(2)[unfolded nm_loc_sum.simps nm_loc_sum'.simps] obtain pf where
    "Rep_preal (mh loc) \<le> Rep_preal s" and
    pf_sum: "pf has_sumA Rep_preal s - Rep_preal (mh loc)" and
    pf: "\<And>lp. option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf lp)) (pf lp = 0) (fnm lp)"
    by blast

  hence pf_nn: "\<And>lp. pf lp \<ge> 0"
    by (smt (verit) has_Some_iff nm_loc_sum'_nonneg)

  have "\<And>lp. \<exists>s''. option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) s'') (s'' = 0) (fnm' lp) \<and> s'' \<le> pf lp" (is "\<And>lp. ?P lp")
  proof -
    fix lp
    show "?P lp"
    proof (cases "fnm' lp")
      case None
      show ?thesis
        apply (rule exI[of _ 0])
        by (simp add: pf_nn None)
    next
      case (Some lpm')
      obtain lpm where "fnm lp = Some lpm"
        using spec[OF conjunct2[OF IH(3)[unfolded less_eq_nested_mask_def \<open>nm' = _\<close> nested_mask_le.simps]],
                   of lp, unfolded Some, simplified]
        by (meson has_Some_iff)

      show ?thesis
      proof (cases "lpm = lpm'")
        case True
        then show ?thesis
          by (metis Some pf \<open>fnm lp = Some lpm\<close> order_refl)
      next
        case False
        hence "snd lpm' \<le> snd lpm"
          using spec[OF conjunct2[OF IH(3)[unfolded less_eq_nested_mask_def \<open>nm' = _\<close> nested_mask_le.simps]],
                     of lp, unfolded Some, simplified]
          by (simp add: \<open>fnm lp = Some lpm\<close> less_eq_nested_mask_def)
        have lpm_sum: "nm_loc_sum loc (snd lpm) (Abs_preal (pf lp))"
          by (metis Abs_preal_inverse \<open>fnm lp = Some lpm\<close> mem_Collect_eq nm_loc_sum.elims(3) option_fold.simps(1) pf pf_nn)
        then obtain s'' where "s'' \<le> Abs_preal (pf lp)" and "nm_loc_sum loc (snd lpm') s''"
          using IH(1)[OF _ _ _ lpm_sum, of "fnm lp" lpm "snd lpm'"]
          by (metis \<open>fnm lp = Some lpm\<close> \<open>snd lpm' \<le> snd lpm\<close> elem_set rangeI snds.intros)
        show ?thesis
          apply (rule exI[of _ "Rep_preal s''"])
          apply (intro conjI)
          unfolding Some
           apply simp
          unfolding nm_loc_sum.simps[symmetric]
           apply fact
          using Abs_preal_inverse \<open>s'' \<le> Abs_preal (pf lp)\<close> less_eq_preal.rep_eq pf_nn
          by auto
      qed
    qed
  qed

  then obtain pf' where
    pf': "\<forall>lp. option_fold (\<lambda>lpm. nm_loc_sum' loc (snd lpm) (pf' lp)) (pf' lp = 0) (fnm' lp)" and
    pf'_le_pf: "\<And>lp. pf' lp \<le> pf lp"
    by metis

  hence pf'_nn: "\<And>lp. pf' lp \<ge> 0"
    by (smt (verit, best) has_Some_iff nm_loc_sum'_nonneg)

  obtain pf'_sum where "pf' has_sumA pf'_sum" and
    "pf'_sum \<le> Rep_preal s - Rep_preal (mh loc)"
    using has_sumA_nonneg_smaller[OF pf_sum pf'_nn pf'_le_pf]
    by (meson le_funI)
  hence "pf'_sum \<ge> 0"
    using has_sum_nonneg pf'_nn
    by blast

  moreover have "\<And>l. mh' l \<le> mh l"
    using IH(3)[unfolded less_eq_nested_mask_def \<open>nm' = _\<close> nested_mask_le.simps]
    by (simp add: le_funD)
  ultimately have "Abs_preal pf'_sum + mh' loc \<le> s"
    using \<open>pf'_sum \<le> _\<close> \<open>pf'_sum \<ge> 0\<close>
    by (smt (verit) Abs_preal_inverse less_eq_preal.rep_eq mem_Collect_eq plus_preal.rep_eq)

  show ?case
    apply (rule exI[of _ "Abs_preal pf'_sum + mh' loc"])
    apply (intro conjI)
     apply fact
    unfolding nm_loc_sum.simps \<open>nm' = _\<close> nm_loc_sum'.simps
    apply (intro conjI)
     apply (simp add: plus_preal.rep_eq prat_non_negative)
    apply (rule exI[of _ pf'])
    apply (intro conjI)
     apply (simp add: \<open>pf' has_sumA pf'_sum\<close> plus_preal.rep_eq \<open>pf'_sum \<ge> 0\<close> Abs_preal_inverse)
    by fact
qed


subsection \<open>Top level mask is smaller than the sum\<close>

lemma mh_le_nm_loc_sum:
  assumes "nm_loc_sum loc nm s"
  shows "get_mh_nm nm loc \<le> s"
  by (metis assms less_eq_preal.rep_eq nm_get_eq nm_loc_sum'.simps nm_loc_sum.elims(2))


end
