theory NestedMaskInst
  imports TotalMaskUtil
begin


subsection \<open>Lemmas\<close>

lemma add_masks_minus:
  assumes "m1 = add_masks (m2 :: ('a, preal) abstract_mask) m3"
  shows "m3 = m1 - m2"
  unfolding fun_diff_def
proof
  fix x

  have "m1 x = (m2 x) + (m3 x)"
    using assms
    by (simp add: add_masks_def)

  thus "m3 x = m1 x - m2 x"
    by (simp add: Rep_preal_inverse minus_preal.abs_eq plus_preal.rep_eq pos_perm_class.sum_larger)
qed

lemma get_mh_nm__merge [simp]:
  shows "get_mh_nm (nested_mask_merge nm1 nm2) = add_masks (get_mh_nm nm1) (get_mh_nm nm2)"
  by (cases nm1, cases nm2, simp)

lemma neq_by_fun:
  assumes "P a \<noteq> P b"
  shows "a \<noteq> b"
  using assms
  by blast


subsection \<open>Monoid\<close>

instantiation nested_mask :: (type) comm_monoid_add
begin

definition zero_nested_mask :: "'a nested_mask" where
  "zero_nested_mask \<equiv> NM zero_mask Map.empty"

definition plus_nested_mask :: "'a nested_mask \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask" where
  "plus_nested_mask \<equiv> nested_mask_merge"

instance proof
  fix a b c :: "'a nested_mask"

  show "a + b + c = a + (b + c)"
  proof (induction a arbitrary: b c)
    case IH: (NM mh\<^sub>a fnm\<^sub>a)
    show ?case
    proof (cases b)
      case b: (NM mh\<^sub>b fnm\<^sub>b)
      show ?thesis
      proof (cases c)
        case c: (NM mh\<^sub>c fnm\<^sub>c)
        show ?thesis
          apply (simp add: b c plus_nested_mask_def)
          apply (intro conjI)
           apply (simp add: add_masks_assoc)
          apply standard
          apply (fold plus_nested_mask_def)
        proof -
          fix lp
          show "((fnm\<^sub>a +\<lparr> \<lambda>lpm\<^sub>1 lpm\<^sub>2. (fst lpm\<^sub>1 + fst lpm\<^sub>2, snd lpm\<^sub>1 + snd lpm\<^sub>2) \<rparr>+ fnm\<^sub>b) +\<lparr> \<lambda>lpm\<^sub>1 lpm\<^sub>2. (fst lpm\<^sub>1 + fst lpm\<^sub>2, snd lpm\<^sub>1 + snd lpm\<^sub>2) \<rparr>+ fnm\<^sub>c) lp =
                (fnm\<^sub>a +\<lparr> \<lambda>lpm\<^sub>1 lpm\<^sub>2. (fst lpm\<^sub>1 + fst lpm\<^sub>2, snd lpm\<^sub>1 + snd lpm\<^sub>2) \<rparr>+ (fnm\<^sub>b +\<lparr> \<lambda>lpm\<^sub>1 lpm\<^sub>2. (fst lpm\<^sub>1 + fst lpm\<^sub>2, snd lpm\<^sub>1 + snd lpm\<^sub>2) \<rparr>+ fnm\<^sub>c)) lp"
            apply (cases "fnm\<^sub>a lp"; cases "fnm\<^sub>b lp"; cases "fnm\<^sub>c lp")
                   apply (simp_all add: pfun_comb_def)
            using IH add.assoc
            by fastforce
        qed
      qed
    qed
  qed

  show "a + b = b + a"
  proof (induction a arbitrary: b)
    case IH: (NM mh\<^sub>a fnm\<^sub>a)
    show ?case
    proof (cases b)
      case b: (NM mh\<^sub>b fnm\<^sub>b)
      show ?thesis
        apply (simp add: b plus_nested_mask_def)
        apply (intro conjI)
         apply (simp add: add_masks_comm)
        apply standard
        apply (fold plus_nested_mask_def)
      proof -
        fix lp
        show "(fnm\<^sub>a +\<lparr> \<lambda>lpm\<^sub>1 lpm\<^sub>2. (fst lpm\<^sub>1 + fst lpm\<^sub>2, snd lpm\<^sub>1 + snd lpm\<^sub>2) \<rparr>+ fnm\<^sub>b) lp =
              (fnm\<^sub>b +\<lparr> \<lambda>lpm\<^sub>1 lpm\<^sub>2. (fst lpm\<^sub>1 + fst lpm\<^sub>2, snd lpm\<^sub>1 + snd lpm\<^sub>2) \<rparr>+ fnm\<^sub>a) lp"
          apply (cases "fnm\<^sub>a lp"; cases "fnm\<^sub>b lp")
             apply (simp_all add: pfun_comb_def)
          using IH add.commute
          by fastforce
      qed
    qed
  qed

  show "0 + a = a"
    apply (cases a)
    apply (simp add: zero_nested_mask_def plus_nested_mask_def)
    apply standard
     apply (simp add: add_masks_comm add_masks_zero_mask)
    apply standard
    apply (simp add: pfun_comb_def)
    done
qed

end


instantiation option :: (comm_monoid_add) comm_monoid_add
begin

definition zero_option :: "'a option" where
  "zero_option \<equiv> None"

definition plus_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "plus_option \<equiv> combine_options (+)"

instance
proof
  fix a b c :: "'a option"
  show "a + b + c = a + (b + c)"
    by (simp add: add.assoc combine_options_assoc plus_option_def)
  show "a + b = b + a"
    by (simp add: add.commute combine_options_commute plus_option_def)
  show "0 + a = a"
    by (simp add: plus_option_def zero_option_def)
qed

end


subsection \<open>Cancellative\<close>

instantiation nested_mask :: (type) cancel_semigroup_add
begin

instance
proof
  fix a b c :: "'a nested_mask"

  show "a + c = b + c \<Longrightarrow> a = b"
  proof (induction c arbitrary: a b)
    case (NM mh fnm)
    show ?case
    proof (rule ccontr)
      assume "a \<noteq> b"
      then consider (mh_diff) "get_mh_nm a \<noteq> get_mh_nm b" | (fnm_diff) "get_fnm_nm a \<noteq> get_fnm_nm b"
        using nested_mask_equality
        by blast
      then show False
      proof cases
        case mh_diff
        then show ?thesis
          by (metis NM.prems add.commute add_masks_minus get_mh_nm__merge plus_nested_mask_def)
      next
        case fnm_diff
        then obtain lp where *: "get_fnm_nm a lp \<noteq> get_fnm_nm b lp"
          by blast
        have "a + NM mh fnm \<noteq> b + NM mh fnm"
          apply (subst nm_get_eq[of a])
          apply (subst nm_get_eq[of b])
          unfolding plus_nested_mask_def
          apply (rule neq_by_fun[of "\<lambda>nm. get_fnm_nm nm lp"])
          apply (cases "get_fnm_nm a lp"; cases "get_fnm_nm b lp"; cases "fnm lp")
                 apply (simp_all add: pfun_comb_def)
          using *
               apply argo+
             apply (smt (verit) Rep_posreal Rep_preal_inverse fst_conv mem_Collect_eq plus_posreal.rep_eq plus_preal.rep_eq pperm_pgt_pnone zero_preal.abs_eq)
            apply (metis Rep_posreal add_0 fst_conv mem_Collect_eq plus_posreal.rep_eq pos_perm_class.padd_cancellative pperm_pgt_pnone)
          using *
           apply force
          by (metis * NM.IH PosReal.padd_cancellative option.set_intros plus_nested_mask_def plus_posreal.rep_eq Rep_posreal_inject[symmetric] prod_eqI rangeI snds.intros)
        then show ?thesis
          using NM
          by meson
      qed
    qed
  qed

  thus "c + a = c + b \<Longrightarrow> a = b"
    by (simp add: add.commute)
qed

end


subsection \<open>Semimodule\<close>

class preal_semimodule =
    fixes scale :: "preal \<Rightarrow> 'a::comm_monoid_add \<Rightarrow> 'a" (infixr "*\<^sub>s" 75)
  assumes scale_add_right: "a *\<^sub>s (x + y) = a *\<^sub>s x + a *\<^sub>s y"
      and scale_add_left: "(a + b) *\<^sub>s x = a *\<^sub>s x + b *\<^sub>s x"
      and scale_scale: "a *\<^sub>s (b *\<^sub>s x) = (a * b) *\<^sub>s x"
      and scale_one: "1 *\<^sub>s x = x"


subsubsection \<open>Lemmas to Prove Instantiation\<close>

lemma mul_mask_0:
  shows "mul_mask 0 m = (\<lambda>_. 0)"
  apply standard
  apply (simp add: mul_mask_def)
  by (metis add_0 distrib_left mult.commute pos_perm_class.padd_cancellative)

lemma mul_mask_1:
  shows "mul_mask 1 m = m"
  apply standard
  by (simp add: mul_mask_def)


subsubsection \<open>Instantiation\<close>

instantiation nested_mask :: (type) preal_semimodule
begin

definition scale_nested_mask :: "preal \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask" where
  "scale_nested_mask = nested_mask_multiply"

instance
proof
  fix a b :: preal
  fix x y :: "'a nested_mask"

  show "a *\<^sub>s (x + y) = a *\<^sub>s x + a *\<^sub>s y"
  proof (induction x arbitrary: y)
    case IH: (NM mh\<^sub>x fnm\<^sub>x)
    obtain mh\<^sub>y fnm\<^sub>y where "y = NM mh\<^sub>y fnm\<^sub>y"
      using nm_get_eq
      by blast
    show ?case
      apply (simp add: scale_nested_mask_def plus_nested_mask_def \<open>y = _\<close>)
      apply (intro conjI)
       apply standard
       apply (simp add: add_masks_def mul_mask_def distrib_left)
      apply (cases "a = 0")
       apply simp
       apply standard
       apply (simp add: pfun_comb_def)
      apply standard
      apply simp
      apply (rename_tac lp)
      apply (case_tac "fnm\<^sub>x lp"; case_tac "fnm\<^sub>y lp")
         apply (simp add: pfun_comb_def)+
      apply (intro conjI)
      using distrib_right
       apply blast
      by (metis (mono_tags, opaque_lifting) IH NestedMaskInst.scale_nested_mask_def option.set_intros plus_nested_mask_def range_eqI snds.intros)
  qed

  show scale_add_left: "(a + b) *\<^sub>s x = a *\<^sub>s x + b *\<^sub>s x"
  proof (induction x)
    case (NM mh fnm)
    then show ?case
      apply (simp add: scale_nested_mask_def plus_nested_mask_def)
      apply (intro conjI)
       apply standard
       apply (simp add: mul_mask_def add_masks_def distrib_right)
      apply standard
      apply (rename_tac lp)
      apply (cases "a = 0"; cases "b = 0"; simp)
         apply (simp add: pfun_comb_def)+
      apply (subgoal_tac "a + b \<noteq> 0")
       apply simp
       apply (case_tac "fnm lp"; simp)
       apply (intro conjI)
        apply (metis distrib_left eq_onp_same_args plus_posreal.abs_eq pperm_pnone_pgt)
       apply (metis range_eqI snds.intros)
      using padd_pos
      by blast
  qed

  show scale_scale: "a *\<^sub>s (b *\<^sub>s x) = (a * b) *\<^sub>s x"
  proof (induction x)
    case (NM mh fnm)
    then show ?case
      apply (simp add: scale_nested_mask_def)
      apply (intro conjI)
       apply standard
       apply (simp add: mul_mask_def mult.assoc)
      apply standard
      apply (rename_tac lp)
      apply (cases "a = 0"; cases "b = 0"; simp)
         apply (simp add: Rep_preal_inject[symmetric] times_preal.rep_eq zero_preal.rep_eq)+
      apply (case_tac "fnm lp"; simp)
      apply (intro conjI)
       apply (metis (full_types) Abs_posreal_inverse map_fun_apply mem_Collect_eq mult.assoc mult.commute pperm_pnone_pgt times_posreal_def zero_preal.rep_eq)
      by (metis range_eqI snds.intros)
  qed

  show scale_one: "1 *\<^sub>s x = x"
  proof (induction x)
    case (NM mh fnm)
    then show ?case
      apply (simp add: scale_nested_mask_def mul_mask_1)
      apply standard
      apply (rename_tac lp)
      apply simp
      apply (case_tac "fnm lp")
       apply simp_all
      apply (subst posreal_id)
      by (metis range_eqI snds.intros split_pairs)
  qed
qed

end


instantiation option :: (preal_semimodule) preal_semimodule
begin

definition scale_option :: "preal \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "scale_option s = map_option ((*\<^sub>s) s)"

instance
proof
  fix a b :: preal
  fix x y :: "'a option"
  show "a *\<^sub>s (x + y) = a *\<^sub>s x + a *\<^sub>s y"
    apply (cases x; cases y)
    by (simp_all add: scale_option_def plus_option_def scale_add_right)
  show "(a + b) *\<^sub>s x = a *\<^sub>s x + b *\<^sub>s x"
    apply (cases x)
    by (simp_all add: scale_option_def plus_option_def scale_add_left)
  show "a *\<^sub>s b *\<^sub>s x = (a * b) *\<^sub>s x"
    apply (cases x)
    by (simp_all add: scale_option_def scale_scale)
  show "1 *\<^sub>s x = x"
    apply (cases x)
    by (simp_all add: scale_option_def scale_one)
qed

end


subsection \<open>Order\<close>

instantiation nested_mask :: (type) order
begin

definition less_eq_nested_mask :: "'a nested_mask \<Rightarrow> 'a nested_mask \<Rightarrow> bool"
  where "nm1 \<le> nm2 \<equiv> nested_mask_le nm1 nm2"

definition less_nested_mask :: "'a nested_mask \<Rightarrow> 'a nested_mask \<Rightarrow> bool"
  where "nm1 < nm2 \<equiv> nested_mask_le nm1 nm2 \<and> nm1 \<noteq> nm2"

instance
proof
  fix x y z :: "'a nested_mask"

  \<comment> \<open>Show the fourth goal first, which is used to prove 1.\<close>
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  proof (induction x arbitrary: y)
    case IH: (NM mh\<^sub>x fnm\<^sub>x)
    obtain mh\<^sub>y fnm\<^sub>y where "y = NM mh\<^sub>y fnm\<^sub>y"
      using nm_get_eq
      by fast
    show ?case
      unfolding \<open>y = _\<close>
      apply (rule nested_mask_equality)
       apply simp_all
      using IH(2,3)[unfolded \<open>y = _\<close> less_eq_nested_mask_def, simplified]
       apply auto[1]
      apply (rule ext)
      apply (rename_tac lp)
      apply (case_tac "fnm\<^sub>x lp"; case_tac "fnm\<^sub>y lp"; simp)
      using IH[unfolded \<open>y = _\<close> less_eq_nested_mask_def, simplified]
        apply (metis (no_types, lifting) old.prod.exhaust option_fold.simps(1) option_fold.simps(2))
      using IH[unfolded \<open>y = _\<close> less_eq_nested_mask_def, simplified]
       apply (metis (no_types, lifting) old.prod.exhaust option_fold.simps(1) option_fold.simps(2))
      using IH[unfolded \<open>y = _\<close> less_eq_nested_mask_def nested_mask_le.simps]
      by (smt (verit, del_insts) option_fold.simps(1) order_less_imp_not_less)
  qed

  thus "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    using less_eq_nested_mask_def less_nested_mask_def
    by force

  show "x \<le> x"
  proof (induction x)
    case (NM mh fnm)
    then show ?case
      unfolding less_eq_nested_mask_def
      apply simp
      by (smt (verit, del_insts) not_None_eq option_fold.simps(1) option_fold.simps(2))
  qed

  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  proof (induction x arbitrary: y z)
    case IH: (NM mh\<^sub>x fnm\<^sub>x)
    obtain mh\<^sub>y fnm\<^sub>y mh\<^sub>z fnm\<^sub>z where "y = NM mh\<^sub>y fnm\<^sub>y" and "z = NM mh\<^sub>z fnm\<^sub>z"
      using nm_get_eq
      by fast+
    show ?case
      unfolding \<open>z = _\<close> less_eq_nested_mask_def nested_mask_le.simps
      apply (intro conjI)
      using IH.prems(1) IH.prems(2) \<open>y = _\<close> \<open>z = _\<close> less_eq_nested_mask_def
       apply auto[1]
      apply standard
      apply (case_tac "fnm\<^sub>x lp"; case_tac "fnm\<^sub>y lp"; case_tac "fnm\<^sub>z lp"; simp)
         apply (metis (no_types, lifting) IH.prems(1) \<open>y = _\<close> less_eq_nested_mask_def nested_mask_le.simps option_fold.simps(1) option_fold.simps(2))
        apply (metis (no_types, lifting) IH.prems(1) \<open>y = _\<close> less_eq_nested_mask_def nested_mask_le.simps option_fold.simps(1) option_fold.simps(2))
       apply (metis (no_types, lifting) IH.prems(2) \<open>y = _\<close> \<open>z = _\<close> less_eq_nested_mask_def nested_mask_le.simps option_fold.simps(1) option_fold.simps(2))
      apply (rename_tac lpm\<^sub>x lpm\<^sub>y lpm\<^sub>z)
      apply (case_tac "lpm\<^sub>x = lpm\<^sub>y"; case_tac "lpm\<^sub>y = lpm\<^sub>z")
         apply simp_all
        apply (smt (verit) IH.prems(2) NestedMaskInst.less_eq_nested_mask_def \<open>y = _\<close> \<open>z = _\<close> nested_mask_le.simps option_fold.simps(1))
       apply (smt (verit) IH.prems(1) NestedMaskInst.less_eq_nested_mask_def \<open>y = _\<close> \<open>z = _\<close> nested_mask_le.simps option_fold.simps(1))
      apply (rule disjI2)
      apply (subgoal_tac "fst lpm\<^sub>x < fst lpm\<^sub>y \<and> nested_mask_le (snd lpm\<^sub>x) (snd lpm\<^sub>y)")
       apply (subgoal_tac "fst lpm\<^sub>y < fst lpm\<^sub>z \<and> nested_mask_le (snd lpm\<^sub>y) (snd lpm\<^sub>z)")
        apply (metis (no_types, opaque_lifting) IH.IH NestedMaskInst.less_eq_nested_mask_def option.set_intros order_less_trans rangeI snds.simps)
       apply (smt (verit, best) IH.prems(2) \<open>y = NM mh\<^sub>y fnm\<^sub>y\<close> \<open>z = NM mh\<^sub>z fnm\<^sub>z\<close> less_eq_nested_mask_def nested_mask_le.simps option_fold.simps(1))
      by (smt (verit, del_insts) IH.prems(1) \<open>y = NM mh\<^sub>y fnm\<^sub>y\<close> less_eq_nested_mask_def nested_mask_le.simps option_fold.simps(1))
  qed
qed

end


subsection \<open>Lemmas that do not belong to instantiations\<close>

lemma posreal_add_greater:
  fixes x y :: posreal
  shows "x + y > x"
  apply (simp add: posreal_to_preal preal_to_real)
  using Rep_posreal less_preal.rep_eq zero_preal.rep_eq
  by fastforce

\<comment> \<open>This lemma could be used to instantiate some useful type class.\<close>
lemma nm_sum_is_bigger:
    fixes x y z :: "'a nested_mask"
  assumes "x = y + z"
    shows "y \<le> x"
  using assms
proof (induction x arbitrary: y z)
  case IH: (NM mh\<^sub>x fnm\<^sub>x)
  obtain mh\<^sub>y fnm\<^sub>y mh\<^sub>z fnm\<^sub>z where "y = NM mh\<^sub>y fnm\<^sub>y" and "z = NM mh\<^sub>z fnm\<^sub>z"
    using nm_get_eq
    by fast+
  note * = IH(2)[unfolded plus_nested_mask_def \<open>y = _\<close> \<open>z = _\<close> nested_mask_merge.simps]
  show ?case
    unfolding \<open>y = _\<close> less_eq_nested_mask_def nested_mask_le.simps
    apply (intro conjI)
    using IH(2)[unfolded plus_nested_mask_def \<open>y = _\<close> \<open>z = _\<close> nested_mask_merge.simps]
     apply (simp add: add_masks_def le_funI pos_perm_class.sum_larger)
    apply standard
    apply (case_tac "fnm\<^sub>x lp"; case_tac "fnm\<^sub>y lp"; case_tac "fnm\<^sub>z lp"; simp)
       apply (metis (no_types, lifting) * combine_options_simps(2) nested_mask.inject option.distinct(1) pfun_comb_def)
    using *
      apply (simp add: pfun_comb_def)
     apply (metis (no_types, lifting) * combine_options_simps(2) nested_mask.inject option.inject pfun_comb_def)
    apply (rename_tac lpm\<^sub>x lpm\<^sub>y lpm\<^sub>z)
    apply (case_tac "lpm\<^sub>x = lpm\<^sub>y")
     apply argo
    apply (rule disjI2)
    apply (intro conjI)
    using arg_cong[where ?f=get_fnm_nm, OF *, simplified]
     apply (simp add: pfun_comb_def)
    using posreal_add_greater
     apply force
    using arg_cong[where ?f=get_fnm_nm, OF *, simplified] IH(1)
    by (metis (mono_tags, lifting) combine_options_simps(3) less_eq_nested_mask_def option.inject option.set_intros pfun_comb_def plus_nested_mask_def range_eqI snd_conv snds.intros)
qed


lemma nm_bigger_has_sum:
    fixes x y z :: "'a nested_mask"
  assumes "y \<le> x"
    shows "\<exists>z. x = y + z"
  using assms
proof (induction x arbitrary: y)
  case IH: (NM mh\<^sub>x fnm\<^sub>x)
  obtain mh\<^sub>y fnm\<^sub>y where "y = NM mh\<^sub>y fnm\<^sub>y"
    using nm_get_eq
    by blast

  define mh\<^sub>z where "mh\<^sub>z = (\<lambda>l. mh\<^sub>x l - mh\<^sub>y l)"
  moreover from assms(1) have "\<And>l. mh\<^sub>y l \<le> mh\<^sub>x l"
    by (metis IH.prems \<open>y = _\<close> le_funD less_eq_nested_mask_def nested_mask_le.simps)
  ultimately have "mh\<^sub>x = add_masks mh\<^sub>y mh\<^sub>z"
    apply simp
    apply standard
    apply (simp add: add_masks_def)
    by (metis add.commute greater_minus_plus)

  have "\<And>lp. \<exists>lpm\<^sub>z. combine_options
                      (\<lambda>lpm\<^sub>1 lpm\<^sub>2. (fst lpm\<^sub>1 + fst lpm\<^sub>2, nested_mask_merge (snd lpm\<^sub>1) (snd lpm\<^sub>2)))
                      (fnm\<^sub>y lp) lpm\<^sub>z = fnm\<^sub>x lp" (is "\<And>lp. ?P lp")
  proof -
    fix lp
    show "?P lp"
    proof (cases "fnm\<^sub>x lp")
      case None
      show ?thesis
      proof (cases "fnm\<^sub>y lp")
        case None
        then show ?thesis
          by auto
      next
        case (Some a)
        then show ?thesis
          using None IH(2)[unfolded \<open>y = _\<close> less_eq_nested_mask_def, simplified]
          by (metis (no_types, lifting) option_fold.simps(1) option_fold.simps(2) prod.collapse)
      qed
    next
      case (Some lpm\<^sub>x)
      show ?thesis
      proof (cases "fnm\<^sub>y lp")
        case None
        show ?thesis
          apply (rule exI[of _ "fnm\<^sub>x lp"])
          by (simp add: None)
      next
        case (Some lpm\<^sub>y)
        show ?thesis
        proof (cases "lpm\<^sub>x = lpm\<^sub>y")
          case True
          show ?thesis
            apply (rule exI[of _ None])
            by (simp add: \<open>fnm\<^sub>x lp = _\<close> \<open>fnm\<^sub>y lp = _\<close> True)
        next
          case False
          hence *: "fst lpm\<^sub>y < fst lpm\<^sub>x \<and> snd lpm\<^sub>y \<le> snd lpm\<^sub>x"
            using spec[OF conjunct2[OF IH(2)[unfolded \<open>y = _\<close> less_eq_nested_mask_def nested_mask_le.simps]],
                       of lp, unfolded \<open>fnm\<^sub>x lp = _\<close> \<open>fnm\<^sub>y lp = _\<close>, simplified,
                       folded less_eq_nested_mask_def]
            by simp
          have "\<exists>nm\<^sub>z. snd lpm\<^sub>x = snd lpm\<^sub>y + nm\<^sub>z"
            apply (rule IH(1)[of "fnm\<^sub>x lp" "lpm\<^sub>x" "snd lpm\<^sub>x" "snd lpm\<^sub>y"])
               apply simp
            unfolding \<open>fnm\<^sub>x lp = _\<close>
              apply simp
             apply (simp add: snds.intros)
            by (simp add: *)
          then obtain nm\<^sub>z where "snd lpm\<^sub>x = snd lpm\<^sub>y + nm\<^sub>z"
            by blast

          show ?thesis
            apply (rule exI[of _ "Some (fst lpm\<^sub>x - fst lpm\<^sub>y, nm\<^sub>z)"])
            apply (simp add: \<open>fnm\<^sub>x lp = _\<close> \<open>fnm\<^sub>y lp = _\<close>)
            apply standard
             apply simp_all
            using conjunct1[OF *]
             apply (simp add: posreal_to_preal preal_to_real)
            using Abs_posreal_inverse conjunct1[OF *] gr_0_is_ppos less_posreal.rep_eq minus_preal.rep_eq ppos.rep_eq
             apply auto[1]
            by (simp add: \<open>snd lpm\<^sub>x = snd lpm\<^sub>y + nm\<^sub>z\<close> plus_nested_mask_def)
        qed
      qed
    qed
  qed
  then obtain fnm\<^sub>z where
    "\<And>lp. combine_options
             (\<lambda>lpm\<^sub>1 lpm\<^sub>2. (fst lpm\<^sub>1 + fst lpm\<^sub>2, nested_mask_merge (snd lpm\<^sub>1) (snd lpm\<^sub>2)))
             (fnm\<^sub>y lp) (fnm\<^sub>z lp) = fnm\<^sub>x lp"
    by meson
  hence "fnm\<^sub>x = (fnm\<^sub>y +\<lparr> \<lambda>lpm\<^sub>1 lpm\<^sub>2. (fst lpm\<^sub>1 + fst lpm\<^sub>2, nested_mask_merge (snd lpm\<^sub>1) (snd lpm\<^sub>2)) \<rparr>+ fnm\<^sub>z)"
    unfolding pfun_comb_def
    by fastforce

  show ?case
    apply (rule exI[of _ "NM mh\<^sub>z fnm\<^sub>z"])
    unfolding \<open>y = _\<close> plus_nested_mask_def
    apply simp
    apply (intro conjI)
    by fact+
qed


end
