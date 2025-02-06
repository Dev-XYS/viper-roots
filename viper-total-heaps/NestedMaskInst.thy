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
             apply (smt (verit) Rep_posreal fst_conv mem_Collect_eq plus_posreal.rep_eq)+
          using *
           apply fastforce
          by (metis * NM.IH Rep_posreal_inject add_right_imp_eq option.set_intros plus_nested_mask_def plus_posreal.rep_eq range_eqI snds.intros surjective_pairing)
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


instantiation nested_mask :: (type) preal_semimodule
begin

definition scale_nested_mask :: "preal \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask" where
  "scale_nested_mask = nested_mask_multiply"

instance
  sorry

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
  sorry

end


end
