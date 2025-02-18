section \<open>Strictly Positive Real Numbers\<close>

theory StrictlyPosReal
  imports Main HOL.Real PosReal HOL.Topological_Spaces HOL.Limits
begin


typedef posreal = "{ r :: preal | r. r > 0 }"
  apply (rule exI[of _ 1])
  using preal_not_0_gt_0
  by fastforce


setup_lifting type_definition_posreal

instantiation posreal :: comm_semiring
begin

lift_definition times_posreal :: "posreal \<Rightarrow> posreal \<Rightarrow> posreal" is "(*)"
  by (simp add: less_preal.rep_eq times_preal.rep_eq zero_preal.rep_eq)

lift_definition plus_posreal :: "posreal \<Rightarrow> posreal \<Rightarrow> posreal" is "(+)"
  by (simp add: less_preal.rep_eq plus_preal.rep_eq zero_preal.rep_eq)

instance proof
  fix a b c :: posreal

  show "a * b * c = a * (b * c)"
    using Rep_posreal_inject ab_semigroup_mult_class.mult_ac(1) times_posreal.rep_eq
    by fastforce

  show "a * b = b * a"
    by (metis (mono_tags) Rep_posreal_inject mult.commute times_posreal.rep_eq)

  show "a + b + c = a + (b + c)"
    by (metis (mono_tags) group_cancel.add1 map_fun_apply plus_posreal.rep_eq plus_posreal_def)

  show "a + b = b + a"
    by (metis (mono_tags) Rep_posreal_inject add.commute plus_posreal.rep_eq)

  show "(a + b) * c = a * c + b * c"
    by (metis (mono_tags, lifting) Rep_posreal_inject distrib_right plus_posreal.rep_eq times_posreal.rep_eq)
qed

end


instantiation posreal :: linorder
begin

lift_definition less_posreal :: "posreal \<Rightarrow> posreal \<Rightarrow> bool" is "(<)" done

lift_definition less_eq_posreal :: "posreal \<Rightarrow> posreal \<Rightarrow> bool" is "(\<le>)" done

instance proof
  fix x y z :: posreal
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (meson less_eq_posreal.rep_eq less_posreal.rep_eq nless_le verit_comp_simplify1(3))
  show "x \<le> x"
    by (simp add: less_eq_posreal.rep_eq)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    using less_eq_posreal.rep_eq by auto
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (simp add: Rep_posreal_inject less_eq_posreal.rep_eq)
  show "x \<le> y \<or> y \<le> x"
    using less_eq_posreal.rep_eq by force
qed

end


instantiation posreal :: minus
begin

definition minus_posreal :: "posreal \<Rightarrow> posreal \<Rightarrow> posreal" where
  "minus_posreal a b = Abs_posreal (Rep_posreal a - Rep_posreal b)"

instance proof qed

end


instantiation posreal :: one
begin

lift_definition one_posreal :: "posreal" is "1"
  by (simp add: pperm_pnone_pgt)

instance proof qed

end


instantiation posreal :: comm_monoid_mult
begin

instance proof
  fix a :: posreal
  show "1 * a = a"
    using Rep_posreal_inject one_posreal.rep_eq times_posreal.rep_eq
    by fastforce
qed

end


instantiation posreal :: inverse
begin

lift_definition divide_posreal :: "posreal \<Rightarrow> posreal \<Rightarrow> posreal" is "(/)"
  by (simp add: less_preal.rep_eq divide_preal.rep_eq zero_preal.rep_eq)

instance proof qed

end


subsection \<open>\<^typ>\<open>posreal\<close> to \<^typ>\<open>real\<close>\<close>

lemmas posreal_to_preal =
  less_eq_posreal.rep_eq
  less_posreal.rep_eq
  plus_posreal.rep_eq
  minus_posreal_def
  times_posreal.rep_eq
  divide_posreal.rep_eq
  Abs_posreal_inverse
  Rep_posreal_inverse
  Rep_posreal_inject[symmetric]


subsection \<open>Arithmetic Operations between \<^typ>\<open>posreal\<close> and \<^typ>\<open>preal\<close>\<close>

(*
lemma pos2p_gt_0:
  shows "pos2p a > 0"
  using Rep_posreal pos2p_def positive_real_preal pperm_pnone_pgt
  by auto

lemma pos2p_p2pos_id:
  shows "p2pos (pos2p x) = x"
  apply (simp add: p2pos_def pos2p_def)
  by (metis Rep_posreal Rep_posreal_inverse Abs_preal_inverse dual_order.order_iff_strict mem_Collect_eq)

lemma p2pos_pos2p_id:
  assumes "x > 0"
  shows "pos2p (p2pos x) = x"
  apply (simp add: p2pos_def pos2p_def)
  using Abs_posreal_inverse Rep_preal_inverse assms less_preal.rep_eq zero_preal.rep_eq
  by force

lemma pos2p_add_distr:
  shows "pos2p a + pos2p b = pos2p (a + b)"
  by (metis Abs_posreal_inverse Rep_preal_inject gr_0_is_ppos mem_Collect_eq p2pos_def plus_posreal.rep_eq plus_preal.rep_eq pos2p_gt_0 pos2p_p2pos_id ppos.rep_eq)

lemma pos2p_mult:
  shows "pos2p a * pos2p b = pos2p (a * b)"
  apply (simp add: pos2p_def posreal_to_real preal_to_real)
  by (metis Abs_posreal_cases Abs_posreal_inverse dual_order.order_iff_strict mem_Collect_eq preal_to_real(12) times_posreal.rep_eq times_preal.rep_eq)
*)


subsection \<open>Some Lemmas\<close>

lemma posreal_id:
  shows "a * Abs_posreal 1 = a"
  by (metis Abs_posreal_inverse Rep_posreal_inject mem_Collect_eq mult.right_neutral pperm_pnone_pgt times_posreal.rep_eq zero_neq_one)

lemma field_inverse_posreal:
  fixes a :: posreal
  shows "(1 / a) * a = 1"
  apply (simp add: posreal_to_preal)
  by (metis Rep_posreal Rep_preal_inject divide_posreal.rep_eq divide_preal.rep_eq mem_Collect_eq nonzero_eq_divide_eq pperm_pgt_pnone times_posreal.rep_eq times_preal.rep_eq zero_preal.rep_eq)

lemma field_divide_inverse_posreal:
  fixes a b :: posreal
  shows "a / b = a * (1 / b)"
  apply (simp add: posreal_to_preal preal_to_real)
  using field_divide_inverse divide_preal.rep_eq one_posreal.rep_eq
  by auto


end
