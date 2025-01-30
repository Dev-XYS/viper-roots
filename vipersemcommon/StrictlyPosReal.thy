section \<open>Strictly Positive Real Numbers\<close>

theory StrictlyPosReal
  imports Main HOL.Real PosReal HOL.Topological_Spaces HOL.Limits
begin


typedef posreal = "{ r :: real | r. r > 0 }" by fastforce


setup_lifting type_definition_posreal

instantiation posreal :: comm_semiring
begin

lift_definition times_posreal :: "posreal \<Rightarrow> posreal \<Rightarrow> posreal" is "(*)" by simp

lift_definition plus_posreal :: "posreal \<Rightarrow> posreal \<Rightarrow> posreal" is "(+)" by simp

instance proof
  fix a b c :: posreal

  show "a * b * c = a * (b * c)"
    using Rep_posreal_inject times_posreal.rep_eq by fastforce

  show "a * b = b * a"
    by (metis (mono_tags) Rep_posreal_inject mult.commute times_posreal.rep_eq)

  show "a + b + c = a + (b + c)"
    using Rep_posreal_inject plus_posreal.rep_eq by fastforce

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


instantiation posreal :: inverse
begin

lift_definition divide_posreal :: "posreal \<Rightarrow> posreal \<Rightarrow> posreal" is "(/)" by simp

instance proof qed

end


subsection \<open>\<^typ>\<open>posreal\<close> to \<^typ>\<open>real\<close>\<close>

lemmas posreal_to_real =
  less_eq_posreal.rep_eq
  less_posreal.rep_eq
  plus_posreal.rep_eq
  divide_posreal.rep_eq
  Abs_posreal_inverse
  Rep_posreal_inverse
  Rep_posreal_inject[symmetric]


subsection \<open>Arithmetic Operations between \<^typ>\<open>posreal\<close> and \<^typ>\<open>preal\<close>\<close>

(* definition posreal_times_preal :: "posreal \<Rightarrow> preal \<Rightarrow> posreal" *)

(* definition posreal_divides_preal :: "preal \<Rightarrow> posreal \<Rightarrow> posreal" (infixl "'/\<^sub>p" 70) where
  "a /\<^sub>p b = Abs_posreal (Rep_preal a / Rep_posreal b)" *)

definition pos2p :: "posreal \<Rightarrow> preal" where
  "pos2p a = Abs_preal (Rep_posreal a)"

definition p2pos :: "preal \<Rightarrow> posreal" where
  "p2pos a = Abs_posreal (Rep_preal a)"

lemma pos2p_gt_0:
  shows "pos2p a > 0"
  using Rep_posreal pos2p_def positive_real_preal pperm_pnone_pgt by auto

end
