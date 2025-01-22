theory NestedMaskInst
  imports TotalMaskUtil
begin


subsection \<open>Uninstantiated Lemmas\<close>


subsection \<open>Monoid\<close>

instantiation nested_mask :: (type) comm_monoid_add
begin

definition zero_nested_mask :: "'a nested_mask" where
  "zero_nested_mask \<equiv> NM zero_mask Map.empty"

definition plus_nested_mask :: "'a nested_mask \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask" where
  "plus_nested_mask \<equiv> nested_mask_merge"

instance
  sorry

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
