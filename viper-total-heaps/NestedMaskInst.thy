theory NestedMaskInst
  imports TotalMaskUtil
begin


lemma nm_multiply_twice:
  fixes f1 f2 :: preal
  shows "nested_mask_multiply (nested_mask_multiply nm f1) f2 = nested_mask_multiply nm (f1 * f2)"
  sorry

lemma nm_multiply_1:
  shows "nested_mask_multiply nm 1 = nm"
  sorry

lemma nm_multiply_merge_distr:
  shows "nested_mask_merge_option (nested_mask_multiply_option nm p) (nested_mask_multiply_option nm q) =
         nested_mask_multiply_option nm (p + q)"
  sorry

lemma nm_multiply_1_opt:
  shows "nested_mask_multiply_option nm 1 = nm"
  by (metis nested_mask_multiply_option.elims nm_multiply_1 zero_neq_one)

lemma nm_add_assoc:
  shows "nested_mask_merge nm1 (nested_mask_merge nm2 nm3) =
         nested_mask_merge (nested_mask_merge nm1 nm2) nm3"
  sorry


end
