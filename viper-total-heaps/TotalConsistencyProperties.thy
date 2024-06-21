theory TotalConsistencyProperties
  imports TotalSemanticsCore TotalSemantics
begin

\<comment> \<open>Local variable assignment preserves internal state consistency.\<close>

lemma var_assignment_preserves_state_consistency:
  assumes "get_total_full \<omega> = \<phi>"
      and "total_heap_consistent \<phi>"
      and "red_stmt_total ctxt R \<Lambda> (LocalAssign x e) \<omega> (RNormal \<omega>')"
      and "get_total_full \<omega>' = \<phi>'"
    shows "total_heap_consistent \<phi>'"
proof -
  obtain v where "\<omega>' = update_var_total \<omega> x v" using assms(3) red_stmt_total.simps by blast
  hence "\<phi> = \<phi>'" using assms(1,4) by force
  thus ?thesis using assms(2) by auto
qed

\<comment> \<open>Unfold statement preserves internal state consistency.\<close>

lemma unfold_preserves_state_consistency:
  assumes "get_total_full \<omega> = \<phi>"
      and "total_heap_consistent \<phi>"
      and "red_stmt_total ctxt R \<Lambda> (Unfold pred_id e_args (PureExp e_p)) \<omega> (RNormal \<omega>')"
      and "get_total_full \<omega>' = \<phi>'"
    shows "total_heap_consistent \<phi>'"
proof -
  obtain vs p where
    vs: "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some vs)" and
    p: "ctxt, (Some \<omega>) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)" and
    result: "th_result_rel (p > 0 \<and> p \<le> Rep_preal (get_mp_total_full \<omega> (pred_id, vs))) True {\<omega>'. \<exists>\<phi>'. \<omega>' = \<omega>\<lparr> get_total_full := \<phi>' \<rparr> \<and> unfold_rel ctxt pred_id vs (Abs_preal p) (get_total_full \<omega>) \<phi>'} (RNormal \<omega>')"
    using assms(3) RedUnfold_case by force
  define W' where W': "W' = {\<omega>'. \<exists>\<phi>'. \<omega>' = \<omega>\<lparr> get_total_full := \<phi>' \<rparr> \<and> unfold_rel ctxt pred_id vs (Abs_preal p) (get_total_full \<omega>) \<phi>'}"
  with result have "th_result_rel (p > 0 \<and> p \<le> Rep_preal (get_mp_total_full \<omega> (pred_id, vs))) True W' (RNormal \<omega>')" by blast
  with W' have "\<omega>' \<in> W'" using th_result_rel_normal by blast
  show "total_heap_consistent \<phi>'"
  proof (simp add: total_heap_consistent_def, standard)
    fix n
    from assms(2) have "total_heap_consistent_unfold_n (get_nm_total \<phi>) (Suc n)"
      by (simp add: total_heap_consistent_def)
    moreover have "unfold_rel ctxt pred_id vs (Abs_preal p) (get_total_full \<omega>) \<phi>'"
      using W' \<open>\<omega>' \<in> W'\<close> assms(4) by force
    ultimately show "total_heap_consistent_unfold_n (get_nm_total \<phi>') n"
      by (smt (z3) Abs_preal_inverse UnfoldStep_cases assms(1) get_mp_total.simps get_mp_total_full.simps less_eq_preal.rep_eq less_preal.rep_eq mem_Collect_eq result th_result_rel_normal unfold_rel.cases zero_preal.rep_eq)
  qed
qed

\<comment> \<open>Field assignment preserves internal state consistency.\<close>

lemma field_assignment_preserves_state_consistency:
  assumes "get_total_full \<omega> = \<phi>"
      and "total_heap_consistent \<phi>"
      and "red_stmt_total ctxt R \<Lambda> (FieldAssign e_r f e) \<omega> (RNormal \<omega>')"
      and "get_total_full \<omega>' = \<phi>'"
    shows "total_heap_consistent \<phi>'"
proof -
  obtain addr v where "ctxt, (Some \<omega>) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address addr))" and
    "\<omega>' = update_hh_loc_total_full \<omega> (addr,f) v"
    using assms(3) red_stmt_total.simps by blast (* This is quite slow. Any better method? *)
  hence "get_nm_total \<phi> = get_nm_total \<phi>'"
    using assms(1,4) by force
  thus ?thesis using assms(2)
    by (simp add: total_heap_consistent_def)
qed

\<comment> \<open>A fraction of a consistent total state is external consistent.\<close>

lemma fraction_consistent_external:
    fixes frac :: preal
  assumes "consistent_external ctxt \<omega> (pred_id,vs) p"
      and "0 < frac \<and> frac < 1"
      and "nm = nested_mask_multiply (get_nm_total_full \<omega>) frac"
    shows "consistent_external ctxt (update_nm_total_full \<omega> nm) (pred_id,vs) (p * frac)"
  oops

end
