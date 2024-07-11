theory TotalInternalConsistency
  imports TotalSemanticsCore TotalSemantics NestedMaskProperties
begin


subsection \<open>Old Internal Consistency\<close>

\<comment> \<open>Local variable assignment preserves internal state consistency.\<close>

lemma var_assignment_preserves_internal_consistency:
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

lemma unfold_preserves_internal_consistency:
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

lemma field_assignment_preserves_internal_consistency:
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


subsection \<open>New Internal Consistency\<close>

definition internal_consistent' :: "'a nested_mask \<Rightarrow> bool" where
  "internal_consistent' nm \<equiv> \<forall>loc. \<exists>s. s \<le> 1 \<and> nm_loc_sum loc nm s"


lemma shift_up_preserves_loc_sum:
  assumes "shift_up pred_id vs q nm nm'"
      and "nm_loc_sum loc nm s"
    shows "nm_loc_sum loc nm' s"
proof -
  from assms(1) obtain mh mp fnm pnm p mp' fnm' nm_sub where
    nm: "nm = NM mh mp fnm" and
    pnm: "Some pnm = fnm (pred_id,vs)" and
    "p = mp (pred_id,vs)" and
    "q \<le> p" and
    "q \<noteq> 0" and
    "mp' = mp( (pred_id,vs) := p - q )" and
    fnm': "fnm' = fnm( (pred_id,vs) := if q = p then None else Some (nested_mask_multiply pnm ((p - q) / p)) )" and
    nm_sub: "nm_sub = NM mh mp' fnm'" and
    nm': "nm' = nested_mask_merge nm_sub (nested_mask_multiply pnm (q / p))"
    by (smt (verit, best) shift_up_simp)
  have "fnm' (pred_id,vs) = None \<longleftrightarrow> q = p"
    apply (cases "q = p")
    by (simp add: fnm')+
  from assms(2) obtain pf where
    pf: "pf has_sumA (s - mh loc) \<and>
         (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf ploc)) (pf ploc = 0) (fnm ploc))"
    using nm nm_loc_sum.simps by blast
  then obtain ps where pnm_sum: "nm_loc_sum loc pnm ps"
    by (metis option_fold.simps(1) pnm)
  with pf have "s - mh loc \<ge> ps"
    by (metis all_pos has_sumA_nonneg_ge_one_preal nm_loc_sum_unique option_fold.simps(1) pnm)
  hence "s \<ge> ps"
    by (metis assms(2) nm nm_loc_sum.simps order.trans psub_smaller)

  \<comment> \<open>sum of \<^term>\<open>nm_sub\<close>\<close>
  from pnm_sum have "option_fold (\<lambda>nm. nm_loc_sum loc nm (ps * ((p - q) / p))) (ps * ((p - q) / p) = 0) (fnm' (pred_id,vs))"
    apply (cases "fnm' (pred_id,vs)")
     apply simp_all
     apply (metis Rep_preal_inverse \<open>fnm' (pred_id, vs) = None \<longleftrightarrow> q = p\<close> cancel_comm_monoid_add_class.diff_cancel div_0 divide_preal.rep_eq minus_preal.rep_eq mult_not_zero zero_preal.rep_eq)
    by (smt (verit, del_insts) \<open>q \<le> p\<close> all_pos divide_preal.rep_eq fnm' fun_upd_same less_eq_preal.rep_eq map_upd_eqD1 minus_preal.rep_eq mult_not_zero nm_loc_sum_mult nonzero_eq_divide_eq option.distinct(1) order_antisym pperm_pnone_pgt zero_preal.rep_eq)
  moreover have "option_fold (\<lambda>nm. nm_loc_sum loc nm ps) (ps = 0) (fnm (pred_id,vs))"
    by (metis option_fold.simps(1) pnm pnm_sum)
  moreover have "fnm' = fnm( (pred_id, vs) := fnm' (pred_id, vs) )"
    by (simp add: fnm')
  ultimately have nm_sub_sum: "nm_loc_sum loc nm_sub (s - ps + ps * ((p - q) / p))"
    using nm_loc_sum_change_sum[of loc mh mp fnm s ps "(pred_id,vs)" "ps * ((p - q) / p)" "fnm' (pred_id,vs)" mp'] nm assms(2) fnm' nm_sub
    by argo

  \<comment> \<open>sum of q/p of pnm\<close>
  have pnm_frac_sum: "nm_loc_sum loc (nested_mask_multiply pnm (q / p)) (ps * (q / p))"
    by (metis Rep_preal_inverse \<open>q \<le> p\<close> \<open>q \<noteq> pos_perm_class.pnone\<close> divide_eq_0_iff divide_preal.rep_eq leD nm_loc_sum_mult pnm_sum preal_not_0_gt_0 zero_preal.rep_eq)

  \<comment> \<open>sum of nm'\<close>
  have "s - ps + ps * ((p - q) / p) + ps * (q / p) = s"
  proof -
    have "s - ps + ps * ((p - q) / p) + ps * (q / p) = s - ps + (ps * ((p - q) / p) + ps * (q / p))"
      using add.assoc by auto
    moreover have "ps * ((p - q) / p) + ps * (q / p) = ps * ((p - q) / p + q / p)"
      by (simp add: distrib_left)
    moreover have "(p - q) / p + q / p = (p - q + q) / p"
      by (simp add: PosReal.field_divide_inverse distrib_right)
    moreover have "(p - q + q) / p = 1"
      by (metis Rep_preal_inverse \<open>q \<le> p\<close> \<open>q \<noteq> pos_perm_class.pnone\<close> diff_add_cancel div_self divide_preal.rep_eq less_eq_preal.rep_eq minus_preal.rep_eq one_preal.rep_eq order_antisym plus_preal.rep_eq prat_non_negative zero_preal.rep_eq)
    moreover have "s - ps + ps = s"
      using greater_minus_plus \<open>ps \<le> s\<close> by auto
    ultimately show ?thesis
      by auto
  qed
  thus "nm_loc_sum loc nm' s"
    by (metis pnm_frac_sum nm_sub_sum nm' nm_loc_sum_add)
qed


lemma shift_up_preserves_internal_consistency:
  assumes "shift_up pred_id vs q nm nm'"
      and "internal_consistent' nm"
    shows "internal_consistent' nm'"
  (* apply (simp add: internal_consistent'_def, standard, standard) *)
  sorry


end
