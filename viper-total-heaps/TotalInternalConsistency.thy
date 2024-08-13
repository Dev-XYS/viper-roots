theory TotalInternalConsistency
  imports TotalSemanticsCore TotalSemantics TotalSemanticsProperties NestedMaskProperties
begin


subsection \<open>Old Internal Consistency\<close>

\<comment> \<open>Old internal consistency definition\<close>

inductive total_heap_consistent_unfold_n :: "'a nested_mask \<Rightarrow> nat \<Rightarrow> bool"
  where
  Zero:
  "\<lbrakk> valid_heap_mask (get_mh_nm nm)
   \<rbrakk> \<Longrightarrow>
   total_heap_consistent_unfold_n nm 0"
| UnfoldStep:
  "\<lbrakk> \<And> pred_id vs q nm'. q \<le> get_mp_nm nm (pred_id,vs) \<Longrightarrow> q > 0 \<Longrightarrow>
         shift_up pred_id vs q nm nm' \<Longrightarrow>
         total_heap_consistent_unfold_n nm' n
   \<rbrakk> \<Longrightarrow>
   total_heap_consistent_unfold_n nm (Suc n)"

inductive_cases UnfoldStep_cases: "total_heap_consistent_unfold_n nm (Suc n)"

definition total_heap_consistent :: "'a total_state \<Rightarrow> bool" where
  "total_heap_consistent \<phi> \<equiv> \<forall> n. total_heap_consistent_unfold_n (get_nm_total \<phi>) n"


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
    result: "unfold_rel ctxt pred_id vs (Abs_preal p) (get_total_full \<omega>) \<phi>'" and
    \<omega>': "\<omega>' = \<omega>\<lparr> get_total_full := \<phi>' \<rparr>"
    using assms(3) RedUnfold_case
    by (metis assms(4) full_total_state.select_convs(3) full_total_state.surjective full_total_state.update_convs(3))
  show "total_heap_consistent \<phi>'"
    sorry
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

definition consistent_internal :: "'a nested_mask \<Rightarrow> bool" where
  "consistent_internal nm \<equiv> \<forall>loc. \<exists>s. s \<le> 1 \<and> nm_loc_sum loc nm s"


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


subsubsection \<open>Unfold preserves internal consistency\<close>

lemma shift_up_preserves_internal_consistency:
  assumes "shift_up pred_id vs q nm nm'"
      and "consistent_internal nm"
    shows "consistent_internal nm'"
  by (meson assms(1) assms(2) consistent_internal_def shift_up_preserves_loc_sum)


subsubsection \<open>Fold preserves internal consistency\<close>

lemma fold_rel_preserves_loc_sum:
  assumes "fold_rel ctxt pred_id vs p \<omega> (RNormal \<omega>')"
      and "nm_loc_sum loc (get_nm_total_full \<omega>) s"
    shows "nm_loc_sum loc (get_nm_total_full \<omega>') s"
proof -
  obtain pred_decl pred_body \<omega>0 \<omega>1 nm_exh where
    "ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl" and
    "ViperLang.predicate_decl.body pred_decl = Some pred_body" and
    "p \<noteq> 0" and
    \<omega>0: "\<omega>0 = \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty, get_total_full = get_total_full \<omega> \<rparr>" and
    exh: "red_exhale ctxt \<omega>0 (syntactic_mult (Rep_preal p) pred_body) \<omega>0 (RNormal \<omega>1)" and
    nm_sub: "nm_exh = nested_mask_subtract (get_nm_total_full \<omega>0) (get_nm_total_full \<omega>1)" and
    \<omega>': "\<omega>' = \<lparr> get_store_total = get_store_total \<omega>,
                get_trace_total = get_trace_total \<omega>,
                get_total_full = add_to_nm_loc_total
                  (add_to_mp_loc_total (get_total_full \<omega>1) (pred_id,vs) p)
                  (pred_id,vs) nm_exh
              \<rparr>"
    using assms(1)
    by (auto elim: FoldRelNormal_case)

  define nm0 where "nm0 = get_nm_total_full \<omega>0"
  define nm1 where "nm1 = get_nm_total_full \<omega>1"
  define nm' where "nm' = get_nm_total_full \<omega>'"

  have "nm0 = get_nm_total_full \<omega>"
    by (simp add: \<omega>0 nm0_def)
  hence "nm_loc_sum loc nm0 s"
    using assms(2) by blast

  have "nm0 = nested_mask_merge nm1 nm_exh"
    using exhale_fraction[OF exh] nested_mask_sub_add[OF nm_sub] exhale_smaller[OF exh]
    apply simp
    by (metis TotalStateUtil.get_nm_total_full.simps get_fnm_nm.elims get_nm_loc_nm.simps nm0_def nm1_def)
  moreover obtain s1 s_exh where
    "nm_loc_sum loc nm1 s1" and
    "nm_loc_sum loc nm_exh s_exh"
    sorry
  ultimately have "s = s1 + s_exh"
    by (metis \<open>nm0 = get_nm_total_full \<omega>\<close> assms(2) nm_loc_sum_add nm_loc_sum_unique)

  have "nm_loc_sum loc (get_nm_total (add_to_mp_loc_total (get_total_full \<omega>1) (pred_id,vs) p)) s1"
    apply simp
    using \<open>nm_loc_sum loc nm1 s1\<close> nm1_def nm_loc_sum.elims(2) by fastforce
  hence "nm_loc_sum loc (get_nm_total_full \<omega>') (s1 + s_exh)"
    by (simp add: \<open>nm_loc_sum loc nm_exh s_exh\<close> nm_loc_sum_add_to_sub \<omega>')

  thus ?thesis
    using \<open>s = s1 + s_exh\<close> by blast
qed


lemma fold_rel_preserves_internal_consistency:
  assumes "fold_rel ctxt pred_id vs p \<omega> (RNormal \<omega>')"
      and "consistent_internal (get_nm_total_full \<omega>)"
    shows "consistent_internal (get_nm_total_full \<omega>')"
  by (metis assms(1) assms(2) consistent_internal_def fold_rel_preserves_loc_sum)


end
