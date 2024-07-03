theory TotalConsistencyProperties
  imports TotalSemanticsCore TotalSemantics
begin


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


\<comment> \<open>Helper lemmas on singleton masks\<close>

lemma singleton_mh_multiply:
  shows "singleton_mh loc (q * p) = ((*) q) \<circ> singleton_mh loc p"
  apply standard
  apply simp
  by (metis Rep_preal_inverse mult_eq_0_iff times_preal.rep_eq zero_preal.rep_eq)

lemma singleton_mp_multiply:
  shows "singleton_mp loc (q * p) = ((*) q) \<circ> singleton_mp loc p"
  apply standard
  apply simp
  by (metis Rep_preal_inverse mult_eq_0_iff times_preal.rep_eq zero_preal.rep_eq)


\<comment> \<open>Helper lemmas on masks and \<^const>\<open>nested_mask_multiply\<close>\<close>

lemma zero_mh_multiply:
  fixes frac :: preal
  shows "field_mask_multiply zero_mh frac = zero_mh"
  apply standard
  apply simp
  by (metis Rep_preal_inverse mult_zero_right times_preal.rep_eq zero_preal.rep_eq)

lemma zero_mp_multiply:
  fixes frac :: preal
  shows "predicate_mask_multiply zero_mp frac = zero_mp"
  apply standard
  apply simp
  by (metis Rep_preal_inverse mult_zero_right times_preal.rep_eq zero_preal.rep_eq)

lemma get_mh_multiply [simp]:
  fixes frac :: preal
  shows "get_mh_nm (nested_mask_multiply (get_nm_total \<phi>) frac) = field_mask_multiply (get_mh_total \<phi>) frac"
  by (metis get_fnm_nm.cases get_mh_nm.simps get_mh_total.simps nested_mask_multiply.simps)

lemma get_mp_multiply [simp]:
  fixes frac :: preal
  shows "get_mp_nm (nested_mask_multiply (get_nm_total \<phi>) frac) = predicate_mask_multiply (get_mp_total \<phi>) frac"
  by (metis get_fnm_nm.cases get_mp_nm.simps get_mp_total.simps nested_mask_multiply.simps)

lemma get_nm_loc_total_multiply [simp]:
  fixes frac :: preal
  shows "get_nm_loc_total (\<phi>\<lparr>get_nm_total := nested_mask_multiply (get_nm_total \<phi>) frac\<rparr>) loc =
         get_nm_loc_nm (nested_mask_multiply (get_nm_total \<phi>) frac) loc"
  by (metis TotalStateUtil.get_nm_loc_total.simps get_fnm_nm.simps get_fnm_total.simps get_nm_loc_nm.simps nested_mask_multiply.elims total_state.simps(2) total_state.simps(5) total_state.surjective)

lemma get_nm_loc_nm_multiply:
  fixes frac :: preal
  shows "get_nm_loc_nm (nested_mask_multiply nm frac) loc =
         map_option (\<lambda>m. nested_mask_multiply m frac) (get_nm_loc_nm nm loc)"
  by (metis comp_apply get_fnm_nm.cases get_nm_loc_nm.simps nested_mask_multiply.simps)

lemma nm_multiply_none:
    fixes frac :: preal
  assumes "frac > 0"
    shows "(get_nm_loc_nm nm loc = None) = (get_nm_loc_nm (nested_mask_multiply nm frac) loc = None)"
  by (metis None_eq_map_option_iff get_nm_loc_nm.elims get_nm_loc_nm.simps nested_mask_multiply.simps o_apply)

lemma nm_multiply_mp_value:
  fixes frac
  shows "get_mp_nm (nested_mask_multiply nm frac) loc = frac * get_mp_nm nm loc"
  by (metis get_mp_multiply get_mp_total.elims o_def predicate_mask_multiply.elims total_state.select_convs(2))

lemma nm_multiply_back:
    fixes frac :: preal
  assumes "frac > 0"
      and "get_mp_nm (nested_mask_multiply nm frac) loc = q"
    shows "get_mp_nm nm loc = q / frac"
  by (metis Rep_preal_inverse assms(1) assms(2) divide_preal.rep_eq dual_order.refl linorder_not_less nm_multiply_mp_value nonzero_mult_div_cancel_left times_preal.rep_eq zero_preal.rep_eq)

lemma nm_multiply_twice:
  fixes f1 f2 :: preal
  shows "nested_mask_multiply (nested_mask_multiply nm f1) f2 = nested_mask_multiply nm (f1 * f2)"
  sorry

lemma nm_multiply_1:
  shows "nested_mask_multiply nm 1 = nm"
  sorry

lemma nm_multiply_back_nm:
    fixes frac :: preal
  assumes "frac > 0"
      and "nm' = nested_mask_multiply nm frac"
    shows "nm = nested_mask_multiply nm' (1 / frac)"
proof -
  from assms(2) have "nested_mask_multiply nm' (1 / frac)
                      = nested_mask_multiply (nested_mask_multiply nm frac) (1 / frac)"
    by auto
  show "nm = nested_mask_multiply nm' (1 / frac)" using nm_multiply_twice nm_multiply_1
    by (metis PosReal.field_divide_inverse PosReal.field_inverse assms(1) assms(2) mult.commute order_less_irrefl)
qed

lemma mh_split_multiply:
  fixes frac :: preal
  assumes "mh_split mh mh\<^sub>1 mh\<^sub>2"
  shows "mh_split (field_mask_multiply mh frac) (field_mask_multiply mh\<^sub>1 frac) (field_mask_multiply mh\<^sub>2 frac)"
  apply simp
  apply standard
  by (metis PosReal.pmult_distr assms comp_apply fun_comb_def mh_split.elims(2))

lemma mp_split_multiply:
  fixes frac :: preal
  assumes "mp_split mp mp\<^sub>1 mp\<^sub>2"
  shows "mp_split (predicate_mask_multiply mp frac) (predicate_mask_multiply mp\<^sub>1 frac) (predicate_mask_multiply mp\<^sub>2 frac)"
  apply simp
  apply standard
  by (metis (no_types, opaque_lifting) PosReal.pmult_distr assms comp_eq_dest_lhs fun_comb_def mp_split.simps)


\<comment> \<open>Other helper lemmas\<close>

lemma total_state_update_nm_read:
  shows "get_nm_total (\<phi>\<lparr> get_nm_total := nm \<rparr>) = nm"
  by simp


\<comment> \<open>Expression evaluation is deterministic.\<close>

lemma eval_is_deterministic:
  assumes "ctxt, (Some \<omega>\<^sub>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t v\<^sub>1"
      and "ctxt, (Some \<omega>\<^sub>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t v\<^sub>2"
    shows "v\<^sub>1 = v\<^sub>2"
  sorry


\<comment> \<open>Combinability of fractional resources.\<close>

lemma fraction_combinability:
  assumes "sat ctxt \<phi> mh\<^sub>1 mp\<^sub>1 (syntactic_mult (Rep_preal p) A)"
      and "sat ctxt \<phi> mh\<^sub>2 mp\<^sub>2 (syntactic_mult (Rep_preal q) A)"
      and "mh_split mh mh\<^sub>1 mh\<^sub>2"
      and "mp_split mp mp\<^sub>1 mp\<^sub>2"
  shows "sat ctxt \<phi> mh mp (syntactic_mult (Rep_preal (p + q)) A)"
  oops


\<comment> \<open>A fraction of the mask satisfies the syntactic multiplication of the assertion.\<close>

inductive_cases SatAtomic_case: "sat ctxt \<omega> mh mp (Atomic x)"
inductive_cases SatAcc_case: "sat ctxt \<omega> mh mp (Atomic (Acc e_r f (PureExp e_p)))"
inductive_cases SatAccWildcard_case: "sat ctxt \<omega> mh mp (Atomic (Acc e_r f Wildcard))"
inductive_cases SatAccPred_case: "sat ctxt \<omega> mh mp (Atomic (AccPredicate pred_id e_args (PureExp e_p)))"
inductive_cases SatAccPredWildcard_case: "sat ctxt \<omega> mh mp (Atomic (AccPredicate pred_id e_args Wildcard))"
inductive_cases SatImp_case: "sat ctxt \<omega> mh mp (Imp e A)"
inductive_cases SatCond_case: "sat ctxt \<omega> mh mp (CondAssert e A B)"
inductive_cases SatImpureAnd_case: "sat ctxt \<omega> mh mp (ImpureAnd A B)"
inductive_cases SatImpureOr_case: "sat ctxt \<omega> mh mp (ImpureOr A B)"
inductive_cases SatWand_case: "sat ctxt \<omega> mh mp (A --* B)"
inductive_cases SatForAll_case: "sat ctxt \<omega> mh mp (ForAll ty A)"
inductive_cases SatExists_case: "sat ctxt \<omega> mh mp (Exists ty A)"

lemma sat_Acc_mp_zero:
  assumes "sat ctxt \<omega> mh mp (Atomic (Acc e_r f perm))"
  shows "mp = zero_mp"
  using SatAtomic_case assms by blast

lemma sat_AccPred_mh_zero:
  assumes "sat ctxt \<omega> mh mp (Atomic (AccPredicate pred_id e_args perm))"
  shows "mh = zero_mh"
  using SatAtomic_case assms by blast

lemma sat_Imp_True_or_False:
  assumes "sat ctxt \<omega> mh mp (Imp e A)"
  shows "ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True) \<or> ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
  using SatImp_case assms by blast

lemma sat_Cond_True_or_False:
  assumes "sat ctxt \<omega> mh mp (CondAssert e A B)"
  shows "ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True) \<or> ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
  using SatCond_case assms by blast

lemma sat_Imp_False_only_zero:
  assumes "sat ctxt \<omega> mh mp (Imp e A)"
      and "ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    shows "mh = zero_mh" and "mp = zero_mp"
   apply (rule SatImp_case)
     apply auto
  using assms(1) apply blast
  using assms(2) eval_is_deterministic apply blast
  apply (rule SatImp_case)
    apply auto
  using assms(1) apply blast
  using assms(2) eval_is_deterministic apply blast
  done

lemma fractionability_SatAcc:
  fixes p q :: preal
  assumes "q > 0"
      and "sat ctxt \<omega> mh zero_mp (syntactic_mult (Rep_preal p) (Atomic (Acc e_r f (PureExp e_p))))"
    shows "sat ctxt \<omega> (field_mask_multiply mh q) zero_mp (syntactic_mult (Rep_preal (q * p)) (Atomic (Acc e_r f (PureExp e_p))))"
proof -
  from assms(2) have "sat ctxt \<omega> mh zero_mp (Atomic (Acc e_r f (PureExp (Binop (ELit (LPerm (Rep_preal p))) Mult e_p))))"
    by simp
  then obtain v_r v_pp a where
    v_r_eval: "ctxt, (Some \<omega>) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef v_r)" and
    v_pp_eval: "ctxt, (Some \<omega>) \<turnstile> \<langle>Binop (ELit (LPerm (Rep_preal p))) Mult e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_pp)" and
    addr: "a = the_address v_r" and
    v_p_pos: "v_pp \<ge> 0" and
    mh_sing: "if v_r = Null then v_pp = 0 else mh = singleton_mh (a,f) (Abs_preal v_pp)"
    using SatAcc_case[of ctxt \<omega> mh zero_mp e_r f "Binop (ELit (LPerm (Rep_preal p))) Mult e_p" thesis] by blast
  show "sat ctxt \<omega> (field_mask_multiply mh q) zero_mp (syntactic_mult (Rep_preal (q * p)) (Atomic (Acc e_r f (PureExp e_p))))"
    apply simp
    apply (rule SatAcc)
    using v_r_eval apply blast
       prefer 2 using addr apply blast
  proof -
    from v_pp_eval obtain v_p where v_p_eval: "ctxt, (Some \<omega>) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val v_p"
      using RedBinop_case
      by (metis eval_binop_lazy.simps(23) option.distinct(1))
    show "ctxt, Some \<omega> \<turnstile> \<langle>Binop (ELit (LPerm (Rep_preal (PosReal.pmult q p)))) Mult e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm (Rep_preal q * v_pp))"
      apply standard
         apply auto
        apply standard
      using v_p_eval apply blast
    proof -
      from v_pp_eval v_p_eval have "eval_binop (val_of_lit (LPerm (Rep_preal p))) Mult v_p = BinopNormal (VPerm v_pp)"
        by (metis (no_types, lifting) RedLit_case TotalSemanticsCoreHelper.RedBinop_case eval_binop_lazy.simps(23) eval_is_deterministic extended_val.inject not_None_eq)
      thus "eval_binop (val_of_lit (LPerm (Rep_preal (PosReal.pmult q p)))) Mult v_p = BinopNormal (VPerm (Rep_preal q * v_pp))"
        using eval_binop_perm_mult_constant times_preal.rep_eq by auto
    qed
  next
    show "0 \<le> Rep_preal q * v_pp"
      by (simp add: prat_non_negative v_p_pos)
  next
    from mh_sing show "if v_r = Null then Rep_preal q * v_pp = 0 else (*) q \<circ> mh = singleton_mh (a, f) (Abs_preal (Rep_preal q * v_pp))"
      apply (cases "v_r = Null")
       apply auto[1]
      using singleton_mh_multiply
      by (metis Rep_preal_inverse eq_onp_same_args prat_non_negative times_preal.abs_eq v_p_pos)
  qed
qed

lemma fractionability_SatAcc_Wildcard:
  fixes p q :: preal
  assumes "p > 0" and "q > 0"
      and "sat ctxt \<omega> mh zero_mp (syntactic_mult (Rep_preal p) (Atomic (Acc e_r f Wildcard)))"
    shows "sat ctxt \<omega> (field_mask_multiply mh q) zero_mp (syntactic_mult (Rep_preal (q * p)) (Atomic (Acc e_r f Wildcard)))"
  apply simp
  apply standard
   apply auto
    defer 1
  using assms less_preal.rep_eq times_preal.rep_eq zero_preal.rep_eq apply fastforce
   apply (simp add: order_less_le prat_non_negative)
  by (smt (z3) SatAccWildcard SatAccWildcard_case assms(3) is_singleton_mh.simps less_preal.rep_eq order_less_le pperm_pnone_pgt real_mult_permexpr.simps(1) singleton_mh_multiply syntactic_mult.simps(2) times_preal.rep_eq zero_less_mult_iff zero_preal.rep_eq)

lemma fractionability_SatAccPred:
  fixes p q :: preal
  assumes "p > 0" and "q > 0"
      and "sat ctxt \<omega> zero_mh mp (syntactic_mult (Rep_preal p) (Atomic (AccPredicate pred_id e_args (PureExp e_p))))"
    shows "sat ctxt \<omega> zero_mh (predicate_mask_multiply mp q) (syntactic_mult (Rep_preal (q * p)) (Atomic (AccPredicate pred_id e_args (PureExp e_p))))"
proof -
  from assms have "sat ctxt \<omega> zero_mh mp (Atomic (AccPredicate pred_id e_args (PureExp (Binop (ELit (LPerm (Rep_preal p))) Mult e_p))))"
    by simp
  then obtain v_args v_pp where
    v_args_eval: "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some v_args)" and
    v_pp_eval: "ctxt, (Some \<omega>) \<turnstile> \<langle>Binop (ELit (LPerm (Rep_preal p))) Mult e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_pp)" and
    v_p_pos: "v_pp \<ge> 0" and
    mp_sing: "mp = singleton_mp (pred_id,v_args) (Abs_preal v_pp)"
    using SatAccPred_case by meson
  show "sat ctxt \<omega> zero_mh (predicate_mask_multiply mp q) (syntactic_mult (Rep_preal (q * p)) (Atomic (AccPredicate pred_id e_args(PureExp e_p))))"
    apply simp
    apply (rule SatAccPred)
    using v_args_eval apply blast
  proof -
    from v_pp_eval obtain v_p where v_p_eval: "ctxt, (Some \<omega>) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val v_p"
      using RedBinop_case
      by (metis eval_binop_lazy.simps(23) option.distinct(1))
    show "ctxt, Some \<omega> \<turnstile> \<langle>Binop (ELit (LPerm (Rep_preal (PosReal.pmult q p)))) Mult e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm (Rep_preal q * v_pp))"
      apply standard
         apply auto
        apply standard
      using v_p_eval apply blast
    proof -
      from v_pp_eval v_p_eval have "eval_binop (val_of_lit (LPerm (Rep_preal p))) Mult v_p = BinopNormal (VPerm v_pp)"
        by (metis (no_types, lifting) RedLit_case TotalSemanticsCoreHelper.RedBinop_case eval_binop_lazy.simps(23) eval_is_deterministic extended_val.inject not_None_eq)
      thus "eval_binop (val_of_lit (LPerm (Rep_preal (PosReal.pmult q p)))) Mult v_p = BinopNormal (VPerm (Rep_preal q * v_pp))"
        using eval_binop_perm_mult_constant times_preal.rep_eq by auto
    qed
  next
    show "0 \<le> Rep_preal q * v_pp"
      by (simp add: prat_non_negative v_p_pos)
  next
    from mp_sing show "(*) q \<circ> mp = singleton_mp (pred_id,v_args) (Abs_preal (Rep_preal q * v_pp))"
      using singleton_mp_multiply
      by (metis Rep_preal_inverse eq_onp_same_args prat_non_negative times_preal.abs_eq v_p_pos)
  qed
qed

lemma fractionability_SatAccPred_Wildcard:
  fixes p q :: preal
  assumes "p > 0" and "q > 0"
      and "sat ctxt \<omega> zero_mh mp (syntactic_mult (Rep_preal p) (Atomic (AccPredicate pred_id e_args Wildcard)))"
    shows "sat ctxt \<omega> zero_mh (predicate_mask_multiply mp q) (syntactic_mult (Rep_preal (q * p)) (Atomic (AccPredicate pred_id e_args Wildcard)))"
  apply simp
  apply standard
   apply auto
    defer 1
  using assms less_preal.rep_eq times_preal.rep_eq zero_preal.rep_eq apply fastforce
   apply (simp add: order_less_le prat_non_negative)
proof -
  from assms have "sat ctxt \<omega> zero_mh mp (Atomic (AccPredicate pred_id e_args Wildcard))"
    by (metis Rep_preal_inject order_less_le prat_non_negative real_mult_permexpr.simps(1) syntactic_mult.simps(3) zero_preal.rep_eq)
  then obtain v_args where
    "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some v_args)" and
    "is_singleton_mp (pred_id,v_args) mp"
    by (metis SatAccPredWildcard_case is_singleton_mp.elims(3))
  then show "sat ctxt \<omega> zero_mh ((*) q \<circ> mp) (Atomic (AccPredicate pred_id e_args Wildcard))"
    by (metis Rep_preal_inject SatAccPredWildcard SatAccPredWildcard_case assms(2) is_singleton_mp.elims(3) mult_eq_0_iff pperm_pnone_pgt singleton_mp_multiply times_preal.rep_eq zero_preal.rep_eq)
qed

lemma fractionability:
    fixes p :: preal
  assumes "p > 0"
      and "sat ctxt \<omega> mh mp A"
    shows "sat ctxt (mult_nm_total_full \<omega> p) (field_mask_multiply mh p) (predicate_mask_multiply mp p) (syntactic_mult (Rep_preal p) A)"
  sorry

lemma fractionabilityI:
  fixes p :: preal
  assumes "p > 0"
      and "sat ctxt \<omega> mh mp A"
      and "\<omega>' = mult_nm_total_full \<omega> p"
      and "mh' = field_mask_multiply mh p"
      and "mp' = predicate_mask_multiply mp p"
    shows "sat ctxt \<omega>' mh' mp' (syntactic_mult (Rep_preal p) A)"
  using assms fractionability by blast

lemma fractionability_inv:
    fixes p :: preal
  assumes "p > 0"
      and "sat ctxt \<omega> mh mp (syntactic_mult (Rep_preal p) A)"
    shows "sat ctxt (mult_nm_total_full \<omega> (1/p)) (field_mask_multiply mh (1/p)) (predicate_mask_multiply mp (1/p)) A"
  sorry

(* lemma fractionability_1:
  assumes "sat ctxt \<omega> mh mp (syntactic_mult 1 A)"
    shows "sat ctxt \<omega> mh mp A"
  sorry *)

lemma fractionability_pq:
    fixes p q :: preal
  assumes "p > 0" and "q > 0"
      and "sat ctxt \<omega> mh mp (syntactic_mult (Rep_preal p) A)"
    shows "sat ctxt (mult_nm_total_full \<omega> q) (field_mask_multiply mh q) (predicate_mask_multiply mp q) (syntactic_mult (Rep_preal (q * p)) A)"
proof -
  define \<omega>\<^sub>0 where \<omega>\<^sub>0: "\<omega>\<^sub>0 = mult_nm_total_full \<omega> (1/p)"
  define mh\<^sub>0 where mh\<^sub>0: "mh\<^sub>0 = field_mask_multiply mh (1/p)"
  define mp\<^sub>0 where mp\<^sub>0: "mp\<^sub>0 = predicate_mask_multiply mp (1/p)"
  show ?thesis
    apply (rule fractionabilityI)
    using assms(1) assms(2) less_preal.rep_eq times_preal.rep_eq zero_preal.rep_eq apply force
  proof -
    show "sat ctxt \<omega>\<^sub>0 mh\<^sub>0 mp\<^sub>0 A"
      using \<omega>\<^sub>0 assms(1) assms(3) fractionability_inv mh\<^sub>0 mp\<^sub>0 by blast
  next
    show "mult_nm_total_full \<omega> q = mult_nm_total_full \<omega>\<^sub>0 (q*p)"
      apply (simp add: \<omega>\<^sub>0)
      by (metis assms(1) mult.commute nm_multiply_back_nm nm_multiply_twice)
  next
    show "field_mask_multiply mh q = field_mask_multiply mh\<^sub>0 (q*p)"
      apply (simp add: mh\<^sub>0)
      apply standard
      by (metis (no_types, lifting) PosReal.field_divide_inverse PosReal.field_inverse assms(1) comp_apply lambda_one linorder_neq_iff mult.assoc mult.left_commute)
  next
    show "predicate_mask_multiply mp q = predicate_mask_multiply mp\<^sub>0 (q*p)"
      apply (simp add: mp\<^sub>0)
      apply standard
      by (metis (no_types, lifting) PosReal.field_divide_inverse PosReal.field_inverse assms(1) comp_apply lambda_one linorder_neq_iff mult.assoc mult.left_commute)
  qed
qed

(* lemma fractionability_original:
    fixes p q :: preal
  assumes "p > 0" and "q > 0"
      and "sat ctxt \<omega> mh mp (syntactic_mult (Rep_preal p) A)"
    shows "sat ctxt \<omega> (field_mask_multiply mh q) (predicate_mask_multiply mp q) (syntactic_mult (Rep_preal (q * p)) A)"
  using assms(3)
proof (induct A arbitrary: mh mp)
  case IH: (Atomic x)
  show ?case
  proof (cases x)
    case (Pure e)
    then show ?thesis
      by (smt (verit, best) IH SatAtomic_case atomic_assert.simps(5) atomic_assert.simps(7) syntactic_mult.simps(1) zero_mh_multiply zero_mp_multiply)
  next
    case (Acc e_r f perm)
    then have "mp = zero_mp"
      using IH sat_Acc_mp_zero by fastforce
    show ?thesis
    proof (cases perm)
      case (PureExp x1)
      then show ?thesis
      using IH fractionability_SatAcc[of q ctxt \<omega> mh p e_r f] assms
      by (metis Acc \<open>mp = zero_mp\<close> zero_mp_multiply)
    next
      case Wildcard
      then show ?thesis
        using fractionability_SatAcc_Wildcard
        by (metis Acc IH \<open>mp = zero_mp\<close> assms zero_mp_multiply)
    qed
  next
    case (AccPredicate pred_id e_args perm)
    then have "mh = zero_mh"
      using IH sat_AccPred_mh_zero by fastforce
    show ?thesis
    proof (cases perm)
      case (PureExp x1)
      then show ?thesis
        by (metis AccPredicate IH \<open>mh = zero_mh\<close> assms fractionability_SatAccPred zero_mh_multiply)
    next
      case Wildcard
      then show ?thesis
        using fractionability_SatAccPred_Wildcard
        by (metis AccPredicate IH \<open>mh = zero_mh\<close> assms zero_mh_multiply)
    qed
  qed
next
  case IH: (Imp e A)
  then consider (True) "ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)" |
               (False) "ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    using sat_Imp_True_or_False by fastforce
  then show ?case
  proof (cases)
    case True
    then show ?thesis
      by (metis IH.hyps IH.prems SatImpFalse SatImpTrue SatImp_case syntactic_mult.simps(4) zero_mh_multiply zero_mp_multiply)
  next
    case False
    then show ?thesis using IH
    proof -
      from IH False have "mh = zero_mh" and "mp = zero_mp"
        by (simp add: sat_Imp_False_only_zero)+
      thus "sat ctxt \<omega> (field_mask_multiply mh q) (predicate_mask_multiply mp q) (syntactic_mult (Rep_preal (q * p)) (Imp e A))"
        by (metis False SatImpFalse syntactic_mult.simps(4) zero_mh_multiply zero_mp_multiply)
    qed
  qed
next
  case IH: (CondAssert e A B)
  then consider (True) "ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)" |
               (False) "ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    using sat_Cond_True_or_False by fastforce
  then show ?case
  proof (cases)
    case True
    then show ?thesis
      by (metis (full_types) IH.hyps(1) IH.prems SatCondTrue SatCond_case eval_is_deterministic extended_val.inject syntactic_mult.simps(11) val.inject(2))
  next
    case False
    then show ?thesis
      by (metis (full_types) IH.hyps(2) IH.prems SatCondFalse SatCond_case eval_is_deterministic extended_val.inject syntactic_mult.simps(11) val.inject(2))
  qed
next
  case (ImpureAnd A1 A2)
  then show ?case
    using SatImpureAnd_case by fastforce
next
  case (ImpureOr A1 A2)
  then show ?case
    using SatImpureOr_case by fastforce
next
  case IH: (Star A B)
  then obtain mh\<^sub>1 mh\<^sub>2 mp\<^sub>1 mp\<^sub>2 where
    mh_split: "mh_split mh mh\<^sub>1 mh\<^sub>2" and
    mp_split: "mp_split mp mp\<^sub>1 mp\<^sub>2" and
    sat_A: "sat ctxt \<omega> mh\<^sub>1 mp\<^sub>1 (syntactic_mult (Rep_preal p) A)" and
    sat_B: "sat ctxt \<omega> mh\<^sub>2 mp\<^sub>2 (syntactic_mult (Rep_preal p) B)"
    unfolding syntactic_mult.simps using SatStar
    by (smt (verit) assert.distinct(35) assert.distinct(9) assert.inject(6) assert.simps(33) sat.simps)
  show ?case
    apply (simp only: syntactic_mult.simps)
    apply (rule SatStar)
       apply (rule mh_split_multiply, rule mh_split)
      apply (rule mp_split_multiply, rule mp_split)
    using sat_A sat_B IH by presburger+
next
  case (Wand A1 A2)
  then show ?case
    using SatWand_case by fastforce
next
  case (ForAll x1a A)
  then show ?case
    using SatForAll_case by fastforce
next
  case (Exists x1a A)
  then show ?case
    using SatExists_case by fastforce
qed *)


\<comment> \<open>The total state \<phi> we give to \<^const>\<open>sat\<close> does not matter.\<close>

lemma update_nm_total_full_trace_unchanged:
  shows "get_trace_total \<omega> = get_trace_total (update_nm_total_full \<omega> nm)"
  by force

lemma update_nm_total_full_store_unchanged:
  shows "get_store_total \<omega> = get_store_total (update_nm_total_full \<omega> nm)"
  by force

lemma eval_frac_mask_does_not_matter:
  fixes frac :: preal
  assumes "frac > 0"
      and "supported_pred_expr e"
  shows "ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v \<Longrightarrow>
         ctxt, (Some (update_nm_total_full \<omega> (nested_mask_multiply (get_nm_total_full \<omega>) frac))) \<turnstile> \<langle>e; (update_nm_total_full \<omega> (nested_mask_multiply (get_nm_total_full \<omega>) frac))\<rangle> [\<Down>]\<^sub>t Val v"
    and "red_pure_exps_total ctxt (Some \<omega>) es \<omega> vs \<Longrightarrow>
         red_pure_exps_total ctxt (Some (update_nm_total_full \<omega> (nested_mask_multiply (get_nm_total_full \<omega>) frac))) es (update_nm_total_full \<omega> (nested_mask_multiply (get_nm_total_full \<omega>) frac)) vs"
  using assms(2)
proof (induct rule: red_pure_exp_total_red_pure_exps_total.inducts)
  case (RedLit \<omega>_def l uu)
  then show ?case
    using red_pure_exp_total_red_pure_exps_total.RedLit by blast
next
  case (RedVar \<omega> n v \<omega>_def)
  then show ?case
    by (simp add: red_pure_exp_total_red_pure_exps_total.RedVar)
next
  case (RedResult \<omega> v \<omega>_def)
  then show ?case
    by (simp add: red_pure_exp_total_red_pure_exps_total.RedResult)
next
  case (RedBinopLazy \<omega>_def e1 \<omega> v1 bop v e2)
  then show ?case
    by (simp add: red_pure_exp_total_red_pure_exps_total.RedBinopLazy)
next
  case (RedBinop \<omega>_def e1 \<omega> v1 e2 v2 bop v)
  then show ?case
    by (simp add: red_pure_exp_total_red_pure_exps_total.RedBinop)
next
  case (RedBinopRightFailure \<omega>_def e1 \<omega> v1 e2 bop)
  then show ?case
    by (simp add: red_pure_exp_total_red_pure_exps_total.RedBinopRightFailure)
next
  case (RedBinopOpFailure \<omega>_def e1 \<omega> v1 e2 v2 bop)
  then show ?case
    by (simp add: red_pure_exp_total_red_pure_exps_total.RedBinopOpFailure)
next
  case (RedUnop \<omega>_def e \<omega> v unop v')
  then show ?case
    by (simp add: red_pure_exp_total_red_pure_exps_total.RedUnop)
next
  case (RedCondExpTrue \<omega>_def e1 \<omega> e2 r e3)
  then show ?case
    by (simp add: red_pure_exp_total_red_pure_exps_total.RedCondExpTrue)
next
  case (RedCondExpFalse \<omega>_def e1 \<omega> e3 r e2)
  then show ?case
    by (simp add: red_pure_exp_total_red_pure_exps_total.RedCondExpFalse)
next
  case (RedOld \<omega> l \<phi> \<omega>_def' \<omega>_def e v)
  then show ?case by simp
next
  case (RedOldFailure \<omega> l \<omega>_def e)
  then show ?case by simp
next
  case (RedField \<omega>_def e \<omega> a f v)
  then show ?case sorry
next
  case (RedFieldNullFailure \<omega>_def e \<omega> f)
  then show ?case sorry
next
  case (RedPermNull \<omega>_def e \<omega> f)
  then show ?case sorry
next
  case (RedPerm \<omega>_def e \<omega> a f v)
  then show ?case by simp
next
  case (RedUnfolding ubody \<omega> v p es)
  then show ?case sorry
next
  case (RedUnfoldingDefNoPred \<omega>_def es \<omega> vs pred_id pred_decl p ubody)
  then show ?case sorry
next
  case (RedUnfoldingDef \<omega>_def es \<omega> vs p nm' \<omega>'_def ubody v)
  then show ?case sorry
next
  case (RedSubFailure e' \<omega>_def \<omega>)
  then show ?case sorry
next
  case (RedExpListCons \<omega>_def e \<omega> v es res res')
  then show ?case sorry
next
  case (RedExpListFailure \<omega>_def e \<omega> es)
  then show ?case sorry
next
  case (RedExpListNil \<omega>_def \<omega>)
  then show ?case
    using red_pure_exp_total_red_pure_exps_total.RedExpListNil by blast
qed

(* lemma sat_\<phi>_does_not_matter:
  fixes frac :: preal
  assumes "frac > 0"
    shows "sat ctxt \<omega> mh mp A \<Longrightarrow> sat ctxt (update_nm_total_full \<omega> (nested_mask_multiply (get_nm_total_full \<omega>) frac)) mh mp A"
proof (induct A arbitrary: \<omega> mh mp)
  case (Atomic x)
  show ?case
  proof (cases x)
    case (Pure x1)
    then show ?thesis
      by (smt (verit) Atomic SatAtomic_case assms atomic_assert.distinct(1) atomic_assert.simps(7) eval_frac_mask_does_not_matter(1) sat.simps)
  next
    case (Acc x21 x22 x23)
    then show ?thesis
      by (smt (verit) Atomic SatAtomic_case assms atomic_assert.distinct(5) eval_frac_mask_does_not_matter(1) is_singleton_mh.elims(3) sat.simps)
  next
    case (AccPredicate x31 x32 x33)
    then show ?thesis
      by (smt (verit) Atomic assert.simps(11) assert.simps(13) assert.simps(19) assms eval_frac_mask_does_not_matter(1) eval_frac_mask_does_not_matter(2) sat.simps)
  qed
next
  case (Imp e A)
  then consider (True) "ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)" |
               (False) "ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    using sat_Imp_True_or_False by fastforce
  then show ?case
  proof (cases)
    case True
    hence "ctxt, Some (update_nm_total_full \<omega> (nested_mask_multiply (get_nm_total_full \<omega>) frac)) \<turnstile> \<langle>e;(update_nm_total_full \<omega> (nested_mask_multiply (get_nm_total_full \<omega>) frac))\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
      using eval_frac_mask_does_not_matter assms by blast
    thus ?thesis
      by (metis Imp.hyps Imp.prems SatImpTrue SatImp_case True eval_is_deterministic extended_val.inject val.inject(2))
  next
    case False
    then show ?thesis
      by (metis Imp.prems SatImpFalse assms eval_frac_mask_does_not_matter(1) sat_Imp_False_only_zero(1) sat_Imp_False_only_zero(2))
  qed
next
  case (CondAssert e A B)
  then consider (True) "ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)" |
               (False) "ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    using sat_Cond_True_or_False by fastforce
  then show ?case
  proof (cases)
    case True
    then show ?thesis
      by (metis CondAssert.hyps(1) CondAssert.hyps(2) CondAssert.prems SatCondFalse SatCondTrue SatCond_case assms eval_frac_mask_does_not_matter(1))
  next
    case False
    then show ?thesis
      by (metis CondAssert.hyps(1) CondAssert.hyps(2) CondAssert.prems SatCondFalse SatCondTrue SatCond_case assms eval_frac_mask_does_not_matter(1))
  qed
next
  case (ImpureAnd A1 A2)
  then show ?case
    using SatImpureAnd_case by blast
next
  case (ImpureOr A1 A2)
  then show ?case
    using SatImpureOr_case by blast
next
  case (Star A1 A2)
  then show ?case
    by (smt (verit) assert.inject(6) assert.simps(19) assert.simps(33) assert.simps(45) sat.simps)
next
  case (Wand A1 A2)
  then show ?case
    using SatWand_case by blast
next
  case (ForAll x1a A)
  then show ?case
    using SatForAll_case by blast
next
  case (Exists x1a A)
  then show ?case
    using SatExists_case by blast
qed *)


\<comment> \<open>A fraction of a consistent total state is external consistent.\<close>

lemma predicate_\<omega>_multiply:
  fixes frac :: preal
  shows "\<lparr> get_store_total = nth_option vs,
           get_trace_total = \<lambda>x. None,
           get_total_full = \<phi>\<lparr> get_nm_total := nested_mask_multiply (get_nm_total \<phi>) frac \<rparr> \<rparr> =
         mult_nm_total_full
         \<lparr> get_store_total = nth_option vs,
           get_trace_total = \<lambda>x. None,
           get_total_full = \<phi> \<rparr>
         frac"
  by force

lemma fraction_consistent_external':
  fixes frac :: preal
  assumes "0 < frac \<and> frac < 1"
    shows "consistent_external_wrt_ploc ctxt \<phi> (pred_id,vs) p \<Longrightarrow>
           consistent_external_wrt_ploc ctxt (mult_nm_total \<phi> frac) (pred_id,vs) (frac * p)"
      and "consistent_external ctxt \<phi> \<Longrightarrow>
           consistent_external ctxt (mult_nm_total \<phi> frac)"
proof (induction rule: consistent_external_wrt_ploc_consistent_external.inducts)
  case IH: (SatStep pred_id pred_decl pred_body vs \<phi> p)
  show ?case
    apply (rule SatStep)
        defer 3
    using IH apply blast+
    using IH.hyps(2) assms less_preal.rep_eq times_preal.rep_eq zero_preal.rep_eq apply auto[1]
    apply (simp del: field_mask_multiply.simps predicate_mask_multiply.simps)
    apply (simp only: predicate_\<omega>_multiply)
    apply (rule fractionability_pq)
    using IH.hyps(2) apply blast
    apply (simp add: assms)
    using IH.IH(2) by fastforce
next
  case IH: (SatAll \<phi>)
  show ?case
  proof (standard, simp del: get_nm_loc_total.simps)
    have "\<And>loc. ((get_mp_nm (get_nm_total \<phi>) loc) = 0) = (get_nm_loc_nm (get_nm_total \<phi>) loc = None)"
      by (metis IH.hyps TotalStateUtil.get_nm_loc_total.elims eq_fst_iff get_fnm_nm.elims get_fnm_total.simps get_mp_total.simps get_nm_loc_nm.simps)
    hence "\<And>loc. ((get_mp_nm (get_nm_total \<phi>) loc) = 0) = (get_nm_loc_nm (nested_mask_multiply (get_nm_total \<phi>) frac) loc = None)"
      using nm_multiply_none assms by blast
    thus "\<And>pred_id vs. (frac * (get_mp_nm (get_nm_total \<phi>) (pred_id,vs)) = PosReal.pnone) = (get_nm_loc_nm (nested_mask_multiply (get_nm_total \<phi>) frac) (pred_id,vs) = None)"
      by (smt (verit) Rep_preal_inverse assms less_preal.rep_eq mult_eq_0_iff times_preal.rep_eq zero_preal.rep_eq)
  next
    fix pred_id vs q nm'
    assume perm: "get_mp_total (mult_nm_total \<phi> frac) (pred_id, vs) = q"
       and nm': "Some nm' = TotalStateUtil.get_nm_loc_total (mult_nm_total \<phi> frac) (pred_id, vs)"
    hence "get_mp_total \<phi> (pred_id,vs) = q / frac" using nm_multiply_back
      by (metis assms get_mp_total.simps mult_nm_total.elims total_state.simps(2) total_state.surjective total_state.update_convs(2))
    moreover from nm' have nm'_frac: "Some nm' = get_nm_loc_nm (nested_mask_multiply (get_nm_total \<phi>) frac) (pred_id,vs)"
      using get_nm_loc_total_multiply by auto
    have "Some (nested_mask_multiply nm' (1 / frac)) = get_nm_loc_total \<phi> (pred_id,vs)"
    proof simp
      from nm'_frac obtain nm where "Some nm = get_nm_loc_total \<phi> (pred_id,vs)"
        by (metis TotalStateUtil.get_nm_loc_total.simps assms get_fnm_nm.elims get_fnm_total.simps get_nm_loc_nm.simps nm_multiply_none not_None_eq)
      moreover hence "get_nm_loc_nm (nested_mask_multiply (get_nm_total \<phi>) frac) (pred_id,vs) = Some (nested_mask_multiply nm frac)"
        by (metis TotalStateUtil.get_nm_loc_total.elims get_fnm_nm.cases get_fnm_nm.simps get_fnm_total.simps get_nm_loc_nm.simps get_nm_loc_nm_multiply option.simps(9))
      ultimately show "Some (nested_mask_multiply nm' (1 / frac)) = get_fnm_nm (get_nm_total \<phi>) (pred_id, vs)"
        using assms nm'_frac nm_multiply_back_nm by force
    qed
    moreover note IH(3)
    ultimately have "consistent_external_wrt_ploc ctxt
                       (\<phi>\<lparr> get_nm_total := nested_mask_multiply (get_nm_total (\<phi>\<lparr> get_nm_total := (nested_mask_multiply nm' (1 / frac)) \<rparr>)) frac \<rparr>)
                       (pred_id,vs) q"
      using perm by force
    moreover have "\<phi>\<lparr> get_nm_total := nested_mask_multiply (get_nm_total (\<phi>\<lparr> get_nm_total := (nested_mask_multiply nm' (1 / frac)) \<rparr>)) frac \<rparr>
                   = \<phi>\<lparr> get_nm_total := nm' \<rparr>"
      by (metis assms mult.commute nm_multiply_back_nm nm_multiply_twice total_state_update_nm_read)
    ultimately show "consistent_external_wrt_ploc ctxt
                       (mult_nm_total \<phi> frac\<lparr>get_nm_total := nm'\<rparr>)
                       (pred_id,vs) q"
      by fastforce
  qed
qed

lemma fraction_consistent_external:
    fixes frac :: preal
  assumes "consistent_external_wrt_ploc ctxt \<phi> (pred_id,vs) p"
      and "0 < frac \<and> frac < 1"
      and "nm = nested_mask_multiply (get_nm_total \<phi>) frac"
    shows "consistent_external_wrt_ploc ctxt (update_nm_total \<phi> nm) (pred_id,vs) (p * frac)"
  oops


\<comment> \<open>Unfold statement preserves external state consistency.\<close>

lemma unfold_preserves_external_consistency:
  assumes "consistent_external ctxt \<phi>"
      and "get_total_full \<omega> = \<phi>"
      and "red_stmt_total ctxt R \<Lambda> (Unfold pred_id e_args (PureExp e_p)) \<omega> (RNormal \<omega>')"
      and "get_total_full \<omega>' = \<phi>'"
    shows "consistent_external ctxt \<phi>'"
  oops

end
