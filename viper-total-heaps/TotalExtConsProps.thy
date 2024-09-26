section \<open>Properties of External Consistency\<close>

theory TotalExtConsProps
  imports TotalExternalConsistency TotalStateProperties TotalSemProperties
begin


subsection \<open>Helper Lemma (Todo: move to proper places)\<close>

lemma total_state_update_nm_read:
  shows "get_nm_total (\<phi>\<lparr> get_nm_total := nm \<rparr>) = nm"
  by simp

lemma supported_sub_expr_supported:
  assumes "supported_pred_expr e"
  shows "list_all supported_pred_expr (sub_pure_exp_total e)"
  using assms
  by (induct e; simp add: list_all_length)

lemma update_mp_loc_total_preserves_hh:
  shows "get_hh_total (upd_mp_loc_total \<phi> ploc mp) = get_hh_total \<phi>"
  sorry

lemma add_to_nm_loc_total_preserves_hh:
  shows "get_hh_total (add_to_nm_loc_total \<phi> ploc nm) = get_hh_total \<phi>"
  sorry

lemma nm_subtract_mh:
  shows "get_mh_nm (nested_mask_subtract nm\<^sub>1 nm\<^sub>2) = get_mh_nm nm\<^sub>1 - get_mh_nm nm\<^sub>2"
  by (metis get_fnm_nm.cases get_mh_nm.simps nested_mask_subtract.simps)

lemma nm_subtract_mp:
  shows "get_mp_nm (nested_mask_subtract nm\<^sub>1 nm\<^sub>2) = get_mp_nm nm\<^sub>1 - get_mp_nm nm\<^sub>2"
  by (metis get_fnm_nm.cases get_mp_nm.simps nested_mask_subtract.simps)


\<comment> \<open>The total state \<phi> we give to \<^const>\<open>sat\<close> does not matter.\<close>

lemma update_nm_total_full_trace_unchanged:
  shows "get_trace_total \<omega> = get_trace_total (upd_nm_total_full \<omega> nm)"
  by force

lemma update_nm_total_full_store_unchanged:
  shows "get_store_total \<omega> = get_store_total (upd_nm_total_full \<omega> nm)"
  by force

lemma eval_frac_mask_does_not_matter:
    fixes frac :: preal
  assumes "frac > 0"
    shows "ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t v \<Longrightarrow>
           supported_pred_expr e \<Longrightarrow>
           ctxt, map_option (\<lambda>x. mult_nm_total_full x frac) \<omega>_def \<turnstile> \<langle>e; (mult_nm_total_full \<omega> frac)\<rangle> [\<Down>]\<^sub>t v"
      and "red_pure_exps_total ctxt \<omega>_def es \<omega> vs \<Longrightarrow>
           list_all supported_pred_expr es \<Longrightarrow>
           red_pure_exps_total ctxt (map_option (\<lambda>x. mult_nm_total_full x frac) \<omega>_def) es (mult_nm_total_full \<omega> frac) vs"
proof (induction arbitrary: rule: red_pure_exp_total_red_pure_exps_total.inducts)
  case (RedLit \<omega>_def l uu)
  then show ?case
    by (simp add: red_pure_exp_total_red_pure_exps_total.RedLit)
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
  hence e_sup: "supported_pred_expr e" by simp
  moreover have "ctxt, map_option (\<lambda>x. mult_nm_total_full x frac) \<omega>_def \<turnstile>
        \<langle>FieldAcc e f; mult_nm_total_full \<omega> frac\<rangle> [\<Down>]\<^sub>t
        (if if_Some (\<lambda>res. (a, f) \<in> get_valid_locs res) (map_option (\<lambda>x. mult_nm_total_full x frac) \<omega>_def) then Val v else VFailure)"
    apply (rule red_pure_exp_total_red_pure_exps_total.RedField)
    using RedField.IH(2) e_sup apply blast
    using RedField.hyps get_hh_total_full_multiply by blast
  moreover have "if_Some (\<lambda>res. (a, f) \<in> get_valid_locs res) (map_option (\<lambda>x. mult_nm_total_full x frac) \<omega>_def) =
                 if_Some (\<lambda>res. (a, f) \<in> get_valid_locs res) \<omega>_def"
    apply (cases \<omega>_def; simp)
    using assms get_valid_locs_multiply by auto
  ultimately show ?case
    by presburger
next
  case IH: (RedFieldNullFailure \<omega>_def e \<omega> f)
  hence e_sup: "supported_pred_expr e" by simp
  show ?case
    apply (rule red_pure_exp_total_red_pure_exps_total.RedFieldNullFailure)
    using IH e_sup by blast
next
  case (RedPermNull \<omega>_def e \<omega> f)
  then show ?case by simp
next
  case (RedPerm \<omega>_def e \<omega> a f v)
  then show ?case by simp
next
  case IH: (RedUnfolding ubody \<omega> v p es)
  then show ?case
    using RedUnfolding
    by (metis (mono_tags, lifting) option.map_disc_iff pure_exp_pred.elims(2) pure_exp_pred_rec.simps(12) sub_pure_exp_total.simps(9) supported_sub_expr_supported)
next
  case IH: (RedUnfoldingDefNoPred \<omega>_def es \<omega> vs pred_id ubody)
  then show ?case
    by (metis (mono_tags, lifting) RedUnfoldingDefNoPred Rep_preal_inject get_mp_total_full_multiply mult_eq_0_iff option.simps(9) sub_pure_exp_total.simps(9) supported_sub_expr_supported times_preal.rep_eq zero_preal.rep_eq)
next
  case IH: (RedUnfoldingDef \<omega>_def es \<omega> vs perm p nm' \<omega>'_def ubody v)
  hence es_sup: "list_all supported_pred_expr es"
    by (metis sub_pure_exp_total.simps(9) supported_sub_expr_supported)
  show ?case
    apply (simp del: mult_nm_total_full.simps)
    apply (rule red_pure_exp_total_red_pure_exps_total.RedUnfoldingDef)
    using IH es_sup apply simp
       defer 1
    defer 1
    using IH apply (simp, simp)
    sorry \<comment> \<open>depends on the semantics of unfolding\<close>
next
  case IH: (RedSubFailure e' \<omega>_def \<omega>)
  show ?case
    apply (rule red_pure_exp_total_red_pure_exps_total.RedSubFailure)
    using IH supported_sub_expr_supported by blast+
next
  case IH: (RedExpListCons \<omega>_def e \<omega> v es res res')
  hence e_sup: "supported_pred_expr e" and es_sup: "list_all supported_pred_expr es"
    by auto+
  show ?case
    apply (rule red_pure_exp_total_red_pure_exps_total.RedExpListCons)
    using IH e_sup es_sup by blast+
next
  case (RedExpListFailure \<omega>_def e \<omega> es)
  then show ?case
    by (simp add: red_pure_exp_total_red_pure_exps_total.RedExpListFailure)
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


\<comment> \<open>Helper lemmas on \<^const>\<open>sat\<close>\<close>

lemma sat_Acc_mp_zero:
  assumes "sat ctxt \<omega> mh mp (Atomic (Acc e_r f perm))"
  shows "mp = zero_mask"
  using SatAtomic_case assms by blast

lemma sat_AccPred_mh_zero:
  assumes "sat ctxt \<omega> mh mp (Atomic (AccPredicate pred_id e_args perm))"
  shows "mh = zero_mask"
  using SatAtomic_case assms by blast

lemma sat_Imp_True_or_False:
  assumes "sat ctxt \<omega> mh mp (Imp e A)"
  shows "ctxt, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True) \<or> ctxt, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
  using SatImp_case assms by blast

lemma sat_Cond_True_or_False:
  assumes "sat ctxt \<omega> mh mp (CondAssert e A B)"
  shows "ctxt, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True) \<or> ctxt, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
  using SatCond_case assms by blast

lemma sat_Imp_False_only_zero:
  assumes "sat ctxt \<omega> mh mp (Imp e A)"
      and "ctxt, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    shows "mh = zero_mask" and "mp = zero_mask"
   apply (rule SatImp_case)
     apply auto
  using assms(1) apply blast
  using assms(2) eval_is_deterministic apply blast
  apply (rule SatImp_case)
    apply auto
  using assms(1) apply blast
  using assms(2) eval_is_deterministic apply blast
  done


subsection \<open>Fractionability of External Consistent States\<close>

(* lemma combinability_SatAcc:
    fixes p q :: preal
  assumes "p > 0" and "q > 0"
      and "supported_pred_expr e_r"
      and "supported_pred_expr e_p"
      and "sat ctxt \<omega> mh\<^sub>1 zero_mp (syntactic_mult (Rep_preal p) (Atomic (Acc e_r f (PureExp e_p))))"
      and "sat ctxt \<omega> mh\<^sub>2 zero_mp (syntactic_mult (Rep_preal q) (Atomic (Acc e_r f (PureExp e_p))))"
    shows "sat ctxt \<omega> (field_mask_merge mh\<^sub>1 mh\<^sub>2) zero_mp (syntactic_mult (Rep_preal (p + q)) (Atomic (Acc e_r f (PureExp e_p))))"
proof -
  obtain v_r where v_r: "ctxt, None \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef v_r)"
    by (metis SatAcc_case assms(5) real_mult_permexpr.simps(2) syntactic_mult.simps(2))
  define a where "a = the_address v_r"
  from assms(5) have "sat ctxt \<omega> mh\<^sub>1 zero_mp (Atomic (Acc e_r f (PureExp (Binop (ELit (LPerm (Rep_preal p))) Mult e_p))))"
    by simp
  then obtain v_p_p where
    v_p_p: "ctxt, None \<turnstile> \<langle>Binop (ELit (LPerm (Rep_preal p))) Mult e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p_p)" and
    v_p_p_nn:"v_p_p \<ge> 0" and
    mh1: "if v_r = Null then v_p_p = 0 else mh\<^sub>1 = singleton_mh (a,f) (Abs_preal v_p_p)"
    using SatAcc_case[of ctxt \<omega> mh\<^sub>1 zero_mp e_r f]
    by (metis v_r a_def eval_is_deterministic extended_val.inject val.inject(4))
  from assms(6) have "sat ctxt \<omega> mh\<^sub>2 zero_mp (Atomic (Acc e_r f (PureExp (Binop (ELit (LPerm (Rep_preal q))) Mult e_p))))"
    by simp
  then obtain v_p_q where
    v_p_q: "ctxt, None \<turnstile> \<langle>Binop (ELit (LPerm (Rep_preal q))) Mult e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p_q)" and
    v_p_q_nn: "v_p_q \<ge> 0" and
    mh2: "if v_r = Null then v_p_q = 0 else mh\<^sub>2 = singleton_mh (a,f) (Abs_preal v_p_q)"
    using SatAcc_case[of ctxt \<omega> mh\<^sub>2 zero_mp e_r f]
    by (metis v_r a_def eval_is_deterministic extended_val.inject val.inject(4))
  then obtain v_p where
    v_p: "ctxt, None \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val v_p"
    by (metis TotalSemanticsCoreHelper.RedBinop_case eval_binop_lazy.simps(23) option.distinct(1))
  have "ctxt, None \<turnstile> \<langle>Binop (ELit (LPerm (Rep_preal (p + q)))) Mult e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm (v_p_p + v_p_q))"
  proof
    show "ctxt, None \<turnstile> \<langle>ELit (LPerm (Rep_preal (p + q)));\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm (Rep_preal (p + q)))"
      by (metis RedLit val_of_lit.simps(3))
  next
    show "ctxt, None \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val v_p"
      using v_p by auto
  next
    show "eval_binop_lazy (VPerm (Rep_preal (p + q))) Mult = None"
      by auto
  next
    show "eval_binop (Option.is_none (Some \<omega>)) (VPerm (Rep_preal (p + q))) Mult v_p = BinopNormal (VPerm (v_p_p + v_p_q))"
    proof (cases v_p)
      case (VInt x1)
      then show ?thesis sorry
    next
      case (VBool x2)
      then show ?thesis using v_p_q
        by (metis RedLit TotalSemanticsCoreHelper.RedBinop_case binop_result.distinct(3) eval_binop.simps(12) eval_binop_lazy.simps(23) eval_is_deterministic extended_val.inject option.distinct(1) v_p val_of_lit.simps(3))
    next
      case (VPerm x3)
      then show ?thesis sorry
    next
      case (VRef x4)
      then show ?thesis sorry
    next
      case (VAbs x5)
      then show ?thesis sorry
    qed
  qed
  moreover have "v_p_p + v_p_q \<ge> 0"
    using v_p_p_nn v_p_q_nn by auto
  moreover have "if v_r = Null then v_p_p + v_p_q = 0 else field_mask_merge mh\<^sub>1 mh\<^sub>2 = singleton_mh (a,f) (Abs_preal v_p_p + Abs_preal v_p_q)"
    apply (cases "v_r = Null"; simp)
    using mh1 mh2 apply auto[1]
    apply standard
    by (simp add: fun_comb_def mh1 mh2)
  moreover have "Abs_preal v_p_p + Abs_preal v_p_q = Abs_preal (v_p_p + v_p_q)"
    by (simp add: eq_onp_same_args plus_preal.abs_eq v_p_p_nn v_p_q_nn)
  moreover note this
  show ?thesis
    apply simp
    apply standard
    using v_r apply blast
    using calculation apply blast+
    using calculation a_def apply force
    by auto
qed


lemma combinability_SatAcc_Wildcard:
  assumes "supported_pred_expr e_r"
      and "sat ctxt \<omega> mh\<^sub>1 zero_mp (Atomic (Acc e_r f Wildcard))"
      and "sat ctxt \<omega> mh\<^sub>2 zero_mp (Atomic (Acc e_r f Wildcard))"
    shows "sat ctxt \<omega> (field_mask_merge mh\<^sub>1 mh\<^sub>2) zero_mp (Atomic (Acc e_r f Wildcard))"
  sorry

lemma combinability_SatAccPred:
    fixes p q :: preal
  assumes "p > 0" and "q > 0"
      and "list_all supported_pred_expr e_args"
      and "supported_pred_expr e_p"
      and "sat ctxt \<omega> zero_mh mp\<^sub>1 (syntactic_mult (Rep_preal p) (Atomic (AccPredicate pred_id e_args (PureExp e_p))))"
      and "sat ctxt \<omega> zero_mh mp\<^sub>2 (syntactic_mult (Rep_preal q) (Atomic (AccPredicate pred_id e_args (PureExp e_p))))"
    shows "sat ctxt \<omega> zero_mh (predicate_mask_merge mp\<^sub>1 mp\<^sub>2) (syntactic_mult (Rep_preal (p + q)) (Atomic (AccPredicate pred_id e_args (PureExp e_p))))"
  sorry

lemma combinability_SatAccPred_Wildcard:
  assumes "list_all supported_pred_expr e_args"
      and "sat ctxt \<omega> zero_mh mp\<^sub>1 (Atomic (AccPredicate pred_id e_args Wildcard))"
      and "sat ctxt \<omega> zero_mh mp\<^sub>2 (Atomic (AccPredicate pred_id e_args Wildcard))"
    shows "sat ctxt \<omega> zero_mh (predicate_mask_merge mp\<^sub>1 mp\<^sub>2) (Atomic (AccPredicate pred_id e_args Wildcard))"
  sorry

lemma fraction_combinability:
  assumes "sat ctxt \<omega> mh\<^sub>1 mp\<^sub>1 (syntactic_mult (Rep_preal p) A)"
      and "sat ctxt \<omega> mh\<^sub>2 mp\<^sub>2 (syntactic_mult (Rep_preal q) A)"
      and "mh_split mh mh\<^sub>1 mh\<^sub>2"
      and "mp_split mp mp\<^sub>1 mp\<^sub>2"
      and "supported_pred_body A"
      and "p > 0" and "q > 0"
    shows "sat ctxt \<omega> mh mp (syntactic_mult (Rep_preal (p + q)) A)"
  using assms(1-5)
proof (induct A arbitrary: mh\<^sub>1 mh\<^sub>2 mp\<^sub>1 mp\<^sub>2 mh mp)
  case IH: (Atomic x)
  show ?case
  proof (cases x)
    case (Pure e)
    then show ?thesis
      by (smt (verit) IH.prems(1) IH.prems(2) IH.prems(3) IH.prems(4) SatAtomic_case atomic_assert.distinct(1) atomic_assert.distinct(3) mh_split_zero mp_split_zero syntactic_mult.simps(1))
  next
    case (Acc e_r f perm)
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      moreover hence "supported_pred_expr e_r" and "supported_pred_expr e_p"
        using Acc IH.prems(5) by force+
      ultimately show ?thesis
        using combinability_SatAcc[of p q e_r e_p ctxt \<omega> mh\<^sub>1 f mh\<^sub>2] IH assms(6,7)
        by (metis Acc field_mask_merge.simps mh_split.elims(2) mp_split_zero sat_Acc_mp_zero syntactic_mult.simps(2))
    next
      case Wildcard
      moreover hence "supported_pred_expr e_r"
        using Acc IH.prems(5) by force
      ultimately show ?thesis
        using combinability_SatAcc_Wildcard[of e_r ctxt \<omega> mh\<^sub>1 f mh\<^sub>2] IH
        by (smt (verit) Acc Rep_preal_inject assms(6) assms(7) field_mask_merge.simps less_preal.rep_eq mh_split.elims(2) mp_split_zero padd_pos prat_non_negative real_mult_permexpr.simps(1) sat_Acc_mp_zero syntactic_mult.simps(2) zero_preal.rep_eq)
    qed
  next
    case (AccPredicate pred_id e_args perm)
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      moreover hence "list_all supported_pred_expr e_args" and "supported_pred_expr e_p"
         apply (metis (no_types, lifting) AccPredicate Ball_set IH.prems(5) assert_pred.elims(2) assert_pred_rec.simps(1) atomic_assert_pred.elims(2) atomic_assert_pred_rec.simps(5))
        using AccPredicate IH.prems(5) calculation by auto
      ultimately show ?thesis
        using combinability_SatAccPred[of p q e_args e_p ctxt \<omega> mp\<^sub>1 pred_id mp\<^sub>2] IH assms(6,7)
        by (metis (no_types, lifting) AccPredicate mh_split_zero mp_split.elims(2) predicate_mask_merge.simps sat_AccPred_mh_zero syntactic_mult.simps(3))
    next
      case Wildcard
      moreover hence "list_all supported_pred_expr e_args"
        by (metis (no_types, lifting) AccPredicate IH.prems(5) assert_pred.elims(2) assert_pred_rec.simps(1) atomic_assert_pred.elims(2) atomic_assert_pred_rec.simps(4) list_all_length)
      ultimately show ?thesis
        using combinability_SatAccPred_Wildcard[of e_args ctxt \<omega> mp\<^sub>1 pred_id mp\<^sub>2] IH
        by (smt (verit, best) AccPredicate PosReal.ppos.rep_eq assms(6) assms(7) gr_0_is_ppos mh_split_zero mp_split.elims(2) padd_pos preal_not_0_gt_0 predicate_mask_merge.simps real_mult_permexpr.simps(1) sat_AccPred_mh_zero syntactic_mult.simps(3))
    qed
  qed
next
  case IH: (Imp e A)
  have e_sup: "supported_pred_expr e" and A_sup: "supported_pred_body A"
    using IH.prems(5) by force+
  from IH consider (True) "ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)" |
               (False) "ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    using sat_Imp_True_or_False
    by (metis syntactic_mult.simps(4))
  then show ?case
  proof (cases)
    case True
    show ?thesis
      apply simp
      by (metis A_sup IH.hyps IH.prems(1) IH.prems(2) IH.prems(3) IH.prems(4) SatImpTrue SatImp_case True eval_is_deterministic extended_val.inject syntactic_mult.simps(4) val.inject(2))
  next
    case False
    hence "mh\<^sub>1 = zero_mh" and "mh\<^sub>2 = zero_mh" and "mp\<^sub>1 = zero_mp" and "mp\<^sub>2 = zero_mp"
         apply (metis IH.prems(1) sat_Imp_False_only_zero(1) syntactic_mult.simps(4))
      apply (metis False IH.prems(2) sat_Imp_False_only_zero(1) syntactic_mult.simps(4))
      apply (metis False IH.prems(1) sat_Imp_False_only_zero(2) syntactic_mult.simps(4))
      by (metis False IH.prems(2) sat_Imp_False_only_zero(2) syntactic_mult.simps(4))
    hence "mh = zero_mh" and "mp = zero_mp"
      using IH.prems(3) mh_split_zero apply blast
      using IH.prems(4) \<open>mp\<^sub>1 = zero_mp\<close> \<open>mp\<^sub>2 = zero_mp\<close> mp_split_zero by blast
    show ?thesis
      apply simp
      apply (rule SatImpFalse)
        apply (simp add: False)
      using IH \<open>mh = zero_mh\<close> \<open>mp = zero_mp\<close> by force+
  qed
next
  case IH: (CondAssert e A B)
  have e_sup: "supported_pred_expr e" and A_sup: "supported_pred_body A" and B_sup: "supported_pred_body B"
    using IH.prems(5) by force+
  from IH consider (True) "ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)" |
               (False) "ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    using sat_Cond_True_or_False
    by (metis syntactic_mult.simps(11))
  then show ?case
  proof (cases)
    case True
    then show ?thesis
      by (smt (verit) A_sup IH.hyps(1) IH.prems(1) IH.prems(2) IH.prems(3) IH.prems(4) SatCond_case eval_is_deterministic extended_val.inject sat.simps syntactic_mult.simps(11) val.inject(2))
  next
    case False
    then show ?thesis
      by (smt (verit) B_sup IH.hyps(2) IH.prems(1) IH.prems(2) IH.prems(3) IH.prems(4) SatCond_case eval_is_deterministic extended_val.inject sat.simps syntactic_mult.simps(11) val.inject(2))
  qed
next
  case (ImpureAnd A1 A2)
  then show ?case
    by (metis SatImpureAnd_case syntactic_mult.simps(8))
next
  case (ImpureOr A1 A2)
  then show ?case
    by (metis SatImpureOr_case syntactic_mult.simps(9))
next
  case IH: (Star A B)
  hence A_sup: "supported_pred_body A" and B_sup: "supported_pred_body B"
    by force+
  from IH have "sat ctxt \<omega> mh\<^sub>1 mp\<^sub>1 (syntactic_mult (Rep_preal p) A && syntactic_mult (Rep_preal p) B)"
    by simp
  then obtain mh\<^sub>1A mh\<^sub>1B mp\<^sub>1A mp\<^sub>1B where
    mh_split_p: "mh_split mh\<^sub>1 mh\<^sub>1A mh\<^sub>1B" and
    mp_split_p: "mp_split mp\<^sub>1 mp\<^sub>1A mp\<^sub>1B" and
    sat_A_p: "sat ctxt \<omega> mh\<^sub>1A mp\<^sub>1A (syntactic_mult (Rep_preal p) A)" and
    sat_B_p: "sat ctxt \<omega> mh\<^sub>1B mp\<^sub>1B (syntactic_mult (Rep_preal p) B)"
    using SatStar_case[of ctxt \<omega> mh\<^sub>1 mp\<^sub>1]
    by (metis (no_types, lifting) mh_split.simps mp_split.simps)
  from IH have "sat ctxt \<omega> mh\<^sub>2 mp\<^sub>2 (syntactic_mult (Rep_preal q) A && syntactic_mult (Rep_preal q) B)"
    by simp
  then obtain mh\<^sub>2A mh\<^sub>2B mp\<^sub>2A mp\<^sub>2B where
    mh_split_q: "mh_split mh\<^sub>2 mh\<^sub>2A mh\<^sub>2B" and
    mp_split_q: "mp_split mp\<^sub>2 mp\<^sub>2A mp\<^sub>2B" and
    sat_A_q: "sat ctxt \<omega> mh\<^sub>2A mp\<^sub>2A (syntactic_mult (Rep_preal q) A)" and
    sat_B_q: "sat ctxt \<omega> mh\<^sub>2B mp\<^sub>2B (syntactic_mult (Rep_preal q) B)"
    using SatStar_case[of ctxt \<omega> mh\<^sub>2 mp\<^sub>2]
    by (metis (no_types, lifting) mh_split.simps mp_split.simps)
  obtain mhA mhB where mh_split_A: "mh_split mhA mh\<^sub>1A mh\<^sub>2A" and mh_split_B: "mh_split mhB mh\<^sub>1B mh\<^sub>2B"
    by auto+
  obtain mpA mpB where mp_split_A: "mp_split mpA mp\<^sub>1A mp\<^sub>2A" and mp_split_B: "mp_split mpB mp\<^sub>1B mp\<^sub>2B"
    by auto+
  show ?case
  proof (simp, rule SatStar)
    show "mh_split mh mhA mhB"
      using IH.prems(3) mh_split_A mh_split_B mh_split_p mh_split_q mh_split_twice by blast
    show "mp_split mp mpA mpB"
      using IH.prems(4) mp_split_A mp_split_B mp_split_p mp_split_q mp_split_twice by blast
    show "sat ctxt \<omega> mhA mpA (syntactic_mult (Rep_preal (p + q)) A)"
      using IH(1) A_sup mh_split_A mp_split_A sat_A_p sat_A_q by blast
    show "sat ctxt \<omega> mhB mpB (syntactic_mult (Rep_preal (p + q)) B)"
      using IH(2) B_sup mh_split_B mp_split_B sat_B_p sat_B_q by blast
  qed
next
  case (Wand A1 A2)
  then show ?case
    by (metis SatWand_case syntactic_mult.simps(10))
next
  case (ForAll x1a A)
  then show ?case
    by (metis SatForAll_case syntactic_mult.simps(6))
next
  case (Exists x1a A)
  then show ?case
    by (metis SatExists_case syntactic_mult.simps(7))
qed *)


\<comment> \<open>Fractionability of fractional resources.\<close>

lemma fractionability_SatAcc:
    fixes p :: preal
    assumes "p > 0"
      and "supported_pred_expr e_r"
      and "supported_pred_expr e_p"
      and "sat ctxt \<omega> mh zero_mask (Atomic (Acc e_r f (PureExp e_p)))"
    shows "sat ctxt \<omega> (field_mask_multiply p mh) zero_mask (syntactic_mult (Rep_preal p) (Atomic (Acc e_r f (PureExp e_p))))"
proof -
  from assms(4) obtain v_r v_p a where
    v_r_eval: "ctxt, None \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef v_r)" and
    v_p_eval: "ctxt, None \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
    a_eval: "a = the_address v_r" and
    v_p_pos: "v_p \<ge> 0" and
    mh_sing: "if v_r = Null then v_p = 0 \<and> mh = zero_mask else mh = singleton_mh (a,f) (Abs_preal v_p)"
    using SatAcc_case by meson
  show ?thesis
    apply (simp only: syntactic_mult.simps real_mult_permexpr.simps)
    apply (rule SatAcc)
         prefer 3
         apply (simp only: a_eval)
        prefer 5
    subgoal by auto
  proof -
    from v_r_eval show "ctxt, None \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef v_r)"
      using eval_frac_mask_does_not_matter(1)
      by blast
  next
    show "ctxt, None \<turnstile> \<langle>Binop (real_to_expr (Rep_preal p)) Mult e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm (Rep_preal p * v_p))"
      apply (rule RedBinop)
         prefer 3
      subgoal by auto
    proof -
      show "ctxt, None \<turnstile> \<langle>real_to_expr (Rep_preal p); \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm (Rep_preal p))"
        by (metis RedLit real_to_expr.elims val_of_lit.simps(3))
    next
      from v_p_eval show "ctxt, None \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)"
        by blast
    next
      show "eval_binop (Option.is_none None) (VPerm (Rep_preal p)) Mult (VPerm v_p) = BinopNormal (VPerm (Rep_preal p * v_p))"
        by force
    qed
  next
    show "0 \<le> Rep_preal p * v_p"
      by (simp add: prat_non_negative v_p_pos)
  next
    show "if v_r = Null then Rep_preal p * v_p = 0 \<and> field_mask_multiply p mh = zero_mask else field_mask_multiply p mh = singleton_mh (the_address v_r, f) (Abs_preal (Rep_preal p * v_p))"
      apply simp
      apply (rule conjI)
      using mh_sing zero_mh_multiply
       apply force
      by (metis Rep_preal_inverse a_eval eq_onp_same_args mh_sing prat_non_negative singleton_mh_multiply times_preal.abs_eq v_p_pos)

  qed
qed

lemma fractionability_SatAcc_Wildcard:
  fixes p :: preal
  assumes "p > 0"
      and "supported_pred_expr e_r"
      and "sat ctxt \<omega> mh zero_mask (Atomic (Acc e_r f Wildcard))"
    shows "sat ctxt \<omega> (field_mask_multiply p mp) zero_mask (syntactic_mult (Rep_preal p) (Atomic (Acc e_r f Wildcard)))"
proof -
  from assms(3) obtain v_r a where
    v_r_eval: "ctxt, None \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef v_r)" and
    a_eval: "a = the_address v_r" and
    v_r_non_null: "v_r \<noteq> Null" and
    mh_sing: "is_singleton_mh (a,f) mh"
    using SatAccWildcard_case by (metis is_singleton_mh.elims(3))
  from assms(1) have "Rep_preal p \<noteq> 0" and "Rep_preal p > 0"
     apply (simp add: less_preal.rep_eq zero_preal.rep_eq)
    using assms(1) less_preal.rep_eq zero_preal.rep_eq by force
  show ?thesis
    apply (simp del: mult_nm_total_full.simps field_mask_multiply.simps add: \<open>Rep_preal p \<noteq> 0\<close> \<open>Rep_preal p > 0\<close>)
    apply (rule SatAccWildcard)
        prefer 2
        apply (simp only: a_eval)
       prefer 4
    subgoal by auto
  proof -
    show "ctxt, None \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef v_r)"
      using v_r_eval by blast
  next
    show "v_r \<noteq> Null" using v_r_non_null by auto
  next
    show "is_singleton_mh (the_address v_r, f) (field_mask_multiply p mp)"
      apply simp
      using mh_sing
      sorry
  qed
qed

lemma fractionability_SatAccPred:
  fixes p :: preal
  assumes "p > 0"
      and "list_all supported_pred_expr e_args"
      and "supported_pred_expr e_p"
      and "sat ctxt \<omega> zero_mask mp (Atomic (AccPredicate pred_id e_args (PureExp e_p)))"
    shows "sat ctxt \<omega> zero_mask (predicate_mask_multiply p mp) (syntactic_mult (Rep_preal p) (Atomic (AccPredicate pred_id e_args (PureExp e_p))))"
proof -
  from assms(4) obtain v_args v_p where
    v_args_eval: "red_pure_exps_total ctxt None e_args \<omega> (Some v_args)" and
    v_p_eval: "ctxt, None \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
    v_p_pos: "v_p \<ge> 0" and
    mp_sing: "mp = singleton_mp (pred_id,v_args) (Abs_preal v_p)"
    using SatAccPred_case by meson
  show ?thesis
    apply (simp only: syntactic_mult.simps real_mult_permexpr.simps)
    apply (rule SatAccPred)
    using v_args_eval
        prefer 4
    subgoal by auto
  proof -
    from v_args_eval show "red_pure_exps_total ctxt None e_args \<omega> (Some v_args)"
      using assms(1,2) by fastforce
  next
    show "ctxt, None \<turnstile> \<langle>Binop (real_to_expr (Rep_preal p)) Mult e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm (Rep_preal p * v_p))"
      apply (rule RedBinop)
         prefer 3
      subgoal by auto
    proof -
      show "ctxt, None \<turnstile> \<langle>real_to_expr (Rep_preal p); \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm (Rep_preal p))"
        by (metis RedLit real_to_expr.elims val_of_lit.simps(3))
    next
      from v_p_eval show "ctxt, None \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)"
        using assms(1) assms(3) by fastforce
    next
      show "eval_binop (Option.is_none None) (VPerm (Rep_preal p)) Mult (VPerm v_p) = BinopNormal (VPerm (Rep_preal p * v_p))"
        by force
    qed
  next
    show "0 \<le> Rep_preal p * v_p"
      by (simp add: prat_non_negative v_p_pos)
  next
    show "predicate_mask_multiply p mp = singleton_mp (pred_id, v_args) (Abs_preal (Rep_preal p * v_p))"
      apply simp
      apply standard
      by (metis Rep_preal_inverse eq_onp_same_args mp_sing prat_non_negative singleton_mp_multiply times_preal.abs_eq v_p_pos)
  qed
qed

lemma fractionability_SatAccPred_Wildcard:
  fixes p :: preal
  assumes "p > 0"
      and "list_all supported_pred_expr e_args"
      and "sat ctxt \<omega> zero_mask mp (Atomic (AccPredicate pred_id e_args Wildcard))"
    shows "sat ctxt \<omega> zero_mask (predicate_mask_multiply p mp) (syntactic_mult (Rep_preal p) (Atomic (AccPredicate pred_id e_args Wildcard)))"
proof -
  from assms(3) obtain v_args where
    v_args_eval: "red_pure_exps_total ctxt None e_args \<omega> (Some v_args)" and
    mp_sing: "is_singleton_mp (pred_id,v_args) mp"
    using SatAccPredWildcard_case
    by (metis is_singleton_mp.elims(3))
  from assms(1) have "Rep_preal p \<noteq> 0" and "Rep_preal p > 0"
     apply (simp add: less_preal.rep_eq zero_preal.rep_eq)
    using assms(1) less_preal.rep_eq zero_preal.rep_eq by force
  show ?thesis
    apply (simp del: mult_nm_total_full.simps field_mask_multiply.simps add: \<open>Rep_preal p \<noteq> 0\<close> \<open>Rep_preal p > 0\<close>)
    apply (rule SatAccPredWildcard)
      prefer 2
    subgoal by auto
  proof -
    from v_args_eval show "red_pure_exps_total ctxt None e_args \<omega> (Some v_args)"
      using assms(1) assms(2) by fastforce
  next
    show "is_singleton_mp (pred_id, v_args) (PosReal.pmult p \<circ> mp)"
      apply simp
      using mp_sing
      by (metis \<open>Rep_preal p \<noteq> 0\<close> is_singleton_mp.simps less_preal.rep_eq mult_eq_0_iff pperm_pnone_pgt singleton_mp_multiply times_preal.rep_eq zero_preal.rep_eq)
  qed
qed

lemma fractionability:
    fixes p :: preal
  assumes "p > 0"
      and "supported_pred_body A"
      and "sat ctxt \<omega> mh mp A"
    shows "sat ctxt \<omega> (field_mask_multiply p mh) (predicate_mask_multiply p mp) (syntactic_mult (Rep_preal p) A)"
  using assms(2) assms(3)
proof (induct A arbitrary: mh mp)
  case IH: (Atomic x)
  show ?case
  proof (cases x)
    case (Pure e)
    hence e_eval: "ctxt, None \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)" and
          mh_zero: "mh = zero_mask" and
          mp_zero: "mp = zero_mask"
      using IH.prems(2) SatAtomic_case by blast+
    show ?thesis
      apply (simp del: mult_nm_total_full.simps field_mask_multiply.simps add: Pure)
      apply (rule SatPure)
    proof -
      from e_eval show "ctxt, None \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
        by blast
    next
      from mh_zero show "field_mask_multiply p mh = zero_mask"
        using zero_mh_multiply by auto
    next
      from mp_zero show "(\<lambda>a. p * (mp a)) = zero_mask"
        unfolding zero_mask_def
        by simp
    qed
  next
    case (Acc e_r f perm)
    then have "mp = zero_mask"
      using IH sat_Acc_mp_zero by fastforce
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      then show ?thesis using fractionability_SatAcc
        by (metis Acc IH.prems(1) IH.prems(2) \<open>mp = zero_mask\<close> assert_pred.elims(2) assert_pred_rec.simps(1) assms(1) atomic_assert_pred.elims(2) atomic_assert_pred_rec.simps(3) zero_mp_multiply)
    next
      case Wildcard
      then show ?thesis using fractionability_SatAcc_Wildcard
        by (metis Acc IH.prems(1) IH.prems(2) \<open>mp = zero_mask\<close> assert_pred.elims(2) assert_pred_rec.simps(1) assms(1) atomic_assert_pred.elims(2) atomic_assert_pred_rec.simps(2) zero_mp_multiply)
    qed
  next
    case (AccPredicate pred_id e_args perm)
    then have "mh = zero_mask"
      using IH sat_AccPred_mh_zero by blast
    have "list_all no_perm_pure_exp e_args" and "list_all no_old_pure_exp e_args"
      using AccPredicate IH.prems(1) IH.prems(2) SatAtomic_case assert_pred.elims(2) by fastforce+
    hence "list_all supported_pred_expr e_args"
      using Ball_set by blast
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      then show ?thesis using fractionability_SatAccPred
        by (metis (no_types, lifting) AccPredicate IH.prems(1) IH.prems(2) \<open>list_all supported_pred_expr e_args\<close> \<open>mh = zero_mask\<close> assert_pred.elims(2) assert_pred_rec.simps(1) assms(1) atomic_assert_pred.elims(2) atomic_assert_pred_rec.simps(5) zero_mh_multiply)
    next
      case Wildcard
      then show ?thesis using fractionability_SatAccPred_Wildcard
        by (metis (no_types, lifting) AccPredicate IH.prems(2) \<open>list_all supported_pred_expr e_args\<close> \<open>mh = zero_mask\<close> assms(1) zero_mh_multiply)
    qed
  qed
next
  case IH: (Imp e A)
  have e_sup: "supported_pred_expr e" and A_sup: "supported_pred_body A"
    using IH.prems(1) by force+
  from IH consider (True) "ctxt, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)" |
               (False) "ctxt, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    using sat_Imp_True_or_False by fastforce
  then show ?case
  proof (cases)
    case True
    show ?thesis
      apply (simp only: syntactic_mult.simps)
      apply (rule SatImpTrue)
      using IH e_sup A_sup True
       apply metis
      by (metis A_sup IH.hyps IH.prems(2) SatImp_case True eval_is_deterministic(1) extended_val.inject val.inject(2))
  next
    case False
    show ?thesis
      apply (simp only: syntactic_mult.simps)
      apply (rule SatImpFalse)
      using IH e_sup A_sup False
        apply metis
      using False IH.prems(2) sat_Imp_False_only_zero zero_mh_multiply zero_mp_multiply
      by blast+
  qed
next
  case IH: (CondAssert e A B)
  have e_sup: "supported_pred_expr e" and A_sup: "supported_pred_body A" and B_sup: "supported_pred_body B"
    using IH.prems(1) by force+
  from IH consider (True) "ctxt, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)" |
               (False) "ctxt, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    using sat_Cond_True_or_False by fastforce
  then show ?case
  proof (cases)
    case True
    show ?thesis
      apply (simp only: syntactic_mult.simps)
      apply (rule SatCondTrue)
      using IH e_sup A_sup True
       apply metis
      by (metis A_sup IH.hyps(1) IH.prems(2) SatCond_case True eval_is_deterministic(1) extended_val.inject val.inject(2))
  next
    case False
    show ?thesis
      apply (simp only: syntactic_mult.simps)
      apply (rule SatCondFalse)
      using IH e_sup B_sup False
       apply metis
      by (metis B_sup False IH.hyps(2) IH.prems(2) SatCond_case eval_is_deterministic(1) extended_val.inject val.inject(2))
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
  case IH: (Star A B)
  then obtain mh\<^sub>1 mh\<^sub>2 mp\<^sub>1 mp\<^sub>2 where
    mh_split: "mh_split mh mh\<^sub>1 mh\<^sub>2" and
    mp_split: "mp_split mp mp\<^sub>1 mp\<^sub>2" and
    sat_A: "sat ctxt \<omega> mh\<^sub>1 mp\<^sub>1 A" and
    sat_B: "sat ctxt \<omega> mh\<^sub>2 mp\<^sub>2 B"
    by (auto elim: SatStar_case)
  show ?case
    apply (simp only: syntactic_mult.simps)
    apply (rule SatStar)
       apply (rule mh_split_multiply, rule mh_split)
      apply (rule mp_split_multiply, rule mp_split)
    using sat_A sat_B IH
    by (meson assert_pred.elims(1) assert_pred_rec.simps(4))+
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
qed


lemma fractionabilityI:
  fixes p :: preal
  assumes "p > 0"
      and "supported_pred_body A"
      and "sat ctxt \<omega> mh mp A"
      and "mh' = field_mask_multiply p mh"
      and "mp' = predicate_mask_multiply p mp"
    shows "sat ctxt \<omega> mh' mp' (syntactic_mult (Rep_preal p) A)"
  using assms fractionability by blast

lemma fractionability_inv:
    fixes p :: preal
  assumes "p > 0"
      and "sat ctxt \<omega> mh mp (syntactic_mult (Rep_preal p) A)"
    shows "sat ctxt \<omega> (field_mask_multiply (1/p) mh) (predicate_mask_multiply (1/p) mp) A"
  sorry

(* lemma fractionability_1:
  assumes "sat ctxt \<omega> mh mp (syntactic_mult 1 A)"
    shows "sat ctxt \<omega> mh mp A"
  sorry *)

lemma fractionability_pq:
    fixes p q :: preal
  assumes "p > 0" and "q > 0"
      and "supported_pred_body A"
      and "sat ctxt \<omega> mh mp (syntactic_mult (Rep_preal p) A)"
    shows "sat ctxt \<omega> (field_mask_multiply q mh) (predicate_mask_multiply q mp) (syntactic_mult (Rep_preal (q * p)) A)"
proof -
  define mh\<^sub>0 where mh\<^sub>0: "mh\<^sub>0 = field_mask_multiply (1/p) mh"
  define mp\<^sub>0 where mp\<^sub>0: "mp\<^sub>0 = predicate_mask_multiply (1/p) mp"
  show ?thesis
    apply (rule fractionabilityI)
    using assms(1) assms(2) less_preal.rep_eq times_preal.rep_eq zero_preal.rep_eq apply force
       apply (simp only: assms(3))
  proof -
    show "sat ctxt \<omega> mh\<^sub>0 mp\<^sub>0 A"
      using assms(1) assms(4) fractionability_inv mh\<^sub>0 mp\<^sub>0
      by blast
  next
    show "field_mask_multiply q mh = field_mask_multiply (q*p) mh\<^sub>0"
      apply (simp add: mh\<^sub>0)
      apply standard
      by (metis (no_types, lifting) PosReal.field_divide_inverse PosReal.field_inverse assms(1) comp_apply lambda_one linorder_neq_iff mult.assoc mult.left_commute)
  next
    show "predicate_mask_multiply q mp = predicate_mask_multiply (q*p) mp\<^sub>0"
      apply (simp add: mp\<^sub>0)
      apply standard
      by (metis (no_types, lifting) PosReal.field_divide_inverse PosReal.field_inverse assms(1) comp_apply lambda_one linorder_neq_iff mult.assoc mult.left_commute)
  qed
qed


\<comment> \<open>A fraction of a consistent total state is external consistent.\<close>

lemma fraction_consistent_external:
  fixes frac :: preal
  assumes "0 < frac"
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
    apply (rule fractionability_pq)
    using IH.hyps(2) apply blast
      apply (simp add: assms)
     defer 1
    using IH.IH(2) apply fastforce
    sorry \<comment> \<open>supported_pred_body\<close>
next
  case IH: (SatAll \<phi>)
  show ?case
  proof (standard, simp del: get_nm_loc_total.simps)
    have "\<And>loc. ((get_mp_nm (get_nm_total \<phi>) loc) = 0) = (get_nm_loc_nm (get_nm_total \<phi>) loc = None)"
      by (metis IH.hyps TotalStateUtil.get_nm_loc_total.elims eq_fst_iff get_fnm_nm.elims get_fnm_total.simps get_mp_total.simps get_nm_loc_nm.simps)
    hence "\<And>loc. ((get_mp_nm (get_nm_total \<phi>) loc) = 0) = (get_nm_loc_nm (frac *\<^sub>s get_nm_total \<phi>) loc = None)"
      using nm_multiply_none assms by blast
    thus "\<And>pred_id vs. (frac * (get_mp_nm (get_nm_total \<phi>) (pred_id,vs)) = 0) = (get_nm_loc_nm (frac *\<^sub>s get_nm_total \<phi>) (pred_id,vs) = None)"
      by (smt (verit) Rep_preal_inverse assms less_preal.rep_eq mult_eq_0_iff times_preal.rep_eq zero_preal.rep_eq)
  next
    fix pred_id vs q nm'
    assume perm: "get_mp_total (mult_nm_total \<phi> frac) (pred_id, vs) = q"
       and nm': "Some nm' = TotalStateUtil.get_nm_loc_total (mult_nm_total \<phi> frac) (pred_id, vs)"
    hence "get_mp_total \<phi> (pred_id,vs) = q / frac" using nm_multiply_back
      by (metis assms get_mp_total.simps mult_nm_total.elims total_state.simps(2) total_state.surjective total_state.update_convs(2))
    moreover from nm' have nm'_frac: "Some nm' = get_nm_loc_nm (frac *\<^sub>s get_nm_total \<phi>) (pred_id,vs)"
      using get_nm_loc_total_multiply by auto
    have "Some ((1 / frac) *\<^sub>s nm') = get_nm_loc_total \<phi> (pred_id,vs)"
    proof simp
      from nm'_frac obtain nm where "Some nm = get_nm_loc_total \<phi> (pred_id,vs)"
        by (metis TotalStateUtil.get_nm_loc_total.simps assms get_fnm_nm.elims get_fnm_total.simps get_nm_loc_nm.simps nm_multiply_none not_None_eq)
      moreover hence "get_nm_loc_nm (frac *\<^sub>s get_nm_total \<phi>) (pred_id,vs) = Some (frac *\<^sub>s nm)"
        by (metis TotalStateUtil.get_nm_loc_total.elims get_fnm_nm.cases get_fnm_nm.simps get_fnm_total.simps get_nm_loc_nm.simps get_nm_loc_nm_multiply option.simps(9))
      ultimately show "Some ((1 / frac) *\<^sub>s nm') = get_fnm_nm (get_nm_total \<phi>) (pred_id, vs)"
        using assms nm'_frac
        by (simp add: PosReal.field_divide_inverse PosReal.field_inverse preal_semimodule_class.scale_one preal_semimodule_class.scale_scale)
    qed
    moreover note IH(3)
    ultimately have "consistent_external_wrt_ploc ctxt
                       (\<phi>\<lparr> get_nm_total := frac *\<^sub>s (get_nm_total (\<phi>\<lparr> get_nm_total := ((1 / frac) *\<^sub>s nm') \<rparr>)) \<rparr>)
                       (pred_id,vs) q"
      using perm by force
    moreover have "\<phi>\<lparr> get_nm_total := frac *\<^sub>s (get_nm_total (\<phi>\<lparr> get_nm_total := ((1 / frac) *\<^sub>s nm') \<rparr>)) \<rparr>
                 = \<phi>\<lparr> get_nm_total := nm' \<rparr>"
      by (metis \<open>Some ((pos_perm_class.pwrite / frac) *\<^sub>s nm') = get_nm_loc_total \<phi> (pred_id, vs)\<close> get_fnm_nm.simps get_fnm_total.simps get_mh_nm.cases get_nm_loc_nm.simps get_nm_loc_nm_multiply get_nm_loc_total.elims nm'_frac option.map(2) option.sel total_state_update_nm_read)
      ultimately show "consistent_external_wrt_ploc ctxt
                       (mult_nm_total \<phi> frac\<lparr>get_nm_total := nm'\<rparr>)
                       (pred_id,vs) q"
      by fastforce
  qed
qed


subsection \<open>Combinability of External Consistent States\<close>

lemma sum_consistent_external:
  assumes "consistent_external ctxt (\<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>1 \<rparr>)"
      and "consistent_external ctxt (\<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>2 \<rparr>)"
    shows "consistent_external ctxt (\<lparr> get_hh_total = hh, get_nm_total = nested_mask_merge nm\<^sub>1 nm\<^sub>2 \<rparr>)"
  sorry


end
