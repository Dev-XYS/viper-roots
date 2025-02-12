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

lemma syntactic_mult_supported:
  assumes "supported_pred_body A"
      and "p \<ge> 0"
    shows "supported_pred_body (syntactic_mult p A)"
  using assms
  apply (induction A)
          apply (rename_tac atm)
          apply (case_tac atm)
            defer
            apply (rename_tac e_r f perm)
            apply (case_tac perm)
             defer
             defer
             apply (rename_tac pid e_args perm)
             apply (case_tac perm)
              defer
              defer
  by simp_all

(*
lemma nm_subtract_mh:
  shows "get_mh_nm (nested_mask_subtract nm\<^sub>1 nm\<^sub>2) = get_mh_nm nm\<^sub>1 - get_mh_nm nm\<^sub>2"
  by (metis get_fnm_nm.cases get_mh_nm.simps nested_mask_subtract.simps)

lemma nm_subtract_mp:
  shows "get_mp_nm (nested_mask_subtract nm\<^sub>1 nm\<^sub>2) = get_mp_nm nm\<^sub>1 - get_mp_nm nm\<^sub>2"
  by (metis get_fnm_nm.cases get_mp_nm.simps nested_mask_subtract.simps)
*)


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
  have "get_mp_total_full (mult_nm_total_full \<omega>_def frac) (pred_id, vs) = 0"
    using IH(3)
    apply simp
    by (metis comp_apply get_mp_nm.simps mult_zero_right nm_multiply_mp_value preal_to_real(10) times_preal.rep_eq zero_preal.rep_eq)
  show ?case
    apply (simp del: mult_nm_total_full.simps)
    by (metis (mono_tags, lifting) IH.IH(2) IH.prems RedUnfoldingDefNoPred \<open>get_mp_total_full (mult_nm_total_full \<omega>_def frac) (pred_id, vs) = pos_perm_class.pnone\<close> option.simps(9) sub_pure_exp_total.simps(9) supported_sub_expr_supported)
next
  case IH: (RedUnfoldingDef \<omega>_def es \<omega> vs perm p nm' \<omega>'_def ubody v)
  hence es_sup: "list_all supported_pred_expr es" and
        body_sup: "supported_pred_expr ubody"
     apply (metis sub_pure_exp_total.simps(9) supported_sub_expr_supported)
    using IH.prems
    by auto
  have nm_unfold:
    "shift_up p vs
     (get_mp_total_full (mult_nm_total_full \<omega>_def frac) (p, vs) / Abs_preal 2)
     (get_nm_total_full (mult_nm_total_full \<omega>_def frac)) (frac *\<^sub>s nm')"
    using shift_up_frac[OF assms(1) IH(7), simplified IH(5)]
    apply (simp add: mul_mask_def)
    by (metis PosReal.field_divide_inverse comp_apply get_mp_nm.simps mult.assoc nm_multiply_mp_value)
  show ?case
    apply (simp del: mult_nm_total_full.simps)
    apply (rule RedUnfoldingDef)
    using IH es_sup
         apply simp
        apply blast
       apply simp
       apply (metis IH.hyps(1) IH.hyps(2) PosReal.field_divide_inverse Rep_preal_inverse assms comp_apply get_mp_nm.simps get_mp_total.simps get_mp_total_full.elims mult_zero_left nm_multiply_back preal_not_0_gt_0 times_preal.rep_eq zero_preal.rep_eq)
    using nm_unfold
      apply blast
     apply simp
    using IH(4)[OF body_sup, simplified IH(8), simplified] nm_unfold
    by auto
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


subsection \<open>Fractionability of fractional resources.\<close>

lemma fractionability_SatAcc:
    fixes p :: preal
  assumes "supported_pred_expr e_r"
      and "supported_pred_expr e_p"
      and "sat ctxt \<omega> mh zero_mask (Atomic (Acc e_r f (PureExp e_p)))"
    shows "sat ctxt \<omega> (mul_mask p mh) zero_mask (syntactic_mult (Rep_preal p) (Atomic (Acc e_r f (PureExp e_p))))"
proof -
  from assms(3) obtain v_r v_p a where
    v_r_eval: "ctxt, None \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef v_r)" and
    v_p_eval: "ctxt, None \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
    a_eval: "a = the_address v_r" and
    v_p_pos: "v_p \<ge> 0" and
    mh_sing: "if v_r = Null then v_p = 0 \<and> mh = zero_mask else mh = singleton_mh (a,f) (Abs_preal v_p)"
    using SatAcc_case
    by meson
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
    show "if v_r = Null then Rep_preal p * v_p = 0 \<and> mul_mask p mh = zero_mask else mul_mask p mh = singleton_mh (the_address v_r, f) (Abs_preal (Rep_preal p * v_p))"
      apply (simp add: mul_mask_def)
      apply (rule conjI)
      using mh_sing zero_mh_multiply
       apply (metis mul_mask_def)
      by (metis Abs_preal_inverse Rep_preal_inverse a_eval mem_Collect_eq mh_sing singleton_mh_multiply times_preal.rep_eq v_p_pos)
  qed
qed

lemma fractionability_SatAcc_Wildcard:
    fixes p :: preal
  assumes "supported_pred_expr e_r"
      and "sat ctxt \<omega> mh zero_mask (Atomic (Acc e_r f Wildcard))"
    shows "sat ctxt \<omega> (mul_mask p mh) zero_mask (syntactic_mult (Rep_preal p) (Atomic (Acc e_r f Wildcard)))"
proof -
  from assms(2) obtain v_r a where
    v_r_eval: "ctxt, None \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef v_r)" and
    a_eval: "a = the_address v_r" and
    v_r_non_null: "v_r \<noteq> Null" and
    mh_sing: "is_singleton_mh (a,f) mh"
    using SatAccWildcard_case
    by (metis is_singleton_mh.elims(3))
  show ?thesis
  proof (cases "p = 0")
    case True
    then show ?thesis
      apply (simp add: zero_preal.rep_eq mul_mask_def)
      apply (rule SatAcc)
           apply (rule v_r_eval)
      using RedLit[where ?l="NoPerm"]
          apply auto[1]
         apply (rule a_eval)
        apply simp
      using v_r_non_null zero_preal_def
       apply (metis (mono_tags, lifting) is_singleton_mh.simps map_fun_apply mh_sing mult_eq_0_iff singleton_mh_multiply times_preal_def zero_preal.rep_eq)
      by simp
  next
    case False
    hence "Rep_preal p \<noteq> 0" and "Rep_preal p > 0"
      using preal_to_real(10) zero_preal.rep_eq
       apply force
      using False PosReal.ppos.rep_eq gr_0_is_ppos pperm_pnone_pgt
      by blast
    show ?thesis
      apply (simp del: mult_nm_total_full.simps add: \<open>Rep_preal p \<noteq> 0\<close> \<open>Rep_preal p > 0\<close>)
      apply (rule SatAccWildcard)
          prefer 2
          apply (simp only: a_eval)
         prefer 4
        subgoal
          by auto
    proof -
      show "ctxt, None \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef v_r)"
        using v_r_eval
        by blast
    next
      show "v_r \<noteq> Null"
        using v_r_non_null
        by auto
    next
      show "is_singleton_mh (the_address v_r, f) (mul_mask p mh)"
        apply (simp add: mul_mask_def)
        using mh_sing
        by (metis \<open>Rep_preal p \<noteq> 0\<close> a_eval is_singleton_mh.simps less_preal.rep_eq mult_eq_0_iff pperm_pnone_pgt singleton_mh_multiply times_preal.rep_eq zero_preal.rep_eq)
    qed
  qed
qed

lemma fractionability_SatAccPred:
    fixes p :: preal
  assumes "list_all supported_pred_expr e_args"
      and "supported_pred_expr e_p"
      and "sat ctxt \<omega> zero_mask mp (Atomic (AccPredicate pred_id e_args (PureExp e_p)))"
    shows "sat ctxt \<omega> zero_mask (mul_mask p mp) (syntactic_mult (Rep_preal p) (Atomic (AccPredicate pred_id e_args (PureExp e_p))))"
proof -
  from assms(3) obtain v_args v_p where
    v_args_eval: "red_pure_exps_total ctxt None e_args \<omega> (Some v_args)" and
    v_p_eval: "ctxt, None \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
    v_p_pos: "v_p \<ge> 0" and
    mp_sing: "mp = singleton_mp (pred_id,v_args) (Abs_preal v_p)"
    using SatAccPred_case
    by meson
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
    show "mul_mask p mp = singleton_mp (pred_id, v_args) (Abs_preal (Rep_preal p * v_p))"
      apply (simp add: mul_mask_def)
      apply standard
      by (metis Rep_preal_inverse eq_onp_same_args mp_sing prat_non_negative singleton_mp_multiply times_preal.abs_eq v_p_pos)
  qed
qed

lemma fractionability_SatAccPred_Wildcard:
    fixes p :: preal
  assumes "list_all supported_pred_expr e_args"
      and "sat ctxt \<omega> zero_mask mp (Atomic (AccPredicate pred_id e_args Wildcard))"
    shows "sat ctxt \<omega> zero_mask (mul_mask p mp) (syntactic_mult (Rep_preal p) (Atomic (AccPredicate pred_id e_args Wildcard)))"
proof -
  from assms(2) obtain v_args where
    v_args_eval: "red_pure_exps_total ctxt None e_args \<omega> (Some v_args)" and
    mp_sing: "is_singleton_mp (pred_id,v_args) mp"
    using SatAccPredWildcard_case
    by (metis is_singleton_mp.elims(3))
  show ?thesis
  proof (cases "p = 0")
    case True
    then show ?thesis
      apply (simp add: zero_preal.rep_eq mul_mask_def)
      apply (rule SatAccPred)
          apply (rule v_args_eval)
      using RedLit[where ?l="NoPerm"]
         apply auto[1]
        apply simp
       apply simp
      apply standard
      by (metis Rep_preal_inverse comp_apply mult_eq_0_iff singleton_mp.elims times_preal.rep_eq zero_preal.rep_eq)
  next
    case False
    hence "Rep_preal p \<noteq> 0" and "Rep_preal p > 0"
      using preal_to_real(10) zero_preal.rep_eq
       apply force
      using False PosReal.ppos.rep_eq gr_0_is_ppos pperm_pnone_pgt
      by blast
    show ?thesis
      apply (simp del: mult_nm_total_full.simps add: \<open>Rep_preal p \<noteq> 0\<close> \<open>Rep_preal p > 0\<close>)
      apply (rule SatAccPredWildcard)
        prefer 2
      subgoal by auto
    proof -
      from v_args_eval show "red_pure_exps_total ctxt None e_args \<omega> (Some v_args)"
        using assms(1) assms(2) by fastforce
    next
      show "is_singleton_mp (pred_id, v_args) (mul_mask p mp)"
        apply (simp add: mul_mask_def)
        using mp_sing
        by (metis \<open>Rep_preal p \<noteq> 0\<close> is_singleton_mp.simps less_preal.rep_eq mult_eq_0_iff pperm_pnone_pgt singleton_mp_multiply times_preal.rep_eq zero_preal.rep_eq)
    qed
  qed
qed

lemma fractionability:
    fixes p :: preal
  assumes "supported_pred_body A"
      and "sat ctxt \<omega> mh mp A"
    shows "sat ctxt \<omega> (mul_mask p mh) (mul_mask p mp) (syntactic_mult (Rep_preal p) A)"
  using assms(1,2)
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
      apply (simp del: mult_nm_total_full.simps add: Pure)
      apply (rule SatPure)
    proof -
      from e_eval show "ctxt, None \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
        by blast
    next
      from mh_zero show "mul_mask p mh = zero_mask"
        using zero_mh_multiply by auto
    next
      from mp_zero show "mul_mask p mp = zero_mask"
        unfolding zero_mask_def
        using mp_zero zero_mp_multiply
        by force
    qed
  next
    case (Acc e_r f perm)
    then have "mp = zero_mask"
      using IH sat_Acc_mp_zero by fastforce
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      then show ?thesis using fractionability_SatAcc
        by (metis Acc IH.prems(1) IH.prems(2) \<open>mp = zero_mask\<close> assert_pred.elims(2) assert_pred_rec.simps(1) atomic_assert_pred.elims(2) atomic_assert_pred_rec.simps(3) zero_mp_multiply)
    next
      case Wildcard
      then show ?thesis using fractionability_SatAcc_Wildcard
        by (metis Acc IH.prems(1) IH.prems(2) \<open>mp = zero_mask\<close> assert_pred.elims(2) assert_pred_rec.simps(1) atomic_assert_pred.elims(2) atomic_assert_pred_rec.simps(2) zero_mp_multiply)
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
        by (metis (no_types, lifting) AccPredicate IH.prems(1) IH.prems(2) \<open>list_all supported_pred_expr e_args\<close> \<open>mh = zero_mask\<close> assert_pred.elims(2) assert_pred_rec.simps(1) atomic_assert_pred.elims(2) atomic_assert_pred_rec.simps(5) zero_mh_multiply)
    next
      case Wildcard
      then show ?thesis using fractionability_SatAccPred_Wildcard
        by (metis (no_types, lifting) AccPredicate IH.prems(2) \<open>list_all supported_pred_expr e_args\<close> \<open>mh = zero_mask\<close> zero_mh_multiply)
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
  assumes "supported_pred_body A"
      and "sat ctxt \<omega> mh mp A"
      and "mh' = mul_mask p mh"
      and "mp' = mul_mask p mp"
    shows "sat ctxt \<omega> mh' mp' (syntactic_mult (Rep_preal p) A)"
  using assms fractionability
  by blast

\<comment> \<open>This lemma does not hold. It could be the case that some permission in A evaluates to an
    integer (so \<^const>\<open>sat\<close> does not hold), but the syntactic multiplication makes it a \<^const>\<open>VPerm\<close>.\<close>
lemma fractionability_inv:
    fixes p :: preal
  assumes "p > 0"
      and "sat ctxt \<omega> mh mp (syntactic_mult (Rep_preal p) A)"
    shows "sat ctxt \<omega> (mul_mask (1/p) mh) (mul_mask (1/p) mp) A"
  oops


lemma eval_mul_0_eq_0:
  assumes "ctxt, \<omega>_def \<turnstile> \<langle>Binop (ELit NoPerm) Mult e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
  shows "p = 0"
proof -
  obtain v1 v2 where
    "ctxt, \<omega>_def \<turnstile> \<langle>ELit NoPerm; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1" and
    v2: "ctxt, \<omega>_def \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2" and
    "eval_binop_lazy v1 Mult = None" and
    "eval_binop (Option.is_none \<omega>_def) v1 Mult v2 = BinopNormal (VPerm p)"
    using assms
    by (fastforce elim: RedBinop_case)
  hence *: "(\<exists>p2. v2 = VPerm p2) \<or> (\<exists>i2. v2 = VInt i2)"
    by (cases v1; cases v2; simp)
  have "ctxt, \<omega>_def \<turnstile> \<langle>Binop (ELit NoPerm) Mult e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm 0)"
    apply (rule RedBinop)
       apply (rule RedLit)
      apply (rule v2)
     apply simp
    using *
    by force
  thus ?thesis
    using assms(1) eval_is_deterministic(1) by blast
qed


lemma eval_0_eq_0:
  assumes "ctxt, \<omega>_def \<turnstile> \<langle>ELit NoPerm; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
  shows "p = 0"
  by (metis RedLit assms eval_is_deterministic(1) extended_val.inject val.inject(3) val_of_lit.simps(3))


lemma synmult_0_mh_0:
  assumes "sat ctxt \<omega> mh mp (syntactic_mult 0 A)"
  shows "mh = zero_mask"
  using assms
proof (induction A arbitrary: mh mp)
  case (Atomic atm)
  show ?case
  proof (cases atm)
    case (Pure _)
    then show ?thesis
      using Atomic SatAtomic_case
      by fastforce
  next
    case (Acc e_r f perm)
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      show ?thesis
        apply (rule SatAcc_case[OF Atomic[simplified Acc PureExp, simplified]])
        by (metis eval_mul_0_eq_0 singleton_mh.elims zero_mask_def zero_preal.abs_eq)
    next
      case Wildcard
      show ?thesis
        apply (rule SatAcc_case[OF Atomic[simplified Acc Wildcard, simplified]])
        by (metis eval_0_eq_0 singleton_mh.elims zero_mask_def zero_preal.abs_eq)
    qed
  next
    case (AccPredicate pid e_args perm)
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      show ?thesis
        apply (rule SatAccPred_case[OF Atomic[simplified AccPredicate PureExp, simplified]])
        by fastforce
    next
      case Wildcard
      show ?thesis
        apply (rule SatAccPred_case[OF Atomic[simplified AccPredicate Wildcard, simplified]])
        by fastforce
    qed
  qed
next
  case (Star A1 A2)
  then show ?case
    by (metis (no_types, lifting) SatStar_case mh_split.simps mh_split_zero syntactic_mult.simps(5))
qed (fastforce elim: sat.cases)+


lemma synmult_0_mp_0:
  assumes "sat ctxt \<omega> mh mp (syntactic_mult 0 A)"
  shows "mp = zero_mask"
  using assms
proof (induction A arbitrary: mh mp)
  case (Atomic atm)
  show ?case
  proof (cases atm)
    case (Pure _)
    then show ?thesis
      using Atomic SatAtomic_case
      by fastforce
  next
    case (Acc e_r f perm)
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      show ?thesis
        apply (rule SatAcc_case[OF Atomic[simplified Acc PureExp, simplified]])
        by fast
    next
      case Wildcard
      show ?thesis
        apply (rule SatAcc_case[OF Atomic[simplified Acc Wildcard, simplified]])
        by fast
    qed
  next
    case (AccPredicate pid e_args perm)
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      show ?thesis
        apply (rule SatAccPred_case[OF Atomic[simplified AccPredicate PureExp, simplified]])
        by (metis eval_mul_0_eq_0 singleton_mp.elims zero_mask_def zero_preal.abs_eq)
    next
      case Wildcard
      show ?thesis
        apply (rule SatAccPred_case[OF Atomic[simplified AccPredicate Wildcard, simplified]])
        by (metis eval_0_eq_0 singleton_mp.elims zero_mask_def zero_preal.abs_eq)
    qed
  qed
next
  case (Star A1 A2)
  then show ?case
    by (metis (no_types, lifting) SatStar_case mp_split.simps mp_split_zero syntactic_mult.simps(5))
qed (fastforce elim: sat.cases)+


lemma eval_mul_two_perms_1:
  assumes "ctxt, \<omega>_def \<turnstile> \<langle>Binop (real_to_expr q) Mult (Binop (real_to_expr p) Mult e); \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
  shows "ctxt, \<omega>_def \<turnstile> \<langle>Binop (real_to_expr (p * q)) Mult e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
proof -
  from assms obtain v1 v2 where
    v1: "ctxt, \<omega>_def \<turnstile> \<langle>real_to_expr q; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1" and
    v2: "ctxt, \<omega>_def \<turnstile> \<langle>Binop (real_to_expr p) Mult e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2" and
    "eval_binop_lazy v1 Mult = None" and
    v1_mult_v2: "eval_binop (Option.is_none \<omega>_def) v1 Mult v2 = BinopNormal v"
    by (auto elim: RedBinop_case)

  from v1[simplified] have "v1 = VPerm q"
    by (auto elim: RedLit_case)

  from v2[simplified] obtain v21 v22 where
    v21: "ctxt, \<omega>_def \<turnstile> \<langle>real_to_expr p; \<omega>\<rangle> [\<Down>]\<^sub>t Val v21" and
    v22: "ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v22" and
    "eval_binop_lazy v21 Mult = None" and
    v21_mult_v22: "eval_binop (Option.is_none \<omega>_def) v21 Mult v22 = BinopNormal v2"
    by (auto elim: RedBinop_case)

  from v21[simplified] have "v21 = VPerm p"
    by (auto elim: RedLit_case)

  show ?thesis
    apply simp
    apply (rule RedBinop)
       apply (rule RedLit)
      apply fact
     apply simp
    apply (cases v22)
        apply simp_all
    using v1_mult_v2[simplified \<open>v1 = _\<close>] v21_mult_v22[simplified \<open>v21 = _\<close>]
    by fastforce+
qed


lemma eval_mul_two_perms:
  assumes "ctxt, \<omega>_def \<turnstile> \<langle>Binop (real_to_expr q) Mult (real_to_expr p); \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
  shows "ctxt, \<omega>_def \<turnstile> \<langle>real_to_expr (p * q); \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
proof -
  from assms obtain v1 v2 where
    v1: "ctxt, \<omega>_def \<turnstile> \<langle>real_to_expr q; \<omega>\<rangle> [\<Down>]\<^sub>t Val v1" and
    v2: "ctxt, \<omega>_def \<turnstile> \<langle>real_to_expr p; \<omega>\<rangle> [\<Down>]\<^sub>t Val v2" and
    "eval_binop_lazy v1 Mult = None" and
    v1_mult_v2: "eval_binop (Option.is_none \<omega>_def) v1 Mult v2 = BinopNormal v"
    by (auto elim: RedBinop_case)

  hence "v1 = VPerm q" and "v2 = VPerm p"
    by (auto elim: RedLit_case)
  hence "v = VPerm (p * q)"
    using v1_mult_v2
    by force

  show ?thesis
    apply (simp add: \<open>v = _\<close>)
    by (metis RedLit val_of_lit.simps(3))
qed


lemma synmult_once_twice_Acc:
  assumes "p \<ge> 0" and "q \<ge> 0"
      and "sat ctxt \<omega> mh mp (syntactic_mult q (syntactic_mult p (Atomic (Acc e_r f (PureExp e_p)))))"
    shows "sat ctxt \<omega> mh mp (syntactic_mult (p * q) (Atomic (Acc e_r f (PureExp e_p))))"
proof -
  from assms(3)[simplified] obtain v_r v_p a where
    v_r: "ctxt, None \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef v_r)" and
    v_p: "ctxt, None \<turnstile> \<langle>Binop (ELit (LPerm q)) Mult (Binop (ELit (LPerm p)) Mult e_p); \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
    a: "a = the_address v_r" and
    v_p_nn: "v_p \<ge> 0" and
    mh: "if v_r = Null then v_p = 0 \<and> mh = zero_mask else mh = singleton_mh (a,f) (Abs_preal v_p)" and
    mp: "mp = zero_mask"
    by (auto elim: SatAcc_case)

  show ?thesis
    apply simp
    apply (rule SatAcc)
         defer
         apply (rule eval_mul_two_perms_1[of ctxt None q p e_p \<omega> "VPerm v_p", simplified, OF v_p])
    by fact+
qed


lemma synmult_once_twice_AccWildcard:
  assumes "p \<ge> 0" and "q \<ge> 0"
      and "sat ctxt \<omega> mh mp (syntactic_mult q (syntactic_mult p (Atomic (Acc e_r f Wildcard))))"
    shows "sat ctxt \<omega> mh mp (syntactic_mult (p * q) (Atomic (Acc e_r f Wildcard)))"
proof (cases "p = 0")
  case True
  from assms(3)[simplified True, simplified] obtain v_r v_p a where
    v_r: "ctxt, None \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef v_r)" and
    v_p: "ctxt, None \<turnstile> \<langle>Binop (ELit (LPerm q)) Mult (ELit NoPerm); \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
    a: "a = the_address v_r" and
    v_p_nn: "v_p \<ge> 0" and
    mh: "if v_r = Null then v_p = 0 \<and> mh = zero_mask else mh = singleton_mh (a,f) (Abs_preal v_p)" and
    mp: "mp = zero_mask"
    by (auto elim: SatAcc_case)

  have "v_p = 0"
    by (metis eval_0_eq_0 eval_mul_two_perms lambda_zero real_to_expr.simps v_p)

  show ?thesis
    apply (simp add: True)
    apply (rule SatAcc)
         defer
         apply (rule RedLit[where ?l="NoPerm", simplified])
        apply fact
       apply fast
    using \<open>v_p = 0\<close> mh
      apply force
    by fact+
next
  case False
  hence "p > 0"
    using assms(1)
    by auto

  show ?thesis
  proof (cases "q = 0")
    case True
    show ?thesis
      apply (simp add: False True)
      by (rule assms(3)[simplified True, simplified, simplified False \<open>p > 0\<close>, simplified])
  next
    case False
    hence "q > 0"
      using assms(2)
      by auto

    show ?thesis
      apply (simp add: \<open>p \<noteq> 0\<close> \<open>p > 0\<close> \<open>q \<noteq> 0\<close> \<open>q > 0\<close>)
      by (rule assms(3)[simplified, simplified \<open>p \<noteq> 0\<close> \<open>p > 0\<close>, simplified, simplified \<open>q \<noteq> 0\<close> \<open>q > 0\<close>, simplified])
  qed
qed


lemma synmult_once_twice_AccPred:
  assumes "p \<ge> 0" and "q \<ge> 0"
      and "sat ctxt \<omega> mh mp (syntactic_mult q (syntactic_mult p (Atomic (AccPredicate pid e_args (PureExp e_p)))))"
    shows "sat ctxt \<omega> mh mp (syntactic_mult (p * q) (Atomic (AccPredicate pid e_args (PureExp e_p))))"
proof -
  from assms(3)[simplified] obtain v_args v_p where
    v_args: "red_pure_exps_total ctxt None e_args \<omega> (Some v_args)" and
    v_p: "ctxt, None \<turnstile> \<langle>Binop (ELit (LPerm q)) Mult (Binop (ELit (LPerm p)) Mult e_p); \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
    v_p_nn: "v_p \<ge> 0" and
    mh: "mh = zero_mask" and
    mp: "mp = singleton_mp (pid,v_args) (Abs_preal v_p)"
    by (auto elim: SatAccPred_case)

  show ?thesis
    apply simp
    apply (rule SatAccPred)
        defer
        apply (rule eval_mul_two_perms_1[of ctxt None q p e_p \<omega> "VPerm v_p", simplified, OF v_p])
    by fact+
qed


lemma synmult_once_twice_AccPredWildcard:
  assumes "p \<ge> 0" and "q \<ge> 0"
      and "sat ctxt \<omega> mh mp (syntactic_mult q (syntactic_mult p (Atomic (AccPredicate pid e_args Wildcard))))"
    shows "sat ctxt \<omega> mh mp (syntactic_mult (p * q) (Atomic (AccPredicate pid e_args Wildcard)))"
proof (cases "p = 0")
  case True
  from assms(3)[simplified True, simplified] obtain v_args v_p where
    v_args: "red_pure_exps_total ctxt None e_args \<omega> (Some v_args)" and
    v_p: "ctxt, None \<turnstile> \<langle>Binop (ELit (LPerm q)) Mult (ELit NoPerm); \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
    v_p_nn: "v_p \<ge> 0" and
    mh: "mh = zero_mask" and
    mp: "mp = singleton_mp (pid,v_args) (Abs_preal v_p)"
    by (auto elim: SatAccPred_case)

  have "v_p = 0"
    by (metis eval_0_eq_0 eval_mul_two_perms lambda_zero real_to_expr.simps v_p)

  show ?thesis
    apply (simp add: True)
    apply (rule SatAccPred)
        apply fact
       apply (rule RedLit[where ?l="NoPerm", simplified])
      apply fast
     apply fact
    using \<open>v_p = 0\<close> mp
    by force
next
  case False
  hence "p > 0"
    using assms(1)
    by auto

  show ?thesis
  proof (cases "q = 0")
    case True
    show ?thesis
      apply (simp add: False True)
      by (rule assms(3)[simplified True, simplified, simplified False \<open>p > 0\<close>, simplified])
  next
    case False
    hence "q > 0"
      using assms(2)
      by auto

    show ?thesis
      apply (simp add: \<open>p \<noteq> 0\<close> \<open>p > 0\<close> \<open>q \<noteq> 0\<close> \<open>q > 0\<close>)
      by (rule assms(3)[simplified, simplified \<open>p \<noteq> 0\<close> \<open>p > 0\<close>, simplified, simplified \<open>q \<noteq> 0\<close> \<open>q > 0\<close>, simplified])
  qed
qed


lemma synmult_once_twice:
  assumes "p \<ge> 0" and "q \<ge> 0"
      and "sat ctxt \<omega> mh mp (syntactic_mult q (syntactic_mult p A))"
    shows "sat ctxt \<omega> mh mp (syntactic_mult (p * q) A)"
  using assms(3)
proof (induction A arbitrary: mh mp)
  case IH: (Atomic atm)
  show ?case
  proof (cases atm)
    case (Pure e)
    then show ?thesis
      using IH
      by force
  next
    case (Acc e_r f perm)
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      then show ?thesis
        using Acc IH assms(1) assms(2) synmult_once_twice_Acc
        by blast
    next
      case Wildcard
      then show ?thesis
        using Acc IH assms(1) assms(2) synmult_once_twice_AccWildcard
        by blast
    qed
  next
    case (AccPredicate pid e_args perm)
    show ?thesis
    proof (cases perm)
      case (PureExp x1)
      then show ?thesis
        using AccPredicate IH assms(1) assms(2) synmult_once_twice_AccPred
        by blast
    next
      case Wildcard
      then show ?thesis
        using AccPredicate IH assms(1) assms(2) synmult_once_twice_AccPredWildcard
        by blast
    qed
  qed
next
  case (Imp _ _)
  then show ?case
    by (metis SatImpTrue SatImp_case sat.intros(8) syntactic_mult.simps(4))
next
  case (CondAssert _ _ _)
  then show ?case
    by (metis SatCond_case sat.intros(10) sat.intros(9) syntactic_mult.simps(11))
next
  case IH: (Star _ _)
  show ?case
    apply simp
    using IH(3)[simplified]
    by (smt (verit) IH.IH(1) IH.IH(2) assert.inject(6) assert.simps(19) assert.simps(33) assert.simps(45) sat.simps)
qed (fastforce elim: sat.cases)+


lemma fractionability_pq:
    fixes p q :: preal
  assumes "supported_pred_body A"
      and "sat ctxt \<omega> mh mp (syntactic_mult (Rep_preal p) A)"
    shows "sat ctxt \<omega> (mul_mask q mh) (mul_mask q mp) (syntactic_mult (Rep_preal (q * p)) A)"
  apply (subgoal_tac "Rep_preal (q * p) = Rep_preal p * Rep_preal q")
   apply simp
   apply (rule synmult_once_twice)
  using prat_non_negative
     apply presburger+
   apply (rule fractionabilityI[OF _ assms(2)])
  using assms(1) prat_non_negative syntactic_mult_supported
     apply presburger
    apply simp+
  using times_preal.rep_eq
  by auto


\<comment> \<open>A fraction of a consistent total state is external consistent.\<close>

lemma nm_frac_mh_frac:
  fixes frac :: preal
  shows "get_mh_total (mult_nm_total \<phi> frac) = mul_mask frac (get_mh_total \<phi>)"
  by simp

lemma nm_frac_mp_frac:
  fixes frac :: preal
  shows "get_mp_total (mult_nm_total \<phi> frac) = mul_mask frac (get_mp_total \<phi>)"
  using get_mp_multiply
  by auto

lemma nm_mult_lpm:
  assumes "Some (p\<^sub>f,nm\<^sub>f) = get_fnm_nm (f *\<^sub>s nm) lp"
  obtains p' nm' where "Some (p',nm') = get_fnm_nm nm lp \<and> pos2p p\<^sub>f = f * pos2p p' \<and> nm\<^sub>f = f *\<^sub>s nm'"
  using assms
  apply (cases nm)
  apply (simp add: scale_nested_mask_def)
  apply (cases "f = 0")
   apply simp_all
  by (smt (verit) assms comp_apply fst_conv get_fnm_nm.simps get_mp_nm.simps map_option_eq_Some nm_multiply_mp_value option_fold.simps(1) prod.collapse snd_conv)

lemma fraction_consistent_external:
  fixes frac :: preal
  assumes "ctxt_wf_pred ctxt"
    shows "consistent_external_wrt_ploc ctxt \<phi> (pid,vs) p \<Longrightarrow>
           consistent_external_wrt_ploc ctxt (mult_nm_total \<phi> frac) (pid,vs) (frac * p)"
      and "consistent_external ctxt \<phi> \<Longrightarrow>
           consistent_external ctxt (mult_nm_total \<phi> frac)"
proof (induction rule: consistent_external_wrt_ploc_consistent_external.inducts)
  case IH: (SatStep pred_id pred_decl pred_body vs \<phi> p)
  show ?case
    apply (rule SatStep)
        defer 4
    using IH
        apply blast+
    apply (subst nm_frac_mh_frac)
    apply (subst nm_frac_mp_frac)
    apply (rule fractionability_pq)
    using IH.IH(1) IH.hyps assms ctxt_wf_pred_def
     apply blast
    using IH.IH(3)
    by auto
next
  case IH: (SatAll \<phi>)
  show ?case
  proof
    fix pid vs q\<^sub>f nm\<^sub>f
    assume lpm\<^sub>f: "Some (q\<^sub>f,nm\<^sub>f) = get_fnm_total (mult_nm_total \<phi> frac) (pid,vs)"
    obtain q nm where
      lpm: "Some (q,nm) = get_fnm_total \<phi> (pid,vs)" and
      q\<^sub>f: "pos2p q\<^sub>f = frac * pos2p q" and
      nm\<^sub>f: "nm\<^sub>f = frac *\<^sub>s nm"
      using nm_mult_lpm[OF lpm\<^sub>f[simplified]]
      apply simp
      by metis

    show "consistent_external_wrt_ploc ctxt (mult_nm_total \<phi> frac\<lparr> get_nm_total := nm\<^sub>f \<rparr>) (pid,vs) (pos2p q\<^sub>f)"
      using IH(2)[OF lpm]
      by (simp add: q\<^sub>f nm\<^sub>f)
  qed
qed


subsection \<open>Combinability of External Consistent States\<close>

lemma combinability_sat_Acc:
  assumes "sat ctxt \<omega> mh\<^sub>1 mp\<^sub>1 (syntactic_mult p (Atomic (Acc e_r f (PureExp e_p))))"
      and "sat ctxt \<omega> mh\<^sub>2 mp\<^sub>2 (syntactic_mult q (Atomic (Acc e_r f (PureExp e_p))))"
    shows "sat ctxt \<omega> (add_masks mh\<^sub>1 mh\<^sub>2) (add_masks mp\<^sub>1 mp\<^sub>2) (syntactic_mult (p + q) (Atomic (Acc e_r f (PureExp e_p))))"
proof -
  from assms(1)[simplified] obtain v_r v_p\<^sub>1 a where
    "ctxt, None \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef v_r)" and
    v_p\<^sub>1: "ctxt, None \<turnstile> \<langle>Binop (ELit (LPerm p)) Mult e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p\<^sub>1)" and
    "a = the_address v_r" and
    "v_p\<^sub>1 \<ge> 0" and
    mh\<^sub>1: "if v_r = Null then v_p\<^sub>1 = 0 \<and> mh\<^sub>1 = zero_mask else mh\<^sub>1 = singleton_mh (a,f) (Abs_preal v_p\<^sub>1)" and
    "mp\<^sub>1 = zero_mask"
    by (auto elim: SatAcc_case)

  with assms(2)[simplified] obtain v_p\<^sub>2 where
    v_p\<^sub>2: "ctxt, None \<turnstile> \<langle>Binop (ELit (LPerm q)) Mult e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p\<^sub>2)" and
    "v_p\<^sub>2 \<ge> 0" and
    mh\<^sub>2: "if v_r = Null then v_p\<^sub>2 = 0 \<and> mh\<^sub>2 = zero_mask else mh\<^sub>2 = singleton_mh (a,f) (Abs_preal v_p\<^sub>2)" and
    "mp\<^sub>2 = zero_mask"
    using eval_is_deterministic(1)
    by (blast elim: SatAcc_case)

  obtain val_p where
    val_p: "ctxt, None \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val val_p" and
    v_p\<^sub>1_calc: "eval_binop (Option.is_none None) (VPerm p) Mult val_p = BinopNormal (VPerm v_p\<^sub>1)"
    using v_p\<^sub>1
    by (fastforce elim: RedBinop_case RedLit_case)

  have v_p\<^sub>2_calc: "eval_binop (Option.is_none None) (VPerm q) Mult val_p = BinopNormal (VPerm v_p\<^sub>2)"
    using v_p\<^sub>2 eval_is_deterministic(1)[OF val_p]
    by (fastforce elim: RedBinop_case RedLit_case)

  have "ctxt, None \<turnstile> \<langle>Binop (ELit (LPerm (p + q))) Mult e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm (v_p\<^sub>1 + v_p\<^sub>2))"
    apply (rule RedBinop)
       apply (rule RedLit[where ?l="LPerm (p + q)", simplified])
      apply fact
     apply simp
    apply (cases val_p)
    using v_p\<^sub>1_calc[simplified] v_p\<^sub>2_calc[simplified]
        apply simp
        apply argo
       defer
    using v_p\<^sub>1_calc[simplified] v_p\<^sub>2_calc[simplified]
       apply simp
       apply argo
    using v_p\<^sub>1_calc
    by fastforce+

  show ?thesis
    apply simp
    apply (rule SatAcc)
         apply fact+
    using \<open>0 \<le> v_p\<^sub>1\<close> \<open>0 \<le> v_p\<^sub>2\<close>
      apply auto[1]
     apply (split if_split)
     apply (intro conjI)
      apply (simp add: add_masks_zero_mask mh\<^sub>1 mh\<^sub>2)
     apply (simp add: plus_preal.abs_eq[symmetric, of v_p\<^sub>1 v_p\<^sub>2, simplified eq_onp_def, simplified, OF \<open>v_p\<^sub>1 \<ge> 0\<close> \<open>v_p\<^sub>2 \<ge> 0\<close>])
     apply standard+
     apply (simp add: add_masks_def mh\<^sub>1 mh\<^sub>2)
    by (simp add: \<open>mp\<^sub>1 = _\<close> \<open>mp\<^sub>2 = _\<close> add_masks_zero_mask)
qed


lemma combinability_sat_AccWildcard:
  assumes "sat ctxt \<omega> mh\<^sub>1 mp\<^sub>1 (syntactic_mult p (Atomic (Acc e_r f Wildcard)))"
      and "sat ctxt \<omega> mh\<^sub>2 mp\<^sub>2 (syntactic_mult q (Atomic (Acc e_r f Wildcard)))"
      and "p \<ge> 0"
      and "q \<ge> 0"
    shows "sat ctxt \<omega> (add_masks mh\<^sub>1 mh\<^sub>2) (add_masks mp\<^sub>1 mp\<^sub>2) (syntactic_mult (p + q) (Atomic (Acc e_r f Wildcard)))"
proof (cases "p = 0")
  case True
  show ?thesis
  proof (cases "q = 0")
    case True
    show ?thesis
      apply (simp add: \<open>p = 0\<close> \<open>q = 0\<close>)
      using assms[simplified \<open>p = 0\<close> \<open>q = 0\<close>, simplified]
      by (metis \<open>q = 0\<close> add_masks_zero_mask assms(2) sat_Acc_mp_zero synmult_0_mh_0)
  next
    case False
    then show ?thesis
      by (metis \<open>p = 0\<close> add.left_neutral add_masks_comm add_masks_zero_mask assms(1) assms(2) synmult_0_mh_0 synmult_0_mp_0)
  qed
next
  case False
  show ?thesis
  proof (cases "q = 0")
    case True
    then show ?thesis
      by (metis add.right_neutral add_masks_zero_mask assms(1) assms(2) synmult_0_mh_0 synmult_0_mp_0)
  next
    case False
    have "p > 0" and "q > 0"
      using \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close> assms(3,4)
      by linarith+
    have "p + q > 0"
      using \<open>q \<noteq> 0\<close> assms(3) assms(4)
      by linarith
    hence "p + q \<noteq> 0"
      by linarith

    from assms(1)[simplified, simplified \<open>p \<noteq> 0\<close> \<open>p > 0\<close>, simplified] obtain v_r a where
      v_r: "ctxt, None \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef v_r)" and
      "a = the_address v_r" and
      "v_r \<noteq> Null" and
      mh\<^sub>1: "is_singleton_mh (a,f) mh\<^sub>1" and
      "mp\<^sub>1 = zero_mask"
      by (fastforce elim: SatAccWildcard_case)

    with assms(2)[simplified, simplified \<open>q \<noteq> 0\<close> \<open>q > 0\<close>, simplified] have
      mh\<^sub>1: "is_singleton_mh (a,f) mh\<^sub>2" and
      "mp\<^sub>2 = zero_mask"
      using eval_is_deterministic(1)[OF v_r]
      by (auto elim: SatAccWildcard_case)

    show ?thesis
      apply (simp add: \<open>p + q > 0\<close> \<open>p + q \<noteq> 0\<close>)
      apply (rule SatAccWildcard)
          apply fact+
       apply simp
       apply (rule exI[of _ "mh\<^sub>1 (a,f) + mh\<^sub>2 (a,f)"])
       apply (intro conjI)
        apply (metis add.commute is_singleton_mh.simps linorder_not_less mh\<^sub>1 pos_perm_class.sum_larger preal_not_0_gt_0 singleton_mh.simps)
       apply standard
       apply (simp add: add_masks_def)
       apply (metis SatAccWildcard_case \<open>a = _\<close> assms(1)[simplified, simplified \<open>p \<noteq> 0\<close> \<open>p > 0\<close>, simplified] assms(2)[simplified, simplified \<open>q \<noteq> 0\<close> \<open>q > 0\<close>, simplified] add.right_neutral eval_is_deterministic(1) extended_val.inject singleton_mh.simps v_r val.inject(4))
      by (simp add: \<open>mp\<^sub>1 = _\<close> \<open>mp\<^sub>2 = _\<close> add_masks_zero_mask)
  qed
qed


lemma combinability_sat_AccPred:
  assumes "sat ctxt \<omega> mh\<^sub>1 mp\<^sub>1 (syntactic_mult p (Atomic (AccPredicate pid e_args (PureExp e_p))))"
      and "sat ctxt \<omega> mh\<^sub>2 mp\<^sub>2 (syntactic_mult q (Atomic (AccPredicate pid e_args (PureExp e_p))))"
    shows "sat ctxt \<omega> (add_masks mh\<^sub>1 mh\<^sub>2) (add_masks mp\<^sub>1 mp\<^sub>2) (syntactic_mult (p + q) (Atomic (AccPredicate pid e_args (PureExp e_p))))"
proof -
  from assms(1)[simplified] obtain v_args v_p\<^sub>1 where
    "red_pure_exps_total ctxt None e_args \<omega> (Some v_args)" and
    v_p\<^sub>1: "ctxt, None \<turnstile> \<langle>Binop (ELit (LPerm p)) Mult e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p\<^sub>1)" and
    "v_p\<^sub>1 \<ge> 0" and
    "mh\<^sub>1 = zero_mask" and
    mp\<^sub>1: "mp\<^sub>1 = singleton_mp (pid,v_args) (Abs_preal v_p\<^sub>1)"
    by (auto elim: SatAccPred_case)

  with assms(2)[simplified] obtain v_p\<^sub>2 where
    v_p\<^sub>2: "ctxt, None \<turnstile> \<langle>Binop (ELit (LPerm q)) Mult e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p\<^sub>2)" and
    "v_p\<^sub>2 \<ge> 0" and
    "mh\<^sub>2 = zero_mask" and
    mp\<^sub>2: "mp\<^sub>2 = singleton_mp (pid,v_args) (Abs_preal v_p\<^sub>2)"
    using eval_is_deterministic(2)
    by (blast elim: SatAccPred_case)

  obtain val_p where
    val_p: "ctxt, None \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val val_p" and
    v_p\<^sub>1_calc: "eval_binop (Option.is_none None) (VPerm p) Mult val_p = BinopNormal (VPerm v_p\<^sub>1)"
    using v_p\<^sub>1
    by (fastforce elim: RedBinop_case RedLit_case)

  have v_p\<^sub>2_calc: "eval_binop (Option.is_none None) (VPerm q) Mult val_p = BinopNormal (VPerm v_p\<^sub>2)"
    using v_p\<^sub>2 eval_is_deterministic(1)[OF val_p]
    by (fastforce elim: RedBinop_case RedLit_case)

  have "ctxt, None \<turnstile> \<langle>Binop (ELit (LPerm (p + q))) Mult e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm (v_p\<^sub>1 + v_p\<^sub>2))"
    apply (rule RedBinop)
       apply (rule RedLit[where ?l="LPerm (p + q)", simplified])
      apply fact
     apply simp
    apply (cases val_p)
    using v_p\<^sub>1_calc[simplified] v_p\<^sub>2_calc[simplified]
        apply simp
        apply argo
       defer
    using v_p\<^sub>1_calc[simplified] v_p\<^sub>2_calc[simplified]
       apply simp
       apply argo
    using v_p\<^sub>1_calc
    by fastforce+

  show ?thesis
    apply simp
    apply (rule SatAccPred)
        apply fact+
    using \<open>0 \<le> v_p\<^sub>1\<close> \<open>0 \<le> v_p\<^sub>2\<close>
      apply auto[1]
     apply (simp add: \<open>mh\<^sub>1 = _\<close> \<open>mh\<^sub>2 = _\<close> add_masks_zero_mask)
    apply (simp add: plus_preal.abs_eq[symmetric, of v_p\<^sub>1 v_p\<^sub>2, simplified eq_onp_def, simplified, OF \<open>v_p\<^sub>1 \<ge> 0\<close> \<open>v_p\<^sub>2 \<ge> 0\<close>])
    apply standard+
    by (simp add: add_masks_def mp\<^sub>1 mp\<^sub>2)
qed


lemma combinability_sat_AccPredWildcard:
  assumes "sat ctxt \<omega> mh\<^sub>1 mp\<^sub>1 (syntactic_mult p (Atomic (AccPredicate pid e_args Wildcard)))"
      and "sat ctxt \<omega> mh\<^sub>2 mp\<^sub>2 (syntactic_mult q (Atomic (AccPredicate pid e_args Wildcard)))"
      and "p \<ge> 0"
      and "q \<ge> 0"
    shows "sat ctxt \<omega> (add_masks mh\<^sub>1 mh\<^sub>2) (add_masks mp\<^sub>1 mp\<^sub>2) (syntactic_mult (p + q) (Atomic (AccPredicate pid e_args Wildcard)))"
proof (cases "p = 0")
  case True
  show ?thesis
  proof (cases "q = 0")
    case True
    show ?thesis
      apply (simp add: \<open>p = 0\<close> \<open>q = 0\<close>)
      using assms[simplified \<open>p = 0\<close> \<open>q = 0\<close>, simplified]
      by (metis \<open>q = 0\<close> add_masks_zero_mask assms(2) sat_AccPred_mh_zero synmult_0_mp_0)
  next
    case False
    then show ?thesis
      by (metis \<open>p = 0\<close> add.left_neutral add_masks_comm add_masks_zero_mask assms(1) assms(2) synmult_0_mh_0 synmult_0_mp_0)
  qed
next
  case False
  show ?thesis
  proof (cases "q = 0")
    case True
    then show ?thesis
      by (metis add.right_neutral add_masks_zero_mask assms(1) assms(2) synmult_0_mh_0 synmult_0_mp_0)
  next
    case False
    have "p > 0" and "q > 0"
      using \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close> assms(3,4)
      by linarith+
    have "p + q > 0"
      using \<open>q \<noteq> 0\<close> assms(3) assms(4)
      by linarith
    hence "p + q \<noteq> 0"
      by linarith

    from assms(1)[simplified, simplified \<open>p \<noteq> 0\<close> \<open>p > 0\<close>, simplified] obtain v_args where
      v_args: "red_pure_exps_total ctxt None e_args \<omega> (Some v_args)" and
      "mh\<^sub>1 = zero_mask" and
      mp\<^sub>1: "is_singleton_mp (pid,v_args) mp\<^sub>1"
      by (fastforce elim: SatAccPredWildcard_case)

    with assms(2)[simplified, simplified \<open>q \<noteq> 0\<close> \<open>q > 0\<close>, simplified] have
      "mh\<^sub>2 = zero_mask" and
      mp\<^sub>2: "is_singleton_mp (pid,v_args) mp\<^sub>2"
      using eval_is_deterministic(2)[OF v_args]
      by (auto elim: SatAccPredWildcard_case)

    show ?thesis
      apply (simp add: \<open>p + q > 0\<close> \<open>p + q \<noteq> 0\<close>)
      apply (rule SatAccPredWildcard)
        apply fact+
       apply (simp add: \<open>mh\<^sub>1 = _\<close> \<open>mh\<^sub>2 = _\<close> add_masks_zero_mask)
      apply simp
      apply (rule exI[of _ "mp\<^sub>1 (pid,v_args) + mp\<^sub>2 (pid,v_args)"])
      apply (intro conjI)
       apply (metis is_singleton_mp.simps mp\<^sub>1 padd_pos pperm_pnone_pgt singleton_mp.simps)
      apply standard
      apply (simp add: add_masks_def)
      by (metis mp\<^sub>2 add.comm_neutral is_singleton_mp.simps mp\<^sub>1 singleton_mp.simps)
  qed
qed


lemma combinability_sat:
  assumes "sat ctxt \<omega> mh\<^sub>1 mp\<^sub>1 (syntactic_mult p A)"
      and "sat ctxt \<omega> mh\<^sub>2 mp\<^sub>2 (syntactic_mult q A)"
      and "p \<ge> 0"
      and "q \<ge> 0"
    shows "sat ctxt \<omega> (add_masks mh\<^sub>1 mh\<^sub>2) (add_masks mp\<^sub>1 mp\<^sub>2) (syntactic_mult (p + q) A)"
  using assms(1,2)
proof (induction A arbitrary: mh\<^sub>1 mp\<^sub>1 mh\<^sub>2 mp\<^sub>2)
  case IH: (Atomic atm)
  show ?case
  proof (cases atm)
    case (Pure e)
    then show ?thesis
      by (metis IH.prems(1) IH.prems(2) add_masks_zero_mask synmult_0_mh_0 synmult_0_mp_0 syntactic_mult.simps(1))
  next
    case (Acc e_r f perm)
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      show ?thesis
        using combinability_sat_Acc[OF IH[unfolded Acc PureExp]] Acc PureExp
        by fastforce
    next
      case Wildcard
      then show ?thesis
        using combinability_sat_AccWildcard[OF IH[unfolded Acc Wildcard]] Acc Wildcard assms(3,4)
        by fastforce
    qed
  next
    case (AccPredicate pid e_args perm)
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      show ?thesis
        using combinability_sat_AccPred[OF IH[unfolded AccPredicate PureExp]] AccPredicate PureExp
        by fastforce
    next
      case Wildcard
      then show ?thesis
        using combinability_sat_AccPredWildcard[OF IH[unfolded AccPredicate Wildcard]] AccPredicate Wildcard assms(3,4)
        by fastforce
    qed
  qed
next
  case IH: (Imp e A)
  then consider (True) "ctxt, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)" |
               (False) "ctxt, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    using sat_Imp_True_or_False
    by fastforce
  then show ?case
    apply cases
     apply (metis IH.IH IH.prems(1) IH.prems(2) SatImpTrue SatImp_case eval_is_deterministic(1) extended_val.inject syntactic_mult.simps(4) val.inject(2))
    by (metis IH.prems(1) IH.prems(2) SatImpFalse add_masks_zero_mask sat_Imp_False_only_zero(1) sat_Imp_False_only_zero(2) syntactic_mult.simps(4))
next
  case IH: (CondAssert e A B)
  then consider (True) "ctxt, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)" |
               (False) "ctxt, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    using sat_Cond_True_or_False
    by fastforce
  then show ?case
    apply cases
     apply simp
     apply (rule SatCondTrue)
      apply simp
     apply (rule IH(1))
    using SatCond_case[OF IH(3)[simplified]]
      apply (metis eval_is_deterministic(1) extended_val.inject val.inject(2))
    using SatCond_case[OF IH(4)[simplified]]
     apply (metis eval_is_deterministic(1) extended_val.inject val.inject(2))
    apply simp
    by (metis IH.IH(2) SatCondFalse SatCond_case[OF IH(3)[simplified]] SatCond_case[OF IH(4)[simplified]] eval_is_deterministic(1) extended_val.inject val.inject(2))
next
  case IH: (Star A B)
  obtain mh\<^sub>1\<^sub>A mh\<^sub>1\<^sub>B mp\<^sub>1\<^sub>A mp\<^sub>1\<^sub>B where
    "mh_split mh\<^sub>1 mh\<^sub>1\<^sub>A mh\<^sub>1\<^sub>B" and
    "mp_split mp\<^sub>1 mp\<^sub>1\<^sub>A mp\<^sub>1\<^sub>B" and
    "sat ctxt \<omega> mh\<^sub>1\<^sub>A mp\<^sub>1\<^sub>A (syntactic_mult p A)" and
    "sat ctxt \<omega> mh\<^sub>1\<^sub>B mp\<^sub>1\<^sub>B (syntactic_mult p B)"
    using IH(3)
    by (auto elim: SatStar_case)
  moreover obtain mh\<^sub>2\<^sub>A mh\<^sub>2\<^sub>B mp\<^sub>2\<^sub>A mp\<^sub>2\<^sub>B where
    "mh_split mh\<^sub>2 mh\<^sub>2\<^sub>A mh\<^sub>2\<^sub>B" and
    "mp_split mp\<^sub>2 mp\<^sub>2\<^sub>A mp\<^sub>2\<^sub>B" and
    "sat ctxt \<omega> mh\<^sub>2\<^sub>A mp\<^sub>2\<^sub>A (syntactic_mult q A)" and
    "sat ctxt \<omega> mh\<^sub>2\<^sub>B mp\<^sub>2\<^sub>B (syntactic_mult q B)"
    using IH(4)
    by (auto elim: SatStar_case)

  ultimately have
    "sat ctxt \<omega> (add_masks mh\<^sub>1\<^sub>A mh\<^sub>2\<^sub>A) (add_masks mp\<^sub>1\<^sub>A mp\<^sub>2\<^sub>A) (syntactic_mult (p + q) A)" and
    "sat ctxt \<omega> (add_masks mh\<^sub>1\<^sub>B mh\<^sub>2\<^sub>B) (add_masks mp\<^sub>1\<^sub>B mp\<^sub>2\<^sub>B) (syntactic_mult (p + q) B)"
    using IH(1,2)
    by blast+

  show ?case
    apply simp
    apply (rule SatStar)
       defer
       defer
       apply fact+
     apply (meson \<open>mh_split mh\<^sub>1 mh\<^sub>1\<^sub>A mh\<^sub>1\<^sub>B\<close> \<open>mh_split mh\<^sub>2 mh\<^sub>2\<^sub>A mh\<^sub>2\<^sub>B\<close> mh_split.elims(3) mh_split_twice)
    by (meson \<open>mp_split mp\<^sub>1 mp\<^sub>1\<^sub>A mp\<^sub>1\<^sub>B\<close> \<open>mp_split mp\<^sub>2 mp\<^sub>2\<^sub>A mp\<^sub>2\<^sub>B\<close> mp_split.elims(3) mp_split_twice)
qed (auto elim: sat.cases)+


lemma sum_consistent_external_helper:
  assumes
    "\<And>x y lp p q.
        x \<in> range fnm\<^sub>1 \<Longrightarrow>
        y \<in> range fnm\<^sub>2 \<Longrightarrow>
        \<not> Option.is_none x \<Longrightarrow>
        \<not> Option.is_none y \<Longrightarrow>
        consistent_external_wrt_ploc ctxt
         \<lparr> get_hh_total = hh, get_nm_total = snd (the x) \<rparr> lp p \<Longrightarrow>
        consistent_external_wrt_ploc ctxt
         \<lparr> get_hh_total = hh, get_nm_total = snd (the y) \<rparr> lp q \<Longrightarrow>
        consistent_external_wrt_ploc ctxt
         \<lparr> get_hh_total = hh, get_nm_total = snd (the x) + snd (the y) \<rparr> lp (p + q)"
      and "consistent_external ctxt \<lparr> get_hh_total = hh, get_nm_total = NM mh\<^sub>1 fnm\<^sub>1 \<rparr>"
      and "consistent_external ctxt \<lparr> get_hh_total = hh, get_nm_total = NM mh\<^sub>2 fnm\<^sub>2 \<rparr>"
    shows "consistent_external ctxt \<lparr> get_hh_total = hh, get_nm_total = NM mh\<^sub>1 fnm\<^sub>1 + NM mh\<^sub>2 fnm\<^sub>2 \<rparr>"
proof
  fix pid vs r nm'
  assume lpm: "Some (r,nm') = get_fnm_total \<lparr> get_hh_total = hh, get_nm_total = NM mh\<^sub>1 fnm\<^sub>1 + NM mh\<^sub>2 fnm\<^sub>2 \<rparr> (pid,vs)"
  show "consistent_external_wrt_ploc ctxt
          (\<lparr> get_hh_total = hh, get_nm_total = NM mh\<^sub>1 fnm\<^sub>1 + NM mh\<^sub>2 fnm\<^sub>2 \<rparr>\<lparr> get_nm_total := nm' \<rparr>)
          (pid,vs) (pos2p r)"
  proof (cases "fnm\<^sub>1 (pid,vs)")
    case lpm\<^sub>1: None
    show ?thesis
    proof (cases "fnm\<^sub>2 (pid,vs)")
      case lpm\<^sub>2: None
      show ?thesis
        using lpm[unfolded plus_nested_mask_def, simplified]
        by (simp add: pfun_comb_def lpm\<^sub>1 lpm\<^sub>2)
    next
      case lpm\<^sub>2: (Some lpm\<^sub>2)
      have "(r,nm') = lpm\<^sub>2"
        using lpm[unfolded plus_nested_mask_def, simplified]
        by (auto simp: pfun_comb_def lpm\<^sub>1 lpm\<^sub>2)
      show ?thesis
        apply simp
        using assms(3)
        by (metis SatAll_case \<open>(r, nm') = lpm\<^sub>2\<close> get_fnm_nm.simps lpm\<^sub>2 total_state.select_convs(2) total_state.update_convs(2))
    qed
  next
    case lpm\<^sub>1: (Some lpm\<^sub>1)
    show ?thesis
    proof (cases "fnm\<^sub>2 (pid,vs)")
      case lpm\<^sub>2: None
      have "(r,nm') = lpm\<^sub>1"
        using lpm[unfolded plus_nested_mask_def, simplified]
        by (auto simp: pfun_comb_def lpm\<^sub>1 lpm\<^sub>2)
      show ?thesis
        apply simp
        using assms(2)
        by (metis SatAll_case \<open>(r, nm') = lpm\<^sub>1\<close> get_fnm_nm.simps lpm\<^sub>1 total_state.select_convs(2) total_state.update_convs(2))
    next
      case lpm\<^sub>2: (Some lpm\<^sub>2)
      have "(r,nm') = (fst lpm\<^sub>1 + fst lpm\<^sub>2, snd lpm\<^sub>1 + snd lpm\<^sub>2)"
        using lpm[unfolded plus_nested_mask_def, simplified, folded plus_nested_mask_def]
        by (auto simp: pfun_comb_def lpm\<^sub>1 lpm\<^sub>2)
      then show ?thesis
        apply (simp add: pos2p_add_distr[symmetric])
        apply (rule assms(1)[of "Some lpm\<^sub>1" "Some lpm\<^sub>2", simplified])
           apply (metis lpm\<^sub>1 range_eqI)
          apply (metis lpm\<^sub>2 range_eqI)
         apply (metis assms(2) consistent_external.cases get_fnm_nm.simps get_fnm_total.simps lpm\<^sub>1 prod.collapse total_state.select_convs(2) total_state.update_convs(2))
        by (metis assms(3) consistent_external.cases get_fnm_nm.simps get_fnm_total.simps lpm\<^sub>2 prod.collapse total_state.select_convs(2) total_state.update_convs(2))
    qed
  qed
qed


lemma sum_consistent_external:
    shows "consistent_external ctxt (\<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>1 \<rparr>) \<Longrightarrow>
           consistent_external ctxt (\<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>2 \<rparr>) \<Longrightarrow>
           consistent_external ctxt (\<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>1 + nm\<^sub>2 \<rparr>)"
      and "consistent_external_wrt_ploc ctxt (\<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>1 \<rparr>) lp p \<Longrightarrow>
           consistent_external_wrt_ploc ctxt (\<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>2 \<rparr>) lp q \<Longrightarrow>
           consistent_external_wrt_ploc ctxt (\<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>1 + nm\<^sub>2 \<rparr>) lp (p + q)"
proof (induction arbitrary: lp p q rule: nested_mask_merge.induct[of _ nm\<^sub>1 nm\<^sub>2])
  case IH: (1 mh\<^sub>1 fnm\<^sub>1 mh\<^sub>2 fnm\<^sub>2)
  {
    case 1
    show ?case
      using sum_consistent_external_helper[OF _ 1(1) 1(2)] IH(2)
      by fastforce
  next
    case 2
    obtain pid vs where "lp = (pid,vs)"
      by fastforce
    obtain pdecl pbody where
      pdecl: "ViperLang.predicates (program_total ctxt) pid = Some pdecl" and
      pbody: "ViperLang.predicate_decl.body pdecl = Some pbody" and
      "vals_well_typed (absval_interp_total ctxt) vs (ViperLang.predicate_decl.args pdecl)" and
      sat\<^sub>1: "sat ctxt
         \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty, get_total_full = \<lparr> get_hh_total = hh, get_nm_total = NM mh\<^sub>1 fnm\<^sub>1 \<rparr>\<lparr> get_nm_total := 0 \<rparr> \<rparr>
         (get_mh_total \<lparr> get_hh_total = hh, get_nm_total = NM mh\<^sub>1 fnm\<^sub>1 \<rparr>)
         (get_mp_total \<lparr> get_hh_total = hh, get_nm_total = NM mh\<^sub>1 fnm\<^sub>1 \<rparr>)
         (syntactic_mult (Rep_preal p) pbody)" and
      extcons\<^sub>1: "consistent_external ctxt \<lparr> get_hh_total = hh, get_nm_total = NM mh\<^sub>1 fnm\<^sub>1 \<rparr>"
      using 2(1)[unfolded \<open>lp = _\<close>]
      by (auto elim: SatStep_case)

    hence
      sat\<^sub>2: "sat ctxt
         \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty, get_total_full = \<lparr> get_hh_total = hh, get_nm_total = NM mh\<^sub>2 fnm\<^sub>2 \<rparr>\<lparr> get_nm_total := 0 \<rparr> \<rparr>
         (get_mh_total \<lparr> get_hh_total = hh, get_nm_total = NM mh\<^sub>2 fnm\<^sub>2 \<rparr>)
         (get_mp_total \<lparr> get_hh_total = hh, get_nm_total = NM mh\<^sub>2 fnm\<^sub>2 \<rparr>)
         (syntactic_mult (Rep_preal q) pbody)" and
      extcons\<^sub>2: "consistent_external ctxt \<lparr> get_hh_total = hh, get_nm_total = NM mh\<^sub>2 fnm\<^sub>2 \<rparr>"
      using 2(2)[unfolded \<open>lp = _\<close>]
      by (auto elim: SatStep_case)

    show ?case
      unfolding \<open>lp = _\<close>
      apply (rule SatStep)
          apply fact+
       apply (simp del: get_mp_nm.simps add: get_mp_nm_distr_over_plus plus_preal.rep_eq)
       apply (rule combinability_sat)
      using sat\<^sub>1
          apply simp
      using sat\<^sub>2
         apply simp
        apply (simp add: prat_non_negative)+
      using sum_consistent_external_helper[OF _ extcons\<^sub>1 extcons\<^sub>2] IH(2)
      by fastforce
  }
qed


subsection \<open>Fractioning Nested Mask\<close>

\<comment> \<open>Todo: move to somewhere else\<close>
lemma split_implies_le:
  assumes "mp_split mp mp\<^sub>1 mp\<^sub>2"
  shows "mp\<^sub>1 \<le> mp" and "mp\<^sub>2 \<le> mp"
  using assms less_eq_add_masks
   apply auto[1]
  using assms
  by (metis add_masks_comm less_eq_add_masks mp_split.elims(2))


subsection \<open>Empty States\<close>

lemma empty_consistent_external:
  shows "consistent_external ctxt (\<lparr> get_hh_total = hh, get_nm_total = 0 \<rparr>)"
  apply standard
  unfolding zero_nested_mask_def
  by simp


end
