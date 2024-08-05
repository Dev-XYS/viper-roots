theory TotalConsistencyProperties
  imports TotalSemanticsCore TotalSemantics TotalInternalConsistency
begin


\<comment> \<open>Helper lemmas on singleton masks\<close>

lemma singleton_mh_multiply:
  shows "singleton_mh loc (q * p) = ((*) q) \<circ> singleton_mh loc p"
  by (standard, simp)

lemma singleton_mp_multiply:
  shows "singleton_mp loc (q * p) = ((*) q) \<circ> singleton_mp loc p"
  by (standard, simp)


\<comment> \<open>Helper lemmas on masks and \<^const>\<open>nested_mask_multiply\<close>\<close>

lemma zero_mh_multiply:
  fixes frac :: preal
  shows "field_mask_multiply zero_mh frac = zero_mh"
  by (standard, simp)

lemma zero_mp_multiply:
  fixes frac :: preal
  shows "predicate_mask_multiply zero_mp frac = zero_mp"
  by (standard, simp)

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

lemma get_mp_total_full_multiply:
  fixes frac :: preal
  assumes "get_mp_total_full \<omega> loc = p"
  shows "get_mp_total_full (mult_nm_total_full \<omega> frac) loc = p * frac"
  apply simp
  using PosReal.pmult_comm assms by fastforce

lemma get_hh_total_full_multiply:
  fixes frac :: preal
  assumes "get_hh_total_full \<omega> loc = v"
  shows "get_hh_total_full (mult_nm_total_full \<omega> frac) loc = v"
  apply simp
  using assms by force

lemma get_valid_locs_multiply:
  fixes frac :: preal
  assumes "frac > 0"
  shows "get_valid_locs \<omega> = get_valid_locs (mult_nm_total_full \<omega> frac)"
  apply (simp add: get_valid_locs_def)
  apply (rule Set.Collect_cong)
  apply standard
  using PosReal.pgt.rep_eq assms preal_pnone_pgt times_preal.rep_eq zero_preal.rep_eq by force+

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

lemma mh_split_zero:
  assumes "mh_split mh zero_mh zero_mh"
  shows "mh = zero_mh"
  apply standard
  apply simp
  by (metis add.right_neutral assms fun_comb_def mh_split.elims(2) zero_mh.simps)

lemma mp_split_zero:
  assumes "mp_split mp zero_mp zero_mp"
  shows "mp = zero_mp"
  apply standard
  apply simp
  by (metis add.right_neutral assms fun_comb_def mp_split.simps zero_mp.simps)

lemma mh_split_twice:
  assumes "mh_split s a b"
      and "mh_split a a1 a2"
      and "mh_split b b1 b2"
      and "mh_split s1 a1 b1"
      and "mh_split s2 a2 b2"
    shows "mh_split s s1 s2"
  apply simp
  apply standard
  apply (simp add: fun_comb_def)
proof -
  fix x
  have "s1 x = a1 x + b1 x"
    by (metis assms(4) fun_comb_def mh_split.elims(1))
  moreover have "s2 x = a2 x + b2 x"
    by (metis assms(5) fun_comb_def mh_split.elims(1))
  ultimately show "s x = s1 x + s2 x"
    by (metis (no_types, lifting) ab_semigroup_add_class.add_ac(1) assms(1-3) fun_comb_def group_cancel.add2 mh_split.elims(2))
qed

lemma mp_split_twice:
  assumes "mp_split s a b"
      and "mp_split a a1 a2"
      and "mp_split b b1 b2"
      and "mp_split s1 a1 b1"
      and "mp_split s2 a2 b2"
    shows "mp_split s s1 s2"
  apply simp
  apply standard
  apply (simp add: fun_comb_def)
proof -
  fix x
  have "s1 x = a1 x + b1 x"
    by (metis assms(4) fun_comb_def mp_split.elims(1))
  moreover have "s2 x = a2 x + b2 x"
    by (metis assms(5) fun_comb_def mp_split.elims(1))
  ultimately show "s x = s1 x + s2 x"
    by (metis (no_types, lifting) ab_semigroup_add_class.add_ac(1) assms(1-3) fun_comb_def group_cancel.add2 mp_split.elims(2))
qed


\<comment> \<open>Other helper lemmas\<close>

lemma total_state_update_nm_read:
  shows "get_nm_total (\<phi>\<lparr> get_nm_total := nm \<rparr>) = nm"
  by simp

lemma supported_sub_expr_supported:
  assumes "supported_pred_expr e"
  shows "list_all supported_pred_expr (sub_pure_exp_total e)"
  using assms
  by (induct e; simp add: list_all_length)


\<comment> \<open>Expression evaluation is deterministic.\<close>

lemma eval_is_deterministic:
  assumes "ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t v\<^sub>1"
      and "ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t v\<^sub>2"
    shows "v\<^sub>1 = v\<^sub>2"
  sorry


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
  case (RedUnfolding ubody \<omega> v p es)
  show ?case
    using RedUnfolding.IH(2) RedUnfolding.prems red_pure_exp_total_red_pure_exps_total.RedUnfolding by fastforce
next
  case IH: (RedUnfoldingDefNoPred \<omega>_def es \<omega> vs pred_id pred_decl p ubody)
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
  shows "mp = zero_mp"
  using SatAtomic_case assms by blast

lemma sat_AccPred_mh_zero:
  assumes "sat ctxt \<omega> mh mp (Atomic (AccPredicate pred_id e_args perm))"
  shows "mh = zero_mh"
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


\<comment> \<open>Combinability of fractional resources.\<close>


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
      and "sat ctxt \<omega> mh zero_mp (Atomic (Acc e_r f (PureExp e_p)))"
    shows "sat ctxt (mult_nm_total_full \<omega> p) (field_mask_multiply mh p) zero_mp (syntactic_mult (Rep_preal p) (Atomic (Acc e_r f (PureExp e_p))))"
proof -
  from assms(4) obtain v_r v_p a where
    v_r_eval: "ctxt, None \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef v_r)" and
    v_p_eval: "ctxt, None \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
    a_eval: "a = the_address v_r" and
    v_p_pos: "v_p \<ge> 0" and
    mh_sing: "if v_r = Null then v_p = 0 else mh = singleton_mh (a,f) (Abs_preal v_p)"
    using SatAcc_case by meson
  show ?thesis
    apply (simp only: syntactic_mult.simps real_mult_permexpr.simps)
    apply (rule SatAcc)
         prefer 3
         apply (simp only: a_eval)
        prefer 5
    subgoal by auto
  proof -
    from v_r_eval show "ctxt, None \<turnstile> \<langle>e_r; mult_nm_total_full \<omega> p\<rangle> [\<Down>]\<^sub>t Val (VRef v_r)"
      using eval_frac_mask_does_not_matter(1)
      by (metis assms(1) assms(2) option.map_disc_iff)
  next
    show "ctxt, None \<turnstile> \<langle>Binop (real_to_expr (Rep_preal p)) Mult e_p; mult_nm_total_full \<omega> p\<rangle> [\<Down>]\<^sub>t Val (VPerm (Rep_preal p * v_p))"
      apply (rule RedBinop)
         prefer 3
      subgoal by auto
    proof -
      show "ctxt, None \<turnstile> \<langle>real_to_expr (Rep_preal p); mult_nm_total_full \<omega> p\<rangle> [\<Down>]\<^sub>t Val (VPerm (Rep_preal p))"
        by (metis RedLit real_to_expr.elims val_of_lit.simps(3))
    next
      from v_p_eval show "ctxt, None \<turnstile> \<langle>e_p; mult_nm_total_full \<omega> p\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)"
        using eval_frac_mask_does_not_matter(1) assms(1) assms(3) option.simps(9) by fastforce
    next
      show "eval_binop (Option.is_none None) (VPerm (Rep_preal p)) Mult (VPerm v_p) = BinopNormal (VPerm (Rep_preal p * v_p))"
        by force
    qed
  next
    show "0 \<le> Rep_preal p * v_p"
      by (simp add: prat_non_negative v_p_pos)
  next
    show "if v_r = Null then Rep_preal p * v_p = 0 else field_mask_multiply mh p = singleton_mh (the_address v_r, f) (Abs_preal (Rep_preal p * v_p))"
      apply simp
      by (metis Rep_preal_inverse a_eval eq_onp_same_args mh_sing prat_non_negative singleton_mh_multiply times_preal.abs_eq v_p_pos)
  qed
qed

lemma fractionability_SatAcc_Wildcard:
  fixes p :: preal
  assumes "p > 0"
      and "supported_pred_expr e_r"
      and "sat ctxt \<omega> mh zero_mp (Atomic (Acc e_r f Wildcard))"
    shows "sat ctxt (mult_nm_total_full \<omega> p) (field_mask_multiply mh p) zero_mp (syntactic_mult (Rep_preal p) (Atomic (Acc e_r f Wildcard)))"
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
    show "ctxt, None \<turnstile> \<langle>e_r;mult_nm_total_full \<omega> p\<rangle> [\<Down>]\<^sub>t Val (VRef v_r)"
      using assms(1) assms(2) eval_frac_mask_does_not_matter(1) v_r_eval option.simps(9) by fastforce
  next
    show "v_r \<noteq> Null" using v_r_non_null by auto
  next
    show "is_singleton_mh (the_address v_r, f) (field_mask_multiply mh p)"
      apply simp
      using mh_sing
      by (metis a_eval assms(1) is_singleton_mh.simps less_preal.rep_eq mult_eq_0_iff pperm_pnone_pgt singleton_mh_multiply times_preal.rep_eq zero_preal.rep_eq)
  qed
qed

lemma fractionability_SatAccPred:
  fixes p :: preal
  assumes "p > 0"
      and "list_all supported_pred_expr e_args"
      and "supported_pred_expr e_p"
      and "sat ctxt \<omega> zero_mh mp (Atomic (AccPredicate pred_id e_args (PureExp e_p)))"
    shows "sat ctxt (mult_nm_total_full \<omega> p) zero_mh (predicate_mask_multiply mp p) (syntactic_mult (Rep_preal p) (Atomic (AccPredicate pred_id e_args (PureExp e_p))))"
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
    from v_args_eval show "red_pure_exps_total ctxt None e_args (mult_nm_total_full \<omega> p) (Some v_args)"
      using eval_frac_mask_does_not_matter(2) assms(1,2) by fastforce
  next
    show "ctxt, None \<turnstile> \<langle>Binop (real_to_expr (Rep_preal p)) Mult e_p; mult_nm_total_full \<omega> p\<rangle> [\<Down>]\<^sub>t Val (VPerm (Rep_preal p * v_p))"
      apply (rule RedBinop)
         prefer 3
      subgoal by auto
    proof -
      show "ctxt, None \<turnstile> \<langle>real_to_expr (Rep_preal p); mult_nm_total_full \<omega> p\<rangle> [\<Down>]\<^sub>t Val (VPerm (Rep_preal p))"
        by (metis RedLit real_to_expr.elims val_of_lit.simps(3))
    next
      from v_p_eval show "ctxt, None \<turnstile> \<langle>e_p; mult_nm_total_full \<omega> p\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)"
        using eval_frac_mask_does_not_matter(1) assms(1) assms(3) by fastforce
    next
      show "eval_binop (Option.is_none None) (VPerm (Rep_preal p)) Mult (VPerm v_p) = BinopNormal (VPerm (Rep_preal p * v_p))"
        by force
    qed
  next
    show "0 \<le> Rep_preal p * v_p"
      by (simp add: prat_non_negative v_p_pos)
  next
    show "predicate_mask_multiply mp p = singleton_mp (pred_id, v_args) (Abs_preal (Rep_preal p * v_p))"
      apply simp
      apply standard
      by (metis Rep_preal_inverse eq_onp_same_args mp_sing prat_non_negative singleton_mp_multiply times_preal.abs_eq v_p_pos)
  qed
qed

lemma fractionability_SatAccPred_Wildcard:
  fixes p :: preal
  assumes "p > 0"
      and "list_all supported_pred_expr e_args"
      and "sat ctxt \<omega> zero_mh mp (Atomic (AccPredicate pred_id e_args Wildcard))"
    shows "sat ctxt (mult_nm_total_full \<omega> p) zero_mh (predicate_mask_multiply mp p) (syntactic_mult (Rep_preal p) (Atomic (AccPredicate pred_id e_args Wildcard)))"
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
    from v_args_eval show "red_pure_exps_total ctxt None e_args (mult_nm_total_full \<omega> p) (Some v_args)"
      using assms(1) assms(2) eval_frac_mask_does_not_matter(2) by fastforce
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
    shows "sat ctxt (mult_nm_total_full \<omega> p) (field_mask_multiply mh p) (predicate_mask_multiply mp p) (syntactic_mult (Rep_preal p) A)"
  using assms(2) assms(3)
proof (induct A arbitrary: mh mp)
  case IH: (Atomic x)
  show ?case
  proof (cases x)
    case (Pure e)
    hence e_eval: "ctxt, None \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)" and
          mh_zero: "mh = zero_mh" and
          mp_zero: "mp = zero_mp"
      using IH.prems(2) SatAtomic_case by blast+
    show ?thesis
      apply (simp del: mult_nm_total_full.simps field_mask_multiply.simps add: Pure)
      apply (rule SatPure)
    proof -
      from e_eval show "ctxt, None \<turnstile> \<langle>e;mult_nm_total_full \<omega> p\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
        by (metis IH.prems(1) Pure assert_pred.elims(2) assert_pred_rec.simps(1) assms(1) atomic_assert_pred.elims(2) atomic_assert_pred_rec.simps(1) eval_frac_mask_does_not_matter(1) option.map_disc_iff)
    next
      from mh_zero show "field_mask_multiply mh p = zero_mh"
        using zero_mh_multiply by auto
    next
      from mp_zero show "(\<lambda>a. p * (mp a)) = zero_mp"
        using Rep_preal_inject times_preal.rep_eq zero_preal.rep_eq by fastforce
    qed
  next
    case (Acc e_r f perm)
    then have "mp = zero_mp"
      using IH sat_Acc_mp_zero by fastforce
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      then show ?thesis using fractionability_SatAcc
        by (metis Acc IH.prems(1) IH.prems(2) PureExp \<open>mp = zero_mp\<close> assert_pred.elims(2) assert_pred_rec.simps(1) assms(1) atomic_assert_pred.elims(2) atomic_assert_pred_rec.simps(3) zero_mp_multiply)
    next
      case Wildcard
      then show ?thesis using fractionability_SatAcc_Wildcard
        by (metis Acc IH.prems(1) IH.prems(2) \<open>mp = zero_mp\<close> assert_pred.elims(2) assert_pred_rec.simps(1) assms(1) atomic_assert_pred.elims(2) atomic_assert_pred_rec.simps(2) zero_mp_multiply)
    qed
  next
    case (AccPredicate pred_id e_args perm)
    then have "mh = zero_mh"
      using IH sat_AccPred_mh_zero by fastforce
    have "list_all no_perm_pure_exp e_args" and "list_all no_old_pure_exp e_args"
      using AccPredicate IH.prems(1) IH.prems(2) SatAtomic_case assert_pred.elims(2) by fastforce+
    hence "list_all supported_pred_expr e_args"
      using Ball_set by blast
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      then show ?thesis using fractionability_SatAccPred
        by (metis (no_types, lifting) AccPredicate IH.prems(1) IH.prems(2) \<open>list_all supported_pred_expr e_args\<close> \<open>mh = zero_mh\<close> assert_pred.elims(2) assert_pred_rec.simps(1) assms(1) atomic_assert_pred.elims(2) atomic_assert_pred_rec.simps(5) zero_mh_multiply)
    next
      case Wildcard
      then show ?thesis using fractionability_SatAccPred_Wildcard
        by (metis (no_types, lifting) AccPredicate IH.prems(2) \<open>list_all supported_pred_expr e_args\<close> \<open>mh = zero_mh\<close> assms(1) zero_mh_multiply)
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
      using IH e_sup A_sup True eval_frac_mask_does_not_matter(1)
       apply (metis assms(1) option.map_disc_iff)
      by (metis A_sup IH.hyps IH.prems(2) SatImp_case True eval_is_deterministic extended_val.inject val.inject(2))
  next
    case False
    show ?thesis
      apply (simp only: syntactic_mult.simps)
      apply (rule SatImpFalse)
      using IH e_sup A_sup False eval_frac_mask_does_not_matter(1)
        apply (metis assms(1) option.map_disc_iff)
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
      using IH e_sup A_sup True eval_frac_mask_does_not_matter(1)
       apply (metis assms(1) option.map_disc_iff)
      by (metis A_sup IH.hyps(1) IH.prems(2) SatCond_case True eval_is_deterministic extended_val.inject val.inject(2))
  next
    case False
    show ?thesis
      apply (simp only: syntactic_mult.simps)
      apply (rule SatCondFalse)
      using IH e_sup B_sup False eval_frac_mask_does_not_matter(1)
       apply (metis assms(1) option.map_disc_iff)
      by (metis B_sup False IH.hyps(2) IH.prems(2) SatCond_case eval_is_deterministic extended_val.inject val.inject(2))
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
    unfolding syntactic_mult.simps using SatStar
    by (smt (verit) assert.inject(6) assert.simps(19) assert.simps(33) assert.simps(45) sat.simps)
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
      and "supported_pred_body A"
      and "sat ctxt \<omega> mh mp (syntactic_mult (Rep_preal p) A)"
    shows "sat ctxt (mult_nm_total_full \<omega> q) (field_mask_multiply mh q) (predicate_mask_multiply mp q) (syntactic_mult (Rep_preal (q * p)) A)"
proof -
  define \<omega>\<^sub>0 where \<omega>\<^sub>0: "\<omega>\<^sub>0 = mult_nm_total_full \<omega> (1/p)"
  define mh\<^sub>0 where mh\<^sub>0: "mh\<^sub>0 = field_mask_multiply mh (1/p)"
  define mp\<^sub>0 where mp\<^sub>0: "mp\<^sub>0 = predicate_mask_multiply mp (1/p)"
  show ?thesis
    apply (rule fractionabilityI)
    using assms(1) assms(2) less_preal.rep_eq times_preal.rep_eq zero_preal.rep_eq apply force
        apply (simp only: assms(3))
  proof -
    show "sat ctxt \<omega>\<^sub>0 mh\<^sub>0 mp\<^sub>0 A"
      using \<omega>\<^sub>0 assms(1) assms(4) fractionability_inv mh\<^sub>0 mp\<^sub>0 by blast
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
    apply (simp only: predicate_\<omega>_multiply)
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


\<comment> \<open>The sum of two external consistent states is external consistent.\<close>

lemma sum_consistent_external:
  assumes "consistent_external ctxt (\<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>1 \<rparr>)"
      and "consistent_external ctxt (\<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>2 \<rparr>)"
    shows "consistent_external ctxt (\<lparr> get_hh_total = hh, get_nm_total = nested_mask_merge nm\<^sub>1 nm\<^sub>2 \<rparr>)"
  sorry


\<comment> \<open>Unfold statement preserves external consistency.\<close>

lemma unfold_preserves_external_consistency:
  assumes "consistent_external ctxt \<phi>"
      and "get_total_full \<omega> = \<phi>"
      and "red_stmt_total ctxt R \<Lambda> (Unfold pred_id e_args (PureExp e_p)) \<omega> (RNormal \<omega>')"
      and "get_total_full \<omega>' = \<phi>'"
    shows "consistent_external ctxt \<phi>'"
proof -
  obtain vs v_p where
    "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some vs)" and
    "ctxt, (Some \<omega>) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
    "unfold_rel ctxt pred_id vs (Abs_preal v_p) (get_total_full \<omega>) \<phi>'" and
    "\<omega>' = \<omega>\<lparr> get_total_full := \<phi>' \<rparr>"
    using assms
    by (auto elim: RedUnfold_case)
  then obtain nm nm' where
    "shift_up pred_id vs (Abs_preal v_p) nm nm'" and
    nm: "get_nm_total \<phi> = nm" and
    \<phi>'_nm: "get_nm_total \<phi>' = nm'" and
    hh_unchanged: "get_hh_total \<phi>' = get_hh_total \<phi>"
    using assms(2) unfold_rel.simps by blast
  then obtain mh mp fnm pnm p mp' fnm' nm'_sub where
    nm_decomp: "nm = NM mh mp fnm" and
    pnm: "Some pnm = fnm (pred_id,vs)" and
    p: "p = mp (pred_id,vs)" and
    "Abs_preal v_p \<le> p" and
    "Abs_preal v_p \<noteq> 0" and
    mp': "mp' = mp( (pred_id,vs) := p - Abs_preal v_p )" and
    fnm': "fnm' = fnm( (pred_id,vs) := if Abs_preal v_p = p then None else Some (nested_mask_multiply pnm ((p - Abs_preal v_p) / p)) )" and
    nm'_sub: "nm'_sub = NM mh mp' fnm'" and
    nm': "nm' = nested_mask_merge nm'_sub (nested_mask_multiply pnm (Abs_preal v_p / p))"
    by (auto elim: shift_up_case)

  have "Abs_preal v_p \<noteq> p \<Longrightarrow> consistent_external ctxt (\<phi>\<lparr> get_nm_total := nested_mask_multiply pnm ((p - Abs_preal v_p) / p) \<rparr>)"
  proof -
    assume "Abs_preal v_p \<noteq> p"
    hence "Abs_preal v_p > 0"
      using \<open>Abs_preal v_p \<noteq> 0\<close> preal_not_0_gt_0 by blast
    have "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := pnm \<rparr>) (pred_id,vs) p"
      using assms(1) nm nm_decomp pnm p SatAll_case by fastforce
    hence "consistent_external ctxt (\<phi>\<lparr> get_nm_total := pnm \<rparr>)"
      using SatStep_case by blast
    moreover have "(p - Abs_preal v_p) / p > 0" \<comment> \<open>Simple lemma but hard to prove\<close>
    proof -
      have "p - Abs_preal v_p > 0"
        by (metis \<open>Abs_preal v_p \<le> p\<close> \<open>Abs_preal v_p \<noteq> p\<close> add_0 greater_minus_plus pperm_pnone_pgt)
      thus ?thesis
        using \<open>pos_perm_class.pnone < Abs_preal v_p\<close> divide_preal.rep_eq less_preal.rep_eq minus_preal.rep_eq preal_not_0_gt_0 zero_preal.rep_eq by fastforce
    qed
    moreover have *: "\<phi>\<lparr> get_nm_total := nested_mask_multiply pnm ((p - Abs_preal v_p) / p) \<rparr>
                 = mult_nm_total (\<phi>\<lparr> get_nm_total := pnm \<rparr>) ((p - Abs_preal v_p) / p)"
      by simp
    ultimately show ?thesis
      using fraction_consistent_external(2)[of "(p - Abs_preal v_p) / p" ctxt "\<phi>\<lparr> get_nm_total := pnm \<rparr>"]
      by presburger
  qed

  have nm'_sub_consistent: "consistent_external ctxt (\<phi>\<lparr> get_nm_total := nm'_sub \<rparr>)"
    apply (rule SatAll)
     apply simp
  proof -
    have *: "\<And>pred_id vs. (get_mp_nm nm (pred_id, vs) = 0) = (get_fnm_nm nm (pred_id, vs) = None)"
      by (metis SatAll_case assms(1) nm)
    show "\<And>pred_id vs. (get_mp_nm nm'_sub (pred_id, vs) = 0) = (get_fnm_nm nm'_sub (pred_id, vs) = None)"
    proof -
      fix pred_id vs
      have "(mp' (pred_id,vs) = 0) = (fnm' (pred_id,vs) = None)"
        apply (cases "Abs_preal v_p = p")
        using * fnm' minus_preal.abs_eq mp' nm_decomp zero_preal_def apply auto[1]
        using * \<open>Abs_preal v_p \<le> p\<close> fnm' greater_minus_plus mp' nm_decomp by fastforce
      thus "(get_mp_nm nm'_sub (pred_id, vs) = 0) = (get_fnm_nm nm'_sub (pred_id, vs) = None)"
        by (simp add: nm'_sub)
    qed
    show "\<And>pred_id vs q nm'.
             get_mp_total (\<phi>\<lparr>get_nm_total := nm'_sub\<rparr>) (pred_id, vs) = q \<Longrightarrow>
             Some nm' = TotalStateUtil.get_nm_loc_total (\<phi>\<lparr>get_nm_total := nm'_sub\<rparr>) (pred_id, vs) \<Longrightarrow>
             consistent_external_wrt_ploc ctxt (\<phi>\<lparr>get_nm_total := nm'_sub, get_nm_total := nm'\<rparr>) (pred_id, vs) q"
    proof -
      fix pred_id' vs' q nm''
      assume pred_perm: "get_mp_total (\<phi>\<lparr>get_nm_total := nm'_sub\<rparr>) (pred_id', vs') = q" and
             nm'': "Some nm'' = TotalStateUtil.get_nm_loc_total (\<phi>\<lparr>get_nm_total := nm'_sub\<rparr>) (pred_id', vs')"
      show "consistent_external_wrt_ploc ctxt (\<phi>\<lparr>get_nm_total := nm'_sub, get_nm_total := nm''\<rparr>) (pred_id', vs') q"
      proof (cases "(pred_id',vs') = (pred_id,vs)")
        case True
        hence [simp]: "nm'' = nested_mask_multiply pnm ((p - Abs_preal v_p) / p)"
          by (smt (verit) TotalStateUtil.get_nm_loc_total.simps fnm' fun_upd_same get_fnm_nm.simps get_fnm_total.simps nm'' nm'_sub option.distinct(1) option.inject total_state.select_convs(2) total_state.surjective total_state.update_convs(2))
        hence "p > Abs_preal v_p"
          using True \<open>Abs_preal v_p \<le> p\<close> fnm' nm'' nm'_sub order_le_imp_less_or_eq by fastforce
        moreover have "0 < (p - Abs_preal v_p) / p"
        proof -
          have "p - Abs_preal v_p > 0"
            by (metis \<open>Abs_preal v_p \<le> p\<close> add_0 calculation greater_minus_plus order_less_irrefl pperm_pnone_pgt)
          thus ?thesis
            by (metis Rep_preal_inverse \<open>Abs_preal v_p \<le> p\<close> divide_eq_0_iff divide_preal.rep_eq leD pperm_pnone_pgt psub_smaller zero_preal.rep_eq)
        qed
        moreover from True have [simp]: "q = p - Abs_preal v_p"
          using mp' nm'_sub pred_perm by force
        moreover have pnm_consistent: "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := pnm \<rparr>) (pred_id, vs) p"
          using SatAll_case assms(1) nm nm_decomp p pnm by fastforce
        moreover have "(p - Abs_preal v_p) / p * p = p - Abs_preal v_p"
          by (metis * Rep_preal_inverse divide_preal.rep_eq get_fnm_nm.simps get_mp_nm.simps nm_decomp nonzero_eq_divide_eq option.distinct(1) p pnm times_preal.rep_eq zero_preal.abs_eq)
        ultimately show ?thesis
          using pnm_consistent
                fraction_consistent_external(1)[of "(p - Abs_preal v_p) / p" ctxt "\<phi>\<lparr>get_nm_total := pnm\<rparr>" pred_id vs p]
          by (simp add: True)
      next
        case False
        then show ?thesis
          using SatAll_case nm'' pred_perm assms(1) fnm' mp' nm nm'_sub nm_decomp total_state.select_convs(2) by fastforce
      qed
    qed
  qed

  \<comment> \<open>The shifted part\<close>
  have shift_consistent: "consistent_external ctxt (\<phi>\<lparr> get_nm_total := nested_mask_multiply pnm (Abs_preal v_p / p) \<rparr>)"
  proof -
    have "consistent_external ctxt (\<phi>\<lparr> get_nm_total := pnm \<rparr>)"
      by (metis TotalStateUtil.get_nm_loc_total.simps assms(1) consistent_external.cases consistent_external_wrt_ploc.cases get_fnm_nm.simps get_fnm_total.simps nm nm_decomp pnm)
    moreover have "Abs_preal v_p / p > 0"
      by (metis Rep_preal_inverse \<open>Abs_preal v_p \<le> p\<close> \<open>Abs_preal v_p \<noteq> pos_perm_class.pnone\<close> divide_eq_0_iff divide_preal.rep_eq leD preal_not_0_gt_0 zero_preal.rep_eq)
    ultimately show ?thesis
      using fraction_consistent_external(2)[of "Abs_preal v_p / p" ctxt "\<phi>\<lparr> get_nm_total := pnm \<rparr>"]
      by simp
  qed

  \<comment> \<open>Use combinability\<close>
  have "\<phi>' = \<phi>\<lparr> get_nm_total := nested_mask_merge nm'_sub (nested_mask_multiply pnm (Abs_preal v_p / p)) \<rparr>"
    using \<phi>'_nm hh_unchanged nm' by force
  show ?thesis
    using nm'_sub_consistent
    by (metis (full_types) shift_consistent \<phi>'_nm hh_unchanged nm' old.unit.exhaust sum_consistent_external total_state.surjective total_state.update_convs(2))
qed


\<comment> \<open>Field assignment preserves external state consistency.\<close>

\<comment> \<open>Begin: self-framing\<close>

definition assertion_framing_state :: "'a total_context \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where
    "assertion_framing_state ctxt A \<omega> \<equiv>
      \<forall> res. red_inhale ctxt A \<omega> res \<longrightarrow> res \<noteq> RFailure"

definition assertion_self_framing_store :: "'a total_context \<Rightarrow> assertion \<Rightarrow> 'a store \<Rightarrow> bool"
  where
    "assertion_self_framing_store ctxt A \<sigma> \<equiv>
      \<forall> \<omega>. assertion_framing_state ctxt A (update_store_total \<omega> \<sigma>)"

definition pred_self_framing :: "'a total_context \<Rightarrow> predicate_decl => bool"
  where
    "pred_self_framing ctxt pred_decl = True"

lemma assertion_framing_star:
  assumes "assertion_framing_state ctxt (A1 && A2) \<omega>"
  shows "assertion_framing_state ctxt A1 \<omega> \<and>
        (\<forall> \<omega>'. red_inhale ctxt A1 \<omega> (RNormal \<omega>') \<longrightarrow> assertion_framing_state ctxt A2 \<omega>')" (is "?Goal1 \<and> ?Goal2")
proof
  show "assertion_framing_state ctxt A1 \<omega>"
    unfolding assertion_framing_state_def
  proof (rule allI | rule impI)+
    fix res
    assume "red_inhale ctxt A1 \<omega> res"

    thus "res \<noteq> RFailure"
      using assms InhStarFailureMagic assertion_framing_state_def
      by blast
  qed
next
  show ?Goal2
  proof (rule allI | rule impI)+
    fix \<omega>'
    assume InhA1: "red_inhale ctxt A1 \<omega> (RNormal \<omega>')"
    show "assertion_framing_state ctxt A2 \<omega>'"
      unfolding assertion_framing_state_def
      using InhA1 InhStarNormal assertion_framing_state_def assms by blast
  qed
qed

lemma assertion_framing_imp:
  assumes "assertion_framing_state ctxt (Imp e A) \<omega>"
     and "ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool True))"
   shows "assertion_framing_state ctxt A \<omega>"
  using assms
  unfolding assertion_framing_state_def
  by (auto intro: InhImpTrue)

lemma assertion_framing_cond_assert_true:
  assumes "assertion_framing_state ctxt (CondAssert e A B) \<omega>"
      and "ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool True))"
    shows "assertion_framing_state ctxt A \<omega>"
  using assms
  unfolding assertion_framing_state_def
  by (auto intro: InhCondAssertTrue)

lemma assertion_framing_cond_assert_false:
  assumes "assertion_framing_state ctxt (CondAssert e A B) \<omega>"
      and "ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool False))"
    shows "assertion_framing_state ctxt B \<omega>"
  using assms
  unfolding assertion_framing_state_def
  by (auto intro: InhCondAssertFalse)

\<comment> \<open>End: self-framing\<close>

lemma field_assignment_no_perm_PEC:
  assumes "consistent_external ctxt \<phi>"
      and "nm_loc_sum loc (get_nm_total \<phi>) 0"
      and "\<And>pred_id pred_decl.
              ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl \<Longrightarrow>
              pred_self_framing ctxt pred_decl"
    shows "consistent_external_wrt_ploc ctxt \<phi> (pred_id,vs) p \<Longrightarrow>
           consistent_external_wrt_ploc ctxt (update_hh_loc_total \<phi> loc v) (pred_id,vs) p"
      and "consistent_external ctxt \<phi> \<Longrightarrow>
           consistent_external ctxt (update_hh_loc_total \<phi> loc v)"
proof (induct rule: consistent_external_wrt_ploc_consistent_external.inducts)
  case (SatStep pred_id pred_decl pred_body vs \<phi> p)
  then show ?case sorry
next
  case (SatAll \<phi>)
  then show ?case sorry
qed


lemma field_assignment_preserves_external_consistency':
  assumes "consistent_external ctxt \<phi>"
      and "consistent_internal (get_nm_total \<phi>)"
      and "get_mh_total \<phi> loc = 1"
      and "\<And>pred_id pred_decl.
              ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl \<Longrightarrow>
              pred_self_framing ctxt pred_decl"
    shows "consistent_external ctxt (update_hh_loc_total \<phi> loc v)"
proof -
  have zero_perm: "\<And>ploc nm. get_nm_loc_total \<phi> ploc = Some nm \<Longrightarrow> nm_loc_sum loc nm 0" sorry
  show ?thesis
    apply standard
    using assms(1) SatAll_case[of ctxt \<phi>]
     apply fastforce
  proof -
    fix pred_id vs q nm'
    assume "get_mp_total (update_hh_loc_total \<phi> loc v) (pred_id, vs) = q"
       and nm': "Some nm' = get_nm_loc_total (update_hh_loc_total \<phi> loc v) (pred_id, vs)"
    hence "get_mp_total \<phi> (pred_id, vs) = q"
      and "Some nm' = get_nm_loc_total \<phi> (pred_id, vs)"
      by simp+
    moreover hence "consistent_external_wrt_ploc ctxt (\<phi>\<lparr>get_nm_total := nm'\<rparr>) (pred_id, vs) q"
      by (metis assms(1) consistent_external.cases)
    moreover have "update_hh_loc_total \<phi> loc v\<lparr>get_nm_total := nm'\<rparr> = update_hh_loc_total (\<phi>\<lparr>get_nm_total := nm'\<rparr>) loc v"
      by simp
    ultimately show "consistent_external_wrt_ploc ctxt (update_hh_loc_total \<phi> loc v\<lparr>get_nm_total := nm'\<rparr>) (pred_id, vs) q"
      by (metis assms(4) consistent_external_wrt_ploc.cases field_assignment_no_perm_PEC(1) total_state_update_nm_read zero_perm)
  qed
qed


end
