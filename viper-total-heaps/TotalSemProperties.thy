section \<open>Basic Properties of THSem\<close>

text \<open>This file contains lemmas that can be proved using only the semantics.
  More complex lemmas are contained in \<open>TotalSemanticsProperties.thy\<close>.\<close>

theory TotalSemProperties
  imports TotalSemantics TotalInternalConsistency
begin


subsection \<open>Auxiliary lemmas\<close>

lemma pure_exp_pred_subexp:
  assumes "pure_exp_pred p e"
  shows "list_all (pure_exp_pred p) (sub_pure_exp_total e)"
  using assms
  by (cases e) simp_all

lemma atomic_assert_pred_subexp:
  assumes "atomic_assert_pred p_atm p_e atm"
  shows "list_all (pure_exp_pred p_e) (sub_expressions_atomic atm)"
  using assms
  apply (cases atm)
    apply simp_all  
  apply (metis atomic_assert_pred_rec.simps(2) atomic_assert_pred_rec.simps(3) list.pred_inject(1) list.pred_inject(2) pure_exp_pred.simps sub_expressions_exp_or_wildcard.cases sub_expressions_exp_or_wildcard.simps(1) sub_expressions_exp_or_wildcard.simps(2))
  by (metis atomic_assert_pred_rec.simps(4) atomic_assert_pred_rec.simps(5) list.pred_inject(1) list.pred_inject(2) sub_expressions_exp_or_wildcard.cases sub_expressions_exp_or_wildcard.simps(1) sub_expressions_exp_or_wildcard.simps(2))

lemma assert_pred_atomic_subexp:
  assumes "assert_pred p_assert p_atm p_e (Atomic atm)"
  shows "list_all (pure_exp_pred p_e) (sub_expressions_atomic atm)"
  using assms atomic_assert_pred_subexp
  by simp

lemma assert_pred_subexp:
  assumes "assert_pred p_assert p_atm p_e A"
  shows "list_all (pure_exp_pred p_e) (direct_sub_expressions_assertion A)"
  apply (cases A)
          apply simp_all
  using assert_pred_atomic_subexp assms
    apply blast
  using assms
  by simp_all

lemma free_var_subexp:
  shows "\<Union> (set (map free_var_pure_exp (sub_pure_exp_total e))) \<subseteq> free_var_pure_exp e"
  by (cases e) auto  


lemma less_eq_valid_locs_subset_total_state:
  assumes "\<omega> \<le> \<omega>'"
  shows "get_valid_locs \<omega> \<subseteq> get_valid_locs \<omega>'"
proof -
  from \<open>\<omega> \<le> \<omega>'\<close> have "get_mh_total_full \<omega> \<le> get_mh_total_full \<omega>'" (is "?m \<le> ?m'")
    using less_eq_full_total_stateD_2 less_eq_nested_maskD
    by auto

  show ?thesis
  proof
    fix lh
    assume "lh \<in> get_valid_locs \<omega>"    
    hence "?m lh > 0"
      by (simp add: get_valid_locs_def)

    hence "?m' lh > 0"
      using \<open>?m \<le> ?m'\<close>
      by (meson dual_order.strict_trans1 le_funE)
    thus "lh \<in> get_valid_locs \<omega>'"
      by (simp add: get_valid_locs_def)
  qed
qed

subsection \<open>Well-typed store\<close>

lemma vpr_store_well_typed_map_upds:
  assumes StoreWellTy: "vpr_store_well_typed (absval_interp_total ctxt_vpr) \<Lambda> \<sigma>"
      and RetsTy1: "vals_well_typed (absval_interp_total ctxt_vpr) v_rets ts"
      and RetsTy2: "list_all2 (\<lambda>y t. y = Some t) (map \<Lambda> ys) ts"
    shows "vpr_store_well_typed (absval_interp_total ctxt_vpr) \<Lambda> (map_upds \<sigma> ys v_rets)"
  unfolding vpr_store_well_typed_def
proof (rule allI |rule impI)+
  fix y t
  assume "\<Lambda> y = Some t"

  have LengthEq: "length ys = length v_rets"
    using RetsTy1 RetsTy2
    unfolding vals_well_typed_def
    by (metis length_map list_all2_lengthD)

  let ?A = "absval_interp_total ctxt_vpr"
  show "map_option (get_type (absval_interp_total ctxt_vpr)) ((\<sigma>(ys [\<mapsto>] v_rets)) y) = Some t" (is "?lhs = _")
  proof (cases "y \<in> set ys")
    case True
    from this obtain i where *: "i < length ys \<and> y = ys ! i \<and> (\<sigma>(ys [\<mapsto>] v_rets)) y = Some (v_rets ! i)"
      using map_upds_lookup_element LengthEq
      by meson
    hence **: "?lhs = Some ((get_type ?A) (v_rets ! i))"
      by blast

    from * \<open>\<Lambda> y = Some t\<close> have "t = ts ! i"
      using RetsTy2
      by (simp add: list_all2_conv_all_nth)

    hence "(get_type ?A) (v_rets ! i) = t"
      using RetsTy1 * LengthEq
      unfolding vals_well_typed_def
      by force

    then show ?thesis 
      using **
      by blast
  next
    case False
    hence "?lhs = map_option (get_type (absval_interp_total ctxt_vpr)) (\<sigma> y)"
      by simp
    also have "... = Some t"
      using StoreWellTy \<open>\<Lambda> y = Some t\<close>
      unfolding vpr_store_well_typed_def
      by blast
    finally show ?thesis
      by blast
  qed
qed

lemma vpr_store_well_typed_shift:
  assumes "vpr_store_well_typed A \<Lambda> \<sigma>"
      and "get_type A v = \<tau>"
    shows "vpr_store_well_typed A (shift_and_add \<Lambda> \<tau>) (shift_and_add \<sigma> v)"
  using assms
  unfolding vpr_store_well_typed_def shift_and_add_def
  by simp

lemma vpr_store_well_typed_unshift:
  assumes "vpr_store_well_typed A (shift_and_add \<Lambda> \<tau>) \<sigma>"
  shows "vpr_store_well_typed A \<Lambda> (unshift_2 1 \<sigma>)"
  using assms
  unfolding vpr_store_well_typed_def shift_and_add_def unshift_2_def
  by simp 

subsection \<open>Expression evaluation\<close>

lemma red_exp_unop_sub_failure:
  assumes "ctxt, \<omega>def_opt \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  shows "ctxt, \<omega>def_opt \<turnstile> \<langle>Unop uop e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  apply (rule RedSubFailure)
  using assms
  by (simp add: RedExpListFailure assms)+

lemma red_exp_binop_sub_left_failure:
  assumes "ctxt, \<omega>def_opt \<turnstile> \<langle>e1; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  shows "ctxt, \<omega>def_opt \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  apply (rule RedSubFailure)
  using assms
  by (simp add: RedExpListFailure assms)+

lemma red_exp_field_sub_failure:
  assumes "ctxt, \<omega>def_opt \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  shows "ctxt, \<omega>def_opt \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  apply (rule RedSubFailure)
  using assms
  by (simp add: RedExpListFailure assms)+

lemma red_exp_condexp_sub_failure:
  assumes "ctxt, \<omega>def_opt \<turnstile> \<langle>cond; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  shows "ctxt, \<omega>def_opt \<turnstile> \<langle>CondExp cond thn els; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
  apply (rule RedSubFailure)
  using assms
  by (simp add: RedExpListFailure assms)+


inductive_cases RedCondExp_elim: "ctxt, \<omega>_def \<turnstile> \<langle>CondExp cond e1 e2; \<omega>\<rangle> [\<Down>]\<^sub>t r"
inductive_cases RedUnop_elim: "ctxt, \<omega>_def \<turnstile> \<langle>Unop uop e; \<omega>\<rangle> [\<Down>]\<^sub>t r"
inductive_cases RedBinop_elim: "ctxt, \<omega>_def \<turnstile> \<langle>Binop e1 bop e2; \<omega>\<rangle> [\<Down>]\<^sub>t r"
inductive_cases RedFieldAcc_elim: "ctxt, \<omega>_def \<turnstile> \<langle>FieldAcc e f; \<omega>\<rangle> [\<Down>]\<^sub>t r"
inductive_cases RedOld_elim: "ctxt, \<omega>_def \<turnstile> \<langle>Old lbl e; \<omega>\<rangle> [\<Down>]\<^sub>t r"
inductive_cases RedPerm_elim: "ctxt, \<omega>_def \<turnstile> \<langle>Perm e f; \<omega>\<rangle> [\<Down>]\<^sub>t r"
inductive_cases RedUnfolding_elim: "ctxt, \<omega>_def \<turnstile> \<langle>Unfolding pid es ubody; \<omega>\<rangle> [\<Down>]\<^sub>t r"


lemma shift_up_deterministic:
  assumes "shift_up pid vs p nm nm\<^sub>1"
      and "shift_up pid vs p nm nm\<^sub>2"
    shows "nm\<^sub>1 = nm\<^sub>2"
  by (smt (verit) Pair_inject assms option.inject pperm_pgt_pnone shift_up.simps)


lemma eval_single_eval_list_helper:
  assumes "\<And>e r\<^sub>1 r\<^sub>2. e \<in> set es \<Longrightarrow>
                     ctxt, \<omega>_def\<^sub>1 \<turnstile> \<langle>e;\<omega>\<^sub>1\<rangle> [\<Down>]\<^sub>t r\<^sub>1 \<Longrightarrow>
                     ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t r\<^sub>2 \<Longrightarrow> r\<^sub>1 = r\<^sub>2"
      and "red_pure_exps_total ctxt \<omega>_def\<^sub>1 es \<omega>\<^sub>1 rs\<^sub>1"
      and "red_pure_exps_total ctxt \<omega>_def\<^sub>2 es \<omega>\<^sub>2 rs\<^sub>2"
    shows "rs\<^sub>1 = rs\<^sub>2"
  using assms
proof (induction es arbitrary: rs\<^sub>1 rs\<^sub>2)
  case Nil
  then show ?case
    using RedExpListNil red_exp_list_failure_Nil
    by blast
next
  case IH: (Cons e es)
  then show ?case
    by (safe elim!: RedExpListConsGeneral_case; simp; fastforce)
qed


lemma eval_is_deterministic_single:
  assumes "ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t r\<^sub>1"
      and "ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t r\<^sub>2"
    shows "r\<^sub>1 = r\<^sub>2"
  using assms
proof (induction e arbitrary: \<omega>_def \<omega> r\<^sub>1 r\<^sub>2)
  case IH: (Unop uop e)
  then show ?case
    by (safe elim!: RedUnop_elim; simp; fastforce elim: red_pure_exps_total_singleton)
next
  case IH: (Binop e1 bop e2)
  then show ?case
    by (safe elim!: RedBinop_elim; simp; fastforce elim: red_pure_exps_total_singleton)
next
  case IH: (CondExp cond e1 e2)
  then show ?case
    by (safe elim!: RedCondExp_elim; simp; blast elim: red_pure_exps_total_singleton)
next
  case (FieldAcc e f)
  then show ?case
    by (safe elim!: RedFieldAcc_elim; simp; blast elim: red_pure_exps_total_singleton)
next
  case (Old lbl e)
  then show ?case
    by (safe elim!: RedOld_elim; simp; blast elim: red_pure_exps_total_singleton)
next
  case (Perm e f)
  then show ?case
    by (safe elim!: RedPerm_elim; simp; blast elim: red_pure_exps_total_singleton)
next
  case IH: (Unfolding pid es ubody)
  show ?case
  proof (cases \<omega>_def)
    case None
    show ?thesis
      using IH[unfolded \<open>\<omega>_def = _\<close>] eval_single_eval_list_helper
      by (smt (verit, best) RedUnfolding_elim option.distinct(1) sub_pure_exp_total.simps(9))
  next
    case (Some \<omega>\<^sub>0)
    then show ?thesis
      using IH
      apply (safe elim!: RedUnfolding_elim; simp)
      by (metis eval_single_eval_list_helper order_less_le option.sel option.distinct(1) shift_up_deterministic)+
  qed
qed (fastforce intro: red_pure_exp_intros elim: red_pure_exp_total.cases)+


lemma eval_is_deterministic:
  shows "ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t r\<^sub>1 \<Longrightarrow>
         ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t r\<^sub>2 \<Longrightarrow>
         r\<^sub>1 = r\<^sub>2"
    and "red_pure_exps_total ctxt \<omega>_def es \<omega> rs\<^sub>1 \<Longrightarrow>
         red_pure_exps_total ctxt \<omega>_def es \<omega> rs\<^sub>2 \<Longrightarrow>
         rs\<^sub>1 = rs\<^sub>2"
  using eval_is_deterministic_single eval_single_eval_list_helper
  by blast+


subsubsection \<open>Main lemmas\<close>

\<comment>\<open>The generalization of the following lemma to function calls will require a condition on the function interpretation,
   which states how the well-definedness of functions is affected when adjusting the well-definedness state.\<close>

lemma red_pure_exp_different_def_state:
  shows "ctxt, \<omega>def_opt \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t res \<Longrightarrow>
           res = Val v \<Longrightarrow>
           no_perm_pure_exp e \<and> no_unfolding_pure_exp e \<Longrightarrow>
           ctxt, \<omega>def_opt' \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v \<or> ctxt, \<omega>def_opt' \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t VFailure" and
          "red_pure_exps_total ctxt \<omega>def_opt es \<omega> resES \<Longrightarrow>
           resES = Some vs \<Longrightarrow>
           list_all (\<lambda>e. no_perm_pure_exp e \<and> no_unfolding_pure_exp e) es \<Longrightarrow>
           red_pure_exps_total ctxt \<omega>def_opt' es \<omega> (Some vs) \<or> red_pure_exps_total ctxt \<omega>def_opt' es \<omega> None"
proof (induction arbitrary: v \<omega>def_opt' and vs \<omega>def_opt' rule: red_pure_exp_inducts)
  case (RedLit \<omega>_def l uu)
  then show ?case 
    by (auto intro: red_pure_exp_intros)
next
  case (RedVar \<omega> n v \<omega>_def)
  then show ?case 
    by (auto intro: red_pure_exp_intros)
next
  case (RedResult \<omega> v \<omega>_def)
  then show ?case 
    by (auto intro: red_pure_exp_intros)
next
  case (RedBinopLazy \<omega>_def e1 \<omega> v1 bop v e2)
  from this consider (Normal) "ctxt, \<omega>def_opt' \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1" | 
                     (Failure) "ctxt, \<omega>def_opt' \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by auto
  then show ?case 
  proof cases
    case Normal
    then show ?thesis 
      using RedBinopLazy
      by (auto intro: red_pure_exp_intros)
  next
    case Failure  
    have "ctxt, \<omega>def_opt' \<turnstile> \<langle>Binop e1 bop e2;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
      apply (rule RedSubFailure)
      by (auto intro: red_pure_exp_intros Failure)      
    thus ?thesis 
      by simp
  qed    
next
  case (RedBinop \<omega>_def e1 \<omega> v1 e2 v2 bop v3)
  from this consider (NormalE1) "ctxt, \<omega>def_opt' \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1" |
                     (FailureE1) "ctxt, \<omega>def_opt' \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by fastforce
  then show ?case 
  proof cases
    case NormalE1   
    from RedBinop consider (NormalE2) "ctxt, \<omega>def_opt' \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v2" |
                           (FailureE2) "ctxt, \<omega>def_opt' \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure" 
      by auto
    then show ?thesis 
    proof (cases)
      case NormalE2
      show ?thesis using NormalE1 RedBinop(5-8)
        apply (subgoal_tac "eval_binop (Option.is_none \<omega>def_opt') v1 bop v2 = BinopNormal v \<or>
                            eval_binop (Option.is_none \<omega>def_opt') v1 bop v2 = BinopOpFailure")
        using NormalE2 RedBinopOpFailure red_pure_exp_total_red_pure_exps_total.RedBinop
         apply blast
        by (simp add: eval_total_non_total_same_or_fail)
    next
      case FailureE2
      have "ctxt, \<omega>def_opt' \<turnstile> \<langle>Binop e1 bop e2;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
        apply (rule RedBinopRightFailure)
           apply (rule NormalE1)
          apply (rule FailureE2)
        using RedBinop
         apply blast
        by (metis RedBinop.hyps(2) binop_result.distinct(1) binop_result.distinct(3) eval_total_non_total_same_or_fail)
      thus ?thesis
        by simp
    qed      
  next
    case FailureE1
    then show ?thesis 
      by (blast intro: red_exp_binop_sub_left_failure)      
  qed
next
  case (RedBinopRightFailure \<omega>_def e1 \<omega> v1 e2 bop)
  then show ?case by simp \<comment>\<open>cannot occur\<close>
next
  case (RedBinopOpFailure \<omega>_def e1 \<omega> v1 e2 v2 bop)
  then show ?case by simp \<comment>\<open>cannot occur\<close>
next
  case (RedUnop \<omega>_def e \<omega> v1 unop v2)
  from this consider (Normal) "ctxt, \<omega>def_opt' \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1" |
                     (Failure) "ctxt, \<omega>def_opt' \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by fastforce
  thus ?case
  proof cases
    case Normal
    with RedUnop show ?thesis 
    by (auto intro: red_pure_exp_intros)      
  next
    case Failure
    then show ?thesis 
      by (auto intro: red_exp_unop_sub_failure)
  qed
next
  case (RedCondExpTrue \<omega>_def e1 \<omega> e2 r e3)
  then show ?case 
    using red_exp_condexp_sub_failure TotalExpressions.RedCondExpTrue
    by fastforce
next
  case (RedCondExpFalse \<omega>_def e1 \<omega> e3 r e2)
  then show ?case 
    using red_exp_condexp_sub_failure TotalExpressions.RedCondExpFalse
    by fastforce
next
  case (RedOld \<omega> l \<phi> \<omega>_def e v)
  then show ?case 
  by (auto intro: red_pure_exp_intros)
next
  case (RedOldFailure \<omega> l \<omega>_def e)
  then show ?case by simp \<comment>\<open>cannot occur\<close>
next
  case (RedField \<omega>_def e \<omega> a f v1)
  from this consider (NormalRef) "ctxt, \<omega>def_opt' \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))"
                   | (FailRef) "ctxt, \<omega>def_opt' \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by auto
  then show ?case
  proof cases
    case NormalRef
    show ?thesis
     using NormalRef RedField TotalExpressions.RedField
     by (fastforce split: if_split if_split_asm)
  next
    case FailRef
    then show ?thesis 
      by (blast intro: red_exp_field_sub_failure)
  qed
next
  case (RedFieldNullFailure \<omega>_def e \<omega> f)
  then show ?case by simp \<comment>\<open>cannot occur\<close>
next
  case (RedPermNull \<omega>_def e \<omega> f)
  then show ?case by auto \<comment>\<open>cannot occur\<close>    
next
  case (RedPerm \<omega>_def e \<omega> a f v)
  then show ?case by auto \<comment>\<open>cannot occur\<close>    
next
  case (RedUnfolding ubody \<omega> v p es)
  then show ?case by auto \<comment>\<open>cannot occur\<close>    
next
  case (RedUnfoldingDefNoPred \<omega>_def es \<omega> vs pred_id pred_decl p ubody)
  then show ?case by auto \<comment>\<open>cannot occur\<close>    
next
  case (RedUnfoldingDef \<omega>_def es \<omega> vs p \<omega>'_def ubody v)
  then show ?case by auto \<comment>\<open>cannot occur\<close>    
next
  case (RedSubFailure e' \<omega>_def \<omega>)
  then show ?case by simp \<comment>\<open>cannot occur\<close>
next
  case (RedExpListCons \<omega>_def e \<omega> v es res res')
  from this consider (NormalHd) "ctxt, \<omega>def_opt' \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v" |
                     (FailHd) "ctxt, \<omega>def_opt' \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t VFailure"
    by auto
  then show ?case 
  proof cases
    case NormalHd
    from RedExpListCons obtain vs' where "vs = v#vs'" and "res = Some vs'"
      by blast
   
    with RedExpListCons consider
        (NormalTl) "red_pure_exps_total ctxt \<omega>def_opt' es \<omega> (Some vs')"
      | (FailTl) "red_pure_exps_total ctxt \<omega>def_opt' es \<omega> None"
      by auto

    then show ?thesis
    proof cases
      case NormalTl
      then show ?thesis 
        using NormalHd \<open>vs = _\<close>
        by (auto intro: red_pure_exp_intros)
    next
      case FailTl
      then show ?thesis 
      using NormalHd
      by (auto intro: red_pure_exp_intros)
    qed
  next
    case FailHd
    then show ?thesis 
      by (auto intro: red_pure_exp_intros)      
  qed
next
  case (RedExpListFailure \<omega>_def e \<omega> es)
  then show ?case by simp \<comment>\<open>cannot occur\<close>
next
  case (RedExpListNil \<omega>_def \<omega>)
  then show ?case 
  by (auto intro: red_pure_exp_intros)
qed


\<comment>\<open>The generalization of the following lemma to function calls will require a restriction on the function interpretation,
   which states that the mask has no effect on function values.\<close>

lemma red_pure_exp_only_differ_on_mask:
  shows "ctxt, \<omega>def_opt \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t resE \<Longrightarrow>
         no_perm_pure_exp e \<and> no_unfolding_pure_exp e \<Longrightarrow>
         get_store_total \<omega> = get_store_total \<omega>' \<and> 
         get_trace_total \<omega> = get_trace_total \<omega>' \<and>
         get_hh_total_full \<omega> = get_hh_total_full \<omega>' \<Longrightarrow>
         ctxt, \<omega>def_opt \<turnstile> \<langle>e; \<omega>'\<rangle> [\<Down>]\<^sub>t resE" and
        "red_pure_exps_total ctxt \<omega>def_opt es \<omega> resES \<Longrightarrow>
                 list_all (\<lambda>e. no_perm_pure_exp e \<and> no_unfolding_pure_exp e) es \<Longrightarrow>
                 get_store_total \<omega> = get_store_total \<omega>' \<and> 
                 get_trace_total \<omega> = get_trace_total \<omega>' \<and>
                 get_hh_total_full \<omega> = get_hh_total_full \<omega>' \<Longrightarrow>
                 red_pure_exps_total ctxt \<omega>def_opt es \<omega>' resES"
proof (induction arbitrary: \<omega>' and \<omega>' rule: red_pure_exp_inducts)
  case (RedLit \<omega>_def l uu)
  then show ?case 
    by (auto intro: red_pure_exp_intros)
next
  case (RedVar \<omega> n v \<omega>_def)
  then show ?case 
    by (auto intro: red_pure_exp_intros)
next
  case (RedResult \<omega> v \<omega>_def)
  then show ?case 
    by (auto intro: red_pure_exp_intros)
next
  case (RedBinopLazy \<omega>_def e1 \<omega> v1 bop v e2)
  then show ?case 
    by (auto intro: red_pure_exp_intros)
next
  case (RedBinop \<omega>_def e1 \<omega> v1 e2 v2 bop v)
  then show ?case 
  by (auto intro: red_pure_exp_intros)
next
  case (RedBinopRightFailure \<omega>_def e1 \<omega> v1 e2 bop)
  then show ?case 
  by (auto intro: red_pure_exp_intros)
next
  case (RedBinopOpFailure \<omega>_def e1 \<omega> v1 e2 v2 bop)
  then show ?case 
  by (auto intro: red_pure_exp_intros)
next
  case (RedUnop \<omega>_def e \<omega> v unop v')
  then show ?case 
  by (auto intro: red_pure_exp_intros)
next
  case (RedCondExpTrue \<omega>_def e1 \<omega> e2 r e3)
  then show ?case 
  by (auto intro: red_pure_exp_intros)
next
  case (RedCondExpFalse \<omega>_def e1 \<omega> e3 r e2)
  then show ?case 
  by (auto intro: red_pure_exp_intros)
next
  case (RedOld \<omega> l \<phi> \<omega>_def e v)
  then show ?case
  by (auto intro: red_pure_exp_intros)
next
  case (RedOldFailure \<omega> l \<omega>_def e)
  then show ?case
  by (auto intro: red_pure_exp_intros)
next
  case (RedField \<omega>_def e \<omega> a f v)
  hence "get_hh_total_full \<omega>' (a,f) = v"
    by simp

  moreover from RedField have "ctxt, \<omega>_def \<turnstile> \<langle>e;\<omega>'\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))"
    by simp

  ultimately show ?case 
    by (fastforce intro: TotalExpressions.RedField)
next
  case (RedFieldNullFailure \<omega>_def e \<omega> f)
  then show ?case 
    by (auto intro: red_pure_exp_intros)
next
  case (RedPermNull \<omega>_def e \<omega> f)
  then show ?case by auto \<comment>\<open>cannot occur\<close>    
next
  case (RedPerm \<omega>_def e \<omega> a f v)
  then show ?case by auto \<comment>\<open>cannot occur\<close>    
next
  case (RedUnfolding ubody \<omega> v p es)
  then show ?case by auto \<comment>\<open>cannot occur\<close>    
next
  case (RedUnfoldingDefNoPred \<omega>_def es \<omega> vs pred_id p ubody)
  then show ?case by auto \<comment>\<open>cannot occur\<close>    
next
  case (RedUnfoldingDef \<omega>_def es \<omega> vs p \<omega>'_def ubody v)
  then show ?case by auto \<comment>\<open>cannot occur\<close>    
next
  case (RedSubFailure e' \<omega>_def \<omega>)
  from \<open>no_perm_pure_exp e' \<and> no_unfolding_pure_exp e'\<close> have
     "list_all (\<lambda>e. no_perm_pure_exp e) (sub_pure_exp_total e')" and
     "list_all (\<lambda>e. no_unfolding_pure_exp e) (sub_pure_exp_total e')"
    using pure_exp_pred_subexp
    by blast+
  hence "list_all (\<lambda>e. no_perm_pure_exp e \<and> no_unfolding_pure_exp e) (sub_pure_exp_total e')"
    by (simp add: list_all_length)    
  with RedSubFailure show ?case 
  by (auto intro: red_pure_exp_intros)    
next
  case (RedExpListCons \<omega>_def e \<omega> v es res res')
  then show ?case 
    by (auto intro: red_pure_exp_intros)
next
  case (RedExpListFailure \<omega>_def e \<omega> es)
  then show ?case 
  by (auto intro: red_pure_exp_intros)
next
  case (RedExpListNil \<omega>_def \<omega>)
  then show ?case 
  by (auto intro: red_pure_exp_intros)
qed


subsection \<open>Inhale\<close>

text \<open>Inhale only changes mask\<close>

lemma inhale_perm_single_store_same:
  assumes  "\<omega>' \<in> inhale_perm_single R \<omega> lh popt"
  shows "get_store_total \<omega>' = get_store_total \<omega>"
  using assms
  unfolding inhale_perm_single_def
  by auto

lemma inhale_perm_single_trace_same:
  assumes  "\<omega>' \<in> inhale_perm_single R \<omega> lh popt"
  shows "get_trace_total \<omega>' = get_trace_total \<omega>"
  using assms
  unfolding inhale_perm_single_def
  by auto

lemma inhale_perm_single_heap_same:
  assumes  "\<omega>' \<in> inhale_perm_single R \<omega> lh popt"
  shows "get_hh_total_full \<omega>' = get_hh_total_full \<omega>"
  using assms
  unfolding inhale_perm_single_def
  by fastforce

lemma inhale_perm_single_pred_store_same:
  assumes  "\<omega>' \<in> inhale_perm_single_pred ctxt R \<omega> lh popt"
  shows "get_store_total \<omega>' = get_store_total \<omega>"
  using assms
  unfolding inhale_perm_single_pred_def
  by auto

lemma inhale_perm_single_pred_trace_same:
  assumes  "\<omega>' \<in> inhale_perm_single_pred ctxt R \<omega> lh popt"
  shows "get_trace_total \<omega>' = get_trace_total \<omega>"
  using assms
  unfolding inhale_perm_single_pred_def
  by auto

lemma inhale_perm_single_pred_heap_same:
  assumes  "\<omega>' \<in> inhale_perm_single_pred ctxt R \<omega> lh popt"
  shows "get_hh_total_full \<omega>' = get_hh_total_full \<omega>"
  using assms 
  unfolding inhale_perm_single_pred_def
  by fastforce

lemmas inhale_perm_single_only_mask_changed=
  inhale_perm_single_store_same
  inhale_perm_single_trace_same
  inhale_perm_single_heap_same

lemmas inhale_perm_pred_single_only_mask_changed=
  inhale_perm_single_pred_store_same
  inhale_perm_single_pred_trace_same
  inhale_perm_single_pred_heap_same

lemma inhale_only_changes_mask:
  shows "red_inhale ctxt R A \<omega> res \<Longrightarrow> (\<And>\<omega>'. res = RNormal \<omega>' \<Longrightarrow> 
             get_store_total \<omega>' = get_store_total \<omega> \<and>
             get_trace_total \<omega>' = get_trace_total \<omega> \<and>
             get_hh_total_full \<omega>' = get_hh_total_full \<omega>)"
proof (induction rule: red_inhale.inducts)
  case (InhAcc \<omega> e_r r e_p p W' f res)
  then show ?case 
    by (metis inhale_perm_single_only_mask_changed singleton_iff th_result_rel_normal)
next
  case (InhAccPred \<omega> e_p p e_args v_args W' pred_id res)
  then show ?case 
    using inhale_perm_pred_single_only_mask_changed th_result_rel_normal
    by metis
next
  case (InhAccWildcard \<omega> e_r r W' f res)
  then show ?case     
    by (metis inhale_perm_single_only_mask_changed th_result_rel_normal)
next
  case (InhAccPredWildcard \<omega> e_args v_args W' pred_id res)
  then show ?case
    using inhale_perm_pred_single_only_mask_changed th_result_rel_normal
    by metis
next
  case (InhPure \<omega> e b)
  then show ?case
    by (metis result_total.distinct(3) result_total.inject)
next
  case (InhSubExpFailure A \<omega>)
  then show ?case by simp
next
  case (InhStarNormal A \<omega> \<omega>'' B res)
  then show ?case by presburger
next
  case (InhStarFailureMagic A \<omega> resA B)
  then show ?case by simp
next
  case (InhImpTrue \<omega> e A res)
  then show ?case by simp
next
  case (InhImpFalse \<omega> e A)
  then show ?case by simp
next
  case (InhCondAssertTrue \<omega> e A res B)
  then show ?case by simp
next
  case (InhCondAssertFalse \<omega> e B res A)
  then show ?case by simp
qed


text \<open>inhale preserves failure for smaller states if there is no permission introspection\<close>

lemma inhale_perm_single_leq:
  assumes "\<omega>0 \<le> \<omega>1" and
          ConsistencyDownwardMono: "\<And> \<omega> \<omega>'. \<omega> \<le> \<omega>' \<Longrightarrow> R \<omega>' \<Longrightarrow> R \<omega>" 
  shows "\<forall> \<omega>1' \<in> inhale_perm_single R \<omega>1 lh p_opt. \<exists>\<omega>0' \<le> \<omega>1'. \<omega>0' \<in> inhale_perm_single R \<omega>0 lh p_opt"
proof 
  fix \<omega>1'
  assume "\<omega>1' \<in> inhale_perm_single R \<omega>1 lh p_opt"
  from this obtain p where
    "\<omega>1' = upd_mh_loc_total_full \<omega>1 lh (get_mh_total_full \<omega>1 lh + p)"  and
    PermConstraint: "option_fold ((=) p) (p \<noteq> 0) p_opt" and
    "R \<omega>1'"
    unfolding inhale_perm_single_def
    by blast

  let ?\<omega>0' = "upd_mh_loc_total_full \<omega>0 lh (get_mh_total_full \<omega>0 lh + p)"    

  from \<open>\<omega>0 \<le> \<omega>1\<close> have "(get_mh_total_full \<omega>0 lh) \<le> (get_mh_total_full \<omega>1 lh)"
    using less_eq_full_total_stateD_2
    by (auto dest: le_funD less_eq_nested_maskD)

  hence *: "get_mh_total_full \<omega>0 lh + p \<le> get_mh_total_full \<omega>1 lh + p"
    by (simp add: PosReal.padd_mono)

  hence "?\<omega>0' \<le> \<omega>1'"
    using \<open>\<omega>1' = _\<close> assms update_mh_loc_total_full_mono 
    by blast

  moreover have "?\<omega>0' \<in> inhale_perm_single R \<omega>0 lh p_opt"
    apply (rule inhale_perm_single_elem)
      apply (rule HOL.refl)
    using ConsistencyDownwardMono \<open>\<omega>1' \<in> _\<close> \<open>?\<omega>0' \<le> \<omega>1'\<close> \<open>R \<omega>1'\<close>
     apply blast
    by (rule PermConstraint)

  ultimately show "\<exists>\<omega>0'\<le>\<omega>1'. \<omega>0' \<in> inhale_perm_single R \<omega>0 lh p_opt"
    by blast   
qed

lemma inhale_perm_single_pred_leq:
  assumes "\<omega>0 \<le> \<omega>1" and
          ConsistencyDonwardMono: "\<And> \<omega> \<omega>'. \<omega> \<le> \<omega>' \<Longrightarrow> R \<omega>' \<Longrightarrow> R \<omega>" 
  shows "\<forall> \<omega>1' \<in> inhale_perm_single_pred ctxt R \<omega>1 lh p_opt. \<exists>\<omega>0' \<le> \<omega>1'. \<omega>0' \<in> inhale_perm_single_pred ctxt R \<omega>0 lh p_opt"
proof
  fix \<omega>1'
  assume "\<omega>1' \<in> inhale_perm_single_pred ctxt R \<omega>1 lh p_opt"
  from this obtain p \<phi>_inh where
    "\<omega>1' = (if p = 0 then \<omega>1 else add_to_lpm_nonzero_total_full \<omega>1 lh (Abs_posreal p) (get_nm_total \<phi>_inh))" and
    PermConstraint: "option_fold ((=) p) (p \<noteq> 0) p_opt" and
    "consistent_external_wrt_ploc ctxt \<phi>_inh lh p" and
    "get_hh_total \<phi>_inh = get_hh_total_full \<omega>1" and
    "R \<omega>1'"
    unfolding inhale_perm_single_pred_def
    by blast

  let ?\<omega>0' = "if p = 0 then \<omega>0 else add_to_lpm_nonzero_total_full \<omega>0 lh (Abs_posreal p) (get_nm_total \<phi>_inh)"    

  from \<open>\<omega>0 \<le> \<omega>1\<close> have "(get_mp_total_full \<omega>0 lh) \<le> (get_mp_total_full \<omega>1 lh)"
    using less_eq_full_total_stateD_2
    by (metis get_mp_total.simps get_mp_total_full.simps get_nm_total_full.simps le_fun_def less_eq_nested_maskD)

  hence *: "get_mp_total_full \<omega>0 lh + p \<le> get_mp_total_full \<omega>1 lh + p"
    by (simp add: PosReal.padd_mono)

  hence "?\<omega>0' \<le> \<omega>1'"
    using \<open>\<omega>1' = _\<close> assms add_to_lpm_nonzero_total_full_mono 
    by (metis (mono_tags, lifting))

  moreover have "?\<omega>0' \<in> inhale_perm_single_pred ctxt R \<omega>0 lh p_opt"
    unfolding inhale_perm_single_pred_def
    apply (rule CollectI)
    apply (rule exI[of _ ?\<omega>0'])
    apply (rule exI[of _ \<phi>_inh])
    apply (rule exI[of _ p])
    apply (intro conjI)
         apply simp
        apply fact+
    using \<open>get_hh_total \<phi>_inh = get_hh_total_full \<omega>1\<close> assms(1) less_eq_full_total_stateD_2
      apply fastforce
     apply simp
    using ConsistencyDonwardMono \<open>R \<omega>1'\<close> calculation
    by auto

  ultimately show "\<exists>\<omega>0'\<le>\<omega>1'. \<omega>0' \<in> inhale_perm_single_pred ctxt R \<omega>0 lh p_opt"
    by blast   
qed


lemma eval_no_perm_downwards_mono:
  assumes ConsistencyDownwardMono: "mono_prop_downward_ord R"
    shows "ctxt, \<omega>_def1 \<turnstile> \<langle>e;\<omega>1\<rangle> [\<Down>]\<^sub>t resE \<Longrightarrow> 
           no_perm_pure_exp e \<and> no_unfolding_pure_exp e \<Longrightarrow>
           \<omega>2 \<le> \<omega>1 \<Longrightarrow> 
           \<omega>_def2 \<le> \<omega>_def1 \<Longrightarrow>
           \<omega>_def2 = None \<longleftrightarrow> \<omega>_def1 = None \<Longrightarrow>
           (if resE = VFailure then ctxt, \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure
            else ctxt, \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure \<or> ctxt, \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t resE)" and
          "red_pure_exps_total ctxt \<omega>_def1 es \<omega>1 resES \<Longrightarrow> 
           list_all (\<lambda>e. no_perm_pure_exp e \<and> no_unfolding_pure_exp e) es \<Longrightarrow>
           \<omega>2 \<le> \<omega>1 \<Longrightarrow> 
           \<omega>_def2 \<le> \<omega>_def1 \<Longrightarrow>
           \<omega>_def2 = None \<longleftrightarrow> \<omega>_def1 = None \<Longrightarrow>
           (if resES = None then red_pure_exps_total ctxt \<omega>_def2 es \<omega>2 None
            else red_pure_exps_total ctxt \<omega>_def2 es \<omega>2 None \<or> red_pure_exps_total ctxt \<omega>_def2 es \<omega>2 resES)"
proof (induction arbitrary: \<omega>2 \<omega>_def2 and \<omega>2 \<omega>_def2 rule: red_pure_exp_inducts)
  case (RedLit \<omega>_def l uu)
  then show ?case
    by (auto intro!: red_pure_exp_intros)
next
  case (RedVar \<omega> n v \<omega>_def)
  then show ?case
    by (auto intro!: red_pure_exp_intros dest: less_eq_full_total_stateD)
next
  case (RedResult \<omega> v \<omega>_def)
  then show ?case
    by (auto intro!: red_pure_exp_intros dest: less_eq_full_total_stateD)
next
  case (RedBinopLazy \<omega>_def e1 \<omega> v1 bop v e2)
  then show ?case 
    using TotalExpressions.RedBinopLazy
    by (metis pure_exp_pred.elims(2) pure_exp_pred_rec.simps(4) red_exp_binop_sub_left_failure)
next
  case (RedBinop \<omega>_def e1 \<omega> v1 e2 v2 bop v)
  from this consider (E1Fail) "ctxt, \<omega>_def2 \<turnstile> \<langle>e1;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | 
                     (E1Normal)"ctxt, \<omega>_def2 \<turnstile> \<langle>e1;\<omega>2\<rangle> [\<Down>]\<^sub>t Val v1"
    by auto
  thus ?case 
  proof (cases)
    case E1Fail
    thus ?thesis
      by (simp add: red_exp_binop_sub_left_failure)
  next
    case E1Normal
    from RedBinop consider  (E2Fail) "ctxt, \<omega>_def2 \<turnstile> \<langle>e2;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | 
                            (E2Normal)"ctxt, \<omega>_def2 \<turnstile> \<langle>e2;\<omega>2\<rangle> [\<Down>]\<^sub>t Val v2"
      by auto
    thus ?thesis
    proof (cases)
      case E2Fail
      then show ?thesis 
        using E1Normal
        by (metis RedBinop.hyps(1) RedBinop.hyps(2) RedBinopRightFailure binop_result.distinct(3) binop_result.distinct_disc(1) eval_total_non_total_not_fail_same)
    next
      case E2Normal
      then show ?thesis 
        using E1Normal E2Normal RedBinop        
        by (auto intro: TotalExpressions.RedBinop)
    qed
  qed       
next
  case (RedBinopRightFailure \<omega>_def e1 \<omega> v1 e2 bop)
  from this consider (E1Fail) "ctxt, \<omega>_def2 \<turnstile> \<langle>e1;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | 
                     (E1Normal)"ctxt, \<omega>_def2 \<turnstile> \<langle>e1;\<omega>2\<rangle> [\<Down>]\<^sub>t Val v1"
    by auto
  thus ?case 
  proof (cases)
    case E1Fail
    thus ?thesis
      by (simp add: red_exp_binop_sub_left_failure)
  next
    case E1Normal
    from RedBinopRightFailure have "ctxt, \<omega>_def2 \<turnstile> \<langle>e2;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure"
      by simp
    thus ?thesis
      using E1Normal RedBinopRightFailure
      by (simp add: Option.is_none_def red_pure_exp_total_red_pure_exps_total.RedBinopRightFailure)
  qed
next
  case (RedBinopOpFailure \<omega>_def e1 \<omega> v1 e2 v2 bop)
    from this consider (E1Fail) "ctxt, \<omega>_def2 \<turnstile> \<langle>e1;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | 
                     (E1Normal)"ctxt, \<omega>_def2 \<turnstile> \<langle>e1;\<omega>2\<rangle> [\<Down>]\<^sub>t Val v1"
      by auto
    thus ?case
    proof (cases)
      case E1Fail
      thus ?thesis
        by (simp add: red_exp_binop_sub_left_failure)
    next
      case E1Normal
      from RedBinopOpFailure consider  (E2Fail) "ctxt, \<omega>_def2 \<turnstile> \<langle>e2;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | 
                              (E2Normal)"ctxt, \<omega>_def2 \<turnstile> \<langle>e2;\<omega>2\<rangle> [\<Down>]\<^sub>t Val v2"
        by auto
      thus ?thesis
      proof (cases)
        case E2Fail
        then show ?thesis 
          using E1Normal RedBinopOpFailure
          apply (auto intro!: RedBinopRightFailure)
          by blast
      next
        case E2Normal
        then show ?thesis 
          using E1Normal RedBinopOpFailure
          by (auto intro!: TotalExpressions.RedBinopOpFailure)
      qed
    qed
next
  case (RedUnop \<omega>_def e \<omega> v unop v')
    from this consider (EFail) "ctxt, \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | 
                     (ENormal)"ctxt, \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val v"
      by auto
    thus ?case
    proof (cases)
      case EFail
      then show ?thesis 
        by (simp add: red_exp_unop_sub_failure)
    next
      case ENormal
      then show ?thesis 
        using RedUnop
        by (auto intro!: TotalExpressions.RedUnop)
    qed
next
  case (RedCondExpTrue \<omega>_def e1 \<omega> e2 r e3)
    from this consider (E1Fail) "ctxt, \<omega>_def2 \<turnstile> \<langle>e1;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | 
                     (E1Normal)"ctxt, \<omega>_def2 \<turnstile> \<langle>e1;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
      by auto
    thus ?case
    proof (cases)
      case E1Fail
      then show ?thesis 
        by (simp add: red_exp_condexp_sub_failure)
    next
      case E1Normal
      from this consider "r = VFailure \<and> ctxt, \<omega>_def2 \<turnstile> \<langle>e2;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" |
                         "r \<noteq> VFailure \<and> ctxt, \<omega>_def2 \<turnstile> \<langle>e2;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" |
                         "r \<noteq> VFailure \<and> ctxt, \<omega>_def2 \<turnstile> \<langle>e2;\<omega>2\<rangle> [\<Down>]\<^sub>t r"
        using RedCondExpTrue
        by (fastforce split: if_split_asm)
      then show ?thesis 
      by (cases) (auto intro!: TotalExpressions.RedCondExpTrue intro: E1Normal)
    qed
next
  case (RedCondExpFalse \<omega>_def e1 \<omega> e3 r e2)
    from this consider (E1Fail) "ctxt, \<omega>_def2 \<turnstile> \<langle>e1;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | 
                     (E1Normal)"ctxt, \<omega>_def2 \<turnstile> \<langle>e1;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
      by auto
    thus ?case
    proof (cases)
      case E1Fail
      then show ?thesis 
        by (simp add: red_exp_condexp_sub_failure)
    next
      case E1Normal
      from this consider "r = VFailure \<and> ctxt, \<omega>_def2 \<turnstile> \<langle>e3;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" |
                         "r \<noteq> VFailure \<and> ctxt, \<omega>_def2 \<turnstile> \<langle>e3;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" |
                         "r \<noteq> VFailure \<and> ctxt, \<omega>_def2 \<turnstile> \<langle>e3;\<omega>2\<rangle> [\<Down>]\<^sub>t r"
        using RedCondExpFalse
        by (fastforce split: if_split_asm)
      then show ?thesis 
      by (cases) (auto intro!: TotalExpressions.RedCondExpFalse intro: E1Normal)
    qed
next
  case (RedOld \<omega> l \<phi> \<omega>_def' \<omega>_def e v)
  from this obtain \<phi>' where Trace2: "get_trace_total \<omega>2 l = Some \<phi>'" and "\<phi>' \<le> \<phi>"
    using less_eq_full_total_stateD
    by blast

  from \<open>\<omega>2 \<le> \<omega>\<close> \<open>\<phi>' \<le> \<phi>\<close>
  have *: "\<omega>2 \<lparr> get_total_full := \<phi>' \<rparr> \<le> \<omega> \<lparr> get_total_full := \<phi> \<rparr>"    
    by (simp add: less_eq_full_total_state_ext_def)

  let ?\<omega>_def2' = "map_option (get_total_full_update (\<lambda>_. \<phi>')) \<omega>_def2"
  have "?\<omega>_def2' \<le> map_option (get_total_full_update (\<lambda>_. \<phi>)) \<omega>_def"
  proof (cases \<omega>_def2)
    case None
    then show ?thesis 
      by (simp add: less_eq_option_def)
  next
    case (Some \<omega>_def2_val)
    with \<open>\<omega>_def2 \<le> \<omega>_def\<close> obtain \<omega>_def_val where
       "\<omega>_def = Some \<omega>_def_val" and
       "\<omega>_def2_val \<le> \<omega>_def_val"
      by (auto simp add: less_eq_option_def)

    show ?thesis 
      unfolding \<open>\<omega>_def2 =_\<close> \<open>\<omega>_def = _\<close>
      apply (simp, rule less_eq_Some)
      apply (rule less_eq_full_total_stateI2)
      using less_eq_full_total_stateD[OF \<open>\<omega>_def2_val \<le> \<omega>_def_val\<close>] \<open>\<phi>' \<le> \<phi>\<close>
      by simp_all     
  qed

  hence **: "map_option (get_total_full_update (\<lambda>_. \<phi>')) \<omega>_def2 \<le> \<omega>_def'"
    by (simp add: \<open>\<omega>_def' = _\<close>)

  from RedOld have ***: "no_perm_pure_exp e \<and> no_unfolding_pure_exp e"
    by simp

  have ****: "map_option (get_total_full_update (\<lambda>_. \<phi>')) \<omega>_def2 = None \<longleftrightarrow> (\<omega>_def' = None)"
    unfolding \<open>\<omega>_def' = _\<close>
    using \<open>(\<omega>_def2 = None) = (\<omega>_def = None)\<close>
    by simp

  from RedOld.IH(2)[OF *** * ** ****]
  consider "v = VFailure \<and> ctxt, ?\<omega>_def2' \<turnstile> \<langle>e;\<omega>2\<lparr>get_total_full := \<phi>'\<rparr>\<rangle> [\<Down>]\<^sub>t VFailure" |
           "v \<noteq> VFailure \<and> ctxt, ?\<omega>_def2' \<turnstile> \<langle>e;\<omega>2\<lparr>get_total_full := \<phi>'\<rparr>\<rangle> [\<Down>]\<^sub>t v" |
           "v \<noteq> VFailure \<and> ctxt, ?\<omega>_def2' \<turnstile> \<langle>e;\<omega>2\<lparr>get_total_full := \<phi>'\<rparr>\<rangle> [\<Down>]\<^sub>t VFailure"
    using \<open>(\<omega>_def2 = None) = (\<omega>_def = None)\<close>
    by (fastforce split: if_split_asm)
  thus ?case
   by (cases) (auto intro: TotalExpressions.RedOld Trace2)
next
  case (RedOldFailure \<omega> l \<omega>_def e)
  hence "get_trace_total \<omega>2 l = None"
    by (blast dest: less_eq_full_total_stateD)
  then show ?case 
    by (auto intro!: TotalExpressions.RedOldFailure dest: less_eq_full_total_stateD)
next
  case (RedField \<omega>_def e \<omega> a f v)
  from this consider (EFail) "ctxt, \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | 
                   (ENormal)"ctxt, \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))"
    by auto
  thus ?case
  proof (cases)
    case EFail
    then show ?thesis 
      by (simp add: red_exp_field_sub_failure)
  next
    case ENormal
    have "get_hh_total_full \<omega>2 = get_hh_total_full \<omega>"
      using \<open>\<omega>2 \<le> \<omega>\<close>
      by (fastforce dest: less_eq_full_total_stateD less_eq_total_stateD)
    hence HeapVal: "get_hh_total_full \<omega>2 (a,f) = v"
      using RedField
      by argo
    show ?thesis 
    proof (cases \<omega>_def)
      case None
      hence "\<omega>_def2 = None"
        using \<open>\<omega>_def2 \<le> \<omega>_def\<close>
        by (simp add: less_eq_option_def)

      have "ctxt, None \<turnstile> \<langle>FieldAcc e f;\<omega>2\<rangle> [\<Down>]\<^sub>t Val v"
        apply (rule RedField_no_def_normalI)
      using ENormal \<open>\<omega>_def2 = _\<close>  HeapVal
      by auto

    thus ?thesis
      unfolding \<open>\<omega>_def = _\<close> \<open>\<omega>_def2 = _\<close>
      by auto
    next
      case (Some \<omega>_def_val)
      from this obtain \<omega>_def2_val where "\<omega>_def2 = Some \<omega>_def2_val" and "\<omega>_def2_val \<le> \<omega>_def_val"
        using \<open>\<omega>_def2 \<le> \<omega>_def\<close> \<open>(\<omega>_def2 = None) = (\<omega>_def = None)\<close>
        unfolding less_eq_option_def
        by blast        

      hence ValidLocsSmaller: "get_valid_locs \<omega>_def2_val \<subseteq> get_valid_locs \<omega>_def_val"
        using less_eq_valid_locs_subset_total_state
        by blast

      show ?thesis
      proof (cases "(a, f) \<in> get_valid_locs \<omega>_def2_val")
        case True
        hence "ctxt, Some \<omega>_def2_val \<turnstile> \<langle>FieldAcc e f;\<omega>2\<rangle> [\<Down>]\<^sub>t Val v"
          by (auto intro!: RedField_def_normalI 
                   intro: ENormal[simplified \<open>\<omega>_def2 = _\<close>] HeapVal)
        then show ?thesis
          using True ValidLocsSmaller 
          unfolding \<open>\<omega>_def = _\<close> \<open>\<omega>_def2 = _\<close>
          by auto
      next
        case False
        hence "ctxt, Some \<omega>_def2_val \<turnstile> \<langle>FieldAcc e f;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure"
          by (auto intro!: RedField_def_failureI 
                   intro: ENormal[simplified \<open>\<omega>_def2 = _\<close>] HeapVal)
        then show ?thesis 
          using False ValidLocsSmaller 
          unfolding \<open>\<omega>_def = _\<close> \<open>\<omega>_def2 = _\<close>
          by auto
      qed
    qed
  qed
next
  case (RedFieldNullFailure \<omega>_def e \<omega> f)
  then show ?case 
  by (metis pure_exp_pred.elims(2) pure_exp_pred_rec.simps(6) red_exp_field_sub_failure red_pure_exp_total_red_pure_exps_total.RedFieldNullFailure)
next
  case (RedPermNull \<omega>_def e \<omega> f)
  then show ?case by simp \<comment>\<open>cannot occur\<close>
next
  case (RedPerm \<omega>_def e \<omega> a f v)
  then show ?case by simp \<comment>\<open>cannot occur\<close>
next
  case (RedUnfolding ubody \<omega> v p es)
  then show ?case by simp \<comment>\<open>cannot occur\<close>
next
  case (RedUnfoldingDefNoPred \<omega>_def es \<omega> vs pred_id pred_decl p ubody)
  then show ?case by simp \<comment>\<open>cannot occur\<close>
next
  case (RedUnfoldingDef \<omega>_def es \<omega> vs p \<omega>'_def ubody v)
  then show ?case by simp \<comment>\<open>cannot occur\<close>
next
  case (RedSubFailure e' \<omega>_def \<omega>)
  then show ?case 
    by (metis (mono_tags, lifting) Ball_set_list_all pure_exp_pred_subexp TotalExpressions.RedSubFailure)
next
  case (RedExpListCons \<omega>_def e \<omega> v es res res')
  then show ?case 
    by (metis (no_types, lifting) RedExpListFailure list_all_simps(1) option.simps(8) TotalExpressions.RedExpListCons)
next
  case (RedExpListFailure \<omega>_def e \<omega> es)
  then show ?case 
    by (simp add: TotalExpressions.RedExpListFailure)
next
  case (RedExpListNil \<omega>_def \<omega>)
  then show ?case 
    by (simp add: TotalExpressions.RedExpListNil)
qed


lemma inhale_no_perm_downwards_mono:
  assumes ConsistencyDownwardMono: "mono_prop_downward_ord R"
    shows "red_inhale ctxt R A \<omega>1 res1 \<Longrightarrow> 
           no_perm_assertion A \<and> no_unfolding_assertion A \<Longrightarrow>
           \<omega>2 \<le> \<omega>1 \<Longrightarrow>
           res1 \<noteq> RMagic \<Longrightarrow> 
           (res1 = RFailure \<longrightarrow> red_inhale ctxt R A \<omega>2 RFailure) \<and>
           (\<forall>\<omega>1'. res1 = RNormal \<omega>1' \<longrightarrow> 
                  (red_inhale ctxt R A \<omega>2 RFailure \<or> 
                     (\<exists>\<omega>2'. \<omega>2' \<le> \<omega>1' \<and> red_inhale ctxt R A \<omega>2 (RNormal \<omega>2'))
                  )
           )"
proof (induction arbitrary: \<omega>2 rule: red_inhale.inducts)
  case (InhAcc \<omega> e_r r e_p p W' f res)
  moreover from this have
      Leq: "Some \<omega>2 \<le> Some \<omega>" and
      SubExpConstraint: "no_perm_pure_exp e_r \<and> no_unfolding_pure_exp e_r \<and> no_perm_pure_exp e_p \<and> no_unfolding_pure_exp e_p"
    by simp_all
  ultimately consider (RefFail) "ctxt, Some \<omega>2 \<turnstile> \<langle>e_r; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | 
                      (RefSuccess) "ctxt, Some \<omega>2 \<turnstile> \<langle>e_r; \<omega>2\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
    by (metis assms eval_no_perm_downwards_mono(1) option.discI)
    
  thus ?case
  proof cases
    case RefFail
    thus ?thesis
      by (auto intro!: red_inhale.intros red_pure_exp_intros)
  next
    case RefSuccess
      from Leq SubExpConstraint InhAcc consider (PermFail) "ctxt, Some \<omega>2 \<turnstile> \<langle>e_p; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | 
                                             (PermSuccess) "ctxt, Some \<omega>2 \<turnstile> \<langle>e_p; \<omega>2\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
        by (metis assms eval_no_perm_downwards_mono(1) option.discI)
      then show ?thesis 
      proof cases
        case PermFail
           have "red_inhale ctxt R (Atomic (Acc e_r f (PureExp e_p))) \<omega>2 RFailure"
             apply (rule InhSubExpFailure)
             apply simp+
             apply (rule RedExpListCons)
             by (auto intro!: RefSuccess RedExpListCons PermFail RedExpListFailure)                      
           then show ?thesis 
             by simp
      next
        case PermSuccess
        then show ?thesis 
        proof (cases "res = RFailure")
          case True
          have "red_inhale ctxt R (Atomic (Acc e_r f (PureExp e_p))) \<omega>2 RFailure"
            apply (rule TotalInhaleExhale.InhAcc)
               apply (rule RefSuccess)
              apply (rule PermSuccess)
             apply blast
            using True InhAcc.hyps THResultFailure th_result_rel_failure_2
            by fastforce
          thus ?thesis
            by simp            
        next
          case False
          with InhAcc.hyps obtain \<omega>' where "res = RNormal \<omega>'" and "\<omega>' \<in> W'"
            by (metis \<open>res \<noteq> RMagic\<close> th_result_rel.cases)          
          
          show ?thesis 
          proof (cases "r = Null")
            case True
            have "red_inhale ctxt R (Atomic (Acc e_r f (PureExp e_p))) \<omega>2 (RNormal \<omega>2)"
              apply (rule TotalInhaleExhale.InhAcc[OF RefSuccess PermSuccess])
               apply simp
              using InhAcc.hyps THResultNormal_alt th_result_rel_normal 
              by (fastforce split: if_split simp: \<open>r = Null\<close> \<open>res = RNormal \<omega>'\<close>)
            thus ?thesis
              using \<open>res = _\<close> \<open>\<omega>2 \<le> _\<close> InhAcc True \<open>\<omega>' \<in> W'\<close>
              by fastforce              
          next
            case False
            hence "\<omega>' \<in> inhale_perm_single R \<omega> (the_address r, f) (Some (Abs_preal p))"
              using InhAcc \<open>\<omega>' \<in> W'\<close>
              by presburger
            from this obtain \<omega>'' where "\<omega>'' \<le> \<omega>'" and "\<omega>'' \<in> inhale_perm_single R \<omega>2 (the_address r, f) (Some (Abs_preal p))"
              using \<open>\<omega>2 \<le> \<omega>\<close> inhale_perm_single_leq ConsistencyDownwardMono[simplified mono_prop_downward_ord_def]
              by blast
            have "red_inhale ctxt R (Atomic (Acc e_r f (PureExp e_p))) \<omega>2 (RNormal \<omega>'')"
              apply (rule TotalInhaleExhale.InhAcc)
                 apply (rule RefSuccess)
                apply (rule PermSuccess)
               apply simp
              apply (simp add: False)
              using \<open>\<omega>'' \<in> _\<close> InhAcc.hyps \<open>res = RNormal \<omega>'\<close> 
              by (auto intro: THResultNormal_alt dest: th_result_rel_normal)
            then show ?thesis
              using \<open>\<omega>'' \<le> \<omega>'\<close> \<open>res = _\<close>              
              by blast
          qed
        qed
      qed
    qed
next
  case (InhAccPred \<omega> e_args v_args e_p p W' pred_id res)
  moreover from this have
      Leq: "Some \<omega>2 \<le> Some \<omega>" 
    by simp
  moreover from InhAccPred have
    SubExpConstraint: "list_all (\<lambda>e. no_perm_pure_exp e \<and> no_unfolding_pure_exp e) (e_args) \<and> no_perm_pure_exp e_p \<and> no_unfolding_pure_exp e_p"
    proof (simp add: assert_pred_atomic_subexp del: pure_exp_pred.simps)
      from InhAccPred have "list_all (\<lambda>e. no_perm_pure_exp e) e_args \<and> list_all (\<lambda>e. no_unfolding_pure_exp e) e_args"
        by (simp add: assert_pred_atomic_subexp del: pure_exp_pred.simps)
      thus "list_all (\<lambda>e. no_perm_pure_exp e \<and> no_unfolding_pure_exp e) e_args"
        by (simp add: list_all_length)
    qed
  ultimately consider (ArgsFail) "red_pure_exps_total ctxt (Some \<omega>2) e_args \<omega>2 None" | 
                      (ArgsSuccess) "red_pure_exps_total ctxt (Some \<omega>2) e_args \<omega>2 (Some v_args)"
    by (metis (no_types, lifting) Some_Some_ifD assms eval_no_perm_downwards_mono(2))
  thus ?case
  proof cases
    case ArgsFail
    hence "e_args \<noteq> []"
      by (meson list.distinct(1) red_exp_list_failure_elim)    
    have "red_inhale ctxt R (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega>2 RFailure"
      apply (rule InhSubExpFailure)
       apply (simp add: \<open>e_args \<noteq> []\<close>)
      apply simp
      using ArgsFail
      by (auto intro: red_pure_exps_total_append_failure)
    thus ?thesis
      by simp            
  next
    case ArgsSuccess
    from Leq SubExpConstraint InhAccPred consider
      (PermFail) "ctxt, Some \<omega>2 \<turnstile> \<langle>e_p; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | 
      (PermSuccess) "ctxt, Some \<omega>2 \<turnstile> \<langle>e_p; \<omega>2\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
      by (metis (no_types, lifting) assms eval_no_perm_downwards_mono(1) option.discI)
      then show ?thesis 
      proof cases
        case PermFail
         have "red_inhale ctxt R (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega>2 RFailure"
           apply (rule InhSubExpFailure)
           apply simp+
           using ArgsSuccess PermFail
           by (auto intro: red_pure_exps_total_append_failure_2 RedExpListFailure)
         then show ?thesis 
           by simp
      next
        case PermSuccess
        then show ?thesis 
        proof (cases "res = RFailure")
          case True
          have "red_inhale ctxt R (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega>2 RFailure"
            apply (rule TotalInhaleExhale.InhAccPred)
               apply (rule ArgsSuccess)
              apply (rule PermSuccess)
             apply blast
            using True InhAccPred.hyps THResultFailure th_result_rel_failure_2 by fastforce
          thus ?thesis
            by simp            
        next
          case False
          with InhAccPred.hyps obtain \<omega>' where "res = RNormal \<omega>'" and "\<omega>' \<in> W'"
            by (metis \<open>res \<noteq> RMagic\<close> th_result_rel.cases)                    

          hence "\<omega>' \<in> inhale_perm_single_pred ctxt R \<omega> (pred_id, v_args) (Some (Abs_preal p))"
            using InhAccPred \<open>\<omega>' \<in> W'\<close>
            by presburger
          from this obtain \<omega>'' where "\<omega>'' \<le> \<omega>'" and "\<omega>'' \<in> inhale_perm_single_pred ctxt R \<omega>2 (pred_id, v_args) (Some (Abs_preal p))"
            using \<open>\<omega>2 \<le> \<omega>\<close>  inhale_perm_single_pred_leq ConsistencyDownwardMono[simplified mono_prop_downward_ord_def]
            by metis
          have "red_inhale ctxt R (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega>2 (RNormal \<omega>'')"
            apply (rule TotalInhaleExhale.InhAccPred[OF ArgsSuccess PermSuccess])
             apply simp
            using \<open>\<omega>'' \<in> _\<close> \<open>res = RNormal \<omega>'\<close> InhAccPred.hyps
            by (auto intro: THResultNormal_alt dest: th_result_rel_normal)
          then show ?thesis
            using \<open>\<omega>'' \<le> \<omega>'\<close> \<open>res = _\<close>              
            by blast
        qed
      qed
    qed
next
  case (InhAccWildcard \<omega> e_r r W' f res)
  moreover from this have
      Leq: "Some \<omega>2 \<le> Some \<omega>" and
      SubExpConstraint: "no_perm_pure_exp e_r \<and> no_unfolding_pure_exp e_r"
    by simp_all
  ultimately consider (RefFail) "ctxt, Some \<omega>2 \<turnstile> \<langle>e_r; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | 
                      (RefSuccess) "ctxt, Some \<omega>2 \<turnstile> \<langle>e_r; \<omega>2\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
    by (metis assms eval_no_perm_downwards_mono(1) option.discI)
  thus ?case
  proof cases
    case RefFail
    thus ?thesis
      by (simp add: InhSubExpFailure RedExpListFailure)
  next
    case RefSuccess
    with InhAccWildcard.hyps obtain \<omega>' where "res = RNormal \<omega>'" and "\<omega>' \<in> W'" and "r \<noteq> Null"
      using \<open>res \<noteq> RMagic\<close>
      by (blast elim: th_result_rel.cases)

      hence "\<omega>' \<in> inhale_perm_single R \<omega> (the_address r, f) None"
        using InhAccWildcard \<open>\<omega>' \<in> W'\<close>
        by argo

      from this obtain \<omega>'' where "\<omega>'' \<le> \<omega>'" and "\<omega>'' \<in> inhale_perm_single R \<omega>2 (the_address r, f) None"
        using \<open>\<omega>2 \<le> \<omega>\<close>  inhale_perm_single_leq ConsistencyDownwardMono[simplified mono_prop_downward_ord_def]
        by metis
      have "red_inhale ctxt R (Atomic (Acc e_r f Wildcard)) \<omega>2 (RNormal \<omega>'')"
        apply (rule TotalInhaleExhale.InhAccWildcard)
          apply (rule RefSuccess)
         apply simp
        using \<open>\<omega>'' \<in> _\<close> \<open>r \<noteq> Null\<close>
        by (auto intro: THResultNormal_alt)              
      then show ?thesis 
        using \<open>\<omega>'' \<le> \<omega>'\<close> \<open>res = _\<close>              
        by blast
    qed    
next
  case (InhAccPredWildcard \<omega> e_args v_args W' pred_id res)
  moreover from this have
      Leq: "Some \<omega>2 \<le> Some \<omega>" 
    by simp
  moreover from InhAccPredWildcard have
    SubExpConstraint: "list_all (\<lambda>e. no_perm_pure_exp e \<and> no_unfolding_pure_exp e) e_args"
    proof (simp add: assert_pred_atomic_subexp del: pure_exp_pred.simps)
      from InhAccPredWildcard have "list_all (\<lambda>e. no_perm_pure_exp e) e_args \<and> list_all (\<lambda>e. no_unfolding_pure_exp e) e_args"
        by (simp add: assert_pred_atomic_subexp del: pure_exp_pred.simps)
      thus "list_all (\<lambda>e. no_perm_pure_exp e \<and> no_unfolding_pure_exp e) e_args"
        by (simp add: list_all_length)
    qed
  ultimately consider (ArgsFail) "red_pure_exps_total ctxt (Some \<omega>2) e_args \<omega>2 None" | 
                      (ArgsSuccess) "red_pure_exps_total ctxt (Some \<omega>2) e_args \<omega>2 (Some v_args)"
    by (metis (no_types, lifting) assms eval_no_perm_downwards_mono(2) option.discI)
  thus ?case
  proof cases
    case ArgsFail
    hence "e_args \<noteq> []"
      by (meson list.distinct(1) red_exp_list_failure_elim)    
    have "red_inhale ctxt R (Atomic (AccPredicate pred_id e_args Wildcard)) \<omega>2 RFailure"
      apply (rule InhSubExpFailure)
      by (simp_all add: \<open>e_args \<noteq> []\<close> ArgsFail)      
    thus ?thesis
      by simp            
  next
    case ArgsSuccess
    then show ?thesis 
    proof (cases "res = RFailure")
      case True
      have "red_inhale ctxt R (Atomic (AccPredicate pred_id e_args Wildcard)) \<omega>2 RFailure"
        apply (rule TotalInhaleExhale.InhAccPredWildcard)
          apply (rule ArgsSuccess)
         apply blast
        using True InhAccPredWildcard.hyps THResultFailure th_result_rel_failure_2 by fastforce
      thus ?thesis
        by simp            
    next
      case False
      with InhAccPredWildcard.hyps obtain \<omega>' where "res = RNormal \<omega>'" and "\<omega>' \<in> W'"
        by (metis \<open>res \<noteq> RMagic\<close> th_result_rel.cases)                    

      hence "\<omega>' \<in> inhale_perm_single_pred ctxt R \<omega> (pred_id, v_args) None"
        using InhAccPredWildcard \<open>\<omega>' \<in> W'\<close>
        by presburger
      from this obtain \<omega>'' where "\<omega>'' \<le> \<omega>'" and "\<omega>'' \<in> inhale_perm_single_pred ctxt R \<omega>2 (pred_id, v_args) None"
        using \<open>\<omega>2 \<le> \<omega>\<close> inhale_perm_single_pred_leq ConsistencyDownwardMono[simplified mono_prop_downward_ord_def]
        by metis
      have "red_inhale ctxt R (Atomic (AccPredicate pred_id e_args Wildcard)) \<omega>2 (RNormal \<omega>'')"
        apply (rule TotalInhaleExhale.InhAccPredWildcard[OF ArgsSuccess])
         apply simp
        using \<open>\<omega>'' \<in> _\<close>
        by (auto intro:  THResultNormal_alt)
      then show ?thesis 
        using \<open>\<omega>'' \<le> \<omega>'\<close> \<open>res = _\<close>              
        by blast
    qed
  qed
next
  case (InhPure \<omega> e b)
  moreover from this have "Some \<omega>2 \<le> Some \<omega>"
    by simp
  moreover from InhPure have SubConstraint: "no_perm_pure_exp e \<and> no_unfolding_pure_exp e"
    by simp
  ultimately consider "ctxt, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | "ctxt, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool b)"
    by (metis assms eval_no_perm_downwards_mono(1) option.discI)
  thus ?case 
  proof cases
    case 1
    have "red_inhale ctxt R (Atomic (Pure e)) \<omega>2 RFailure"
      apply (rule InhSubExpFailure)
      by (simp add: "1" RedExpListFailure)+
    thus ?thesis
      by simp          
  next
    case 2
    then show ?thesis 
      using InhPure.prems(2) TotalInhaleExhale.InhPure
      by force
  qed   
next
  case (InhSubExpFailure A \<omega>)
  moreover from this have "Some \<omega>2 \<le> Some \<omega>"
    by simp
  moreover have "list_all (\<lambda>e. no_perm_pure_exp e \<and> no_unfolding_pure_exp e) (direct_sub_expressions_assertion A)"
  proof -
    from \<open>no_perm_assertion A \<and> no_unfolding_assertion A\<close> have
         "list_all (\<lambda>e. no_perm_pure_exp e) (direct_sub_expressions_assertion A) \<and> list_all (\<lambda>e. no_unfolding_pure_exp e) (direct_sub_expressions_assertion A)"
      using assert_pred_subexp
      by blast
    thus ?thesis
      by (simp add: list_all_length)
  qed
  ultimately show ?case 
    using InhSubExpFailure TotalInhaleExhale.InhSubExpFailure
    by (metis (no_types, lifting) assms eval_no_perm_downwards_mono(2) option.discI)
next
  case (InhStarNormal A \<omega> \<omega>'' B res)
  moreover from this have SubAssertionConstraint: "no_perm_assertion A \<and> no_unfolding_assertion A \<and> no_perm_assertion B \<and> no_unfolding_assertion B"
    by simp
  ultimately have *: "red_inhale ctxt R A \<omega>2 RFailure \<or> (\<exists>\<omega>2'\<le>\<omega>''. red_inhale ctxt R A \<omega>2 (RNormal \<omega>2'))" (is "?FailA \<or> ?SuccessA")
    by blast

  show ?case
  proof (rule conjI, rule impI)
    assume "res = RFailure"
    thus "red_inhale ctxt R (A && B) \<omega>2 RFailure"
      using InhStarNormal SubAssertionConstraint
      by (auto intro: red_inhale_intros)
  next
    show "\<forall>\<omega>1'. res = RNormal \<omega>1' \<longrightarrow>
           red_inhale ctxt R (A && B) \<omega>2 RFailure \<or> (\<exists>\<omega>2'\<le>\<omega>1'. red_inhale ctxt R (A && B) \<omega>2 (RNormal \<omega>2'))"
      using * InhStarNormal SubAssertionConstraint
      by (blast intro: red_inhale_intros)
  qed
next
  case (InhStarFailureMagic A \<omega> resA B)
  then show ?case 
    by (auto intro: red_inhale_intros)        
next
  case (InhImpTrue \<omega> e A res)
  moreover from this have "Some \<omega>2 \<le> Some \<omega>"
    by simp
  moreover from InhImpTrue have SubConstraint: "no_perm_pure_exp e \<and> no_unfolding_pure_exp e \<and> no_perm_assertion A \<and> no_unfolding_assertion A"
    by simp
  ultimately consider "ctxt, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | "ctxt, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
    by (metis assms eval_no_perm_downwards_mono(1) option.distinct(1))
  thus ?case 
  proof cases
    case 1
    then show ?thesis 
      by (simp add: InhSubExpFailure RedExpListFailure)
  next
    case 2
    then show ?thesis 
      using InhImpTrue TotalInhaleExhale.InhImpTrue SubConstraint
      by metis
  qed  
next
  case (InhImpFalse \<omega> e A)
  moreover from this have "Some \<omega>2 \<le> Some \<omega>"
    by simp
  moreover from InhImpFalse have SubConstraint: "no_perm_pure_exp e \<and> no_unfolding_pure_exp e"
    by simp
  ultimately consider "ctxt, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | "ctxt, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    using InhImpFalse
    by (metis assms eval_no_perm_downwards_mono(1) option.discI)
  thus ?case 
  proof cases
    case 1
    then show ?thesis 
      by (simp add: InhSubExpFailure RedExpListFailure)
  next
    case 2
    thus ?thesis
      using InhImpFalse 
      by (blast intro!: red_inhale_intros)
  qed
next
  case (InhCondAssertTrue \<omega> e A res B)
  moreover from this have "Some \<omega>2 \<le> Some \<omega>"
    by simp
  moreover from InhCondAssertTrue have SubConstraint: "no_perm_pure_exp e \<and> no_unfolding_pure_exp e \<and> no_perm_assertion A \<and> no_unfolding_assertion A"
    by simp
  ultimately consider "ctxt, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | "ctxt, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
    by (metis assms eval_no_perm_downwards_mono(1) option.discI)
    thus ?case 
  proof cases
    case 1
    then show ?thesis 
      by (simp add: InhSubExpFailure RedExpListFailure)
  next
    case 2
    thus ?thesis
      using InhCondAssertTrue 
      by (metis SubConstraint TotalInhaleExhale.InhCondAssertTrue)
  qed
next
  case (InhCondAssertFalse \<omega> e B res A)
  moreover from this have "Some \<omega>2 \<le> Some \<omega>"
    by simp
  moreover from InhCondAssertFalse have SubConstraint: "no_perm_pure_exp e \<and> no_unfolding_pure_exp e \<and> no_perm_assertion B \<and> no_unfolding_assertion B"
    by simp
  ultimately consider "ctxt, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure" | "ctxt, Some \<omega>2 \<turnstile> \<langle>e; \<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    by (metis assms eval_no_perm_downwards_mono(1) option.discI)
  thus ?case
  proof cases
    case 1
    then show ?thesis 
      by (simp add: InhSubExpFailure RedExpListFailure)
  next
    case 2
    thus ?thesis
      using InhCondAssertFalse
      by (metis SubConstraint TotalInhaleExhale.InhCondAssertFalse)
  qed
qed


lemma assertion_framing_state_mono:
  assumes "mono_prop_downward_ord StateCons"
      and "assertion_framing_state ctxt StateCons A \<omega>"
      and "\<omega>' \<ge> \<omega>"
      and "no_perm_assertion A \<and> no_unfolding_assertion A"
  shows "assertion_framing_state ctxt StateCons A \<omega>'"
  using assms inhale_no_perm_downwards_mono
  unfolding assertion_framing_state_def
  by blast  


lemma vpr_postcondition_framed_mono:
  assumes "mono_prop_downward_ord StateCons"
      and "vpr_postcondition_framed ctxt StateCons A \<phi> \<sigma>" 
      and "\<phi> \<le> \<phi>'"
      and "no_perm_assertion A \<and> no_unfolding_assertion A"
    shows "vpr_postcondition_framed ctxt StateCons A \<phi>' \<sigma>" 
  unfolding vpr_postcondition_framed_def
proof (rule allI | rule impI)+
  fix \<phi>'' trace

  assume TraceOldLabel: "trace old_label = Some \<phi>'"
     and IntCons: "StateCons \<lparr> get_store_total = \<sigma>, get_trace_total = trace, get_total_full = \<phi>'' \<rparr>"
  
  let ?trace_\<omega> = "trace (old_label \<mapsto> \<phi>)"
  let ?\<omega>' = "\<lparr>get_store_total = \<sigma>, get_trace_total = trace, get_total_full = \<phi>''\<rparr>"
  let ?\<omega> = "\<lparr>get_store_total = \<sigma>, get_trace_total = ?trace_\<omega>, get_total_full = \<phi>''\<rparr>"
  have Leq: "?\<omega> \<le> ?\<omega>'"
    using \<open>\<phi> \<le> \<phi>'\<close> TraceOldLabel
    unfolding less_eq_full_total_state_ext_def
    by auto

  assume "total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) (get_hh_total \<phi>'')"
     and "valid_heap_mask (get_mh_total \<phi>'')"

  moreover from this have "assertion_framing_state ctxt StateCons A ?\<omega>"
    using assms Leq assertion_framing_state_mono TraceOldLabel IntCons
    unfolding vpr_postcondition_framed_def 
    by (simp add: mono_prop_downward_ord_def)

  thus "assertion_framing_state ctxt StateCons A ?\<omega>'"
    using assertion_framing_state_mono Leq assms
    by blast
qed



subsection \<open>Exhale\<close>


lemma exhale_only_changes_total_state_aux:
  assumes "red_exhale ctxt \<omega>def A \<omega> res" and "res = RNormal \<omega>'"
    shows "get_store_total \<omega>' = get_store_total \<omega> \<and>
           get_trace_total \<omega>' = get_trace_total \<omega> \<and>
           get_hh_total_full \<omega>' = get_hh_total_full \<omega>"
  using assms
proof (induction arbitrary: \<omega>')
  case (ExhAcc mh \<omega> e_r r e_p p a f)
  then show ?case by (auto elim: exh_if_total.elims)
next
  case (ExhAccWildcard mh \<omega> e_r r q a f)
  then show ?case by (auto elim: exh_if_total.elims)
next
  case (ExhAccPred mp \<omega> e_args v_args e_p p pred_id r)
  then show ?case
    apply (simp only: exhale_pred_def Let_def)
    by (auto elim: exh_if_total.elims)
next
  case (ExhAccPredWildcard mp \<omega> e_args v_args q pred_id)
  then show ?case
    apply (simp only: exhale_pred_def Let_def)
    by (auto elim: exh_if_total.elims)
next
  case (ExhPure e \<omega> b)
  then show ?case 
    by (auto elim: exh_if_total.elims)
next
  case (ExhStarNormal A \<omega> \<omega>' B res)
  then show ?case by presburger
next
  case (ExhStarFailure A \<omega> B)
  then show ?case by blast
next
  case (ExhImpTrue e \<omega> A res)
  then show ?case by blast
next
  case (ExhImpFalse e \<omega> A)
  then show ?case by fastforce
next
  case (ExhCondTrue e \<omega> A res B)
  then show ?case by blast
next
  case (ExhCondFalse e \<omega> B res A)
  then show ?case by blast
next
  case (ExhSubExpFailure A \<omega>)
  then show ?case by fastforce
qed

lemma exhale_only_changes_total_state:
  assumes "red_stmt_total ctxt R \<Lambda> (Exhale A) \<omega> (RNormal \<omega>')"
  shows "get_store_total \<omega> = get_store_total \<omega>' \<and>
         get_trace_total \<omega> = get_trace_total \<omega>'"
  using assms
proof cases
  case (RedExhale \<omega>_exh)
  then show ?thesis 
    using exhale_only_changes_total_state_aux
    unfolding havoc_locs_state_def
    by (metis (mono_tags, lifting) havoc_locs_state_same_store havoc_locs_state_same_trace \<open>\<omega>' \<in> _\<close>)
qed

(* lemma mask_update_greater_aux:
  assumes "pgte (m l) p"
  shows "m \<ge> m(l := m l - p)"
proof (simp add: le_fun_def)
  show "m l - p \<le> m l"
    unfolding minus_prat_def
    apply (simp add: less_eq_preal.rep_eq minus_preal.rep_eq)
    apply (transfer)
    by (auto)
qed

lemma mask_update_greater_aux_2:
  assumes "pgte (m l) q"
  shows "m \<ge> m(l := q)"
  using assms
  apply (simp add: le_fun_def)
  by (metis PosReal.pgte_antisym PosReal.sum_larger nle_le preal_gte_padd)

lemmas mask_update_succ_aux = succ_maskI[OF mask_update_greater_aux]
lemmas mask_update_succ_aux_2 = succ_maskI[OF mask_update_greater_aux_2]
*)


lemma dec_mh_loc_total_full_smaller:
  shows "dec_mh_loc_total_full \<omega> l p \<le> \<omega>"
  unfolding less_eq_full_total_state_ext_def
  apply (intro conjI; simp)
   apply force
  unfolding less_eq_total_state_ext_def
  apply (intro conjI; simp)
  unfolding less_eq_nested_mask_def
  apply (cases "get_nm_total_full \<omega>")
  apply (simp del: split_paired_All)
  apply (intro conjI)
   apply (simp add: le_funI less_eq_preal.rep_eq minus_preal.rep_eq prat_non_negative)
  by (smt (verit) option.exhaust option_fold.simps(1) option_fold.simps(2))


lemma nm_scale_less_eq_1:
  fixes nm :: "'a nested_mask"
  assumes "f \<le> 1"
  shows "f *\<^sub>s nm \<le> nm"
proof -
  have "f *\<^sub>s nm + (1 - f) *\<^sub>s nm = nm"
    by (metis add.commute assms greater_minus_plus preal_semimodule_class.scale_one scale_add_left)
  thus ?thesis
    by (metis nm_sum_is_bigger)
qed

lemma nm_scale_le_1:
  assumes "f \<le> 1"
  shows "nested_mask_le (f *\<^sub>s nm) nm"
  using assms less_eq_nested_mask_def nm_scale_less_eq_1
  by auto


lemma rm_from_lpm_total_full_smaller:
  shows "rm_from_lpm_total_full \<omega> lp p \<le> \<omega>"
  unfolding less_eq_full_total_state_ext_def
  apply (intro conjI; simp)
   apply force
  unfolding less_eq_total_state_ext_def
  apply (intro conjI; simp)
  unfolding less_eq_nested_mask_def
  apply (cases "get_nm_total_full \<omega>")
  apply (simp del: split_paired_All)
  apply (intro allI)
  apply (rename_tac mh fnm lp')
  apply (case_tac "lp' = lp"; simp)
   apply (case_tac "fnm lp"; simp)
   apply (rename_tac lpm)
   apply (intro impI)
   apply (cases "p = 0")
    apply (rule disjI1)
    apply (metis Rep_posreal_inverse Rep_preal_inverse add.right_neutral all_pos divide_eq_0_iff divide_preal.rep_eq greater_minus_plus preal_semimodule_class.scale_one split_pairs zero_preal.rep_eq)
   apply (rule disjI2)
   apply (intro conjI)
    apply (simp add: Abs_posreal_inverse PosReal.ppos.rep_eq gr_0_is_ppos less_eq_preal.rep_eq less_posreal.rep_eq minus_preal.rep_eq not_le_imp_less preal_not_0_gt_0)
   apply (metis (full_types) all_pos minus_preal.abs_eq nm_scale_le_1 psub_smaller zero_preal_def)
  by (smt (verit, best) option.exhaust option_fold.simps(1) option_fold.simps(2))


lemma exhale_normal_result_smaller':
  assumes "red_exhale ctxt \<omega>def A \<omega> (RNormal \<omega>')"
    shows "\<omega>' \<le>  \<omega>"
  using assms
proof (induction A arbitrary: \<omega> \<omega>')
  case (Atomic atm)
  show ?case
  proof (cases atm)
    case (Pure _)
    show ?thesis
      using Atomic[unfolded Pure] ExhPure_case exh_if_total_normal_2
      by (metis exh_if_total_normal_2 order_class.order_eq_iff result_total.distinct(5))
  next
    case (Acc e_r f perm)
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      show ?thesis
        using ExhAcc_case[OF Atomic[unfolded Acc PureExp], simplified] exh_if_total_normal_2
        by (smt (verit) dec_mh_loc_total_full_smaller order_refl)
    next
      case Wildcard
      show ?thesis
        using Atomic[unfolded Acc Wildcard]
        apply (safe elim!: ExhAcc_case; simp)
        by (metis dec_mh_loc_nm.simps dec_mh_loc_total.simps dec_mh_loc_total_full.simps dec_mh_loc_total_full_smaller exh_if_total_normal_2)
    qed
  next
    case (AccPredicate pid e_args perm)
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      then show ?thesis
        using ExhAccPred_case[OF Atomic[unfolded AccPredicate PureExp], simplified] exh_if_total_normal_2
        by (metis exhale_pred_def rm_from_lpm_total_full_smaller)
    next
      case Wildcard
      then show ?thesis
        using ExhAccPred_case[OF Atomic[unfolded AccPredicate Wildcard], simplified] exh_if_total_normal_2
        by (metis exhale_pred_def rm_from_lpm_total_full_smaller)
    qed
  qed
next
  case (Star A B)
  then show ?case
    apply (safe elim!: ExhStar_case)
    using order.trans
    by blast
qed (auto elim: red_exhale.cases)


lemma exhale_normal_result_smaller:
  assumes "red_exhale ctxt \<omega>def A \<omega> res" and
          "res = RNormal \<omega>'"
        shows "\<omega> \<succeq> \<omega>'"
  apply (rule full_total_state_gte_implies_succ)
  using assms exhale_normal_result_smaller'
   apply blast
  using exhale_only_changes_total_state_aux assms
  by fastforce


\<comment> \<open>Almost the same as the lemma above, just extracting mh and mp.\<close>
lemma exhale_smaller:
  assumes "red_exhale ctxt \<omega>_def A \<omega> (RNormal \<omega>')"
    shows "\<And>x. get_mh_total_full \<omega> x \<ge> get_mh_total_full \<omega>' x"
      and "\<And>x. get_mp_total_full \<omega> x \<ge> get_mp_total_full \<omega>' x"
proof -
  from assms(1) have "\<omega> \<succeq> \<omega>'"
    by (simp add: exhale_normal_result_smaller)
  then obtain \<omega>\<^sub>d where "\<omega>' \<oplus> \<omega>\<^sub>d = Some \<omega>"
    by (metis greater_def)
  have *: "get_nm_total_full \<omega>' + get_nm_total_full \<omega>\<^sub>d = get_nm_total_full \<omega>"
    using \<open>\<omega>' \<oplus> \<omega>\<^sub>d = Some \<omega>\<close>[unfolded plus_full_total_state_ext_def plus_total_state_ext_def]
    by (smt (verit, ccfv_SIG) Some_Some_ifD defined_def full_total_state.select_convs(3) full_total_state.surjective full_total_state.update_convs(3) get_nm_total_full.simps option.sel plus_total_state_ext_def total_state.select_convs(2) total_state.surjective total_state.update_convs(2))

  obtain mh fnm mh' fnm' mh\<^sub>d fnm\<^sub>d where
    nm_\<omega>: "get_nm_total_full \<omega> = NM mh fnm" and
    nm_\<omega>': "get_nm_total_full \<omega>' = NM mh' fnm'" and
    nm_\<omega>\<^sub>d: "get_nm_total_full \<omega>\<^sub>d = NM mh\<^sub>d fnm\<^sub>d"
    using nm_get_eq
    by blast

  fix l
  show "get_mh_total_full \<omega>' l \<le> get_mh_total_full \<omega> l"
    apply simp
    using *[simplified]
    by (metis \<open>\<omega> \<succeq> \<omega>'\<close> full_total_state_succ_implies_gte get_nm_total_full.simps le_fun_def less_eq_full_total_stateD_2 less_eq_nested_maskD)

  fix lp
  show "get_mp_total_full \<omega>' lp \<le> get_mp_total_full \<omega> lp"
    apply (simp add: nm_\<omega>[simplified] nm_\<omega>'[simplified])
    apply (cases "fnm lp"; cases "fnm' lp"; cases "fnm\<^sub>d lp")
           apply simp_all
    using fun_cong[OF conjunct2[OF *[unfolded plus_nested_mask_def nm_\<omega> nm_\<omega>' nm_\<omega>\<^sub>d, simplified]],
                   of lp, simplified pfun_comb_def, simplified]
         apply (auto simp: all_pos)
    by (simp add: padd_pgte plus_posreal.rep_eq)
qed


lemma exhale_pure_normal_same:
  assumes "red_exhale ctxt \<omega>def A \<omega> res" 
      and "res = RNormal \<omega>'"
      and "is_pure A"
    shows "\<omega> = \<omega>'"
  using assms
  by (induction) (auto elim: exh_if_total.elims)


lemma rm_from_lpm_total_full_inverse:
  assumes "\<omega>' = rm_from_lpm_total_full \<omega> lp p\<^sub>d"
      and "get_fnm_total_full \<omega>' lp = Some (p',nm')"
    shows "\<exists>p nm. get_fnm_total_full \<omega> lp = Some (p,nm) \<and> p \<ge> p' \<and> nm' = (Rep_posreal (p' / p)) *\<^sub>s nm"
  apply (rule exI[of _ "Abs_posreal (Rep_posreal p' + p\<^sub>d)"])
  apply (rule exI[of _ "((Rep_posreal p' + p\<^sub>d) / (Rep_posreal p')) *\<^sub>s nm'"])
proof (intro conjI)
  show "get_fnm_total_full \<omega> lp = Some (Abs_posreal (Rep_posreal p' + p\<^sub>d), ((Rep_posreal p' + p\<^sub>d) / (Rep_posreal p')) *\<^sub>s nm')"
  proof -
    obtain p nm where
      lpm: "get_fnm_total_full \<omega> lp = Some (p,nm)" and
      "p\<^sub>d < Rep_posreal p" and
      "p' = Abs_posreal (Rep_posreal p - p\<^sub>d)" and
      "nm' = (1 - p\<^sub>d / Rep_posreal p) *\<^sub>s nm"
      using arg_cong[OF assms(1)[simplified], of "\<lambda>\<omega>. get_fnm_total_full \<omega> lp", unfolded assms(2), simplified]
      apply (cases "get_fnm_total_full \<omega> lp"; simp)
      by (metis Pair_inject leI option.discI option.inject prod.collapse)
    show ?thesis
      unfolding lpm
      apply (rule arg_cong[where ?f=Some])
      apply standard+
      unfolding \<open>p' = _\<close>
       apply (metis Abs_posreal_inverse Rep_posreal_inverse \<open>p\<^sub>d < _\<close> add_0 all_pos greater_minus_plus mem_Collect_eq nless_le)
      unfolding \<open>nm' = _\<close> preal_semimodule_class.scale_scale
      apply (subgoal_tac "(Rep_posreal (Abs_posreal (Rep_posreal p - p\<^sub>d)) + p\<^sub>d) / Rep_posreal (Abs_posreal (Rep_posreal p - p\<^sub>d)) * (1 - p\<^sub>d / Rep_posreal p) = 1")
       apply (simp add: preal_semimodule_class.scale_one)
      apply (subgoal_tac "Rep_posreal (Abs_posreal (Rep_posreal p - p\<^sub>d)) + p\<^sub>d = Rep_posreal p")
       apply (subgoal_tac "pos_perm_class.pwrite - p\<^sub>d / Rep_posreal p = Rep_posreal (Abs_posreal (Rep_posreal p - p\<^sub>d)) / (Rep_posreal p)")
        apply (simp_all add: posreal_to_preal preal_to_real)
      using \<open>p\<^sub>d < Rep_posreal p\<close> divide_preal.rep_eq less_eq_preal.rep_eq less_preal.rep_eq minus_preal.rep_eq one_preal.rep_eq plus_preal.rep_eq times_preal.rep_eq
        apply fastforce
       apply (metis Rep_posreal Rep_preal_inverse add.commute add_diff_cancel_left' all_pos diff_divide_distrib diff_ge_0_iff_ge div_self divide_le_eq_1_pos linorder_neqE_linordered_idom linorder_not_less mem_Collect_eq prat_non_negative zero_preal.rep_eq)
      using Abs_posreal_inverse \<open>p\<^sub>d < Rep_posreal p\<close> less_eq_preal.rep_eq less_preal.rep_eq minus_preal.rep_eq zero_preal.rep_eq
      by auto
  qed

  show "p' \<le> Abs_posreal (Rep_posreal p' + p\<^sub>d)"
    by (metis Abs_posreal_inverse Rep_posreal less_eq_posreal.rep_eq mem_Collect_eq padd_pgte padd_pos pperm_pnone_pgt)

  show "nm' = Rep_posreal (p' / Abs_posreal (Rep_posreal p' + p\<^sub>d)) *\<^sub>s ((Rep_posreal p' + p\<^sub>d) / (Rep_posreal p')) *\<^sub>s nm'"
    apply (subst preal_semimodule_class.scale_scale)
    apply (subgoal_tac "Rep_posreal (p' / Abs_posreal (Rep_posreal p' + p\<^sub>d)) * ((Rep_posreal p' + p\<^sub>d) / (Rep_posreal p')) = 1")
     apply (simp add: preal_semimodule_class.scale_one)
    by (smt (verit, ccfv_threshold) Abs_posreal_inverse Rep_posreal Rep_preal_inverse div_self divide_eq_eq divide_posreal.rep_eq divide_preal.rep_eq mem_Collect_eq one_preal_def padd_pos preal_not_0_gt_0 times_divide_eq_right times_preal.rep_eq zero_preal.rep_eq)
qed


lemma exhale_fraction:
  assumes "red_exhale ctxt \<omega>\<^sub>0 A \<omega> (RNormal \<omega>')"
      and "get_fnm_total_full \<omega>' lp = Some (p', nm')"
    shows "\<exists>p nm. get_fnm_total_full \<omega> lp = Some (p, nm) \<and> p \<ge> p' \<and> nm' = (Rep_posreal (p' / p)) *\<^sub>s nm"
  using assms
proof (induction A arbitrary: \<omega> \<omega>' p' nm')
  case (Atomic atm)
  show ?case
  proof (cases atm)
    case (Pure e)
    hence "\<omega>' = \<omega>"
      by (metis Atomic.prems(1) atomic_assert.disc(1) exhale_pure_normal_same is_pure.simps(1))
    then show ?thesis
      by (metis (mono_tags, lifting) Atomic.prems(2) Rep_posreal Rep_preal_inverse div_self divide_posreal.rep_eq divide_preal.rep_eq mem_Collect_eq one_preal.rep_eq order_refl pperm_pgt_pnone preal_semimodule_class.scale_one zero_preal.abs_eq)
  next
    case (Acc e_r f perm)
    hence "get_fnm_total_full \<omega> = get_fnm_total_full \<omega>'"
    proof (cases perm)
      case (PureExp e_p)
      show ?thesis
        apply (rule ExhAcc_case[OF Atomic(1)[unfolded Acc PureExp]])
         apply simp_all
        apply (case_tac "r = Null")
         apply simp
         apply (metis exh_if_total_normal_2)
        using exh_if_total_normal_2[of _ _ \<omega>']
        by simp
    next
      case Wildcard
      show ?thesis
        apply (rule ExhAcc_case[OF Atomic(1)[unfolded Acc Wildcard]])
         apply simp_all
        using exh_if_total_normal_2[of _ _ \<omega>']
        by simp
    qed
    then show ?thesis
      by (metis (mono_tags, lifting) Atomic.prems(2) Rep_posreal Rep_preal_inverse div_self divide_posreal.rep_eq divide_preal.rep_eq mem_Collect_eq one_preal.rep_eq order_refl pperm_pgt_pnone preal_semimodule_class.scale_one zero_preal.abs_eq)
  next
    case (AccPredicate pid e_args perm)
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      obtain mp v_args v_p where
        "mp = get_mp_total_full \<omega>" and
        "red_pure_exps_total ctxt (Some \<omega>\<^sub>0) e_args \<omega> (Some v_args)" and
        "ctxt, (Some \<omega>\<^sub>0) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm v_p)" and
        res: "RNormal \<omega>' = exh_if_total (v_p \<ge> 0 \<and> mp (pid,v_args) \<ge> Abs_preal v_p)
                                        (exhale_pred \<omega> (pid,v_args) (Abs_preal v_p))"
        using Atomic AccPredicate PureExp
        by (auto elim: ExhAccPred_case)
      show ?thesis
        apply (cases "lp = (pid,v_args)")
         apply (metis Atomic.prems(2) exh_if_total_normal_2 exhale_pred_def res rm_from_lpm_total_full_inverse)
        apply (rule exI[of _ p'])
        apply (rule exI[of _ nm'])
        apply (intro conjI)
        using arg_cong[OF exh_if_total_normal_2[OF res[symmetric], unfolded exhale_pred_def], of "\<lambda>\<omega>. get_fnm_total_full \<omega> lp"] Atomic.prems(2)
          apply simp
         apply order
      by (metis (mono_tags, lifting) Rep_posreal Rep_preal_inverse div_self divide_posreal.rep_eq divide_preal.rep_eq mem_Collect_eq one_preal.rep_eq pperm_pgt_pnone preal_semimodule_class.scale_one zero_preal.abs_eq)
    next
      case Wildcard
      obtain mp v_args q where
        "mp = get_mp_total_full \<omega>" and
        "red_pure_exps_total ctxt (Some \<omega>\<^sub>0) e_args \<omega> (Some v_args)" and
        "mp (pid,v_args) \<noteq> 0 \<Longrightarrow> q > 0 \<and> mp (pid,v_args) > q" and
        res: "RNormal \<omega>' = exh_if_total (mp (pid,v_args) \<noteq> 0) (exhale_pred \<omega> (pid,v_args) q)"
        using Atomic AccPredicate Wildcard
        by (auto elim: ExhAccPredWildcard_case)
      show ?thesis
        apply (cases "lp = (pid,v_args)")
         apply (metis Atomic.prems(2) exh_if_total_normal_2 exhale_pred_def res rm_from_lpm_total_full_inverse)
        apply (rule exI[of _ p'])
        apply (rule exI[of _ nm'])
        apply (intro conjI)
        using arg_cong[OF exh_if_total_normal_2[OF res[symmetric], unfolded exhale_pred_def], of "\<lambda>\<omega>. get_fnm_total_full \<omega> lp"] Atomic.prems(2)
          apply simp
         apply order
      by (metis (mono_tags, lifting) Rep_posreal Rep_preal_inverse div_self divide_posreal.rep_eq divide_preal.rep_eq mem_Collect_eq one_preal.rep_eq pperm_pgt_pnone preal_semimodule_class.scale_one zero_preal.abs_eq)
    qed
  qed
next
  case IH: (Imp e A)
  then consider (True) "ctxt, Some \<omega>\<^sub>0 \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)" |
               (False) "ctxt, Some \<omega>\<^sub>0 \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    by (auto elim: ExhImp_case)
  then show ?case
  proof cases
    case True
    hence "red_exhale ctxt \<omega>\<^sub>0 A \<omega> (RNormal \<omega>')"
      using IH.prems(1) eval_is_deterministic(1)
      by (blast elim: ExhImp_case)
    then show ?thesis
      using IH.IH IH.prems(2)
      by blast
  next
    case False
    hence "\<omega>' = \<omega>"
      using IH.prems(1) eval_is_deterministic(1)
      by (blast elim: ExhImp_case)
    show ?thesis
      apply (rule exI[of _ p'])
      apply (rule exI[of _ nm'])
      by (metis IH.prems(2) PosReal.field_divide_inverse PosReal.field_inverse Rep_posreal \<open>\<omega>' = \<omega>\<close> divide_posreal.rep_eq dual_order.eq_iff leD mem_Collect_eq mult.commute preal_semimodule_class.scale_one)
  qed
next
  case IH: (Star A B)
  then obtain \<omega>\<^sub>A where
    redA: "red_exhale ctxt \<omega>\<^sub>0 A \<omega> (RNormal \<omega>\<^sub>A)" and
    redB: "red_exhale ctxt \<omega>\<^sub>0 B \<omega>\<^sub>A (RNormal \<omega>')"
    by (auto elim: ExhStar_case)

  from IH(2)[OF redB IH(4)] obtain p\<^sub>A nm\<^sub>A where
    lpm\<^sub>A: "get_fnm_total_full \<omega>\<^sub>A lp = Some (p\<^sub>A, nm\<^sub>A)" and
    "p' \<le> p\<^sub>A" and
    "nm' = Rep_posreal (p' / p\<^sub>A) *\<^sub>s nm\<^sub>A"
    by blast

  from IH(1)[OF redA lpm\<^sub>A] obtain p nm where
    lpm: "get_fnm_total_full \<omega> lp = Some (p, nm)" and
    "p\<^sub>A \<le> p" and
    "nm\<^sub>A = Rep_posreal (p\<^sub>A / p) *\<^sub>s nm"
    by blast

  show ?case
    apply (rule exI[of _ p])
    apply (rule exI[of _ nm])
    apply (intro conjI)
      apply fact
    using \<open>p' \<le> p\<^sub>A\<close> \<open>p\<^sub>A \<le> p\<close>
     apply order
    using \<open>nm' = _\<close>[unfolded \<open>nm\<^sub>A = _\<close> preal_semimodule_class.scale_scale]
    apply (subgoal_tac "Rep_posreal (p' / p\<^sub>A) * Rep_posreal (p\<^sub>A / p) = Rep_posreal (p' / p)")
     apply argo
    apply (thin_tac _)
    apply (simp add: posreal_to_preal preal_to_real)
    by (metis Rep_posreal mem_Collect_eq pperm_pgt_pnone preal_to_real(12) zero_preal.abs_eq)
qed (auto elim: red_exhale.cases)+


subsection \<open>Relationship inhale and exhale (Only Lemmas)\<close>

\<comment> \<open>The rest is moved to \<^file>\<open>TotalSemanticsProperties.thy\<close>.\<close>

lemma assertion_framing_state_sub_exps_not_failure:
  assumes AssertionFraming: "assertion_framing_state ctxt StateCons (Atomic atm) \<omega>_inh" 
     and  "es = sub_expressions_atomic atm"
   shows "\<not> red_pure_exps_total ctxt (Some \<omega>_inh) es \<omega>_inh None"
proof (cases es)
  case Nil
  then show ?thesis 
    by (metis Some_Some_ifD red_exp_list_failure_Nil)
next
  case (Cons e es_tl)
  then show ?thesis 
    using AssertionFraming
    unfolding \<open>es = sub_expressions_atomic atm\<close> assertion_framing_state_def
    using InhSubExpFailure
    by (metis direct_sub_expressions_assertion.simps(1) list.discI)
qed

lemma red_pure_exp_sub_exp_atomic_change_state:
  assumes RedExp: "list_all2 (\<lambda>e v. ctxt, Some \<omega>def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v) es vs"
      and OnlyMaskChanged:
          "get_store_total \<omega>_inh = get_store_total \<omega> \<and>
           get_trace_total \<omega>_inh = get_trace_total \<omega> \<and>
           get_hh_total_full \<omega>_inh = get_hh_total_full \<omega>"
      and "es = sub_expressions_atomic atm"
      and ExpConstraint: "list_all (\<lambda>e. no_perm_pure_exp e \<and> no_unfolding_pure_exp e) es"
      and AssertionFraming: "assertion_framing_state ctxt StateCons (Atomic atm) \<omega>_inh"
    shows "list_all2 (\<lambda>e v. ctxt, Some \<omega>_inh \<turnstile> \<langle>e; \<omega>_inh\<rangle> [\<Down>]\<^sub>t Val v) es vs"
proof -
  from AssertionFraming \<open>es = _\<close> have ExpInhNotFailure: "\<not> red_pure_exps_total ctxt (Some \<omega>_inh) es \<omega>_inh None"
    by (blast dest: assertion_framing_state_sub_exps_not_failure)

  from RedExp ExpConstraint ExpInhNotFailure
  show ?thesis  
  proof (induction es arbitrary: vs)
    case Nil
    then show ?case by simp
  next
    case (Cons e es)
    from this obtain v vs_tl where "vs = v#vs_tl"
      using list.exhaust_sel by blast
    with Cons have "ctxt, Some \<omega>def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"
      by blast
    moreover from Cons have "no_perm_pure_exp e \<and> no_unfolding_pure_exp e"
      by (metis list.pred_inject(2))
    ultimately have RedAux: "ctxt, Some \<omega>def \<turnstile> \<langle>e;\<omega>_inh\<rangle> [\<Down>]\<^sub>t Val v"
      using red_pure_exp_only_differ_on_mask(1) OnlyMaskChanged
      by metis
  
    moreover have RedEInh: "ctxt, Some \<omega>_inh \<turnstile> \<langle>e;\<omega>_inh\<rangle> [\<Down>]\<^sub>t Val v"
    proof (rule ccontr)
      assume "\<not> ctxt, Some \<omega>_inh \<turnstile> \<langle>e;\<omega>_inh\<rangle> [\<Down>]\<^sub>t Val v"
      hence "ctxt, Some \<omega>_inh \<turnstile> \<langle>e;\<omega>_inh\<rangle> [\<Down>]\<^sub>t VFailure"
        using red_pure_exp_different_def_state(1)[OF RedAux] Cons
        by auto
      thus False
        using Cons
        by (auto intro: red_pure_exp_intros)
    qed
  
    moreover have "\<not> red_pure_exps_total ctxt (Some \<omega>_inh) es \<omega>_inh None" (is "\<not> ?RedSubExpsFailureInh es")
    proof 
      assume "?RedSubExpsFailureInh es"
  
      hence "?RedSubExpsFailureInh (e#es)"
        using RedEInh
        by (auto intro: red_pure_exp_intros)
  
      thus False
        using Cons
        by simp
    qed
         
    ultimately show ?case 
      using Cons \<open>vs = _\<close>
      by auto       
  qed
qed


subsection \<open>Reduction of statements\<close>

lemma fold_rel_normal_only_changes_mask:
  assumes "fold_rel ctxt pred_id vs q \<omega> (RNormal \<omega>')"
  shows "get_store_total \<omega>' = get_store_total \<omega> \<and>
         get_trace_total \<omega>' = get_trace_total \<omega> \<and>
         get_hh_total_full \<omega>' = get_hh_total_full \<omega>"
  using assms
proof cases
  case (FoldRelNormal pred_decl pred_body \<omega>0 \<omega>1 nm_exh)
  then show ?thesis
    unfolding \<open>\<omega>' = _\<close>
    using exhale_only_changes_total_state_aux[OF FoldRelNormal(5), of \<omega>1]
    by fastforce
qed

lemma red_stmt_preserves_well_typed_store:
  assumes "red_stmt_total ctxt_vpr StateCons \<Lambda> stmt \<omega> res"
      and "res = RNormal \<omega>'"
      and "vpr_store_well_typed (absval_interp_total ctxt_vpr) \<Lambda> (get_store_total \<omega>)"
    shows "vpr_store_well_typed (absval_interp_total ctxt_vpr) \<Lambda> (get_store_total \<omega>')"
  using assms
proof (induction arbitrary: \<omega>')
  case (RedSkip \<Lambda> \<omega>)
  then show ?case by simp
next
  case (RedInhale A \<omega> res \<Lambda>)
  then show ?case 
    by (metis inhale_only_changes_mask)
next
  case (RedExhale \<omega> A \<omega>_exh \<omega>' \<Lambda>)
  then show ?case 
    by (metis (no_types, lifting) exhale_only_changes_total_state_aux havoc_locs_state_same_store result_total.inject)
next
  case (RedHavoc \<Lambda> x ty v \<omega>)
  then show ?case 
    unfolding vpr_store_well_typed_def
    by auto
next
  case (RedLocalAssign \<omega> e v \<Lambda> x ty)
  then show ?case 
    unfolding vpr_store_well_typed_def
    by auto
next
  case (RedMethodCall \<omega> es v_args m mdecl \<Lambda> ys v_rets resPre res resPost)
  obtain \<omega>pre where "resPre = RNormal \<omega>pre"
    using \<open>resPre = RFailure \<or> resPre = RMagic \<Longrightarrow> res = resPre\<close> \<open>res = _\<close>
    by (cases res; cases resPre; auto)

  with RedMethodCall have ResMap: "res = map_result_total (reset_state_after_call ys v_rets \<omega>) resPost"
    by blast

  with \<open>res = RNormal \<omega>'\<close> obtain \<omega>post where "resPost = RNormal \<omega>post"
    by (auto elim: map_result_total.elims)

  with \<open>res = RNormal \<omega>'\<close> ResMap have "\<omega>' = (reset_state_after_call ys v_rets \<omega> \<omega>post)"
    by simp

  moreover have "vpr_store_well_typed (absval_interp_total ctxt_vpr) \<Lambda> (map_upds (get_store_total \<omega>) ys v_rets)"
    using RedMethodCall vpr_store_well_typed_def vpr_store_well_typed_map_upds
    by fast
  ultimately show ?case
    by (simp add: reset_state_after_call_def) 
next
  case (RedUnfold \<omega> e_args v_args e_p v_p pred_id \<phi>' \<omega>' \<Lambda>)
  then show ?case
    by fastforce
(*
next
  case (RedUnfoldWildcard \<omega> e_args v_args pred_id p \<phi>' \<omega>' \<Lambda>)
  then show ?case by auto
*)   
next
  case (RedFold \<omega> e_args v_args e_p v_p pred_id res \<Lambda>)
  then show ?case
    using fold_rel_normal_only_changes_mask
    by metis
(*
next
  case (RedFoldWildcard \<omega> e_args v_args pred_id p res \<Lambda>)
  then show ?case
    using fold_rel_normal_only_changes_mask
    by metis
*)
next
  case (RedScope v \<tau> \<Lambda> scopeBody \<omega> res res_unshift)
  from this obtain \<omega>s where "res = RNormal \<omega>s"
    by (metis map_result_total.elims)

  with RedScope have "\<omega>' = unshift_state_total 1 \<omega>s"
    by simp

  have "vpr_store_well_typed (absval_interp_total ctxt_vpr) (shift_and_add \<Lambda> \<tau>) (get_store_total \<omega>s)"
  proof (rule RedScope.IH[OF \<open>res = RNormal \<omega>s\<close>])
    show "vpr_store_well_typed (absval_interp_total ctxt_vpr) (shift_and_add \<Lambda> \<tau>) (get_store_total (shift_and_add_state_total \<omega> v))"
      using RedScope vpr_store_well_typed_shift
      by fastforce
  qed
      
  then show ?case 
    unfolding \<open>\<omega>' = _\<close>
    using vpr_store_well_typed_unshift
    by auto 
next
  case (RedIfTrue \<omega> e_b \<Lambda> s_thn res s_els)
  then show ?case by blast
next
  case (RedIfFalse \<omega> e_b \<Lambda> s_els res s_thn)
  then show ?case by blast
next
  case (RedSeq \<Lambda> s1 \<omega> \<omega>' s2 res)
  then show ?case by blast
next
  case (RedSeqFailureOrMagic \<Lambda> s1 \<omega> s2)
  then show ?case by blast
qed (auto)

lemma red_stmt_preserves_labels:
  assumes "red_stmt_total ctxt_vpr StateCons \<Lambda> stmt \<omega> res" 
      and "res = RNormal \<omega>'"
      and "get_trace_total \<omega> lbl = Some \<phi>"
    shows "get_trace_total \<omega>' lbl = Some \<phi>"
  using assms
proof (induction arbitrary: \<omega>')
  case (RedInhale A \<omega> res \<Lambda>)
  then show ?case 
    by (metis inhale_only_changes_mask)
next
  case (RedExhale \<omega> A \<omega>_exh \<omega>' \<Lambda>)
  then show ?case 
    by (metis (no_types, lifting) exhale_only_changes_total_state_aux havoc_locs_state_same_trace result_total.inject)
next
  case (RedHavoc \<Lambda> x ty v \<omega>)
  then show ?case 
    using havoc_locs_state_same_trace
    by fastforce
next
  case (RedLocalAssign \<omega> e v \<Lambda> x ty)
  then show ?case by fastforce
next
  case (RedFieldAssign \<omega> e_r addr f e v ty \<Lambda>)
  then show ?case by fastforce    
next
  case (RedMethodCall \<omega> es v_args m mdecl \<Lambda> ys v_rets resPre res resPost)
  from this obtain \<omega>Post where "resPost = RNormal \<omega>Post"
    by (metis map_result_total.simps(2) map_result_total.simps(3) result_total.exhaust)
  moreover from this obtain \<omega>Pre where "resPre = RNormal \<omega>Pre"
    using RedMethodCall
    by (metis result_total.exhaust)
  ultimately have "res = map_result_total (reset_state_after_call ys v_rets \<omega>) (RNormal \<omega>Post)"
    using RedMethodCall
    by blast    
  thus ?case    
    unfolding reset_state_after_call_def
    using \<open>get_trace_total \<omega> lbl = _\<close> \<open>res = RNormal \<omega>'\<close>
    by simp    
next
  case (RedLabel \<omega>' \<omega> lbl \<Lambda>)
  then show ?case 
    by auto
next
  case (RedUnfold \<omega> e_args v_args e_p v_p pred_id \<phi>' \<omega>' \<Lambda>)
  then show ?case
    by fastforce
(*
next
  case (RedUnfoldWildcard \<omega> e_args v_args pred_id p \<phi>' \<omega>' \<Lambda>)
  then show ?case 
    by fastforce
*)
next
  case (RedFold \<omega> e_args v_args e_p v_p pred_id res \<Lambda>)
  then show ?case
    by (auto elim: FoldRelNormal_case)
(*
next
  case (RedFoldWildcard \<omega> e_args v_args pred_id p res \<Lambda>)
  then show ?case
    by (auto elim: FoldRelNormal_case)
*)
next
  case (RedScope v \<tau> \<Lambda> scopeBody \<omega> res res_unshift)
  then show ?case 
  by (cases res) simp_all
next
  case (RedIfTrue \<omega> e_b \<Lambda> s_thn res s_els)
  then show ?case by blast
next
  case (RedIfFalse \<omega> e_b \<Lambda> s_els res s_thn)
  then show ?case by blast
next
  case (RedSeq \<Lambda> s1 \<omega> \<omega>' s2 res)
  then show ?case by blast
qed (simp_all)

lemma red_stmt_preserves_unmodified_variables:
  assumes "red_stmt_total ctxt_vpr StateCons \<Lambda> stmt \<omega> res"
      and "res = RNormal \<omega>'"
      and "x \<notin> modif stmt"
    shows "get_store_total \<omega> x = get_store_total \<omega>' x"
  using assms
proof (induction arbitrary: \<omega>' x)
  case (RedInhale A \<omega> res \<Lambda>)
  then show ?case 
    by (metis inhale_only_changes_mask)
next
  case (RedExhale \<omega> A \<omega>_exh \<omega>' \<Lambda>)
  then show ?case 
    by (metis (no_types, lifting) exhale_only_changes_total_state_aux havoc_locs_state_same_store result_total.inject)
next
  case (RedHavoc \<Lambda> x ty v \<omega>)
  then show ?case by fastforce
next
  case (RedLocalAssign \<omega> e v \<Lambda> x ty)
  then show ?case by fastforce
next
  case (RedFieldAssign \<omega> e_r addr f e v ty \<Lambda>)
  then show ?case
    by fastforce
next
  case (RedMethodCall \<omega> es v_args m mdecl \<Lambda> ys v_rets resPre res resPost)
  from this obtain \<omega>Post where "resPost = RNormal \<omega>Post"
    by (metis map_result_total.simps(2) map_result_total.simps(3) result_total.exhaust)
  moreover from this obtain \<omega>Pre where "resPre = RNormal \<omega>Pre"
    using RedMethodCall
    by (metis result_total.exhaust)
  ultimately have "res = map_result_total (reset_state_after_call ys v_rets \<omega>) (RNormal \<omega>Post)"
    using RedMethodCall
    by blast
  thus ?case
    unfolding reset_state_after_call_def
    using \<open>x \<notin> modif (MethodCall ys m es)\<close> \<open>res = RNormal \<omega>'\<close>
    by auto
next
  case (RedLabel \<omega>' \<omega> lbl \<Lambda>)
  then show ?case by fastforce
next
  case (RedUnfold \<omega> e_args v_args e_p v_p pred_id \<phi>' \<omega>' \<Lambda>)
  then show ?case
    by fastforce
(*
next
  case (RedUnfoldWildcard \<omega> e_args v_args pred_id p \<phi>' \<omega>' \<Lambda>)
  then show ?case
    by fastforce
*)
next
  case (RedFold \<omega> e_args v_args e_p v_p pred_id res \<Lambda>)
  then show ?case
    by (auto elim: FoldRelNormal_case)
(*
next
  case (RedFoldWildcard \<omega> e_args v_args pred_id p res \<Lambda>)
  then show ?case
    by (auto elim: FoldRelNormal_case)
*)
next
  case (RedScope v \<tau> \<Lambda> scopeBody \<omega> res res_unshift)
  from this obtain \<omega>Body where "res = RNormal \<omega>Body"
    by (cases res) auto

  moreover from \<open>x \<notin> _\<close> have "(Suc x) \<notin> modif scopeBody"    
    by (fastforce simp: shift_down_set_def)

  ultimately have "get_store_total (shift_and_add_state_total \<omega> v) (Suc x) = get_store_total \<omega>Body (Suc x)"
    using RedScope.IH
    by blast

  hence *: "get_store_total \<omega> x = get_store_total \<omega>Body (Suc x)"
    by (simp add: shift_and_add_def)

  from \<open>res = RNormal \<omega>Body\<close> RedScope have "\<omega>' = unshift_state_total 1 \<omega>Body"
    by fastforce

  hence "get_store_total \<omega>' x = get_store_total \<omega>Body (Suc x)"
    by (simp add: unshift_2_def)    

  thus ?case
    using * by simp
next
  case (RedIfTrue \<omega> e_b \<Lambda> s_thn res s_els)
  then show ?case by fastforce
next
  case (RedIfFalse \<omega> e_b \<Lambda> s_els res s_thn)
  then show ?case by fastforce
next
  case (RedSeq \<Lambda> s1 \<omega> \<omega>' s2 res)
  then show ?case by fastforce
qed (simp_all)

lemma free_var_atomic_assertion_map_free_var_pure_exp:                                                            
  "free_var_assertion (Atomic A) = \<Union> (set (map free_var_pure_exp (sub_expressions_atomic A)))"
proof (cases A)
  case (Pure e)
  then show ?thesis by simp
next
  case (Acc e f e_p)
  thus ?thesis 
    by (cases e_p) simp_all
next
  case (AccPredicate pred es e_p)
  thus ?thesis 
    apply (cases e_p)
     apply force
    by force
qed  

lemma free_var_assertion_map_free_var_pure_exp:                                                            
  "\<Union> (set (map free_var_pure_exp (direct_sub_expressions_assertion A))) \<subseteq> free_var_assertion A"
  apply (cases A)
  using free_var_atomic_assertion_map_free_var_pure_exp
  by auto

lemma th_result_rel_convert:
  assumes "th_result_rel a b W res"
      and "a = a'"
      and "b = b'"
      and "res' = map_result_total f res"
      and "\<And> \<omega>. \<omega> \<in> W \<Longrightarrow> f \<omega> \<in> W'"
    shows "th_result_rel a' b' W' res'"
  using assms
  by (metis map_result_total.simps(1) map_result_total.simps(2) map_result_total.simps(3) th_result_rel.simps)

lemma inhale_perm_single_similar:
  assumes "\<omega> \<in> inhale_perm_single R \<omega>0 (a, f) (Some (Abs_preal p))"
      and "get_total_full \<omega> = get_total_full \<omega>'"
      and "get_store_total \<omega>' = get_store_total \<omega>1 \<and> get_trace_total \<omega>' = get_trace_total \<omega>1"
    shows "\<omega>' \<in> inhale_perm_single R \<omega>1 (a, f) (Some (Abs_preal p))"
  using assms
  unfolding inhale_perm_single_def
  oops

lemma inhale_perm_single_Some_non_empty_preserve:
  assumes WfConsistent: "wf_total_consistency ctxt R Rt"
      and OnlyStoreDifferent: "get_total_full \<omega> = get_total_full \<omega>' \<and> get_trace_total \<omega> = get_trace_total \<omega>'"
      and InhPermSingle1: "inhale_perm_single R \<omega> lh (Some p) \<noteq> {}"
    shows "inhale_perm_single R \<omega>' lh (Some p) \<noteq> {}"
proof -
  obtain \<omega>\<^sub>i where "\<omega>\<^sub>i = upd_mh_loc_total_full \<omega> lh (get_mh_total_full \<omega> lh + p) \<and> R \<omega>\<^sub>i"
    using InhPermSingle1
    unfolding inhale_perm_single_def
    by fastforce

  hence "wf_mask_simple (get_mh_total_full \<omega>\<^sub>i)"
    using WfConsistent[unfolded wf_total_consistency_def]
    by (metis get_mh_total_full.simps)

  moreover have "get_mh_total_full \<omega>\<^sub>i lh = get_mh_total_full \<omega> lh + p"
    using \<open>\<omega>\<^sub>i = _ \<and> _\<close>
    by fastforce

  ultimately have SufficientPerm: "1 \<ge> (get_mh_total_full \<omega> lh + p)"
    by (metis wf_mask_simple_def)

  let ?\<omega>0 = "(upd_mh_loc_total_full \<omega> lh (get_mh_total_full \<omega> lh + p))"
  have "?\<omega>0 \<in> inhale_perm_single R \<omega> lh (Some p)"
    using inhale_perm_single_nonempty InhPermSingle1
    by blast

  hence "R ?\<omega>0"
    unfolding inhale_perm_single_def
    by blast  
        
  let ?\<omega>1 = "upd_mh_loc_total_full \<omega>' lh (get_mh_total_full \<omega>' lh + p)"
  have "?\<omega>1 \<in> inhale_perm_single R \<omega>' lh (Some p)"
  proof (rule inhale_perm_single_elem, simp)
    show "R ?\<omega>1"
      apply (rule total_consistency_store_update[OF WfConsistent \<open>R ?\<omega>0\<close>])
      using OnlyStoreDifferent
      by auto
  next
    show "option_fold ((=) p) (p \<noteq> 0) (Some p)"
      by simp
  qed
  then show ?thesis 
    by blast
qed


subsection \<open>Temp\<close>

\<comment> \<open>Todo: The \<open>inhale\<close> part is removed.\<close>
lemma red_pure_exp_store_same_on_free_var:
  shows "ctxt, \<omega>_def_opt \<turnstile> \<langle>e;\<omega>1\<rangle> [\<Down>]\<^sub>t resE \<Longrightarrow>
         \<omega>_def_opt = Some \<omega>_def \<Longrightarrow>
        supported_pure_exp e \<Longrightarrow>
        (\<And> x. x \<in> free_var_pure_exp e \<Longrightarrow> get_store_total \<omega>1 x = get_store_total \<omega>2 x) \<Longrightarrow>     
        get_trace_total \<omega>1 = get_trace_total \<omega>2 \<and> get_total_full \<omega>1 = get_total_full \<omega>2 \<Longrightarrow>      
        get_trace_total \<omega>_def = get_trace_total \<omega>_def2 \<and> get_total_full \<omega>_def = get_total_full \<omega>_def2 \<Longrightarrow>  \<comment>\<open>just needed for IH (could also separate result on changing well-definedness state)\<close>                 
        ctxt, Some \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t resE" and
        "red_pure_exps_total ctxt \<omega>_def_opt es \<omega>1 resES \<Longrightarrow> 
         \<omega>_def_opt = Some \<omega>_def \<Longrightarrow>
         (\<And> x. x \<in> \<Union> (set (map free_var_pure_exp es)) \<Longrightarrow> get_store_total \<omega>1 x = get_store_total \<omega>2 x) \<Longrightarrow>
        get_trace_total \<omega>1 = get_trace_total \<omega>2 \<and> get_total_full \<omega>1 = get_total_full \<omega>2 \<Longrightarrow>     
        get_trace_total \<omega>_def = get_trace_total \<omega>_def2 \<and> get_total_full \<omega>_def = get_total_full \<omega>_def2 \<Longrightarrow>  \<comment>\<open>just needed for IH (could also separate result on changing well-definedness state)\<close>          
         list_all (\<lambda>e. supported_pure_exp e) es \<Longrightarrow>
         red_pure_exps_total ctxt (Some (\<omega>_def2)) es \<omega>2 resES"
proof (induction arbitrary: \<omega>_def \<omega>2 \<omega>_def2 and \<omega>_def \<omega>2 \<omega>_def2 and \<omega>2 rule: red_pure_exp_inducts)
  case (RedLit \<omega>_def l uu)
  then show ?case by (auto intro!: red_pure_exp_intros)
next
  case (RedVar \<omega> n v \<omega>_def_opt)
  then show ?case by (auto intro!: red_pure_exp_intros)
next
  case (RedBinopLazy \<omega>_def_opt e1 \<omega> v1 bop v e2)
  then show ?case by (auto intro!: red_pure_exp_intros)
next
  case (RedBinop \<omega>_def_opt e1 \<omega> v1 e2 v2 bop v)  
  hence "ctxt, Some \<omega>_def2 \<turnstile> \<langle>e1; \<omega>2\<rangle> [\<Down>]\<^sub>t Val v1" and "ctxt, Some \<omega>_def2 \<turnstile> \<langle>e2; \<omega>2\<rangle> [\<Down>]\<^sub>t Val v2"
    by fastforce+
  then show ?case
    using RedBinop.hyps(1) RedBinop.hyps(2) RedBinop.prems(1) red_pure_exp_total_red_pure_exps_total.RedBinop
    by fastforce
next
  case (RedBinopRightFailure \<omega>_def_opt e1 \<omega> v1 e2 bop)
  hence "ctxt, Some \<omega>_def2 \<turnstile> \<langle>e1; \<omega>2\<rangle> [\<Down>]\<^sub>t Val v1" and "ctxt, Some \<omega>_def2 \<turnstile> \<langle>e2; \<omega>2\<rangle> [\<Down>]\<^sub>t VFailure"
    by fastforce+
  then show ?case
    using RedBinopRightFailure.hyps(1) RedBinopRightFailure.hyps(2) RedBinopRightFailure.prems(1) red_pure_exp_total_red_pure_exps_total.RedBinopRightFailure
    by force
next
  case (RedBinopOpFailure \<omega>_def_opt e1 \<omega> v1 e2 v2 bop)
  hence "ctxt, Some \<omega>_def2 \<turnstile> \<langle>e1; \<omega>2\<rangle> [\<Down>]\<^sub>t Val v1" and "ctxt, Some \<omega>_def2 \<turnstile> \<langle>e2; \<omega>2\<rangle> [\<Down>]\<^sub>t Val v2"
    by fastforce+
  then show ?case
    apply (cases \<omega>_def_opt)
    using RedBinopOpFailure.prems(1)
     apply blast
    using RedBinopOpFailure
    apply simp
    by (metis (full_types) is_none_code(2) red_pure_exp_total_red_pure_exps_total.RedBinopOpFailure)
next
  case (RedUnop \<omega>_def_opt e \<omega> v unop v')
  then show ?case
    by (auto intro!: red_pure_exp_intros)
next
  case (RedCondExpTrue \<omega>_def_opt e1 \<omega> e2 r e3)
  then show ?case 
    by (auto intro!: TotalExpressions.RedCondExpTrue)
next
  case (RedCondExpFalse \<omega>_def_opt e1 \<omega> e3 r e2)  
  then show ?case 
    by (auto intro!: TotalExpressions.RedCondExpFalse)
next
  case (RedOld \<omega> l \<phi> \<omega>_def' \<omega>_def e v)
  then show ?case
    by (auto intro!: red_pure_exp_intros)
next
  case (RedOldFailure \<omega> l \<omega>_def e)
  then show ?case
    by (auto intro!: red_pure_exp_intros)
next
  case (RedField \<omega>_def_opt e \<omega> a f v)
  hence RedRcv: "ctxt, Some \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))"
    by simp

  from RedField have SameHeap: "get_hh_total_full \<omega>2 (a,f) = v"
    by simp

  show ?case 
  proof (cases "(a,f) \<in> get_valid_locs \<omega>_def")
    case True
    then show ?thesis 
      using RedField RedField_def_normalI[OF RedRcv SameHeap]
      unfolding get_valid_locs_def
      by auto
  next
    case False
    then show ?thesis 
      using RedField RedField_def_failureI[OF RedRcv SameHeap]
      unfolding get_valid_locs_def
      by auto
  qed
next
  case (RedFieldNullFailure \<omega>_def_opt e \<omega> f)
  then show ?case
    by (auto intro!: red_pure_exp_intros)
next
  case (RedPermNull \<omega>_def_opt e \<omega> f)
  then show ?case
    by (auto intro!: red_pure_exp_intros)
next
  case (RedPerm \<omega>_def_opt e \<omega> a f v)
  then show ?case
    by (auto intro!: red_pure_exp_intros)
next
  case (RedUnfolding ubody \<omega> v p es)
  then show ?case
    by simp
next
  case (RedUnfoldingDefNoPred \<omega>_def_opt es \<omega> vs pred_id pred_decl p ubody)
  then show ?case
    by simp \<comment>\<open>cannot occur\<close>
next
  case (RedUnfoldingDef \<omega>_def_opt es \<omega> vs p \<omega>'_def ubody v)
  then show ?case
    by simp \<comment>\<open>cannot occur\<close>
next
  case (RedSubFailure e' \<omega>_def_opt \<omega>)
  hence "list_all supported_pure_exp (sub_pure_exp_total e')"
    using pure_exp_pred_subexp by presburger
  hence "red_pure_exps_total ctxt (Some \<omega>_def2) (sub_pure_exp_total e') \<omega>2 None"
    using RedSubFailure free_var_subexp
    by blast 
  then show ?case 
    using \<open>sub_pure_exp_total e' \<noteq> []\<close>
    by (auto intro!: TotalExpressions.RedSubFailure)
next
  case (RedExpListCons \<omega>_def_opt e \<omega> v es res res')
  then show ?case
    by (auto intro!: red_pure_exp_intros)
next
  case (RedExpListFailure \<omega>_def_opt e \<omega> es)
  hence "ctxt, Some \<omega>_def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t VFailure"
    by auto
  thus ?case
    by (auto intro!: red_pure_exp_intros) 
next
  case (RedExpListNil \<omega>_def_opt \<omega>)
  then show ?case
    by (auto intro!: red_pure_exp_intros)
qed simp_all

\<comment> \<open>Todo: These are the cases for \<open>inhale\<close>\<close>
lemma red_inhale_store_same_on_free_var:
  assumes "red_inhale ctxt R A \<omega>1 res"
      and "supported_assertion A"
      and "\<And> x. x \<in> free_var_assertion A \<Longrightarrow> get_store_total \<omega>1 x = get_store_total \<omega>2 x"
      and "get_trace_total \<omega>1 = get_trace_total \<omega>2 \<and> get_total_full \<omega>1 = get_total_full \<omega>2"
      and "wf_total_consistency ctxt R Rt"
    shows "red_inhale ctxt R A \<omega>2 (map_result_total (\<lambda>\<omega>. \<omega> \<lparr> get_store_total := get_store_total \<omega>2 \<rparr>) res)"
  using assms
proof (induction arbitrary: \<omega>2 rule: red_inhale.inducts)
  case (InhAcc \<omega> e_r r e_p p W' f res)
  note WfConsistent = \<open>wf_total_consistency ctxt R Rt\<close>
  show ?case
  proof (rule red_inhale.InhAcc)
    show "ctxt, Some \<omega>2 \<turnstile> \<langle>e_r;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
      using InhAcc
      by (simp add: red_pure_exp_store_same_on_free_var(1))
  next
    show "ctxt, Some \<omega>2 \<turnstile> \<langle>e_p;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
      using InhAcc
      by (simp add: red_pure_exp_store_same_on_free_var(1))
  next
    let ?W2' = "if r = Null then {\<omega>2} else inhale_perm_single R \<omega>2 (the_address r, f) (Some (Abs_preal p))"
    show "?W2' = ?W2'"
      by simp

    from \<open>th_result_rel (0 \<le> p) (W' \<noteq> {} \<and> (0 < p \<longrightarrow> r \<noteq> Null)) W' res\<close>
    show "th_result_rel (0 \<le> p) (?W2' \<noteq> {} \<and> (0 < p \<longrightarrow> r \<noteq> Null))
             ?W2'
             (map_result_total (get_store_total_update (\<lambda>_. get_store_total \<omega>2)) res)"
    proof (rule th_result_rel_convert)
      let ?f = "get_store_total_update (\<lambda>_. get_store_total \<omega>2)"

      let ?InhSet1 = "\<lambda>a. (inhale_perm_single R \<omega> (a, f) (Some (Abs_preal p)))"
      let ?InhSet2 = "\<lambda>a. (inhale_perm_single R \<omega>2 (a, f) (Some (Abs_preal p)))"

      show "(W' \<noteq> {} \<and> (0 < p \<longrightarrow> r \<noteq> Null)) \<longleftrightarrow> (?W2' \<noteq> {} \<and> (0 < p \<longrightarrow> r \<noteq> Null))"
      proof (cases r)
        case (Address a)        
        then show ?thesis 
          unfolding \<open>W' = _\<close>          
        proof simp
          show "?InhSet1 a = {} \<longleftrightarrow> ?InhSet2 a = {}"
            using inhale_perm_single_Some_non_empty_preserve[OF WfConsistent] InhAcc
            by metis
        qed
      next
        case Null
        then show ?thesis 
          unfolding \<open>W' = _\<close>
          by simp
      qed

      show "map_result_total ?f res = map_result_total ?f res"
        by simp

      fix \<omega>Elem
      assume "\<omega>Elem \<in> W'"
      hence TraceSame: "get_trace_total \<omega>Elem = get_trace_total \<omega>"
        unfolding \<open>W' = _\<close> inhale_perm_single_def
        by (metis InhAcc(3,7) \<open>\<omega>Elem \<in> W'\<close> inhale_perm_single_trace_same singletonD)


      show "\<omega>Elem\<lparr>get_store_total := get_store_total \<omega>2\<rparr> \<in> ?W2'"
      proof (cases r)
        case (Address a)       
        with \<open>\<omega>Elem \<in> W'\<close> inhale_perm_single_nonempty have 
         "\<omega>Elem = upd_mh_loc_total_full \<omega> (a,f) (get_mh_total_full \<omega> (a,f) + Abs_preal p)"
          unfolding \<open>W' = _\<close>
          by fastforce

        from \<open>r = _\<close> 
        show ?thesis
        proof (simp)
          show "\<omega>Elem\<lparr>get_store_total := get_store_total \<omega>2\<rparr> \<in> inhale_perm_single R \<omega>2 (a, f) (Some (Abs_preal p))"
          proof (rule inhale_perm_single_elem)
            show "\<omega>Elem\<lparr>get_store_total := get_store_total \<omega>2\<rparr> = upd_mh_loc_total_full \<omega>2 (a, f) (get_mh_total_full \<omega>2 (a, f) + Abs_preal p)"
              unfolding \<open>\<omega>Elem = _\<close>
            proof -
              have "upd_mh_loc_total_full \<omega> (a, f) (get_mh_total_full \<omega> (a, f) + (Abs_preal p))\<lparr>get_store_total := get_store_total \<omega>2\<rparr> = 
                    upd_mh_loc_total_full (\<omega>\<lparr>get_store_total := get_store_total \<omega>2\<rparr>) (a,f) (get_mh_total_full \<omega> (a, f) + Abs_preal p)"
                by force
              moreover have "(\<omega>\<lparr>get_store_total := get_store_total \<omega>2\<rparr>) = \<omega>2"
                apply (rule full_total_state.equality)
                by (auto simp: TraceSame InhAcc)
              ultimately show 
                "upd_mh_loc_total_full \<omega> (a, f) (get_mh_total_full \<omega> (a, f) + Abs_preal p)\<lparr>get_store_total := get_store_total \<omega>2\<rparr> =
                 upd_mh_loc_total_full \<omega>2 (a, f) (get_mh_total_full \<omega>2 (a, f) + Abs_preal p)"
                using InhAcc
                by force
            qed
          next
            show "R (\<omega>Elem\<lparr>get_store_total := get_store_total \<omega>2\<rparr>)"
            proof -
              from \<open>\<omega>Elem \<in> _\<close> have "R \<omega>Elem"
                unfolding \<open>W' = _\<close> inhale_perm_single_def \<open>r = _\<close>
                by auto
              thus "R (\<omega>Elem\<lparr>get_store_total := get_store_total \<omega>2\<rparr>)"
                using total_consistency_store_update[OF WfConsistent]
                by auto
            qed
          qed simp
        qed
      next
        case Null
        then show ?thesis
          apply simp                    
          apply (rule full_total_state.equality)
             apply simp
            apply (simp add: TraceSame InhAcc)
          apply simp
          using InhAcc
          apply (metis \<open>\<omega>Elem \<in> W'\<close> singletonD)
          by simp          
      qed
    qed (simp)
  qed
next
  case (InhPure \<omega> e b)
  hence "ctxt, Some \<omega>2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool b)"
    by (simp add: red_pure_exp_store_same_on_free_var(1))
  moreover have "\<omega>\<lparr>get_store_total := get_store_total \<omega>2\<rparr> = \<omega>2"
    apply (rule full_total_state.equality)
    by (auto simp: InhPure)
  ultimately show ?case
    using red_inhale.InhPure
    by fastforce    
next
  case (InhSubExpFailure A \<omega>)
  moreover from this have "list_all supported_pure_exp (direct_sub_expressions_assertion A)"
    using assert_pred_subexp
    by (metis list.pred_mono_strong pure_exp_pred.simps)
  moreover have
    FreeVar: "\<And>x. x \<in> \<Union> (set (map free_var_pure_exp (direct_sub_expressions_assertion A))) \<Longrightarrow> get_store_total \<omega> x = get_store_total \<omega>2 x" 
    using free_var_assertion_map_free_var_pure_exp InhSubExpFailure
    by blast    
  ultimately show ?case 
    using InhSubExpFailure red_inhale.InhSubExpFailure
    by (metis map_result_total.simps(3) red_pure_exp_store_same_on_free_var(2))
next
  case (InhStarNormal A \<omega> \<omega>'' B res)
  let ?\<omega>''2 = "(\<omega>'' \<lparr> get_store_total := get_store_total \<omega>2 \<rparr>)"
  from InhStarNormal have "red_inhale ctxt R A \<omega>2 (RNormal ?\<omega>''2)"
    by simp
  moreover have "red_inhale ctxt R B ?\<omega>''2
                             (map_result_total (get_store_total_update (\<lambda>_. get_store_total ?\<omega>''2)) res)"
  proof (rule InhStarNormal(4))
    from InhStarNormal show "supported_assertion B"
      by (meson assert_pred.simps assert_pred_rec.simps(4))
  next
    fix x 
    assume "x \<in> free_var_assertion B"
    hence "x \<in> free_var_assertion (A&&B)"
      by simp
    have "get_store_total \<omega>'' = get_store_total \<omega>"
      using InhStarNormal inhale_only_changes_mask
      by metis
    thus "get_store_total \<omega>'' x = get_store_total (\<omega>''\<lparr>get_store_total := get_store_total \<omega>2\<rparr>) x"
      using InhStarNormal(6) \<open>x \<in> free_var_assertion (A&&B)\<close>
      by auto
  qed (insert \<open>wf_total_consistency ctxt R Rt\<close>, simp)
  ultimately show ?case
    by (auto intro!: red_inhale.InhStarNormal)
next
  case (InhStarFailureMagic A \<omega> resA B)
  then show ?case
    by (metis UnCI assert_pred.elims(2) assert_pred_rec.simps(4) free_var_assertion.simps(4) map_result_total.simps(2) map_result_total.simps(3) red_inhale.InhStarFailureMagic)
    (* by (auto intro!: red_pure_exp_intros simp: red_pure_exp_store_same_on_free_var) *)
next
  case (InhImpTrue \<omega> e A res)
  then show ?case
    by (smt (verit) UnCI assert_pred.elims(2) assert_pred_rec.simps(2) free_var_assertion.simps(2) full_total_state.fold_congs(1) map_result_total.elims map_result_total.simps(1) pure_exp_pred.simps red_inhale.InhImpTrue red_pure_exp_store_same_on_free_var(1))
    (* by (auto intro!: red_pure_exp_intros) *)
next
  case (InhImpFalse \<omega> e res A)
  hence "ctxt, Some \<omega>2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    by (simp add: red_pure_exp_store_same_on_free_var(1))
  hence "red_inhale ctxt R (Imp e A) \<omega>2 (RNormal \<omega>2)"
    by (auto intro!: red_inhale.InhImpFalse)
  moreover have "\<omega>2 = \<omega>\<lparr>get_store_total := get_store_total \<omega>2\<rparr>"
    apply (rule full_total_state.equality)
    using InhImpFalse
    by auto
  ultimately show ?case
    by (simp add: InhImpFalse.hyps(2))
next
  case (InhCondAssertTrue \<omega> e A res B)
  moreover from this have "red_inhale ctxt R A \<omega>2 (map_result_total (get_store_total_update (\<lambda>_. get_store_total \<omega>2)) res)"
    by auto
  ultimately show ?case
    by (simp add: red_inhale.InhCondAssertTrue red_pure_exp_store_same_on_free_var(1))
next
  case (InhCondAssertFalse \<omega> e B res A)
  moreover from this have "red_inhale ctxt R B \<omega>2 (map_result_total (get_store_total_update (\<lambda>_. get_store_total \<omega>2)) res)"
    by auto
  ultimately show ?case
    by (simp add: red_inhale.InhCondAssertFalse red_pure_exp_store_same_on_free_var(1))
qed simp_all


lemma assertion_framing_store_same_on_free_var:
  assumes "wf_total_consistency ctxt StateCons StateCons_t"
      and "assertion_framing_state ctxt StateCons A \<omega>"
      and "\<And> x. x \<in> free_var_assertion A \<Longrightarrow> get_store_total \<omega> x = get_store_total \<omega>' x"
      and "get_trace_total \<omega> = get_trace_total \<omega>' \<and> get_total_full \<omega> = get_total_full \<omega>'"
      and "supported_assertion A"
    shows "assertion_framing_state ctxt StateCons A \<omega>'"
  unfolding assertion_framing_state_def
proof (rule allI | rule impI)+
  fix res
  assume RedInh: "red_inhale ctxt StateCons A \<omega>' res"

  show "res \<noteq> RFailure"
  proof 
    assume "res = RFailure"
    hence "red_inhale ctxt StateCons A \<omega> RFailure"
      using red_inhale_store_same_on_free_var RedInh assms
      by (metis map_result_total.simps(3))      
    thus False
      using assms(2)
      unfolding assertion_framing_state_def
      by blast
  qed
qed


lemma exh_if_total_map_stmt_result_total:
  assumes "b \<longleftrightarrow> b'"
      and "\<omega> = f \<omega>'"
    shows "exh_if_total b \<omega> = map_result_total f (exh_if_total b' \<omega>')" 
  using assms
  apply (cases "exh_if_total b \<omega>")
  apply (erule exh_if_total.elims, simp, simp)+
  done


lemma red_exhale_accI:
  assumes "ctxt, (Some \<omega>0) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
      and "ctxt, (Some \<omega>0) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
      and "a = the_address r"      
      and "\<omega>' = (if r = Null then \<omega> else dec_mh_loc_total_full \<omega> (a,f) (Abs_preal p))" (is "\<omega>' = ?\<omega>def")      
      and "res = exh_if_total (p \<ge> 0 \<and> (if r = Null then p = 0 else get_mh_total_full \<omega> (a,f) \<ge> Abs_preal p)) \<omega>'" 
    shows "red_exhale ctxt \<omega>0 (Atomic (Acc e_r f (PureExp e_p))) \<omega> res"
  unfolding \<open>res = _\<close> \<open>\<omega>' = _\<close>
  apply (rule ExhAcc)
  using assms
  by auto


lemma exhale_same_on_free_var:
  assumes "red_exhale ctxt \<omega>def1 A \<omega>1 res1"
      and "res2 = map_result_total (\<lambda>\<omega>. \<omega> \<lparr> get_store_total := get_store_total \<omega>2 \<rparr>) res1"
      and "\<And> x. x \<in> free_var_assertion A \<Longrightarrow> get_store_total \<omega>1 x = get_store_total \<omega>2 x"
      and "get_trace_total \<omega>1 = get_trace_total \<omega>2 \<and> get_total_full \<omega>1 = get_total_full \<omega>2"
      and "get_trace_total \<omega>def1 = get_trace_total \<omega>def2 \<and> get_total_full \<omega>def1 = get_total_full \<omega>def2"
      and "supported_assertion A"      
    shows "red_exhale ctxt \<omega>def2 A \<omega>2 res2"
  using assms
proof (induction arbitrary: \<omega>2 res2)
  case (ExhAcc mh \<omega> e_r r e_p p a f)

  hence ConstraintExp: "supported_pure_exp e_r \<and> supported_pure_exp e_p"
    by simp

  from ExhAcc have FreeVarExp: "\<And>x. x \<in> free_var_pure_exp e_r \<Longrightarrow> get_store_total \<omega> x = get_store_total \<omega>2 x"
                               "\<And>x. x \<in> free_var_pure_exp e_p \<Longrightarrow> get_store_total \<omega> x = get_store_total \<omega>2 x"
    by simp_all

  with ConstraintExp have RedRef: "ctxt, Some \<omega>def2 \<turnstile> \<langle>e_r;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VRef r)" and
                          RedPerm: "ctxt, Some \<omega>def2 \<turnstile> \<langle>e_p;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
    using ConstraintExp ExhAcc.hyps(2,3) ExhAcc.prems(3,4) FreeVarExp(2) red_pure_exp_store_same_on_free_var(1)
    by blast+

  let ?\<omega>' = "(if r = Null then \<omega>2 else dec_mh_loc_total_full \<omega>2 (the_address r, f) (Abs_preal p))"
  show ?case
  proof (rule red_exhale_accI[OF RedRef RedPerm], simp, simp)
    show "res2 = exh_if_total (0 \<le> p \<and> (if r = Null then p = 0 else get_mh_total_full \<omega>2 (the_address r, f) \<ge> Abs_preal p)) ?\<omega>'"
    proof (cases r)
      case (Address a')
      hence "r = Address a"
        using ExhAcc
        by simp

      show ?thesis 
        unfolding \<open>r = Address a\<close> \<open>res2 = _\<close>
        apply (rule HOL.sym, simp, rule exh_if_total_map_stmt_result_total)
         apply (simp add: ExhAcc.hyps(1) ExhAcc.prems(3))
        using ExhAcc.prems(3)
        by auto
    next
      case Null
      then show ?thesis 
        apply (simp add: \<open>res2 = _\<close>)
        apply (rule HOL.sym)
        apply (rule exh_if_total_map_stmt_result_total)
         apply simp
          apply (rule full_total_state.equality)
        by (simp_all add: ExhAcc)      
    qed
  qed      
next
  case (ExhPure e \<omega> b)
  hence "supported_pure_exp e"
    by simp
  with ExhPure have "ctxt, Some \<omega>def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool b)"
    by (simp add: red_pure_exp_store_same_on_free_var(1))   
  moreover have "\<omega>2 = \<omega>\<lparr>get_store_total := get_store_total \<omega>2\<rparr>"
    apply (rule full_total_state.equality)
    by (auto simp: ExhPure)
  ultimately show ?case
    using TotalInhaleExhale.ExhPure
    by (metis (full_types) ExhPure.prems(1) exh_if_total.simps(1,2) map_result_total.simps(1,3))
next
  case (ExhStarNormal A \<omega> \<omega>'' B res)
  let ?\<omega>''2 = "\<omega>'' \<lparr> get_store_total := get_store_total \<omega>2 \<rparr>"
  from ExhStarNormal have RedExhA: "red_exhale ctxt \<omega>def2 A \<omega>2 (RNormal ?\<omega>''2)"
    by auto

  moreover have "red_exhale ctxt \<omega>def2 B ?\<omega>''2 (map_result_total (get_store_total_update (\<lambda>_. get_store_total ?\<omega>''2)) res)"
  proof (rule ExhStarNormal.IH(2))
    fix x
    assume "x \<in> free_var_assertion B"
    show "get_store_total \<omega>'' x = get_store_total ?\<omega>''2 x"
    proof -
      have "get_store_total \<omega>'' = get_store_total \<omega>"
        using exhale_only_changes_total_state_aux ExhStarNormal
        by blast
      moreover have "get_store_total ?\<omega>''2 = get_store_total \<omega>2"
        using exhale_only_changes_total_state_aux RedExhA
        by blast
      ultimately show ?thesis
        using ExhStarNormal \<open>x \<in> _\<close>
        by simp
    qed
  qed (insert ExhStarNormal, auto)

  ultimately show ?case 
    using \<open>res2 = _\<close>
    by (auto intro: red_exhale.intros)
next
  case (ExhStarFailure A \<omega> B)
  then show ?case 
  by (auto intro: red_exhale.intros)
next
  case (ExhImpTrue e \<omega> A res)  
  hence "supported_pure_exp e"
    by (meson assert_pred.elims(2) assert_pred_rec.simps(2) pure_exp_pred.elims(2))
  with ExhImpTrue have "ctxt, Some \<omega>def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
    using red_pure_exp_store_same_on_free_var(1)
    by (metis UnCI free_var_assertion.simps(2))
  thus ?case
    using ExhImpTrue
    by (auto intro: red_exhale.intros)  
next
  case (ExhImpFalse e \<omega> A)
  hence "supported_pure_exp e"
    by (meson assert_pred.elims(2) assert_pred_rec.simps(2) pure_exp_pred.elims(2))
  with ExhImpFalse have "ctxt, Some \<omega>def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    using red_pure_exp_store_same_on_free_var(1)
    by (metis UnCI free_var_assertion.simps(2))
  moreover have "\<omega>2 = \<omega> \<lparr> get_store_total := get_store_total \<omega>2 \<rparr>"
    apply (rule full_total_state.equality)
    using ExhImpFalse
    by auto
  ultimately show ?case
    using ExhImpFalse
    by (metis map_result_total.simps(1) red_exhale.ExhImpFalse)
next
  case (ExhCondTrue e \<omega> A res B)
  hence "supported_pure_exp e"
    by auto
  hence "ctxt, Some \<omega>def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
    using red_pure_exp_store_same_on_free_var(1)
    by (metis ExhCondTrue.hyps(1) ExhCondTrue.prems(2) ExhCondTrue.prems(3) ExhCondTrue.prems(4) UnCI free_var_assertion.simps(3))
  thus ?case
    using ExhCondTrue
    by (auto intro: red_exhale.intros)
next
  case (ExhCondFalse e \<omega> B res A)
  hence "supported_pure_exp e"
    by auto
  hence "ctxt, Some \<omega>def2 \<turnstile> \<langle>e;\<omega>2\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    using red_pure_exp_store_same_on_free_var(1)
    by (metis ExhCondFalse.hyps(1) ExhCondFalse.prems(2) ExhCondFalse.prems(3) ExhCondFalse.prems(4) UnCI free_var_assertion.simps(3))
  thus ?case
    using ExhCondFalse
    by (auto intro: red_exhale.intros)
next
  case (ExhSubExpFailure A \<omega>)
  hence "list_all supported_pure_exp (direct_sub_expressions_assertion A)"
    by (metis assert_pred_subexp list.pred_mono_strong pure_exp_pred.simps)
  with ExhSubExpFailure have "red_pure_exps_total ctxt (Some \<omega>def2) (direct_sub_expressions_assertion A) \<omega>2 None"
    using red_pure_exp_store_same_on_free_var(2) assert_pred_subexp free_var_assertion_map_free_var_pure_exp
    by blast
  then show ?case 
    using ExhSubExpFailure    
    by (auto intro: TotalInhaleExhale.ExhSubExpFailure)
qed (simp_all)


end
