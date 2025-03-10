section \<open>Key Properties of THSem\<close>

theory TotalSemanticsProperties
  imports TotalSemProperties TotalExtConsProps
begin


subsection \<open>Expression Evaluation Properties\<close>

inductive_cases RedResult_case: "ctxt, \<omega>_def \<turnstile> \<langle>Result; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"

lemma eval_binop_with_True:
  assumes "eval_binop False v1 bop v2 = BinopNormal v"
    shows "eval_binop True v1 bop v2 = BinopNormal v"
  using assms
  apply (cases v1; cases v2; simp; cases bop; simp)
  by (meson binop_result.distinct(5) binop_result.inject)+

lemma eval_binop_with_True_no_type_error:
  assumes "eval_binop False v1 bop v2 \<noteq> BinopTypeFailure"
    shows "eval_binop True v1 bop v2 \<noteq> BinopTypeFailure"
  using assms
  by (cases v1; cases v2; simp; cases bop; simp)


lemma eval_with_None_helper:
  assumes "\<And>e v. e \<in> set es \<Longrightarrow>
                  ctxt, \<omega>_def\<^sub>1 \<turnstile> \<langle>e;\<omega>\<^sub>1\<rangle> [\<Down>]\<^sub>t Val v \<Longrightarrow>
                  ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v"
      and "red_pure_exps_total ctxt \<omega>_def\<^sub>1 es \<omega>\<^sub>1 (Some vs)"
    shows "red_pure_exps_total ctxt \<omega>_def\<^sub>2 es \<omega>\<^sub>2 (Some vs)"
  using assms
proof (induction es arbitrary: vs)
  case Nil
  then show ?case
    using RedExpListNil red_exp_list_failure_Nil
    by blast
next
  case IH: (Cons e es)
  then obtain v res where
    "ctxt, \<omega>_def\<^sub>1 \<turnstile> \<langle>e;\<omega>\<^sub>1\<rangle> [\<Down>]\<^sub>t Val v" and
    es_eval\<^sub>1: "red_pure_exps_total ctxt \<omega>_def\<^sub>1 es \<omega>\<^sub>1 res" and
    "Some vs = map_option (\<lambda>vs. (v#vs)) res"
    by (auto elim: RedExpListCons_case)
  then obtain vs' where "res = Some vs'"
    by fastforce
  show ?case
    apply (rule RedExpListCons)
      apply (rule IH(2))
       apply simp
      apply fact
     apply (rule IH(1))
    using IH(2)
      apply force
     apply (rule es_eval\<^sub>1[unfolded \<open>res = _\<close>])
    by (simp add: \<open>Some vs = _\<close> \<open>res = _\<close>)
qed


lemma eval_with_None:
  assumes "ctxt, Some \<omega>\<^sub>0 \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"
  shows "ctxt, None \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"
  using assms
proof (induction e arbitrary: \<omega>\<^sub>0 \<omega> v)
  case (ELit l)
  then show ?case
    by (metis RedLit RedLit_case)
next
  case (Var x)
  then show ?case
    by (meson RedVar RedVar_case)
next
  case IH: (Unop uop e)
  then obtain v' where
    "ctxt, Some \<omega>\<^sub>0 \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val v'" and
    "eval_unop uop v' = BinopNormal v"
    by (auto elim: RedUnop_case)
  show ?case
    apply (rule RedUnop)
     apply (rule IH(1))
    by fact+
next
  case IH: (Binop e1 bop e2)
  then show ?case
    using eval_binop_with_True is_none_code(2)
    by (smt (verit, ccfv_threshold) RedBinop_case is_none_code(2) red_exp_intros(4) red_exp_intros(5))
next
  case (CondExp cond e1 e2)
  then show ?case
    by (fastforce elim: RedCondExpFalse RedCondExpTrue RedCondExp_case)
next
  case IH: (FieldAcc e f)
  then show ?case
    by (fastforce intro: RedField_no_def_normalI elim: RedField_case)
next
  case IH: (Old lbl e)
  then obtain \<phi> \<omega>_def' where
    "get_trace_total \<omega> lbl = Some \<phi>" and
    "\<omega>_def' = map_option (\<lambda>\<omega>_def_val. \<omega>_def_val\<lparr> get_total_full := \<phi> \<rparr>) (Some \<omega>\<^sub>0)" and
    e_eval: "ctxt, \<omega>_def' \<turnstile> \<langle>e; \<omega>\<lparr> get_total_full := \<phi> \<rparr>\<rangle> [\<Down>]\<^sub>t Val v"
    by (auto elim: RedOld_case)
  show ?case
    apply (rule RedOld)
      apply fact
     apply simp
    using IH.IH \<open>\<omega>_def' = _\<close> e_eval
    by auto
next
  case IH: (Perm e f)
  then show ?case
    by (fastforce intro: RedPerm RedPermNull elim: RedPerm_case)  (* This is concise. Learn why it works. *)
next
  case Result
  then show ?case
    by (meson RedResult RedResult_case)
next
  case IH: (Unfolding pid es ubody)
  obtain vs perm nm' \<omega>'_def where
    "red_pure_exps_total ctxt (Some \<omega>\<^sub>0) es \<omega> (Some vs)" and
    "perm = get_mp_total_full \<omega>\<^sub>0 (pid,vs)" and
    "perm > 0" and
    "shift_up pid vs (perm / Abs_preal 2) (get_nm_total_full \<omega>\<^sub>0) nm'" and
    "\<omega>'_def = upd_nm_total_full \<omega>\<^sub>0 nm'" and
    "ctxt, Some \<omega>'_def \<turnstile> \<langle>ubody; \<omega>\<rangle> [\<Down>]\<^sub>t Val v"
    apply (rule RedUnfoldingDef_case[OF IH(3)])
    by simp
  hence "red_pure_exps_total ctxt None es \<omega> (Some vs)"
    using IH.IH(1) eval_with_None_helper
    by blast
  show ?case
    apply (rule RedUnfolding)
     apply fact
    apply (rule IH(2))
    by fact
qed (fastforce elim: red_pure_exp_total.cases)+


lemma eval_with_same_store_same_hh:
  shows "ctxt, \<omega>_def\<^sub>1 \<turnstile> \<langle>e;\<omega>\<^sub>1\<rangle> [\<Down>]\<^sub>t r\<^sub>1 \<Longrightarrow>
         ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t r\<^sub>2 \<Longrightarrow>
         r\<^sub>1 = Val v\<^sub>1 \<Longrightarrow>
         r\<^sub>2 = Val v\<^sub>2 \<Longrightarrow>
         supported_pred_expr e \<Longrightarrow>
         get_hh_total_full \<omega>\<^sub>1 = get_hh_total_full \<omega>\<^sub>2 \<Longrightarrow>
         get_store_total \<omega>\<^sub>1 = get_store_total \<omega>\<^sub>2 \<Longrightarrow>
         v\<^sub>1 = v\<^sub>2" and
    "red_pure_exps_total ctxt \<omega>_def\<^sub>1 es \<omega>\<^sub>1 rs\<^sub>1 \<Longrightarrow>
         red_pure_exps_total ctxt \<omega>_def\<^sub>2 es \<omega>\<^sub>2 rs\<^sub>2 \<Longrightarrow>
         rs\<^sub>1 = Some vs\<^sub>1 \<Longrightarrow>
         rs\<^sub>2 = Some vs\<^sub>2 \<Longrightarrow>
         list_all supported_pred_expr es \<Longrightarrow>
         get_hh_total_full \<omega>\<^sub>1 = get_hh_total_full \<omega>\<^sub>2 \<Longrightarrow>
         get_store_total \<omega>\<^sub>1 = get_store_total \<omega>\<^sub>2 \<Longrightarrow>
         vs\<^sub>1 = vs\<^sub>2"
proof (induction arbitrary: v\<^sub>1 r\<^sub>2 v\<^sub>2 \<omega>_def\<^sub>2 and vs\<^sub>1 rs\<^sub>2 vs\<^sub>2 rule: red_pure_exp_inducts)
  case (RedLit \<omega>_def l \<omega>\<^sub>1)
  then show ?case
    by (metis RedLit_case extended_val.inject)
next
  case (RedVar \<omega>\<^sub>1 n v\<^sub>1 \<omega>_def)
  then show ?case
    by (metis RedVar_case option.inject)
next
  case (RedResult \<omega> v \<omega>_def)
  then show ?case
    by (metis eval_is_deterministic(1) extended_val.inject red_pure_exp_total_red_pure_exps_total.RedResult)
next
  case IH: (RedBinopLazy \<omega>_def\<^sub>1 e1 \<omega>\<^sub>1 v1\<^sub>1 bop v e2)
  obtain v1\<^sub>2 where "ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e1;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v1\<^sub>2"
    by (metis IH.prems(1) IH.prems(3) red_pure_exp_total_elims(4))
  moreover hence "v1\<^sub>1 = v1\<^sub>2"
    using IH.IH(2) IH.prems(4) IH.prems(5) IH.prems(6)
    by auto
  ultimately show ?case
    using IH.hyps IH.prems(1) IH.prems(2) IH.prems(3) RedBinopLazy eval_is_deterministic(1)
    by blast
next
  case IH: (RedBinop \<omega>_def\<^sub>1 e1 \<omega>\<^sub>1 v1\<^sub>1 e2 v2\<^sub>1 bop v)
  from IH(7,9) obtain v1\<^sub>2 where v1\<^sub>2: "ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e1;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v1\<^sub>2"
    by (blast elim: RedBinop_case)
  moreover hence v1_uni: "\<And>v. ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e1;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v \<Longrightarrow> v = v1\<^sub>2"
    using eval_is_deterministic(1) by blast
  moreover from v1\<^sub>2 IH have "v1\<^sub>1 = v1\<^sub>2"
    by (metis pure_exp_pred.elims(2) pure_exp_pred_rec.simps(4))
  ultimately obtain v2\<^sub>2 where v2\<^sub>2: "ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e2;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v2\<^sub>2"
    by (metis IH.hyps(1) IH.prems(1) IH.prems(3) RedBinop_case option.distinct(1))
  hence "v2\<^sub>1 = v2\<^sub>2"
    using IH(10) IH(11) IH(12) IH(4)
    by auto

  have "eval_binop (Option.is_none \<omega>_def\<^sub>2) v1\<^sub>2 bop v2\<^sub>2 \<noteq> BinopOpFailure"
    using IH.hyps(1) IH.prems(1) IH.prems(3) RedBinopOpFailure \<open>v1\<^sub>1 = v1\<^sub>2\<close> eval_is_deterministic(1) extended_val.discI v1\<^sub>2 v2\<^sub>2
    by blast
  hence "eval_binop (Option.is_none \<omega>_def\<^sub>2) v1\<^sub>2 bop v2\<^sub>2 = BinopNormal v"
    using IH(6) eval_total_non_total_not_fail_same \<open>v1\<^sub>1 = v1\<^sub>2\<close> \<open>v2\<^sub>1 = v2\<^sub>2\<close>
    by blast
  then show ?case
    using IH.hyps(1) IH.prems(1) IH.prems(2) IH.prems(3) RedBinop \<open>v1\<^sub>1 = v1\<^sub>2\<close> eval_is_deterministic v1\<^sub>2 v2\<^sub>2
    by blast
next
  case (RedBinopRightFailure \<omega>_def e1 \<omega> v1 e2 bop)
  then show ?case
    by fastforce
next
  case (RedBinopOpFailure \<omega>_def e1 \<omega> v1 e2 v2 bop)
  then show ?case
    by fastforce
next
  case IH: (RedUnop \<omega>_def\<^sub>1 e \<omega>\<^sub>1 v unop v')
  then obtain v\<^sub>2 where v\<^sub>2: "ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v\<^sub>2"
    by (blast elim: RedUnop_case)
  hence v_uni: "\<And>v. ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v \<Longrightarrow> v = v\<^sub>2"
    using eval_is_deterministic
    by blast
  have "v = v\<^sub>2"
    using IH(2)[OF v\<^sub>2, of v v\<^sub>2] IH.prems(4) IH.prems(5) IH.prems(6)
    by auto
  then show ?case
    using IH.hyps IH.prems(1) IH.prems(2) IH.prems(3) RedUnop eval_is_deterministic v\<^sub>2
    by blast
next
  case IH: (RedCondExpTrue \<omega>_def e1 \<omega> e2 r e3)
  then obtain v1\<^sub>2 where v1\<^sub>2: "ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e1;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v1\<^sub>2"
    by (blast elim: RedCondExp_case)
  with IH have "v1\<^sub>2 = VBool True"
    by fastforce

  have "\<And>v. ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e1;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v \<Longrightarrow> v = VBool True"
    using eval_is_deterministic v1\<^sub>2 \<open>v1\<^sub>2 = VBool True\<close>
    by blast
  then obtain v2\<^sub>2 where v2\<^sub>2: "ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e2;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v2\<^sub>2"
    using IH.prems(1) IH.prems(3) RedCondExp_case
    by blast
  then show ?case
    by (metis IH.IH(4) IH.prems(1) IH.prems(2) IH.prems(3) IH.prems(4) IH.prems(5) IH.prems(6) RedCondExpTrue \<open>\<And>thesis. (\<And>v1\<^sub>2. ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e1;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v1\<^sub>2 \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>\<And>v. ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e1;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v \<Longrightarrow> v = VBool True\<close> eval_is_deterministic(1) pure_exp_pred.elims(1) pure_exp_pred_rec.simps(5))
next
  case IH: (RedCondExpFalse \<omega>_def e1 \<omega> e3 r e2)
  then obtain v1\<^sub>2 where v1\<^sub>2: "ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e1;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v1\<^sub>2"
    by (blast elim: RedCondExp_case)
  with IH have "v1\<^sub>2 = VBool False"
    by fastforce

  have "\<And>v. ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e1;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v \<Longrightarrow> v = VBool False"
    using eval_is_deterministic v1\<^sub>2 \<open>v1\<^sub>2 = VBool False\<close>
    by blast
  then obtain v3\<^sub>2 where v3\<^sub>2: "ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e3;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v3\<^sub>2"
    using IH.prems(1) IH.prems(3) RedCondExp_case
    by blast
  then show ?case
    by (metis IH.IH(4) IH.prems(1) IH.prems(2) IH.prems(3) IH.prems(4) IH.prems(5) IH.prems(6) RedCondExpFalse \<open>\<And>thesis. (\<And>v1\<^sub>2. ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e1;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v1\<^sub>2 \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>\<And>v. ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e1;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v \<Longrightarrow> v = VBool False\<close> eval_is_deterministic(1) pure_exp_pred.elims(1) pure_exp_pred_rec.simps(5))
next
  case (RedOld \<omega> l \<phi> \<omega>_def' \<omega>_def e v)
  then show ?case
    by auto
next
  case (RedOldFailure \<omega> l \<omega>_def e)
  then show ?case
    by blast
next
  case IH: (RedField \<omega>_def e \<omega> a f v)
  then obtain r\<^sub>2 where r\<^sub>2: "ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val r\<^sub>2"
    by (blast elim: RedField_case)
  with IH have "r\<^sub>2 = VRef (Address a)"
    by fastforce
  then show ?case
    by (metis IH.hyps IH.prems(1) IH.prems(2) IH.prems(3) IH.prems(5) RedFieldNormal_case eval_is_deterministic(1) extended_val.inject extended_val.simps(3) r\<^sub>2 ref.sel val.inject(4))
next
  case (RedFieldNullFailure \<omega>_def e \<omega> f)
  then show ?case
    by force
next
  case (RedPermNull \<omega>_def e \<omega> f)
  then show ?case
    by auto
next
  case (RedPerm \<omega>_def e \<omega> a f v)
  then show ?case
    by auto
next
  case IH: (RedUnfolding es \<omega> vs ubody pred_id v)
  show ?case
  proof (cases \<omega>_def\<^sub>2)
    case None
    then obtain v\<^sub>2 where v\<^sub>2: "ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>ubody;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v\<^sub>2"
      using IH
      by (blast elim: RedUnfoldingBoth_case)
    with IH have "v\<^sub>2 = v\<^sub>1"
      by fastforce
    then show ?thesis
      by (metis IH.prems(1) IH.prems(3) None RedUnfolding_case eval_is_deterministic(1) extended_val.inject v\<^sub>2)
  next
    case (Some \<omega>\<^sub>0)
    then obtain v\<^sub>2 \<omega>_def\<^sub>2' where v\<^sub>2: "ctxt, \<omega>_def\<^sub>2' \<turnstile> \<langle>ubody;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v\<^sub>2"
      using IH
      by (blast elim: RedUnfoldingBoth_case)
    with IH have "v\<^sub>2 = v\<^sub>1"
      by fastforce
    then show ?thesis
      by (metis IH.prems(1) IH.prems(3) RedUnfolding_case eval_is_deterministic(1) eval_with_None extended_val.inject option.exhaust v\<^sub>2)
  qed
next
  case (RedUnfoldingDefNoPred \<omega>_def es \<omega> vs pred_id pred_decl p ubody)
  then show ?case
    by fastforce
next
  case IH: (RedUnfoldingDef \<omega>_def es \<omega> vs perm pred_id nm' \<omega>'_def ubody v)
  show ?case
  proof (cases \<omega>_def\<^sub>2)
    case None
    then obtain v\<^sub>2 where v\<^sub>2: "ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>ubody;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v\<^sub>2"
      using IH
      by (blast elim: RedUnfoldingBoth_case)
    with IH have "v\<^sub>2 = v\<^sub>1"
      by fastforce
    then show ?thesis
      using IH.prems(1) IH.prems(3) None eval_is_deterministic(1) v\<^sub>2
      by (metis RedUnfolding_case extended_val.inject)
  next
    case (Some \<omega>\<^sub>0)
    then obtain v\<^sub>2 \<omega>_def\<^sub>2' where v\<^sub>2: "ctxt, \<omega>_def\<^sub>2' \<turnstile> \<langle>ubody;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v\<^sub>2"
      using IH
      by (blast elim: RedUnfoldingBoth_case)
    with IH have "v\<^sub>2 = v\<^sub>1"
      by fastforce
    then show ?thesis
      by (metis IH.prems(1) IH.prems(3) RedUnfolding_case eval_is_deterministic(1) eval_with_None extended_val.inject option.exhaust_sel v\<^sub>2)
  qed
next
  case (RedSubFailure e' \<omega>_def \<omega>)
  then show ?case
    by fastforce
next
  case IH: (RedExpListCons \<omega>_def\<^sub>1 e \<omega>\<^sub>1 v\<^sub>1 es rs'\<^sub>1 rs\<^sub>1)
  then obtain v\<^sub>2 where v\<^sub>2: "ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t Val v\<^sub>2"
    by (blast elim: RedExpList_case)
  with IH have "v\<^sub>2 = v\<^sub>1"
    by fastforce
  from IH obtain vs'\<^sub>2 where vs'\<^sub>2: "red_pure_exps_total ctxt \<omega>_def\<^sub>2 es \<omega>\<^sub>2 (Some vs'\<^sub>2)"
    by (smt (verit, best) RedExpListCons_case map_option_eq_Some)
  moreover have "list_all supported_pred_expr es"
    using IH.prems(4)
    by fastforce
  moreover obtain vs'\<^sub>1 where "rs'\<^sub>1 = Some vs'\<^sub>1"
    using IH.hyps IH.prems(2)
    by blast
  ultimately have "vs'\<^sub>2 = vs'\<^sub>1"
    using IH.IH(4) IH.prems(5) IH.prems(6)
    by auto
  moreover have "\<And>v. ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t v \<Longrightarrow> v = Val v\<^sub>2"
    by (simp add: eval_is_deterministic v\<^sub>2)
  moreover have "\<And>v. red_pure_exps_total ctxt \<omega>_def\<^sub>2 es \<omega>\<^sub>2 v \<Longrightarrow> v = Some vs'\<^sub>2"
    using eval_is_deterministic(2) vs'\<^sub>2
    by blast
  moreover hence "rs\<^sub>2 = map_option ((#) v\<^sub>2) (Some vs'\<^sub>2)"
    by (metis IH.prems(1) IH.prems(3) RedExpListCons_case calculation(2) extended_val.sel)
  ultimately show ?case
    using IH.hyps IH.prems(2) IH.prems(3) \<open>rs'\<^sub>1 = Some vs'\<^sub>1\<close> \<open>v\<^sub>2 = v\<^sub>1\<close>
    by blast
next
  case (RedExpListFailure \<omega>_def e \<omega> es)
  then show ?case
    by fastforce
next
  case (RedExpListNil \<omega>_def \<omega>)
  then show ?case
    using red_exp_list_failure_Nil by auto
qed

lemma eval_ok_no_type_error:
  assumes "get_hh_total_full \<omega>\<^sub>1 = get_hh_total_full \<omega>\<^sub>2"
    and "get_store_total \<omega>\<^sub>1 = get_store_total \<omega>\<^sub>2"
  shows "ctxt, \<omega>_def\<^sub>1 \<turnstile> \<langle>e;\<omega>\<^sub>1\<rangle> [\<Down>]\<^sub>t r\<^sub>1 \<Longrightarrow>
           r\<^sub>1 = Val v\<^sub>1 \<Longrightarrow>
           supported_pred_expr e \<Longrightarrow>
           \<exists>r\<^sub>2. ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t r\<^sub>2" and
    "red_pure_exps_total ctxt \<omega>_def\<^sub>1 es \<omega>\<^sub>1 rs\<^sub>1 \<Longrightarrow>
           rs\<^sub>1 = Some vs\<^sub>1 \<Longrightarrow>
           list_all supported_pred_expr es \<Longrightarrow>
           \<exists>rs\<^sub>2. red_pure_exps_total ctxt \<omega>_def\<^sub>2 es \<omega>\<^sub>2 rs\<^sub>2"
  using assms
proof (induction arbitrary: v\<^sub>1 r\<^sub>2 v\<^sub>2 \<omega>_def\<^sub>2 and vs\<^sub>1 rs\<^sub>2 vs\<^sub>2 \<omega>_def\<^sub>2 rule: red_pure_exp_inducts)
  case (RedLit \<omega>_def l uu)
  then show ?case
    using red_pure_exp_total_red_pure_exps_total.RedLit by blast
next
  case (RedVar \<omega> n v \<omega>_def)
  then show ?case
    by (metis red_pure_exp_total_red_pure_exps_total.RedVar)
next
  case (RedResult \<omega> v \<omega>_def)
  then show ?case
    by (metis red_pure_exp_total_red_pure_exps_total.RedResult)
next
  case IH: (RedBinopLazy \<omega>_def e1 \<omega> v1 bop v e2)
  then obtain r1\<^sub>2 where r1\<^sub>2: "ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e1;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t r1\<^sub>2"
    by (metis pure_exp_pred.elims(2) pure_exp_pred_rec.simps(4))
  show ?case
  proof (cases r1\<^sub>2)
    case (Val v1\<^sub>2)
    with IH r1\<^sub>2 have "v1\<^sub>2 = v1"
      using eval_with_same_store_same_hh(1)[OF IH(1) r1\<^sub>2[simplified Val]]
      by (metis pure_exp_pred.elims(2) pure_exp_pred_rec.simps(4))
    then show ?thesis
      using IH.hyps RedBinopLazy Val r1\<^sub>2
      by blast
  next
    case VFailure
    then show ?thesis
      using red_exp_binop_sub_left_failure r1\<^sub>2
      by blast
  qed
next
  case IH: (RedBinop \<omega>_def e1 \<omega> v1 e2 v2 bop v)
  then obtain r1\<^sub>2 where r1\<^sub>2: "ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e1;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t r1\<^sub>2"
    by (metis pure_exp_pred.elims(2) pure_exp_pred_rec.simps(4))
  show ?case
  proof (cases r1\<^sub>2)
    case (Val v1\<^sub>2)
    hence "r1\<^sub>2 = Val v1"
      using eval_with_same_store_same_hh(1)[OF IH(1) r1\<^sub>2] IH.prems(1) IH.prems(2) IH.prems(3) IH(10)
      by fastforce
    from IH obtain r2\<^sub>2 where r2\<^sub>2: "ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e2;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t r2\<^sub>2"
      by fastforce
    show ?thesis
    proof (cases r2\<^sub>2)
      case (Val v2\<^sub>2)
      hence "r2\<^sub>2 = Val v2"
        using eval_with_same_store_same_hh(1)[OF IH(3) r2\<^sub>2] IH.prems(1) IH.prems(2) IH.prems(3) IH(10)
        by fastforce
      then show ?thesis
        by (metis (full_types) IH.hyps(1) IH.hyps(2) RedBinop RedBinopOpFailure \<open>r1\<^sub>2 = Val v1\<close> eval_total_non_total_same_or_fail r1\<^sub>2 r2\<^sub>2)
    next
      case VFailure
      then show ?thesis
        by (metis IH.hyps(1) IH.hyps(2) RedBinopRightFailure \<open>r1\<^sub>2 = Val v1\<close> binop_result.distinct(3) binop_result.simps(3) eval_total_non_total_same_or_fail r1\<^sub>2 r2\<^sub>2)
    qed
  next
    case VFailure
    then show ?thesis
      using r1\<^sub>2 red_exp_binop_sub_left_failure by blast
  qed
next
  case IH: (RedBinopRightFailure \<omega>_def e1 \<omega> v1 e2 bop)
  then show ?case
    by force
next
  case (RedBinopOpFailure \<omega>_def e1 \<omega> v1 e2 v2 bop)
  then show ?case
    by force
next
  case IH: (RedUnop \<omega>_def e \<omega> v unop v')
  then obtain r\<^sub>2 where r\<^sub>2: "ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t r\<^sub>2"
    by auto
  show ?case
  proof (cases r\<^sub>2)
    case (Val v\<^sub>2)
    with IH r\<^sub>2 have "v\<^sub>2 = v"
      using eval_with_same_store_same_hh(1)[OF IH(1) r\<^sub>2[simplified Val]]
      by (metis pure_exp_pred.elims(2) pure_exp_pred_rec.simps(3))
    then show ?thesis
      using IH.hyps RedBinopLazy Val r\<^sub>2 RedUnop
      by blast
  next
    case VFailure
    then show ?thesis
      using r\<^sub>2 red_exp_unop_sub_failure
      by blast
  qed
next
  case (RedCondExpTrue \<omega>_def e1 \<omega> e2 r e3)
  then show ?case
    by (metis eval_with_same_store_same_hh(1) extended_val.exhaust pure_exp_pred.elims(2) pure_exp_pred_rec.simps(5) red_exp_condexp_sub_failure red_pure_exp_total_red_pure_exps_total.RedCondExpTrue)
next
  case (RedCondExpFalse \<omega>_def e1 \<omega> e3 r e2)
  then show ?case
    by (metis eval_with_same_store_same_hh(1) extended_val.exhaust pure_exp_pred.elims(2) pure_exp_pred_rec.simps(5) red_exp_condexp_sub_failure red_pure_exp_total_red_pure_exps_total.RedCondExpFalse)
next
  case (RedOld \<omega> l \<phi> \<omega>_def' \<omega>_def e v)
  then show ?case
    by simp
next
  case (RedOldFailure \<omega> l \<omega>_def e)
  then show ?case
    by simp
next
  case IH: (RedField \<omega>_def e \<omega> a f v)
  hence e_sup: "supported_pred_expr e"
    by simp
  then obtain r\<^sub>2 where r\<^sub>2: "ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t r\<^sub>2"
    using IH.prems(3) IH(2) IH(7)
    by auto
  show ?case
  proof (cases r\<^sub>2)
    case (Val v\<^sub>2)
    hence "v\<^sub>2 = VRef (Address a)"
      by (metis IH(6) IH(7) IH.IH(1) e_sup eval_with_same_store_same_hh(1) r\<^sub>2)
    then show ?thesis
      using RedField Val r\<^sub>2 by blast
  next
    case VFailure
    then show ?thesis
      using r\<^sub>2 red_exp_field_sub_failure
      by blast
  qed
next
  case (RedFieldNullFailure \<omega>_def e \<omega> f)
  then show ?case
    by simp
next
  case (RedPermNull \<omega>_def e \<omega> f)
  then show ?case
    by simp
next
  case (RedPerm \<omega>_def e \<omega> a f v)
  then show ?case
    by auto
next
  case IH: (RedUnfolding es \<omega> vs ubody v pred_id)
  hence body_sup: "supported_pred_expr ubody"
    by simp
  from IH have "list_all supported_pred_expr es"
    by (metis sub_pure_exp_total.simps(9) supported_sub_expr_supported)
  with IH obtain rs\<^sub>2 where rs\<^sub>2: "red_pure_exps_total ctxt \<omega>_def\<^sub>2 es \<omega>\<^sub>2 rs\<^sub>2"
    by metis
  show ?case
  proof (cases rs\<^sub>2)
    case None
    then show ?thesis
      by (metis RedSubFailure list.discI red_exp_list_failure_elim rs\<^sub>2 sub_pure_exp_total.simps(9))
  next
    case vs\<^sub>2: (Some vs\<^sub>2)
    with IH have "vs\<^sub>2 = vs"
      using \<open>list_all supported_pred_expr es\<close> eval_with_same_store_same_hh(2) rs\<^sub>2
      by fastforce
    show ?thesis
    proof (cases \<omega>_def\<^sub>2)
      case None
      then show ?thesis
        by (metis IH(4) IH.prems(1) IH.prems(3) IH.prems(4) RedUnfolding body_sup rs\<^sub>2 vs\<^sub>2)
    next
      case \<omega>\<^sub>0\<^sub>2: (Some \<omega>\<^sub>0\<^sub>2)
      show ?thesis
      proof (cases "get_mp_total_full \<omega>\<^sub>0\<^sub>2 (pred_id,vs) = 0")
        case True
        show ?thesis
          apply (rule exI[of _ VFailure])
          apply (simp add: \<omega>\<^sub>0\<^sub>2)
          apply (rule RedUnfoldingDefNoPred)
          using rs\<^sub>2 vs\<^sub>2 \<omega>\<^sub>0\<^sub>2
           apply simp
          using IH(3)
          apply simp
          using True \<open>vs\<^sub>2 = vs\<close>
          by fastforce
      next
        case False
        have 1: "\<And>x. x \<ge> x / Abs_preal 2"
          by (simp add: preal_to_real prat_non_negative)
        have 2: "\<And>x. x \<noteq> 0 \<Longrightarrow> x / Abs_preal 2 \<noteq> 0"
          by (simp add: preal_to_real)
        obtain nm' where nm': "shift_up pred_id vs\<^sub>2 (get_mp_total_full \<omega>\<^sub>0\<^sub>2 (pred_id, vs) / Abs_preal 2) (get_nm_total_full \<omega>\<^sub>0\<^sub>2) nm'"
          apply simp
          using "1" \<open>vs\<^sub>2 = vs\<close> shift_up_exists
          by fastforce
        then obtain v\<^sub>2 where v\<^sub>2: "ctxt, Some (upd_nm_total_full \<omega>\<^sub>0\<^sub>2 nm') \<turnstile> \<langle>ubody;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t v\<^sub>2"
          using IH(4)[OF IH(5) body_sup IH(7) IH(8), of "Some (upd_nm_total_full \<omega>\<^sub>0\<^sub>2 nm')"]
          by blast
        show ?thesis
          apply (rule exI)
          apply (simp add: \<omega>\<^sub>0\<^sub>2)
          apply (rule RedUnfoldingDef[where ?perm="get_mp_total_full \<omega>\<^sub>0\<^sub>2 (pred_id,vs)"])
          using rs\<^sub>2 vs\<^sub>2 \<omega>\<^sub>0\<^sub>2
               apply simp
          using \<open>vs\<^sub>2 = vs\<close>
              apply fastforce
          using False preal_not_0_gt_0
             apply blast
          using nm'
            apply simp
           apply blast
          using v\<^sub>2
          by auto
      qed
    qed
  qed
next
  case (RedUnfoldingDefNoPred \<omega>_def es \<omega> vs pred_id ubody)
  then show ?case
    by blast
next
  case IH: (RedUnfoldingDef \<omega>_def es \<omega> vs perm pred_id nm' \<omega>'_def ubody v)
  hence body_sup: "supported_pred_expr ubody"
    by simp
  from IH have "list_all supported_pred_expr es"
    by (metis sub_pure_exp_total.simps(9) supported_sub_expr_supported)
  with IH obtain rs\<^sub>2 where rs\<^sub>2: "red_pure_exps_total ctxt \<omega>_def\<^sub>2 es \<omega>\<^sub>2 rs\<^sub>2"
    by metis
  show ?case
  proof (cases rs\<^sub>2)
    case None
    then show ?thesis
      by (metis RedSubFailure list.discI red_exp_list_failure_elim rs\<^sub>2 sub_pure_exp_total.simps(9))
  next
    case vs\<^sub>2: (Some vs\<^sub>2)
    with IH have "vs\<^sub>2 = vs"
      using \<open>list_all supported_pred_expr es\<close> eval_with_same_store_same_hh(2) rs\<^sub>2
      by fastforce
    show ?thesis
    proof (cases \<omega>_def\<^sub>2)
      case None
      show ?thesis
        by (metis IH.IH(4) IH.prems(1) IH.prems(3) IH.prems(4) None RedUnfolding body_sup rs\<^sub>2 vs\<^sub>2)
    next
      case \<omega>\<^sub>0\<^sub>2: (Some \<omega>\<^sub>0\<^sub>2)
      show ?thesis
      proof (cases "get_mp_total_full \<omega>\<^sub>0\<^sub>2 (pred_id,vs) = 0")
        case True
        show ?thesis
          apply (rule exI[of _ VFailure])
          apply (simp add: \<omega>\<^sub>0\<^sub>2)
          apply (rule RedUnfoldingDefNoPred)
          using rs\<^sub>2 vs\<^sub>2 \<omega>\<^sub>0\<^sub>2
           apply simp
          using IH(3)
          apply simp
          using True \<open>vs\<^sub>2 = vs\<close>
          by fastforce
      next
        case False
        have 1: "\<And>x. x \<ge> x / Abs_preal 2"
          by (simp add: preal_to_real prat_non_negative)
        have 2: "\<And>x. x \<noteq> 0 \<Longrightarrow> x / Abs_preal 2 \<noteq> 0"
          by (simp add: preal_to_real)
        obtain nm' where nm': "shift_up pred_id vs\<^sub>2 (get_mp_total_full \<omega>\<^sub>0\<^sub>2 (pred_id, vs) / Abs_preal 2) (get_nm_total_full \<omega>\<^sub>0\<^sub>2) nm'"
          apply simp
          using "1" \<open>vs\<^sub>2 = vs\<close> shift_up_exists
          by fastforce
        then obtain v\<^sub>2 where v\<^sub>2: "ctxt, Some (upd_nm_total_full \<omega>\<^sub>0\<^sub>2 nm') \<turnstile> \<langle>ubody;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t v\<^sub>2"
          by (metis IH(4) IH.prems(1) IH.prems(3) IH.prems(4) body_sup)
        show ?thesis
          apply (rule exI)
          apply (simp add: \<omega>\<^sub>0\<^sub>2)
          apply (rule RedUnfoldingDef[where ?perm="get_mp_total_full \<omega>\<^sub>0\<^sub>2 (pred_id,vs)"])
          using rs\<^sub>2 vs\<^sub>2 \<omega>\<^sub>0\<^sub>2
               apply simp
          using \<open>vs\<^sub>2 = vs\<close>
              apply fastforce
          using False preal_not_0_gt_0
             apply blast
          using nm'
            apply simp
           apply blast
          using v\<^sub>2
          by auto
      qed
    qed
  qed
next
  case (RedSubFailure e' \<omega>_def \<omega>)
  then show ?case
    by blast
next
  case IH: (RedExpListCons \<omega>_def e \<omega> v es rs rs')
  then obtain r\<^sub>2 where r\<^sub>2: "ctxt, \<omega>_def\<^sub>2 \<turnstile> \<langle>e;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t r\<^sub>2"
    by (metis list_all_simps(1))
  then show ?case
    apply (cases r\<^sub>2)
    using IH.IH(4) IH.hyps IH.prems(1) IH.prems(2) IH.prems(3) IH.prems(4) RedExpListCons list_all_simps(1)
     apply fastforce
    using RedExpListFailure
    by blast
next
  case (RedExpListFailure \<omega>_def e \<omega> es)
  then show ?case
    by blast
next
  case (RedExpListNil \<omega>_def \<omega>)
  then show ?case
    using red_pure_exp_total_red_pure_exps_total.RedExpListNil
    by auto
qed


\<comment> \<open>Helper lemmas\<close>

lemma eval_exhale_sat_helper_helper:
  shows "ctxt, \<omega>_def \<turnstile> \<langle>e;\<omega>\<^sub>1\<rangle> [\<Down>]\<^sub>t r \<Longrightarrow>
         no_perm_pure_exp e \<Longrightarrow>
         no_old_pure_exp e \<Longrightarrow>
         get_store_total \<omega>\<^sub>1 = get_store_total \<omega>\<^sub>2 \<Longrightarrow>
         get_hh_total_full \<omega>\<^sub>1 = get_hh_total_full \<omega>\<^sub>2 \<Longrightarrow>
         r = Val v \<Longrightarrow>
         ctxt, None \<turnstile> \<langle>e;\<omega>\<^sub>2\<rangle> [\<Down>]\<^sub>t r"
    and "red_pure_exps_total ctxt \<omega>_def es \<omega>\<^sub>1 rs \<Longrightarrow>
         list_all no_perm_pure_exp es \<Longrightarrow>
         list_all no_old_pure_exp es \<Longrightarrow>
         get_store_total \<omega>\<^sub>1 = get_store_total \<omega>\<^sub>2 \<Longrightarrow>
         get_hh_total_full \<omega>\<^sub>1 = get_hh_total_full \<omega>\<^sub>2 \<Longrightarrow>
         rs = Some vs \<Longrightarrow>
         red_pure_exps_total ctxt None es \<omega>\<^sub>2 rs"
proof (induction arbitrary: \<omega>_def \<omega>\<^sub>2 v and \<omega>_def \<omega>\<^sub>2 vs rule: red_pure_exp_inducts)
  case IH: (RedBinop \<omega>_def e1 \<omega> v1 e2 v2 bop v)
  show ?case
    apply (rule RedBinop)
       apply (rule IH(2))
    using IH.prems(1-4) apply force+
      apply (rule IH(4))
    using IH.prems(1-4) apply force+
     apply fact
    by (metis (full_types) IH.hyps(2) eval_binop_with_True is_none_code(1))
next
  case (RedField \<omega>_def e \<omega>\<^sub>1 a f v\<^sub>1)
  then show ?case
    by (metis (full_types) RedField_no_def_normalI extended_val.distinct(1) pure_exp_pred.simps pure_exp_pred_rec.simps(6))
next
  case (RedUnfolding es \<omega> vs ubody v pred_id)
  then show ?case
    by (fastforce intro: red_pure_exp_intros)
next
  case (RedUnfoldingDef \<omega>_def es \<omega> vs perm pred_id nm' \<omega>'_def ubody v)
  then show ?case
    by (fastforce intro: RedUnfolding)
next
  case (RedExpListCons \<omega>_def e \<omega> v es res res')
  then show ?case
    by (metis list.pred_inject(2) map_option_eq_Some red_pure_exps_total.simps)
qed (auto intro: red_pure_exp_intros)


lemma eval_exhale_sat_helper:
  shows "ctxt, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v \<Longrightarrow>
         no_perm_pure_exp e \<Longrightarrow>
         no_old_pure_exp e \<Longrightarrow>
         ctxt, None \<turnstile> \<langle>e; \<lparr> get_store_total = get_store_total \<omega>,
                            get_trace_total = \<lambda>x. None,
                            get_total_full = get_total_full \<omega>\<lparr> get_nm_total := 0 \<rparr> \<rparr>\<rangle> [\<Down>]\<^sub>t Val v"
    and "red_pure_exps_total ctxt \<omega>_def es \<omega> (Some vs) \<Longrightarrow>
         list_all no_perm_pure_exp es \<Longrightarrow>
         list_all no_old_pure_exp es \<Longrightarrow>
         red_pure_exps_total ctxt None es
           \<lparr> get_store_total = get_store_total \<omega>,
             get_trace_total = \<lambda>x. None,
             get_total_full = get_total_full \<omega>\<lparr> get_nm_total := 0 \<rparr> \<rparr> (Some vs)"
  using eval_exhale_sat_helper_helper
  by fastforce+


lemma red_pure_exps_append_success:
  assumes "red_pure_exps_total ctxt \<omega>_def es \<omega> (Some rs)"
      and "ctxt, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t (Val v)"
    shows "red_pure_exps_total ctxt \<omega>_def (es @ [e]) \<omega> (Some (rs @ [v]))"
  using assms(1)
proof (induction es)
  case Nil
  then show ?case
    using assms(2) red_exp_list_failure_Nil red_pure_exp_total_red_pure_exps_total.RedExpListCons
    by fastforce
next
  case (Cons a es)
  then show ?case
    by (metis assms(2) list.rel_intros(2) list_all2_Nil list_all2_appendI list_all2_red_pure_exps_total red_pure_exps_total_list_all2)
qed


subsection \<open>Relation between exhale and sat\<close>

lemma exhale_mh_diff:
  shows "get_mh_total_full \<omega> - get_mh_total_full (exhale_pred \<omega> ploc p) = zero_mask"
  apply (simp add: exhale_pred_def)
  apply standard
  unfolding zero_mask_def
  by (simp add: minus_preal.abs_eq zero_preal_def)

lemma exhale_mp_diff:
  assumes "p \<le> get_mp_total_full \<omega> ploc"
  shows "get_mp_total_full \<omega> - get_mp_total_full (exhale_pred \<omega> ploc p) = singleton_mp ploc p"
proof -
  have 1: "get_mp_total_full (exhale_pred \<omega> ploc p) = get_mp_total_full (rm_from_lpm_total_full \<omega> ploc p)"
    by (simp add: exhale_pred_def)
  have 2: "get_mp_total_full \<omega> ploc - (get_mp_total_full \<omega> ploc - p) = p"
    using assms minus_preal_gte
    by auto
  show ?thesis
    apply standard
    apply (simp add: exhale_pred_def)
    apply (cases "get_fnm_total_full \<omega> ploc")
    using all_pos antisym assms minus_preal.abs_eq zero_preal_def
     apply fastforce
    apply simp
    by (smt (verit, ccfv_SIG) "2" Abs_posreal_inverse comp_apply dual_order.eq_iff get_mp_nm.simps get_mp_total.simps get_mp_total_full.simps mem_Collect_eq minus_preal.abs_eq minus_preal_gte option_fold.simps(1) preal_not_0_gt_0 zero_preal_def)
qed

lemma mh_sub_twice:
  assumes "\<And>x. mh0 x \<ge> mh1 x"
      and "\<And>x. mh1 x \<ge> mh2 x"
    shows "mh_split (mh0 - mh2) (mh0 - mh1) (mh1 - mh2)"
  apply simp
  apply standard
  apply (simp add: add_masks_def preal_to_real)
  using assms less_eq_preal.rep_eq
  by auto

lemma mp_sub_twice:
  assumes "\<And>x. mp0 x \<ge> mp1 x"
      and "\<And>x. mp1 x \<ge> mp2 x"
    shows "mp_split (mp0 - mp2) (mp0 - mp1) (mp1 - mp2)"
  apply simp
  apply standard
  apply (simp add: add_masks_def preal_to_real)
  using assms less_eq_preal.rep_eq
  by auto

lemma exhale_diff_sat:
  assumes "red_exhale ctxt R \<omega>\<^sub>0 A \<omega> res" and "res = RNormal \<omega>'"
      and "supported_pred_body A"
      and "consistent_external ctxt (get_total_full \<omega>)"
    shows "sat ctxt (\<lparr> get_store_total = get_store_total \<omega>,
                       get_trace_total = Map.empty,
                       get_total_full = get_total_full \<omega>\<lparr> get_nm_total := 0 \<rparr> \<rparr>)
               (get_mh_total_full \<omega> - get_mh_total_full \<omega>')
               (get_mp_total_full \<omega> - get_mp_total_full \<omega>')
               A"
  using assms(1-3)
proof (induction arbitrary: \<omega>')
  case IH: (ExhAcc mh \<omega> e_r r e_p p a f)
  have 1: "0 \<le> p \<and> (if r = Null then p = 0 else Abs_preal p \<le> mh (a, f))"
   and \<omega>': "\<omega>' = (if r = Null then \<omega> else dec_mh_loc_total_full \<omega> (a, f) (Abs_preal p))"
    using exh_if_total_normal[OF IH(5)] exh_if_total_normal_2[OF IH(5)]
    by blast+
  show ?case
    apply standard
    using IH eval_exhale_sat_helper(1)
         apply fastforce+
    using 1
      apply blast
     apply (cases r)
      apply (simp add: If_def \<omega>')
    using 1 IH.hyps(1) IH.hyps(4) mh_upd_loc_diff minus_preal_gte psub_smaller
      apply auto[1]
    using 1 \<omega>' same_mh_diff
     apply force
    apply standard
    by (simp add: zero_mask_def \<omega>' minus_preal.abs_eq zero_preal.abs_eq)
next
  case IH: (ExhAccWildcard mh \<omega> e_r r a f q)
  have 1: "mh (a,f) \<noteq> 0 \<and> r \<noteq> Null"
   and \<omega>': "\<omega>' = dec_mh_loc_total_full \<omega> (a,f) q"
    using IH.prems(1) exh_if_total_normal exh_if_total_normal_2
    by blast+
  show ?case
    apply standard
    using IH(2,5,6) eval_exhale_sat_helper(1)
        apply fastforce+
    using IH(1,4) dec_mh_mh_diff 1 IH.hyps(3) \<omega>' is_singleton_mh.simps
     apply blast
    using \<omega>' IH.hyps(1) dec_mh_mp_diff
    by blast
next
  case IH: (ExhAccPred mp \<omega> e_args v_args e_p p pred_id pred_decl)
  have 1: "0 \<le> p \<and> Abs_preal p \<le> mp (pred_id, v_args)"
   and \<omega>': "\<omega>' = exhale_pred \<omega> (pred_id, v_args) (Abs_preal p)"
    using IH.prems(1) exh_if_total_normal exh_if_total_normal_2
    by blast+
  from IH(7) have es_sup: "list_all no_perm_pure_exp e_args \<and> list_all no_old_pure_exp e_args"
    by simp
  show ?case
    apply standard
    using eval_exhale_sat_helper(2)[OF IH(2)] es_sup
          apply blast
    using IH(7) eval_exhale_sat_helper(1)[OF IH(3)]
         apply simp
        apply (simp add: 1)
    using IH.hyps(1) \<omega>' exhale_mh_diff
       apply blast
    using IH.hyps(1) \<omega>' exhale_mp_diff 1
      apply blast
    by fact+
next
  case IH: (ExhAccPredWildcard mp \<omega> e_args v_args pred_id q)
  have 1: "mp (pred_id, v_args) \<noteq> 0"
   and 2: "q > 0 \<and> mp (pred_id, v_args) > q"
   and \<omega>': "\<omega>' = exhale_pred \<omega> (pred_id, v_args) q"
    using IH.prems(1) IH.hyps(3) exh_if_total_normal exh_if_total_normal_2
    by blast+
  from IH(7) have es_sup: "list_all no_perm_pure_exp e_args \<and> list_all no_old_pure_exp e_args"
    by simp
  show ?case
    apply standard
    using eval_exhale_sat_helper(2)[OF IH(2)] es_sup
        apply blast
    using IH.hyps(1) \<omega>' exhale_mh_diff
       apply blast
    using 1 2 IH.hyps(1) IH.hyps(3) \<omega>' exhale_mp_diff is_singleton_mp.simps order_less_imp_le
      apply blast
    by fact+
next
  case IH: (ExhPure e \<omega> b)
  show ?case
    apply standard
    using eval_exhale_sat_helper(1)[OF IH(1)] IH.prems(1) IH.prems(2) exh_if_total_normal
      apply fastforce
    using IH.prems(1) exh_if_total_normal_2 same_mh_diff
     apply blast
    using IH.prems(1) exh_if_total_normal_2 same_mp_diff
    by blast
next
  case IH: (ExhStarNormal A \<omega> \<omega>_int B res)
  show ?case
  proof
    define mh\<^sub>A where "mh\<^sub>A = get_mh_total_full \<omega> - get_mh_total_full \<omega>_int"
    define mp\<^sub>A where "mp\<^sub>A = get_mp_total_full \<omega> - get_mp_total_full \<omega>_int"
    define mh\<^sub>B where "mh\<^sub>B = get_mh_total_full \<omega>_int - get_mh_total_full \<omega>'"
    define mp\<^sub>B where "mp\<^sub>B = get_mp_total_full \<omega>_int - get_mp_total_full \<omega>'"
    show "mh_split (get_mh_total_full \<omega> - get_mh_total_full \<omega>') mh\<^sub>A mh\<^sub>B"
      by (metis IH.hyps(1) IH.hyps(2) IH.prems(1) exhale_smaller(1) mh\<^sub>A_def mh\<^sub>B_def mh_sub_twice)
    show "mp_split (get_mp_total_full \<omega> - get_mp_total_full \<omega>') mp\<^sub>A mp\<^sub>B"
      by (metis IH.hyps(1) IH.hyps(2) IH.prems(1) exhale_smaller(2) mp\<^sub>A_def mp\<^sub>B_def mp_sub_twice)
    show "sat ctxt \<lparr> get_store_total = get_store_total \<omega>,
                     get_trace_total = \<lambda>x. None,
                     get_total_full = get_total_full \<omega>\<lparr> get_nm_total := 0 \<rparr> \<rparr>
              (get_mh_total_full \<omega> - get_mh_total_full \<omega>_int)
              (get_mp_total_full \<omega> - get_mp_total_full \<omega>_int)
              A"
      using IH.IH(1) IH.prems(2) by fastforce
    show "sat ctxt \<lparr> get_store_total = get_store_total \<omega>,
                     get_trace_total = \<lambda>x. None,
                     get_total_full = get_total_full \<omega>\<lparr> get_nm_total := 0 \<rparr> \<rparr>
              (get_mh_total_full \<omega>_int - get_mh_total_full \<omega>')
              (get_mp_total_full \<omega>_int - get_mp_total_full \<omega>')
              B"
      by (smt (verit) IH.IH(2) IH.hyps(1) IH.prems(1) IH.prems(2) assert_pred.elims(2) assert_pred_rec.simps(4) exhale_only_changes_total_state_aux get_hh_total_full.elims old.unit.exhaust total_state.surjective total_state.update_convs(2))
  qed
next
  case (ExhStarFailure A \<omega> B)
  then show ?case
    by blast
next
  case (ExhImpTrue e \<omega> A res)
  then show ?case
    by (simp add: SatImpTrue eval_exhale_sat_helper)
next
  case IH: (ExhImpFalse e \<omega> A)
  show ?case
    apply standard
    using IH.hyps IH.prems(2) eval_exhale_sat_helper
      apply force
     apply (metis IH.prems(1) result_total.inject same_mh_diff)
    by (metis IH.prems(1) result_total.inject same_mp_diff)
next
  case (ExhCondTrue e \<omega> A res B)
  then show ?case
    by (simp add: SatCondTrue eval_exhale_sat_helper)
next
  case (ExhCondFalse e \<omega> B res A)
  then show ?case
    by (simp add: SatCondFalse eval_exhale_sat_helper)
next
  case (ExhSubExpFailure A \<omega>)
  then show ?case
    by blast
qed


subsection \<open>Inhale Properties\<close>

lemma inhale_with_more_variables:
  assumes "red_inhale ctxt StateCons A \<omega>\<^sub>1 (RNormal \<omega>\<^sub>1')"
      and "\<And>x v. get_store_total \<omega>\<^sub>1 x = Some v \<Longrightarrow> get_store_total \<omega>\<^sub>2 x = Some v"
      and "get_trace_total \<omega>\<^sub>1 = get_trace_total \<omega>\<^sub>2"
      and "get_total_full \<omega>\<^sub>1 = get_total_full \<omega>\<^sub>2"
      and "\<omega>\<^sub>2' = \<omega>\<^sub>1'\<lparr> get_store_total := get_store_total \<omega>\<^sub>2 \<rparr>"
    shows "red_inhale ctxt StateCons A \<omega>\<^sub>2 (RNormal \<omega>\<^sub>2')"
  sorry


end
