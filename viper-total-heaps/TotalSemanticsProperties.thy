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
  from IH(8) have es_sup: "list_all no_perm_pure_exp e_args \<and> list_all no_old_pure_exp e_args"
    by simp
  show ?case
    apply standard
    using eval_exhale_sat_helper(2)[OF IH(2)] es_sup
           apply blast
    using IH(8) eval_exhale_sat_helper(1)[OF IH(3)]
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
  from IH(8) have es_sup: "list_all no_perm_pure_exp e_args \<and> list_all no_old_pure_exp e_args"
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



subsection \<open>External Consistent State \<Longrightarrow> Inhaled State\<close>


lemma extcons_state_can_be_inhaled_assertion:
  assumes Sat: "sat ctxt \<omega>\<^sub>0 mh mp A"
      and mh_nm: "mh = get_mh_nm nm"
      and mp_nm: "mp = get_mp_nm nm"
      and ExtCons: "consistent_external ctxt \<lparr> get_hh_total = hh, get_nm_total = nm \<rparr>"
      and \<omega>hh: "get_hh_total_full \<omega> = hh"
      and \<omega>\<^sub>0hh: "get_hh_total_full \<omega>\<^sub>0 = hh"
      and SameStore: "get_store_total \<omega> = get_store_total \<omega>\<^sub>0"
      and Framed: "assertion_framing_state ctxt StateCons A \<omega>"
      and SupPred: "supported_pred_body A"
      and FinalIntCons: "StateCons (add_to_nm_total_full \<omega> nm)"
      and MonoCons: "mono_prop_downward StateCons"
      and WfCtxt: "ctxt_pred_syn_wf ctxt"
    shows "red_inhale ctxt StateCons A \<omega> (RNormal (add_to_nm_total_full \<omega> nm))"

  using Sat mh_nm mp_nm ExtCons \<omega>hh SameStore Framed SupPred FinalIntCons
proof (induction A arbitrary: \<omega> nm)

  case IH: (SatAcc e_r r e_p p a mh f mp)
  hence "supported_pred_expr e_r" and "supported_pred_expr e_p"
    by simp+

  obtain r_r where "ctxt, Some \<omega> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t r_r"
    by (metis IH.hyps(1) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh \<open>supported_pred_expr e_r\<close> eval_ok_no_type_error(1))
  obtain r_p where "ctxt, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t r_p"
    by (metis IH.hyps(2) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh \<open>supported_pred_expr e_p\<close> eval_ok_no_type_error(1))

  have "\<And>res. ctxt, Some \<omega> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t res \<Longrightarrow> res \<noteq> VFailure"
    using IH.prems(6) RedExpListFailure assertion_framing_state_sub_exps_not_failure
    by fastforce
  hence eval_e_r: "ctxt, Some \<omega> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
    by (metis IH.hyps(1) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh \<open>ctxt, Some \<omega> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t r_r\<close> \<open>supported_pred_expr e_r\<close> eval_with_same_store_same_hh(1) extended_val.exhaust_sel)

  have "\<And>res. ctxt, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t res \<Longrightarrow> res \<noteq> VFailure"
    using IH.prems(6) RedExpListCons RedExpListFailure assertion_framing_state_sub_exps_not_failure eval_e_r red_pure_exps_total.simps
    by fastforce

  hence eval_e_p: "ctxt, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
    by (metis IH(2) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh \<open>\<And>thesis. (\<And>r_p. ctxt, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t r_p \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>supported_pred_expr e_p\<close> eval_with_same_store_same_hh(1) extended_val.exhaust)

  define W where "W = (if r = Null
                       then {\<omega>}
                       else inhale_perm_single StateCons \<omega> (the_address r, f) (Some (Abs_preal p)))"

  show ?case
    apply standard
    using eval_e_r eval_e_p W_def
       apply blast+
  proof (cases "r = Null")
    case True
    with IH have "p = 0"
      by presburger
    from True W_def have "W = {\<omega>}"
      by auto
    have "nm = 0"
      apply (rule nested_mask_equality)
        apply (simp_all add: zero_nested_mask_def)
      using IH.hyps(5) IH.prems(1) True
        apply auto[1]
      using IH.hyps(6) IH.prems(2)
        apply auto[1]
      using zero_mask_def
      by (metis (no_types, lifting) Rep_posreal comp_apply mem_Collect_eq option.exhaust_sel option_fold.simps(1) pperm_pgt_pnone)
    show "th_result_rel (0 \<le> p) (W \<noteq> {} \<and> (0 < p \<longrightarrow> r \<noteq> Null)) W (RNormal (add_to_nm_total_full \<omega> nm))"
      apply (simp add: \<open>p = 0\<close> \<open>W = {\<omega>}\<close> True th_result_rel.simps)
      by (simp add: zero_nested_mask_def[symmetric] \<open>nm = 0\<close>)
  next
    case False
    have mh: "get_mh_nm nm = singleton_mh (a, f) (Abs_preal p)"
      using False IH.hyps(5) IH.prems(1) by presburger
    have fnm: "get_fnm_nm nm = (\<lambda>_. None)"
      by (metis (mono_tags, lifting) IH.hyps(6) IH.prems(2) Rep_posreal comp_eq_dest_lhs get_mp_nm.simps mem_Collect_eq option.exhaust_sel option_fold.simps(1) preal_not_0_gt_0 zero_mask_def)
    have intcons: "StateCons (upd_mh_loc_total_full \<omega> (the_address r, f) (get_mh_total_full \<omega> (the_address r, f) + Abs_preal p))"
    proof -
      have "upd_mh_loc_total_full \<omega> (the_address r, f) (get_mh_total_full \<omega> (the_address r, f) + Abs_preal p) =
            add_to_nm_total_full \<omega> nm"
        apply (rule full_total_state.equality; simp_all)
        apply (rule total_state.equality; simp_all)
        apply (rule nested_mask_equality; standard; simp add: add_masks_def)
         apply (simp add: mh IH(3))
        unfolding plus_nested_mask_def
        apply (cases "get_nm_total_full \<omega>", cases nm)
        apply simp
        by (metis (no_types, lifting) combine_options_simps(2) fnm get_fnm_nm.simps pfun_comb_def)
      thus ?thesis
        using IH.prems(8) by presburger
    qed
    show "th_result_rel (0 \<le> p) (W \<noteq> {} \<and> (0 < p \<longrightarrow> r \<noteq> Null)) W (RNormal (add_to_nm_total_full \<omega> nm))"
      apply (simp add: IH(4) W_def inhale_perm_single_def False intcons[simplified])
      apply (rule THResultNormal)
      apply (rule Set.CollectI)
      apply (intro conjI)
       apply (rule full_total_state.equality)
          apply simp_all
       apply (rule total_state.equality)
         apply simp_all
       apply (rule nested_mask_equality)
        apply simp_all
        apply (simp add: mh)
        apply standard
        apply simp
        apply (simp add: IH.hyps(3) add_masks_def)
      unfolding plus_nested_mask_def
       apply (cases "get_nm_total_full \<omega>", cases nm)
       apply standard
       apply (simp add: pfun_comb_def)
      using fnm
       apply fastforce
      by (metis IH.prems(8) add_to_nm_total.elims add_to_nm_total_full.simps plus_nested_mask_def)
  qed

next
  case IH: (SatAccWildcard e_r r a f mh mp)

  hence e_r_sup: "supported_pred_expr e_r"
    by auto
  obtain r_r where "ctxt, Some \<omega> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t r_r"
    using eval_ok_no_type_error(1) IH(1,9,10) \<omega>\<^sub>0hh e_r_sup
    by metis
  moreover have "\<And>res. ctxt, Some \<omega> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t res \<Longrightarrow> res \<noteq> VFailure"
    using IH.prems(6) RedExpListFailure assertion_framing_state_sub_exps_not_failure
    by fastforce
  ultimately have e_r_eval: "ctxt, Some \<omega> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
    by (metis IH.hyps(1) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh e_r_sup eval_with_same_store_same_hh(1) extended_val.exhaust)

  define W where "W = inhale_perm_single StateCons \<omega> (the_address r, f) None"

  have "is_singleton_mh (a,f) (get_mh_nm nm)"
    using IH.hyps(4) IH.prems(1)
    by auto
  have "get_mp_nm nm = zero_mask"
    using IH.hyps(5) IH.prems(2)
    by presburger
  hence "get_fnm_nm nm = (\<lambda>_. None)"
    using SatAll_case[OF IH(8)]
    by (metis (mono_tags, lifting) Rep_posreal comp_eq_dest_lhs get_mp_nm.simps mem_Collect_eq option.exhaust option_fold.simps(1) preal_not_0_gt_0 zero_mask_def)

  have "add_to_nm_total_full \<omega> nm \<in> W"
    apply (simp add: W_def inhale_perm_single_def)
    apply (rule exI[of _ "get_mh_nm nm (a,f)"])
    apply (intro conjI)
    using \<open>is_singleton_mh (a, f) (get_mh_nm nm)\<close>
       apply fastforce
     apply (rule full_total_state.equality, simp_all)
     apply (rule total_state.equality, simp_all)
     apply (rule nested_mask_equality, simp_all; standard)
      apply (simp_all add: add_masks_def)
    using IH.hyps(2) \<open>is_singleton_mh (a, f) (get_mh_nm nm)\<close>
      apply force
    unfolding plus_nested_mask_def
     apply (cases "get_nm_total_full \<omega>", cases nm)
     apply (simp add: pfun_comb_def)
    using \<open>get_fnm_nm nm = (\<lambda>_. None)\<close>
     apply auto[1]
    by (metis IH.prems(8) add_to_nm_total.elims add_to_nm_total_full.simps plus_nested_mask_def)
  hence "W \<noteq> {}"
    by fast

  show ?case
    apply (rule InhAccWildcard[where ?W'=W])
    using e_r_eval
      apply simp
    using W_def
     apply force
    using IH.hyps(3) THResultNormal \<open>W \<noteq> {}\<close> \<open>add_to_nm_total_full \<omega> nm \<in> W\<close>
    by auto

next
  case IH: (SatAccPred e_args v_args e_p p mh mp pred_id pred_decl)

  hence e_args_sup: "list_all supported_pred_expr e_args" and
        e_p_sup: "supported_pred_expr e_p"
    by (simp add: list_all_length)+
  then obtain r_vs r_p where
    e_args_res: "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> r_vs" and
    e_p_res: "ctxt, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t r_p"
    using eval_ok_no_type_error IH(1,2,9,10) \<omega>\<^sub>0hh
    by (metis (full_types) IH.prems(4) IH.prems(5))
  have e_args_ok: "\<And>res. red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> res \<Longrightarrow> res \<noteq> None" and
          e_p_ok: "\<And>res. ctxt, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t res \<Longrightarrow> res \<noteq> VFailure"
     apply (metis IH.prems(6) assertion_framing_state_sub_exps_not_failure red_pure_exps_total_append_failure sub_expressions_atomic.simps(3))
    by (metis IH.prems(6) RedExpListFailure e_args_res assertion_framing_state_sub_exps_not_failure red_pure_exps_total_append_failure red_pure_exps_total_append_failure_2 split_option_ex sub_expressions_atomic.simps(3) sub_expressions_exp_or_wildcard.simps(1))
  have e_args_eval: "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some v_args)" and
          e_p_eval: "ctxt, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
    using IH(1) eval_with_same_store_same_hh(2)[OF IH(1)]
    apply (metis IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh e_args_sup not_Some_eq e_args_ok e_args_res)
    by (metis IH(2) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh e_p_res e_p_ok e_p_sup eval_with_same_store_same_hh(1) extended_val.exhaust)

  define W where "W = inhale_perm_single_pred ctxt StateCons \<omega> (pred_id,v_args) (Some (Abs_preal p))"

  have "get_mh_nm nm = zero_mask"
    using IH.hyps(4) IH.prems(1)
    by auto
  have "get_mp_nm nm = singleton_mp (pred_id,v_args) (Abs_preal p)"
    using IH.hyps(5) IH.prems(2)
    by order
  hence "get_mp_nm nm (pred_id,v_args) = Abs_preal p"
    by simp

  have sat: "sat ctxt \<omega>\<^sub>0 mh mp (Atomic (AccPredicate pred_id e_args (PureExp e_p)))"
    using IH
    by (meson SatAccPred)

  obtain nm_pred where
    p_nonzero: "p > 0 \<longrightarrow> get_fnm_nm nm (pred_id,v_args) = Some (Abs_posreal (Abs_preal p), nm_pred)" and
    p_zero: "p = 0 \<longrightarrow> nm_pred = 0"
    using \<open>get_mp_nm nm = _\<close>[THEN fun_cong, of "(pred_id,v_args)", simplified]
    apply (cases "get_fnm_nm nm (pred_id,v_args)"; simp)
    using positive_real_preal
     apply blast
    by (metis Rep_posreal_inverse fstI order_less_irrefl surj_pair)

  have nm_pred_extcons: "consistent_external_wrt_ploc ctxt \<lparr> get_hh_total = hh, get_nm_total = nm_pred \<rparr> (pred_id,v_args) (Abs_preal p)"
    apply (cases "p > 0")
     apply (metis IH.prems(3) SatAll_case \<open>get_mp_nm nm (pred_id, v_args) = Abs_preal p\<close> comp_apply get_mp_nm.simps old.prod.inject option_fold.simps(1) p_nonzero prod.collapse total_state.select_convs(2) total_state.update_convs(2))
    apply (subgoal_tac "p = 0")
     prefer 2
    using IH.hyps(3)
     apply fastforce
    apply (thin_tac _)
    apply (rule SatStep)
         apply (rule IH(6))
        apply (rule IH(7))
       apply (rule IH(8))
      apply (simp add: p_zero)
     apply (simp add: zero_preal_def)
    by (simp add: empty_consistent_external p_zero)

  have "p = 0 \<Longrightarrow> nm = 0"
    apply (rule nested_mask_equality)
     apply (simp add: \<open>get_mh_nm nm = zero_mask\<close> zero_nested_mask_def)
    apply standard
    apply (rename_tac lp)
    apply (cut_tac ?x=lp in \<open>get_mp_nm nm = _\<close>[THEN fun_cong])
    apply (case_tac "get_fnm_nm nm lp"; simp add: zero_nested_mask_def)
    by (metis Rep_posreal mem_Collect_eq pperm_pgt_pnone zero_preal.abs_eq)

  have "Abs_preal p \<noteq> 0 \<Longrightarrow> nm = NM zero_mask [(pred_id,v_args) \<mapsto> (Abs_posreal (Abs_preal p), nm_pred)]"
    apply (rule nested_mask_equality)
     apply (simp add: \<open>get_mh_nm nm = zero_mask\<close> zero_nested_mask_def)
    apply standard
    apply (rename_tac lp)
    apply (cut_tac ?x=lp in \<open>get_mp_nm nm = _\<close>[THEN fun_cong])
    apply (case_tac "get_fnm_nm nm lp")
     apply fastforce
    using IH.hyps(3) Rep_posreal map_upd_Some_unfold mem_Collect_eq option_fold.simps(1) p_nonzero pperm_pgt_pnone zero_preal.abs_eq
    by fastforce

  have "add_to_nm_total_full \<omega> nm \<in> W"
    unfolding W_def inhale_perm_single_pred_def option_fold.simps
    apply (rule CollectI)
    apply simp
    apply (rule exI[of _ "\<lparr> get_hh_total = hh, get_nm_total = nm_pred \<rparr>"])
    apply (intro conjI)
     apply (intro impI)
     apply (intro conjI)
    using nm_pred_extcons
        apply auto[1]
    using IH.prems(4)
       apply auto[1]
      apply (rule full_total_state.equality; simp)
      apply (rule total_state.equality; simp)
    using IH.hyps(3) \<open>p = 0 \<Longrightarrow> nm = 0\<close> positive_real_preal
      apply fastforce
    using IH.prems(8)
     apply auto[1]
    apply (intro impI)
    apply (intro conjI)
    using nm_pred_extcons IH.hyps(3) zero_preal.abs_eq
       apply fastforce
    using IH.prems(4)
      apply auto[1]
     apply (rule full_total_state.equality; simp)
     apply (rule total_state.equality; simp)
     apply (rule nested_mask_equality; simp)
      apply (simp add: \<open>get_mh_nm nm = zero_mask\<close> add_masks_zero_mask)
    using \<open>Abs_preal p \<noteq> 0 \<Longrightarrow> _\<close>
     apply simp
     apply standard
     apply (rename_tac lp)
     apply (cases "get_nm_total_full \<omega>", simp)
     apply (rename_tac mh fnm)
    unfolding plus_nested_mask_def
     apply simp
     apply (case_tac "lp = (pred_id,v_args)"; case_tac "fnm lp"; simp add: pfun_comb_def)
    by (metis IH.prems(8) add_to_nm_total.elims add_to_nm_total_full.simps plus_nested_mask_def)

  show ?case
    apply (rule InhAccPred[where ?W'=W])
    using e_args_eval e_p_eval
       apply simp+
    using W_def
     apply force
    using IH.hyps(3) THResultNormal \<open>add_to_nm_total_full \<omega> nm \<in> W\<close>
    by (metis (full_types) empty_iff)

next
  case IH: (SatAccPredWildcard e_args v_args mh pred_id mp)

  hence e_args_sup: "list_all supported_pred_expr e_args"
    by (simp add: list_all_length)
  then obtain r_vs where
    e_args_res: "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> r_vs"
    using eval_ok_no_type_error(2) IH(1,7,8,10) \<omega>\<^sub>0hh
    by (metis (full_types) IH.prems(5))
  have e_args_ok: "\<And>res. red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> res \<Longrightarrow> res \<noteq> None"
    by (metis IH.prems(6) assertion_framing_state_sub_exps_not_failure red_pure_exps_total_append_failure sub_expressions_atomic.simps(3))
  have e_args_eval: "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some v_args)"
    using IH(1) eval_with_same_store_same_hh(2)[OF IH(1)]
    by (metis IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh e_args_sup not_Some_eq e_args_ok e_args_res)

  define W where "W = inhale_perm_single_pred ctxt StateCons \<omega> (pred_id,v_args) None"

  have "get_mh_nm nm = zero_mask"
    using IH.hyps(2) IH.prems(1)
    by auto
  have "is_singleton_mp (pred_id,v_args) (get_mp_nm nm)"
    using IH.hyps(3) IH.prems(2)
    by meson
  then obtain p where p: "get_mp_nm nm = singleton_mp (pred_id,v_args) p" and "p > 0"
    by auto

  have sat: "sat ctxt \<omega>\<^sub>0 mh mp (Atomic (AccPredicate pred_id e_args Wildcard))"
    using IH
    by (meson SatAccPredWildcard)

  obtain nm_pred where
    p_nonzero: "p > 0 \<longrightarrow> get_fnm_nm nm (pred_id,v_args) = Some (Abs_posreal p, nm_pred)" and
    p_zero: "p = 0 \<longrightarrow> nm_pred = 0"
    using \<open>get_mp_nm nm = _\<close>[THEN fun_cong, of "(pred_id,v_args)", simplified]
    apply (cases "get_fnm_nm nm (pred_id,v_args)"; simp)
    by (metis Rep_posreal_inverse fstI order_less_irrefl surj_pair)

  have nm_pred_extcons: "consistent_external_wrt_ploc ctxt \<lparr> get_hh_total = hh, get_nm_total = nm_pred \<rparr> (pred_id,v_args) p"
    apply (cases "p > 0")
     apply (metis IH.prems(3) SatAll_case mem_Collect_eq p_nonzero posreal_to_preal(8) total_state.select_convs(2) total_state.update_convs(2))
    apply (subgoal_tac "p = 0")
     prefer 2
     apply (simp add: \<open>0 < p\<close>)
    apply (thin_tac _)
    apply (rule SatStep)
         apply (rule IH(4))
        apply (rule IH(5))
       apply (rule IH(6))
      apply (simp add: p_zero)
     apply (simp add: zero_preal_def)
    by (simp add: empty_consistent_external p_zero)

  have "p \<noteq> 0 \<Longrightarrow> nm = NM zero_mask [(pred_id,v_args) \<mapsto> (Abs_posreal p, nm_pred)]"
    apply (rule nested_mask_equality)
     apply (simp add: \<open>get_mh_nm nm = zero_mask\<close> zero_nested_mask_def)
    apply standard
    apply (rename_tac lp)
    apply (cut_tac ?x=lp in \<open>get_mp_nm nm = _\<close>[THEN fun_cong])
    apply (case_tac "get_fnm_nm nm lp")
     apply fastforce
    using IH.hyps(3) Rep_posreal map_upd_Some_unfold mem_Collect_eq option_fold.simps(1) p_nonzero pperm_pgt_pnone zero_preal.abs_eq
    by (metis (mono_tags, lifting) comp_apply get_fnm_nm.simps get_mp_nm.simps singleton_mp.elims)

  have "add_to_nm_total_full \<omega> nm \<in> W"
    unfolding W_def inhale_perm_single_pred_def option_fold.simps
    apply (rule CollectI)
    apply simp
    apply (rule exI[of _ "\<lparr> get_hh_total = hh, get_nm_total = nm_pred \<rparr>"])
    apply (rule exI[of _ p])
    apply (intro conjI)
    using \<open>pos_perm_class.pnone < p\<close>
     apply force
    apply (intro impI)
    apply (intro conjI)
    using nm_pred_extcons
       apply presburger
    using IH.prems(4)
      apply auto[1]
     apply (rule full_total_state.equality; simp)
     apply (rule total_state.equality; simp)
     apply (rule nested_mask_equality; simp)
      apply (simp add: \<open>get_mh_nm nm = zero_mask\<close> add_masks_zero_mask)
    using \<open>p \<noteq> 0 \<Longrightarrow> _\<close>
     apply simp
     apply standard
     apply (rename_tac lp)
     apply (cases "get_nm_total_full \<omega>", simp)
     apply (rename_tac mh fnm)
    unfolding plus_nested_mask_def
     apply simp
     apply (case_tac "lp = (pred_id,v_args)"; case_tac "fnm lp"; simp add: pfun_comb_def)
    by (metis IH.prems(8) add_to_nm_total.elims add_to_nm_total_full.simps plus_nested_mask_def)

  show ?case
    apply (rule InhAccPredWildcard[where ?W'=W])
    using e_args_eval
      apply simp
    using W_def
     apply force
    using IH.hyps(3) THResultNormal \<open>add_to_nm_total_full \<omega> nm \<in> W\<close>
    by (metis (full_types) ex_in_conv)

next
  case IH: (SatPure e mh mp)
  hence "supported_pred_expr e"
    by simp
  then obtain res where \<omega>_eval: "ctxt, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t res"
    by (metis IH.hyps(1) IH.prems(4) IH.prems(5) eval_ok_no_type_error(1) \<omega>\<^sub>0hh)
  show ?case
  proof (cases res)
    case (Val v)
    then have "v = VBool True"
      using eval_with_same_store_same_hh(1)[OF IH(1)] IH(10) IH(7) IH(8) \<omega>\<^sub>0hh \<omega>_eval \<open>supported_pred_expr e\<close>
      apply simp
      by presburger
    have "nm = 0"
      apply (rule nested_mask_equality)
       apply (metis IH.hyps(2) IH.prems(1) zero_nested_mask_def get_mh_nm.simps)
      apply (simp add: zero_nested_mask_def)
      apply standard
      using IH(5)
      by (metis IH.hyps(3) get_mp_0_implies_fnm_None zero_mask_def)
    hence "add_to_nm_total_full \<omega> nm = \<omega>"
      by (simp add: zero_nested_mask_def[symmetric])
    then show ?thesis
      by (metis Val \<omega>_eval \<open>v = VBool True\<close> inh_pure_normal)
  next
    case VFailure
    then show ?thesis
      using IH.prems(6) RedExpListFailure \<omega>_eval assertion_framing_state_sub_exps_not_failure by fastforce
  qed

next
  case IH: (SatStar mh mh\<^sub>1 mh\<^sub>2 mp mp\<^sub>1 mp\<^sub>2 A B)

  hence A_sup: "supported_pred_body A" and B_sup: "supported_pred_body B"
    by simp+

  obtain fnm where fnm: "fnm = get_fnm_nm nm"
    by simp
  obtain fnm\<^sub>1 where fnm\<^sub>1: "\<And>lp. fnm\<^sub>1 lp = (if mp\<^sub>1 lp = 0 then None else Some (Abs_posreal (mp\<^sub>1 lp), (mp\<^sub>1 lp / mp lp) *\<^sub>s (snd (the (fnm lp)))))"
    by simp
  obtain fnm\<^sub>2 where fnm\<^sub>2: "\<And>lp. fnm\<^sub>2 lp = (if mp\<^sub>2 lp = 0 then None else Some (Abs_posreal (mp\<^sub>2 lp), (mp\<^sub>2 lp / mp lp) *\<^sub>s (snd (the (fnm lp)))))"
    by simp
  obtain nm\<^sub>1 where nm\<^sub>1: "nm\<^sub>1 = NM mh\<^sub>1 fnm\<^sub>1"
    by simp
  obtain nm\<^sub>2 where nm\<^sub>2: "nm\<^sub>2 = NM mh\<^sub>2 fnm\<^sub>2"
    by simp

  have "mp\<^sub>1 = get_mp_nm nm\<^sub>1"
    unfolding nm\<^sub>1
    apply simp
    apply standard
    apply (rename_tac lp)
    apply (case_tac "fnm\<^sub>1 lp"; cut_tac ?lp=lp in fnm\<^sub>1; simp)
     apply (metis option.distinct(1))
    by (metis Abs_posreal_inverse Some_Some_ifD fst_eqD mem_Collect_eq option.inject pperm_pnone_pgt)
  have "mp\<^sub>2 = get_mp_nm nm\<^sub>2"
    unfolding nm\<^sub>2
    apply simp
    apply standard
    apply (rename_tac lp)
    apply (case_tac "fnm\<^sub>2 lp"; cut_tac ?lp=lp in fnm\<^sub>2; simp)
     apply (metis option.distinct(1))
    by (metis Abs_posreal_inverse Some_Some_ifD fst_eqD mem_Collect_eq option.inject pperm_pnone_pgt)

  have nm\<^sub>1_cons: "consistent_external ctxt \<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>1 \<rparr>"
  proof
    fix pid vs q nm'
    assume lpm: "Some (q,nm') = get_fnm_total \<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>1 \<rparr> (pid,vs)"
    have "q = Abs_posreal (mp\<^sub>1 (pid,vs))" and
         "nm' = (mp\<^sub>1 (pid,vs) / mp (pid,vs)) *\<^sub>s (snd (the (fnm (pid,vs))))"
      using lpm[unfolded nm\<^sub>1, simplified, simplified fnm\<^sub>1]
      by (cases "mp\<^sub>1 (pid,vs) = 0"; simp)+

    have "mp (pid,vs) \<ge> mp\<^sub>1 (pid,vs)"
      by (meson IH.hyps(2) le_funD split_implies_le(1))
    then obtain q\<^sub>a nm'\<^sub>a where "Some (q\<^sub>a,nm'\<^sub>a) = get_fnm_total \<lparr> get_hh_total = hh, get_nm_total = nm \<rparr> (pid,vs)"
      by (metis IH.prems(2) dual_order.strict_trans1 fnm\<^sub>1 get_fnm_nm.simps get_fnm_total.simps lpm nm\<^sub>1 obtain_lpm_from_mp option.distinct(1) preal_not_0_gt_0 total_state.select_convs(2))

    hence extcons\<^sub>a: "consistent_external_wrt_ploc ctxt \<lparr> get_hh_total = hh, get_nm_total = nm'\<^sub>a \<rparr> (pid,vs) (Rep_posreal q\<^sub>a)"
      by (metis IH.prems(3) consistent_external.cases total_state.update_convs(2))

    have the_eq: "snd (the (fnm (pid,vs))) = nm'\<^sub>a"
      by (metis \<open>Some (q\<^sub>a, nm'\<^sub>a) = _\<close> fnm get_fnm_total.simps option.sel sndI total_state.select_convs(2))

    have q_pos: "mp\<^sub>1 (pid,vs) > 0"
      using fnm\<^sub>1 lpm nm\<^sub>1 preal_not_0_gt_0
      by fastforce

    have "Rep_posreal q\<^sub>a = mp (pid,vs)"
      by (metis Abs_posreal_inverse IH.prems(2) \<open>Some (q\<^sub>a, nm'\<^sub>a) = _\<close> \<open>mp\<^sub>1 (pid, vs) \<le> mp (pid, vs)\<close> dual_order.strict_trans1 fst_conv get_fnm_total.simps mem_Collect_eq obtain_lpm_from_mp option.sel q_pos total_state.select_convs(2))

    show "consistent_external_wrt_ploc ctxt (\<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>1 \<rparr>\<lparr> get_nm_total := nm' \<rparr>) (pid,vs) (Rep_posreal q)"
      apply simp
      unfolding \<open>nm' = _\<close> the_eq \<open>q = _\<close> Abs_posreal_inverse[of "mp\<^sub>1 (pid,vs)", simplified, OF q_pos]
      using fraction_consistent_external(1)[OF WfCtxt extcons\<^sub>a, of "mp\<^sub>1 (pid, vs) / mp (pid, vs)", unfolded \<open>Rep_posreal q\<^sub>a = _\<close>, simplified]
      by (metis (mono_tags, lifting) Rep_preal_inject \<open>mp\<^sub>1 (pid, vs) \<le> mp (pid, vs)\<close> divide_preal.rep_eq dual_order.strict_trans1 nonzero_eq_divide_eq pperm_pgt_pnone q_pos times_preal.rep_eq zero_preal.rep_eq)
  qed

  have nm\<^sub>2_cons: "consistent_external ctxt \<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>2 \<rparr>"
  proof
    fix pid vs q nm'
    assume lpm: "Some (q,nm') = get_fnm_total \<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>2 \<rparr> (pid,vs)"
    have "q = Abs_posreal (mp\<^sub>2 (pid,vs))" and
         "nm' = (mp\<^sub>2 (pid,vs) / mp (pid,vs)) *\<^sub>s (snd (the (fnm (pid,vs))))"
      using lpm[unfolded nm\<^sub>2, simplified, simplified fnm\<^sub>2]
      by (cases "mp\<^sub>2 (pid,vs) = 0"; simp)+

    have "mp (pid,vs) \<ge> mp\<^sub>2 (pid,vs)"
      by (meson IH.hyps(2) le_funE split_implies_le(2))
    then obtain q\<^sub>a nm'\<^sub>a where "Some (q\<^sub>a,nm'\<^sub>a) = get_fnm_total \<lparr> get_hh_total = hh, get_nm_total = nm \<rparr> (pid,vs)"
      by (metis IH.prems(2) dual_order.strict_trans1 fnm\<^sub>2 get_fnm_nm.simps get_fnm_total.simps lpm nm\<^sub>2 obtain_lpm_from_mp option.distinct(1) preal_not_0_gt_0 total_state.select_convs(2))

    hence extcons\<^sub>a: "consistent_external_wrt_ploc ctxt \<lparr> get_hh_total = hh, get_nm_total = nm'\<^sub>a \<rparr> (pid,vs) (Rep_posreal q\<^sub>a)"
      by (metis IH.prems(3) consistent_external.cases total_state.update_convs(2))

    have the_eq: "snd (the (fnm (pid,vs))) = nm'\<^sub>a"
      by (metis \<open>Some (q\<^sub>a, nm'\<^sub>a) = _\<close> fnm get_fnm_total.simps option.sel sndI total_state.select_convs(2))

    have q_pos: "mp\<^sub>2 (pid,vs) > 0"
      using fnm\<^sub>2 lpm nm\<^sub>2 preal_not_0_gt_0
      by fastforce

    have "Rep_posreal q\<^sub>a = mp (pid,vs)"
      by (metis Abs_posreal_inverse IH.prems(2) \<open>Some (q\<^sub>a, nm'\<^sub>a) = _\<close> \<open>mp\<^sub>2 (pid, vs) \<le> mp (pid, vs)\<close> dual_order.strict_trans1 fst_conv get_fnm_total.simps mem_Collect_eq obtain_lpm_from_mp option.sel q_pos total_state.select_convs(2))

    show "consistent_external_wrt_ploc ctxt (\<lparr> get_hh_total = hh, get_nm_total = nm\<^sub>2 \<rparr>\<lparr> get_nm_total := nm' \<rparr>) (pid,vs) (Rep_posreal q)"
      apply simp
      unfolding \<open>nm' = _\<close> the_eq \<open>q = _\<close> Abs_posreal_inverse[of "mp\<^sub>2 (pid,vs)", simplified, OF q_pos]
      using fraction_consistent_external(1)[OF WfCtxt extcons\<^sub>a, of "mp\<^sub>2 (pid, vs) / mp (pid, vs)", unfolded \<open>Rep_posreal q\<^sub>a = _\<close>, simplified]
      by (metis (mono_tags, lifting) Rep_preal_inject \<open>mp\<^sub>2 (pid, vs) \<le> mp (pid, vs)\<close> divide_preal.rep_eq dual_order.strict_trans1 nonzero_eq_divide_eq pperm_pgt_pnone q_pos times_preal.rep_eq zero_preal.rep_eq)
  qed

  have "nm\<^sub>1 + nm\<^sub>2 = nm"
    unfolding plus_nested_mask_def nm\<^sub>1 nm\<^sub>2
    apply simp
    apply (rule nested_mask_equality)
    using IH.hyps(1) IH.prems(1)
     apply auto[1]
    unfolding fnm[symmetric]
    apply simp
    apply standard
    apply (rename_tac lp)
    apply (case_tac "fnm\<^sub>1 lp"; case_tac "fnm\<^sub>2 lp"; simp add: pfun_comb_def)
    subgoal for lp
      apply (subgoal_tac "mp lp = 0")
       apply (metis IH.prems(2) fnm get_mp_0_implies_fnm_None)
      apply (subgoal_tac "mp\<^sub>1 lp = 0 \<and> mp\<^sub>2 lp = 0")
      using IH(2)[simplified, THEN fun_cong, of lp, simplified add_masks_def]
       apply fastforce
      using fnm\<^sub>1[of lp] fnm\<^sub>2[of lp]
      by (metis option.distinct(1))
    subgoal for lp lpm\<^sub>2
      apply (subgoal_tac "mp\<^sub>1 lp = 0 \<and> mp\<^sub>2 lp = mp lp \<and> mp\<^sub>2 lp > 0")
      using fnm\<^sub>2[of lp, simplified]
       apply (metis IH.prems(2) PosReal.field_divide_inverse PosReal.field_inverse Some_Some_ifD fnm obtain_lpm_from_mp option.sel pos_perm_class.pmult_comm preal_semimodule_class.scale_one snd_conv)
      using IH(2)[simplified, THEN fun_cong, of lp, simplified add_masks_def]
      by (metis add.commute fnm\<^sub>1 fnm\<^sub>2 option.distinct(1) padd_pnone preal_not_0_gt_0)
    subgoal for lp lpm\<^sub>1
      apply (subgoal_tac "mp\<^sub>2 lp = 0 \<and> mp\<^sub>1 lp = mp lp \<and> mp\<^sub>1 lp > 0")
      using fnm\<^sub>2[of lp, simplified]
       apply (metis IH.prems(2) PosReal.field_divide_inverse PosReal.field_inverse fnm fnm\<^sub>1 obtain_lpm_from_mp option.sel order_less_le pos_perm_class.pmult_comm preal_semimodule_class.scale_one snd_conv)
      using IH(2)[simplified, THEN fun_cong, of lp, simplified add_masks_def]
      by (metis fnm\<^sub>1 fnm\<^sub>2 option.distinct(1) padd_pnone preal_not_0_gt_0)
    subgoal for lp lpm\<^sub>1 lpm\<^sub>2
    proof -
      assume "fnm\<^sub>1 lp = Some lpm\<^sub>1"
        and "fnm\<^sub>2 lp = Some lpm\<^sub>2"
      have "Rep_posreal (fst lpm\<^sub>1) = mp\<^sub>1 lp"
        using \<open>fnm\<^sub>1 lp = Some lpm\<^sub>1\<close> \<open>mp\<^sub>1 = get_mp_nm nm\<^sub>1\<close> nm\<^sub>1 by auto
      have "Rep_posreal (fst lpm\<^sub>2) = mp\<^sub>2 lp"
        using \<open>fnm\<^sub>2 lp = Some lpm\<^sub>2\<close> \<open>mp\<^sub>2 = get_mp_nm nm\<^sub>2\<close> nm\<^sub>2 by auto
      have "mp lp > 0"
        by (metis IH.hyps(2) \<open>fnm\<^sub>1 lp = Some lpm\<^sub>1\<close> fnm\<^sub>1 le_funD option.distinct(1) order_less_imp_not_less order_less_le preal_not_0_gt_0 split_implies_le(1))
      hence 1: "fnm lp = Some (Abs_posreal (mp lp), snd (the (fnm lp)))"
        by (metis IH.prems(2) fnm obtain_lpm_from_mp option.sel split_pairs)
      have 2: "snd lpm\<^sub>1 = (mp\<^sub>1 lp / mp lp) *\<^sub>s snd (the (fnm lp))"
        by (metis \<open>fnm\<^sub>1 lp = Some lpm\<^sub>1\<close> fnm\<^sub>1 option.discI option.sel split_pairs)
      have 3: "snd lpm\<^sub>2 = (mp\<^sub>2 lp / mp lp) *\<^sub>s snd (the (fnm lp))"
        by (metis \<open>fnm\<^sub>2 lp = Some lpm\<^sub>2\<close> fnm\<^sub>2 option.discI option.sel split_pairs)
      show "Some (fst lpm\<^sub>1 + fst lpm\<^sub>2, nested_mask_merge (snd lpm\<^sub>1) (snd lpm\<^sub>2)) = fnm lp"
        apply (subst 1)
        apply standard+
         apply (rule Rep_posreal_inject[THEN iffD1])
        unfolding plus_posreal.rep_eq
         apply (metis Abs_posreal_inject IH.hyps(2) Rep_posreal Rep_posreal_inverse \<open>Rep_posreal (fst lpm\<^sub>1) = mp\<^sub>1 lp\<close> \<open>Rep_posreal (fst lpm\<^sub>2) = mp\<^sub>2 lp\<close> \<open>pos_perm_class.pnone < mp lp\<close> add_masks_def mem_Collect_eq mp_split.simps)
        unfolding plus_nested_mask_def[symmetric] 2 3
        unfolding preal_semimodule_class.scale_add_left[symmetric]
        using preal_semimodule_class.scale_one IH(2)[simplified, THEN fun_cong, of lp, simplified add_masks_def]
        by (metis PosReal.field_divide_inverse PosReal.field_inverse PosReal.pmult_comm \<open>pos_perm_class.pnone < mp lp\<close> distrib_right preal_not_0_gt_0)
    qed
    done

  define \<omega>\<^sub>A where "\<omega>\<^sub>A = add_to_nm_total_full \<omega> nm\<^sub>1"
  have 1: "add_to_nm_total_full \<omega>\<^sub>A nm\<^sub>2 = add_to_nm_total_full \<omega> nm"
    apply (rule full_total_state.equality; simp_all add: IH \<omega>\<^sub>A_def)
    apply (rule total_state.equality; simp_all add: IH \<omega>\<^sub>A_def)
    using \<open>nm\<^sub>1 + nm\<^sub>2 = nm\<close> ab_semigroup_add_class.add_ac(1)
    by blast

  have "add_to_nm_total_full \<omega> nm \<succeq> add_to_nm_total_full \<omega> nm\<^sub>1"
    apply (simp add: greater_def)
    apply (rule exI[of _ "upd_nm_total_full \<omega> nm\<^sub>2"])
    apply (simp add: plus_full_total_state_ext_def)
    apply standard+
     apply (metis (no_types, lifting) \<open>nm\<^sub>1 + nm\<^sub>2 = nm\<close> ab_semigroup_add_class.add_ac(1) option.sel plus_total_state_ext_def total_state.ext_inject total_state.surjective total_state.update_convs(2))
    by (simp add: defined_def plus_total_state_ext_def)
  hence A_mask_intcons: "StateCons (add_to_nm_total_full \<omega> nm\<^sub>1)"
    using IH(14) MonoCons mono_prop_downwardD
    by blast

  show ?case
    apply (rule InhStarNormal[where ?\<omega>''=\<omega>\<^sub>A])
    unfolding \<open>\<omega>\<^sub>A = _\<close>
    using IH(5)[of nm\<^sub>1 \<omega>]
    apply (metis A_mask_intcons A_sup IH.prems(4) IH.prems(5) IH.prems(6) \<open>mp\<^sub>1 = _\<close> assertion_framing_star get_mh_nm.simps nm\<^sub>1 nm\<^sub>1_cons)
    using IH(6)[of nm\<^sub>2 \<omega>\<^sub>A, OF _ _ nm\<^sub>2_cons] 1
    by (metis A_mask_intcons A_sup B_sup IH.IH(1) IH.prems(4) IH.prems(5) IH.prems(6) IH.prems(8) \<omega>\<^sub>A_def \<open>mp\<^sub>1 = _\<close> \<open>mp\<^sub>2 = _\<close> assertion_framing_star get_mh_nm.simps inhale_only_changes_mask nm\<^sub>1 nm\<^sub>1_cons nm\<^sub>2)

next
  case IH: (SatImpTrue e mh mp A)

  hence e_sup: "supported_pred_expr e" and A_sup: "supported_pred_body A"
    by simp+
  obtain res where res: "ctxt, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t res"
    by (metis IH.hyps(1) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh e_sup eval_ok_no_type_error(1))

  show ?case
  proof (cases res)
    case (Val v\<^sub>2)
    hence "v\<^sub>2 = VBool True"
      using eval_with_same_store_same_hh(1)[OF IH(1) res _ Val e_sup] IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh
      by presburger
    show ?thesis
      apply (rule InhImpTrue)
      using Val \<open>v\<^sub>2 = VBool True\<close> res
       apply blast
      using IH(3)[OF IH(4-8)] A_sup Val \<open>v\<^sub>2 = VBool True\<close> assertion_framing_imp res IH.prems(6,8)
      by blast
  next
    case VFailure
    then show ?thesis
      using IH.prems(6) res assertion_framing_state_def inh_imp_failure by blast
  qed

next
  case IH: (SatImpFalse e mh mp A)

  hence e_sup: "supported_pred_expr e" and A_sup: "supported_pred_body A"
    by simp+
  obtain res where res: "ctxt, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t res"
    by (metis IH.hyps(1) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh e_sup eval_ok_no_type_error(1))

  have "nm = 0"
    apply (simp add: zero_nested_mask_def)
    apply (rule nested_mask_equality, simp_all)
    using IH.hyps(2) IH.prems(1) zero_mask_def
      apply fastforce
    using IH.hyps(3) IH.prems(2) zero_mask_def
    by (metis get_mp_0_implies_fnm_None)

  show ?case
  proof (cases res)
    case (Val v\<^sub>2)
    hence "v\<^sub>2 = VBool False"
      using eval_with_same_store_same_hh(1)[OF IH(1) res _ Val e_sup] IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh
      by presburger
    show ?thesis
      apply (rule InhImpFalse)
      using Val \<open>v\<^sub>2 = VBool False\<close> res
       apply blast
      by (simp add: \<open>nm = 0\<close>)
  next
    case VFailure
    then show ?thesis
      using IH.prems(6) res assertion_framing_state_def inh_imp_failure by blast
  qed

next
  case IH: (SatCondTrue e mh mp A B)

  hence e_sup: "supported_pred_expr e" and A_sup: "supported_pred_body A" and B_sup: "supported_pred_body B"
    by simp+
  obtain res where res: "ctxt, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t res"
    by (metis IH.hyps(1) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh e_sup eval_ok_no_type_error(1))

  show ?case
  proof (cases res)
    case (Val v\<^sub>2)
    hence "v\<^sub>2 = VBool True"
      using eval_with_same_store_same_hh(1)[OF IH(1) res _ Val e_sup] IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh
      by presburger
    show ?thesis
      apply (rule InhCondAssertTrue)
      using Val \<open>v\<^sub>2 = VBool True\<close> res
       apply blast
      using IH(3)[OF IH(4-8)] A_sup Val \<open>v\<^sub>2 = VBool True\<close> assertion_framing_cond_assert_true res IH.prems(6,8)
      by blast
  next
    case VFailure
    then show ?thesis
      using IH.prems(6) res assertion_framing_state_def inh_cond_assert_failure by blast
  qed

next
  case IH: (SatCondFalse e mh mp B A)

  hence e_sup: "supported_pred_expr e" and A_sup: "supported_pred_body A" and B_sup: "supported_pred_body B"
    by simp+
  obtain res where res: "ctxt, Some \<omega> \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t res"
    by (metis IH.hyps(1) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh e_sup eval_ok_no_type_error(1))

  show ?case
  proof (cases res)
    case (Val v\<^sub>2)
    hence "v\<^sub>2 = VBool False"
      using eval_with_same_store_same_hh(1)[OF IH(1) res _ Val e_sup] IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh
      by presburger
    show ?thesis
      apply (rule InhCondAssertFalse)
      using Val \<open>v\<^sub>2 = VBool False\<close> res
       apply blast
      by (metis B_sup IH.IH IH.prems(1-6,8) Val \<open>v\<^sub>2 = VBool False\<close> assertion_framing_cond_assert_false res)
  next
    case VFailure
    then show ?thesis
      using IH.prems(6) res assertion_framing_state_def inh_cond_assert_failure by blast
  qed
qed


lemma extcons_state_can_be_inhaled:
  assumes PredDecl: "ViperLang.predicates (program_total ctxt) pid = Some pdecl"
      and PredBody: "ViperLang.predicate_decl.body pdecl = Some pbody"
      and SupPred: "supported_pred_body pbody"
      and SelfFraming: "\<And>q. assertion_framing_state ctxt StateCons (syntactic_mult q pbody) \<omega>"
      and ExtCons: "consistent_external_wrt_ploc ctxt \<lparr> get_hh_total = hh, get_nm_total = nm \<rparr> (pid,vs) p"
      and \<omega>hh: "get_hh_total_full \<omega> = hh"
      and \<omega>Store: "get_store_total \<omega> = nth_option vs"
      and FinalIntCons: "StateCons (add_to_nm_total_full \<omega> nm)"
      and MonoCons: "mono_prop_downward StateCons"
      and WfCtxt: "ctxt_pred_syn_wf ctxt"
      and "p > 0"
    shows "red_inhale ctxt StateCons (syntactic_mult (Rep_preal p) pbody) \<omega> (RNormal (add_to_nm_total_full \<omega> nm))"
proof -
  have
    "vals_well_typed (absval_interp_total ctxt) vs (predicate_decl.args pdecl)"
    "p = 0 \<Longrightarrow> nm = 0" and
    "p > 0 \<Longrightarrow> sat ctxt \<lparr> get_store_total = nth_option vs,
                   get_trace_total = Map.empty,
                   get_total_full = \<lparr> get_hh_total = hh, get_nm_total = 0 \<rparr> \<rparr>
            (get_mh_nm nm) (get_mp_nm nm)
            (syntactic_mult (Rep_preal p) pbody)" and
    "consistent_external ctxt \<lparr> get_hh_total = hh, get_nm_total = nm \<rparr>"
    using SatStep_case PredDecl PredBody ExtCons
    by fastforce+
  moreover have "assertion_framing_state ctxt StateCons (syntactic_mult (Rep_preal p) pbody) \<omega>"
    using SelfFraming
    by (simp add: calculation(1))
  ultimately show ?thesis
    apply (cases "p > 0")
    using \<omega>Store \<omega>hh extcons_state_can_be_inhaled_assertion FinalIntCons MonoCons
     apply (metis SupPred WfCtxt full_total_state.select_convs(1) full_total_state.select_convs(3) get_hh_total_full.simps prat_non_negative syntactic_mult_supported total_state.select_convs(1))
    apply (subgoal_tac "p = 0")
     prefer 2
    using preal_not_0_gt_0
     apply blast
    apply simp
    using assms(11)
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


lemma inhale_with_substitution:
  assumes "red_inhale ctxt StateCons A (\<omega>\<lparr> get_store_total := nth_option vs \<rparr>) (RNormal (\<omega>'\<lparr> get_store_total := nth_option vs \<rparr>))"
      and "red_pure_exps_total ctxt (Some \<omega>) es \<omega> (Some vs)"
    shows "red_inhale ctxt StateCons (substitute_args_assertion A es) \<omega> (RNormal \<omega>')"
  sorry


\<comment> \<open>Currently not used anywhere.\<close>
lemma inhale_mono:
  assumes "red_inhale ctxt StateCons A \<omega> (RNormal \<omega>')"
  shows "\<omega> \<le> \<omega>'"
  oops



subsection \<open>Relation between Two Self-Framing Definitions\<close>


lemma eval_perm_0_locs_irrelevant:
  assumes "get_store_total \<omega>\<^sub>0 = get_store_total \<omega>\<^sub>0'"
      and "get_trace_total \<omega>\<^sub>0 = get_trace_total \<omega>\<^sub>0'"
      and "differ_only_in_0_perm_locs (get_total_full \<omega>\<^sub>0) (get_total_full \<omega>\<^sub>0')"
      and "get_store_total \<omega> = get_store_total \<omega>'"
      and "get_trace_total \<omega> = get_trace_total \<omega>'"
      and "get_nm_total_full \<omega> = get_nm_total_full \<omega>'"
      and "get_hh_total_full \<omega>\<^sub>0 = get_hh_total_full \<omega>"
      and "get_hh_total_full \<omega>\<^sub>0' = get_hh_total_full \<omega>'"
      and "\<omega>_def = Some \<omega>\<^sub>0"
      and "\<omega>_def' = Some \<omega>\<^sub>0'"
    shows "ctxt, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t r \<Longrightarrow>
           r \<noteq> VFailure \<Longrightarrow>
           ctxt, \<omega>_def' \<turnstile> \<langle>e;\<omega>'\<rangle> [\<Down>]\<^sub>t r"
      and "red_pure_exps_total ctxt \<omega>_def es \<omega> rs \<Longrightarrow>
           rs \<noteq> None \<Longrightarrow>
           red_pure_exps_total ctxt \<omega>_def' es \<omega>' rs"
  using assms
proof (induction arbitrary: \<omega>\<^sub>0 \<omega>_def' \<omega>\<^sub>0' \<omega>' and \<omega>\<^sub>0 \<omega>_def' \<omega>\<^sub>0' \<omega>' rule: red_pure_exp_inducts)
  case IH: (RedBinopLazy \<omega>_def e1 \<omega> v1 bop v e2)
  then show ?case
    by (fastforce intro: RedBinopLazy)
next
  case IH: (RedBinop \<omega>_def e1 \<omega> v1 e2 v2 bop v)
  then show ?case
    by (fastforce intro: RedBinop)
next
  case IH: (RedUnop \<omega>_def e \<omega> v unop v')
  then show ?case
    by (fastforce intro: RedUnop)
next
  case IH: (RedOld \<omega> l \<phi> \<omega>_def'\<^sub>s \<omega>_def e v)
  show ?case
    apply (rule TotalExpressions.RedOld)
    using IH
      apply simp
    using IH
     apply simp
    using IH(3)[unfolded \<open>\<omega>_def'\<^sub>s = _\<close> \<open>\<omega>_def = _\<close>, simplified]
    apply (subgoal_tac "\<omega>\<^sub>0\<lparr> get_total_full := \<phi> \<rparr> = \<omega>\<^sub>0'\<lparr> get_total_full := \<phi> \<rparr>")
     apply (subgoal_tac "\<omega>\<lparr> get_total_full := \<phi> \<rparr> = \<omega>'\<lparr> get_total_full := \<phi> \<rparr>")
      apply argo
    by (rule full_total_state.equality, simp_all add: IH)
next
  case IH: (RedField \<omega>_def e \<omega> a f v)
  have **: "ctxt, \<omega>_def' \<turnstile> \<langle>e;\<omega>'\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))"
    by (metis IH.IH(2) IH.prems(2-11) extended_val.distinct(1))
  show ?case
    unfolding \<open>\<omega>_def = _\<close> \<open>\<omega>_def' = _\<close>
    apply simp
    apply (intro conjI)
     defer
    using IH.prems(1,10)
     apply force
  proof
    assume "(a,f) \<in> get_valid_locs \<omega>\<^sub>0"
    hence "(a,f) \<in> get_valid_locs \<omega>\<^sub>0'"
      using IH(7)[unfolded differ_only_in_0_perm_locs_def]
      unfolding get_valid_locs_def
      by auto
    moreover have "get_hh_total_full \<omega>' (a,f) = v"
      unfolding IH(12)[symmetric]
      using IH(7)[unfolded differ_only_in_0_perm_locs_def]
      by (metis IH.hyps IH.prems(8) \<open>(a, f) \<in> get_valid_locs \<omega>\<^sub>0\<close> get_hh_total_full.simps get_mh_total.simps get_mh_total_full.simps get_valid_locs_def mem_Collect_eq pperm_pgt_pnone sum_0_implies_mh_zero)
    ultimately show "ctxt, Some \<omega>\<^sub>0' \<turnstile> \<langle>FieldAcc e f;\<omega>'\<rangle> [\<Down>]\<^sub>t Val v"
      using ** IH.prems(11) RedField_def_normalI
      by blast
  qed
next
  case IH: (RedPerm \<omega>_def e \<omega> a f v)
  then show ?case
    by (fastforce intro: RedPerm)
next
  case IH: (RedUnfoldingDef \<omega>\<^sub>0\<^sub>f es \<omega> vs perm pid nm' \<omega>\<^sub>0\<^sub>u ubody v)
  hence *: "get_nm_total_full \<omega>\<^sub>0 = get_nm_total_full \<omega>\<^sub>0'"
    by (metis differ_only_in_0_perm_locs_def get_nm_total_full.simps)
  have "\<omega>\<^sub>0\<^sub>f = \<omega>\<^sub>0"
    using IH.prems(10)
    by auto
  define perm' where "perm' = get_mp_total_full \<omega>\<^sub>0' (pid,vs)"
  have **: "\<And>l. nm_loc_sum l (get_nm_total_full \<omega>\<^sub>0) 0 \<Longrightarrow> nm_loc_sum l nm' 0"
    using IH.hyps(3) \<open>\<omega>\<^sub>0\<^sub>f = \<omega>\<^sub>0\<close> shift_up_preserves_loc_sum
    by blast

  show ?case
    unfolding \<open>\<omega>_def' = _\<close>
    apply (rule RedUnfoldingDef)
         apply (rule IH(2)[of \<omega>\<^sub>0 \<omega>\<^sub>0'])
                   apply simp
                  apply fact+
         apply simp
        apply fact
    unfolding \<open>perm' = _\<close>
    using IH.hyps(1,2) * \<open>\<omega>\<^sub>0\<^sub>f = \<omega>\<^sub>0\<close>
       apply auto[1]
    using IH *
      apply simp
     apply (simp del: upd_nm_total_full.simps)
    apply (rule IH(4)[of \<omega>\<^sub>0\<^sub>u "upd_nm_total_full \<omega>\<^sub>0' nm'"])
              apply auto
            apply (simp add: IH.prems(1))
           apply (simp add: IH.hyps(4) IH.prems(2) \<open>\<omega>\<^sub>0\<^sub>f = \<omega>\<^sub>0\<close>)
          apply (simp add: IH.hyps(4) IH.prems(3) \<open>\<omega>\<^sub>0\<^sub>f = \<omega>\<^sub>0\<close>)
    using IH(12)
    unfolding differ_only_in_0_perm_locs_def
    using ** IH.hyps(4) \<open>\<omega>\<^sub>0\<^sub>f = \<omega>\<^sub>0\<close>
         apply force
        apply fact+
    using IH.hyps(4) IH.prems(7-9) \<open>\<omega>\<^sub>0\<^sub>f = \<omega>\<^sub>0\<close>
    by auto
next
  case (RedExpListCons \<omega>_def e \<omega> v es res res')
  then show ?case
    by (metis extended_val.distinct(1) option.simps(8) red_pure_exp_total_red_pure_exps_total.RedExpListCons)
qed (auto intro: red_pure_exp_intros)


lemma eval_perm_0_locs_irrelevant_supported_pred:
  assumes "get_store_total \<omega>\<^sub>0 = get_store_total \<omega>\<^sub>0'"
      and "differ_only_in_0_perm_locs (get_total_full \<omega>\<^sub>0) (get_total_full \<omega>\<^sub>0')"
      and "get_store_total \<omega> = get_store_total \<omega>'"
      and "get_hh_total_full \<omega>\<^sub>0 = get_hh_total_full \<omega>"
      and "get_hh_total_full \<omega>\<^sub>0' = get_hh_total_full \<omega>'"
      and "\<omega>_def = Some \<omega>\<^sub>0"
      and "\<omega>_def' = Some \<omega>\<^sub>0'"
    shows "ctxt, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t r \<Longrightarrow>
           r \<noteq> VFailure \<Longrightarrow>
           supported_pred_expr e \<Longrightarrow>
           ctxt, \<omega>_def' \<turnstile> \<langle>e;\<omega>'\<rangle> [\<Down>]\<^sub>t r"
      and "red_pure_exps_total ctxt \<omega>_def es \<omega> rs \<Longrightarrow>
           rs \<noteq> None \<Longrightarrow>
           list_all supported_pred_expr es \<Longrightarrow>
           red_pure_exps_total ctxt \<omega>_def' es \<omega>' rs"
  using assms
proof (induction arbitrary: \<omega>\<^sub>0 \<omega>_def' \<omega>\<^sub>0' \<omega>' and \<omega>\<^sub>0 \<omega>_def' \<omega>\<^sub>0' \<omega>' rule: red_pure_exp_inducts)
  case IH: (RedBinopLazy \<omega>_def e1 \<omega> v1 bop v e2)
  then show ?case
    by (fastforce intro: RedBinopLazy)
next
  case IH: (RedBinop \<omega>_def e1 \<omega> v1 e2 v2 bop v)
  then show ?case
    by (fastforce intro: RedBinop)
next
  case IH: (RedUnop \<omega>_def e \<omega> v unop v')
  then show ?case
    by (fastforce intro: RedUnop)
next
  case IH: (RedField \<omega>_def e \<omega> a f v)
  have **: "ctxt, \<omega>_def' \<turnstile> \<langle>e;\<omega>'\<rangle> [\<Down>]\<^sub>t Val (VRef (Address a))"
    using IH.IH(2) IH.prems(2-9)
    by auto
  show ?case
    unfolding \<open>\<omega>_def = _\<close> \<open>\<omega>_def' = _\<close>
    apply simp
    apply (intro conjI)
     defer
    using IH.prems(1,8)
     apply force
  proof
    assume "(a,f) \<in> get_valid_locs \<omega>\<^sub>0"
    hence "(a,f) \<in> get_valid_locs \<omega>\<^sub>0'"
      using IH(7)[unfolded differ_only_in_0_perm_locs_def]
      unfolding get_valid_locs_def
      by auto
    moreover have "get_hh_total_full \<omega>' (a,f) = v"
      unfolding IH(12)[symmetric]
      using IH(7)[unfolded differ_only_in_0_perm_locs_def]
      by (metis IH.hyps IH.prems(6,7) \<open>(a, f) \<in> get_valid_locs \<omega>\<^sub>0\<close> get_hh_total_full.simps get_mh_total.simps get_mh_total_full.simps get_valid_locs_def mem_Collect_eq pperm_pgt_pnone sum_0_implies_mh_zero)
    ultimately show "ctxt, Some \<omega>\<^sub>0' \<turnstile> \<langle>FieldAcc e f;\<omega>'\<rangle> [\<Down>]\<^sub>t Val v"
      using ** IH.prems(9) RedField_def_normalI
      by blast
  qed
next
  case IH: (RedUnfoldingDef \<omega>\<^sub>0\<^sub>f es \<omega> vs perm pid nm' \<omega>\<^sub>0\<^sub>u ubody v)
  hence *: "get_nm_total_full \<omega>\<^sub>0 = get_nm_total_full \<omega>\<^sub>0'"
    by (metis differ_only_in_0_perm_locs_def get_nm_total_full.simps)
  have "\<omega>\<^sub>0\<^sub>f = \<omega>\<^sub>0"
    using IH.prems(8)
    by auto
  define perm' where "perm' = get_mp_total_full \<omega>\<^sub>0' (pid,vs)"
  have **: "\<And>l. nm_loc_sum l (get_nm_total_full \<omega>\<^sub>0) 0 \<Longrightarrow> nm_loc_sum l nm' 0"
    using IH.hyps(3) \<open>\<omega>\<^sub>0\<^sub>f = \<omega>\<^sub>0\<close> shift_up_preserves_loc_sum
    by blast

  show ?case
    unfolding \<open>\<omega>_def' = _\<close>
    apply (rule RedUnfoldingDef)
         apply (rule IH(2)[of \<omega>\<^sub>0 \<omega>\<^sub>0'])
                 apply simp
    using IH.prems(2) supported_sub_expr_supported
                apply fastforce
               apply fact+
         apply simp
        apply fact
    unfolding \<open>perm' = _\<close>
    using IH.hyps(1,2) * \<open>\<omega>\<^sub>0\<^sub>f = \<omega>\<^sub>0\<close>
       apply auto[1]
    using IH *
      apply simp
     apply (simp del: upd_nm_total_full.simps)
    apply (rule IH(4)[of \<omega>\<^sub>0\<^sub>u "upd_nm_total_full \<omega>\<^sub>0' nm'"])
            apply (simp add: IH.prems(1))
    using IH.prems(2)
           apply auto[1]
          apply (simp add: IH.hyps(4) IH.prems(3) \<open>\<omega>\<^sub>0\<^sub>f = \<omega>\<^sub>0\<close>)
    using IH(12)
    unfolding differ_only_in_0_perm_locs_def
    using ** IH.hyps(4) \<open>\<omega>\<^sub>0\<^sub>f = \<omega>\<^sub>0\<close>
         apply force
        apply fact
    using IH.hyps(4) IH.prems(6) \<open>\<omega>\<^sub>0\<^sub>f = \<omega>\<^sub>0\<close>
       apply auto[1]
    using IH.hyps(4) IH.prems(7-9) \<open>\<omega>\<^sub>0\<^sub>f = \<omega>\<^sub>0\<close>
    by auto
next
  case (RedExpListCons \<omega>_def e \<omega> v es res res')
  then show ?case
    by (fastforce intro: red_pure_exp_total_red_pure_exps_total.RedExpListCons)
qed (auto intro: red_pure_exp_intros)


lemma eval_None_same_hh:  \<comment> \<open>redundant with @{thm eval_exhale_sat_helper_helper}}\<close>
  assumes "get_hh_total_full \<omega> = get_hh_total_full \<omega>'"
      and "get_store_total \<omega> = get_store_total \<omega>'"
    shows "ctxt, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t r \<Longrightarrow>
           \<omega>_def = None \<Longrightarrow>
           r = Val v \<Longrightarrow>
           supported_pred_expr e \<Longrightarrow>
           ctxt, None \<turnstile> \<langle>e;\<omega>'\<rangle> [\<Down>]\<^sub>t Val v"
      and "red_pure_exps_total ctxt \<omega>_def es \<omega> rs \<Longrightarrow>
           \<omega>_def = None \<Longrightarrow>
           rs = Some vs \<Longrightarrow>
           list_all supported_pred_expr es \<Longrightarrow>
           red_pure_exps_total ctxt None es \<omega>' (Some vs)"
  using assms
proof (induction arbitrary: \<omega>' v and \<omega>' vs rule: red_pure_exp_inducts)
  case (RedField \<omega>_def e \<omega> a f v)
  then show ?case
    by (metis RedField_no_def_normalI eval_exhale_sat_helper_helper(1) option.pred_inject(1))
next
  case (RedUnfolding es \<omega> vs ubody v pred_id)
  then show ?case
    by (meson eval_exhale_sat_helper_helper(1) red_pure_exp_total_red_pure_exps_total.RedUnfolding)
qed (fastforce intro: red_pure_exp_intros)+


lemma framed_sat_irrelevant_perm_0_locs_helper:
    fixes \<phi> :: "'a total_state"
  assumes "red_pure_exps_total ctxt None es \<omega> (Some vs)"
      and Framed: "assertion_framing_state ctxt StateCons A \<omega>\<^sub>0"
      and hh_diff_only: "differ_only_in_0_perm_locs_hh (add_to_nm_total \<phi> (get_nm_total_full \<omega>\<^sub>0)) hh"
      and "get_store_total \<omega>\<^sub>0 = get_store_total \<omega>"
      and "get_hh_total_full \<omega>\<^sub>0 = get_hh_total_full \<omega>"
      and "get_hh_total_full \<omega> = get_hh_total \<phi>"
      and "get_hh_total_full \<omega>' = hh"
      and "get_store_total \<omega>\<^sub>0 = get_store_total \<omega>'"
      and "supported_pred_body A"
      and "es = direct_sub_expressions_assertion A"
    shows "red_pure_exps_total ctxt None es \<omega>' (Some vs)" (is ?P1)
      and "red_pure_exps_total ctxt (Some \<omega>\<^sub>0) es \<omega>\<^sub>0 (Some vs)" (is ?P2)
proof -
  \<comment> \<open>Evaluating \<^term>\<open>es\<close> under \<^term>\<open>\<omega>\<^sub>0\<close> does not result in a type error.\<close>
  have "\<exists>rs. red_pure_exps_total ctxt (Some \<omega>\<^sub>0) es \<omega>\<^sub>0 rs"
    apply (rule eval_ok_no_type_error(2)[OF _ _ assms(1)])
    using assms(4,5)
       apply (force, force)
     apply simp
    by (metis (no_types, lifting) assert_pred_subexp assms(9,10) list_all_length)

  \<comment> \<open>Since, the assertion \<^term>\<open>A\<close> is framed by \<^term>\<open>\<omega>\<^sub>0\<close>, the evaluation of direct sub-expressions cannot fail.\<close>
  then obtain vs' where "red_pure_exps_total ctxt (Some \<omega>\<^sub>0) es \<omega>\<^sub>0 (Some vs')"
    using Framed[unfolded assertion_framing_state_def] InhSubExpFailure \<open>es = _\<close>
    by (metis red_exp_list_failure_Nil split_option_ex)

  \<comment> \<open>The evaluation result is the same.\<close>
  thus ?P2
    by (metis assert_pred_subexp assms(1,4,5,9,10) eval_exhale_sat_helper_helper(2) eval_is_deterministic(2))

  \<comment> \<open>Change the underlying state to \<^term>\<open>\<omega>'\<close>.\<close>
  have "red_pure_exps_total ctxt (Some (upd_hh_total_full \<omega>\<^sub>0 (get_hh_total_full \<omega>'))) es \<omega>' (Some vs)"
    apply (rule eval_perm_0_locs_irrelevant_supported_pred(2)[where \<omega>\<^sub>0=\<omega>\<^sub>0 and \<omega>=\<omega>\<^sub>0 and \<omega>\<^sub>0'="upd_hh_total_full \<omega>\<^sub>0 (get_hh_total_full \<omega>')"]; (rule assms)?)  \<comment> \<open>The instantiation of \<^term>\<open>\<omega>\<^sub>0'\<close> is weird. But it does the trick. Could generalize @{thm eval_perm_0_locs_irrelevant_supported_pred} to unrestrict \<^term>\<open>hh\<close> of well-definedness states.\<close>
            apply simp
    unfolding differ_only_in_0_perm_locs_def
           apply (intro conjI)
            apply simp
    using hh_diff_only[unfolded differ_only_in_0_perm_locs_hh_def]
            apply (metis add.commute add_to_nm_total.simps all_pos assms(5) assms(6) assms(7) get_hh_total_full.simps get_nm_total_full.simps nle_le nm_loc_sum.elims(2) nm_loc_sum_smaller nm_sum_is_bigger total_state.select_convs(1) total_state.select_convs(2) total_state.surjective total_state.update_convs(2))
           prefer 8
           apply (metis (no_types, lifting) assert_pred_subexp assms(10) assms(9) list_all_length)
          apply simp_all
    by fact

  thus ?P1
    by (metis assert_pred_subexp assms(9,10) eval_exhale_sat_helper_helper(2))
qed


lemma eval_list_2D:
  assumes "red_pure_exps_total ctxt \<omega>_def [e1, e2] \<omega> (Some [v1, v2])"
    shows "ctxt, \<omega>_def \<turnstile> \<langle>e1;\<omega>\<rangle> [\<Down>]\<^sub>t Val v1"
      and "ctxt, \<omega>_def \<turnstile> \<langle>e2;\<omega>\<rangle> [\<Down>]\<^sub>t Val v2"
  using assms
  by (fastforce elim: red_exp_list_normal_elim)+


lemma eval_list_append_to_oneD:
  assumes "red_pure_exps_total ctxt \<omega>_def (es @ [e]) \<omega> (Some (vs @ [v]))"
    shows "red_pure_exps_total ctxt \<omega>_def es \<omega> (Some vs) \<and> ctxt, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"
  using assms
proof (induction es arbitrary: vs)
  case Nil
  then show ?case
    apply (intro conjI)
    using red_pure_exps_total.simps red_pure_exps_total_singleton
     apply fastforce
    using red_exp_list_normal_elim[OF Nil, simplified]
    by (metis append1_eq_conv append_Nil option.sel red_exp_list_failure_Nil)
next
  case (Cons a es)
  show ?case
    apply (intro conjI)
    using Cons
     apply (smt (z3) Cons_eq_appendI butlast.simps(2) butlast_snoc list.sel(3) list_all2_Cons1 list_all2_Nil2 list_all2_red_pure_exps_total red_pure_exps_total_list_all2)
    by (smt (verit, ccfv_threshold) Cons.IH Cons.prems append_eq_Cons_conv append_is_Nil_conv list.inject list.simps(3) red_exp_list_normal_elim)
qed


lemma framed_sat_irrelevant_perm_0_locs:
  assumes "sat ctxt \<omega> mh mp A"
      and "mh = get_mh_total \<phi>"
      and "mp = get_mp_total \<phi>"
      and "assertion_framing_state ctxt StateCons A \<omega>\<^sub>0"
      and "StateCons (add_to_nm_total_full \<omega>\<^sub>0 (get_nm_total \<phi>))"
      and "consistent_external ctxt \<phi>"
      and "differ_only_in_0_perm_locs_hh (add_to_nm_total \<phi> (get_nm_total_full \<omega>\<^sub>0)) hh"
      and "get_store_total \<omega>\<^sub>0 = get_store_total \<omega>"
      and "get_hh_total_full \<omega>\<^sub>0 = get_hh_total_full \<omega>"
      and "get_hh_total_full \<omega> = get_hh_total \<phi>"
      and "get_hh_total_full \<omega>' = hh"
      and "get_store_total \<omega>\<^sub>0 = get_store_total \<omega>'"
      and "supported_pred_body A"
      and CtxtPredSynWf: "ctxt_pred_syn_wf ctxt"
      and ConsMono: "mono_prop_downward StateCons"
    shows "sat ctxt \<omega>' mh mp A"
  using assms(1-13)
proof (induction arbitrary: \<phi> \<omega>\<^sub>0 \<omega>' hh rule: sat.inducts)
  case IH: (SatAcc e_r r e_p p a mh f mp)
  have "red_pure_exps_total ctxt None [e_r, e_p] \<omega>' (Some [VRef r, VPerm p])"
    by (rule framed_sat_irrelevant_perm_0_locs_helper(1); (rule IH)?; simp add: IH.hyps(1-2) list_all2_red_pure_exps_total)
  hence "ctxt, None \<turnstile> \<langle>e_r;\<omega>'\<rangle> [\<Down>]\<^sub>t Val (VRef r)" and "ctxt, None \<turnstile> \<langle>e_p;\<omega>'\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
    by (fastforce dest: eval_list_2D)+
  then show ?case
    using IH.hyps(3-6)
    by (blast intro: SatAcc)
next
  case IH: (SatAccWildcard e_r r a f mh mp)
  have "red_pure_exps_total ctxt None [e_r] \<omega>' (Some [VRef r])"
    by (rule framed_sat_irrelevant_perm_0_locs_helper(1); (rule IH)?; simp add: IH.hyps(1-2) list_all2_red_pure_exps_total)
  hence "ctxt, None \<turnstile> \<langle>e_r;\<omega>'\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
    by (fastforce elim: red_exp_list_normal_elim)
  then show ?case
    using IH.hyps
    by (blast intro: SatAccWildcard)
next
  case IH: (SatAccPred e_args v_args e_p p mh mp pid pdecl pbody)
  have "red_pure_exps_total ctxt None (e_args @ [e_p]) \<omega>' (Some (v_args @ [VPerm p]))"
    by (rule framed_sat_irrelevant_perm_0_locs_helper(1); (rule IH)?; simp add: IH.hyps(1-2) red_pure_exps_append_success)
  hence "ctxt, None \<turnstile> \<langle>e_p;\<omega>'\<rangle> [\<Down>]\<^sub>t Val (VPerm p)" and "red_pure_exps_total ctxt None e_args \<omega>' (Some v_args)"
    by (fastforce dest: eval_list_append_to_oneD elim: red_exp_list_normal_elim)+
  then show ?case
    using IH.hyps
    by (blast intro: SatAccPred)
next
  case IH: (SatAccPredWildcard e_args v_args mh pid mp pdecl pbody)
  have "red_pure_exps_total ctxt None e_args \<omega>' (Some v_args)"
    by (rule framed_sat_irrelevant_perm_0_locs_helper(1); (rule IH)?; simp add: IH.hyps(1-2))
  then show ?case
    using IH.hyps
    by (blast intro: SatAccPredWildcard)
next
  case IH: (SatPure e mh mp)
  have "red_pure_exps_total ctxt None [e] \<omega>' (Some [VBool True])"
    by (rule framed_sat_irrelevant_perm_0_locs_helper(1); (rule IH)?; simp add: IH.hyps(1-2) list_all2_red_pure_exps_total)
  then show ?case
    by (metis IH.hyps(2) IH.hyps(3) SatPure list.discI nth_Cons_0 red_exp_list_normal_elim)
next
  case IH: (SatStar mh mh\<^sub>1 mh\<^sub>2 mp mp\<^sub>1 mp\<^sub>2 A B)

  define fnm where fnm: "fnm = get_fnm_total \<phi>"
  obtain fnm\<^sub>1 where fnm\<^sub>1: "\<And>lp. fnm\<^sub>1 lp = (if mp\<^sub>1 lp = 0 then None else Some (Abs_posreal (mp\<^sub>1 lp), (mp\<^sub>1 lp / mp lp) *\<^sub>s (snd (the (fnm lp)))))"
    by simp
  obtain fnm\<^sub>2 where fnm\<^sub>2: "\<And>lp. fnm\<^sub>2 lp = (if mp\<^sub>2 lp = 0 then None else Some (Abs_posreal (mp\<^sub>2 lp), (mp\<^sub>2 lp / mp lp) *\<^sub>s (snd (the (fnm lp)))))"
    by simp
  define nm\<^sub>1 where "nm\<^sub>1 = NM mh\<^sub>1 fnm\<^sub>1"
  define nm\<^sub>2 where "nm\<^sub>2 = NM mh\<^sub>2 fnm\<^sub>2"
  define \<phi>\<^sub>1 where "\<phi>\<^sub>1 = \<phi>\<lparr> get_nm_total := nm\<^sub>1 \<rparr>"
  define \<phi>\<^sub>2 where "\<phi>\<^sub>2 = \<phi>\<lparr> get_nm_total := nm\<^sub>2 \<rparr>"

  have "mp\<^sub>1 = get_mp_total \<phi>\<^sub>1"
    unfolding \<phi>\<^sub>1_def nm\<^sub>1_def
    apply simp
    apply standard
    apply (rename_tac lp)
    apply (case_tac "fnm\<^sub>1 lp"; cut_tac ?lp=lp in fnm\<^sub>1; simp)
     apply (metis option.distinct(1))
    by (metis Abs_posreal_inverse Some_Some_ifD fst_eqD mem_Collect_eq option.inject pperm_pnone_pgt)
  have "mp\<^sub>2 = get_mp_total \<phi>\<^sub>2"
    unfolding \<phi>\<^sub>2_def nm\<^sub>2_def
    apply simp
    apply standard
    apply (rename_tac lp)
    apply (case_tac "fnm\<^sub>2 lp"; cut_tac ?lp=lp in fnm\<^sub>2; simp)
     apply (metis option.distinct(1))
    by (metis Abs_posreal_inverse Some_Some_ifD fst_eqD mem_Collect_eq option.inject pperm_pnone_pgt)

  have \<phi>\<^sub>1_extcons: "consistent_external ctxt \<phi>\<^sub>1"
  proof
    fix pid vs q nm'
    assume lpm: "Some (q,nm') = get_fnm_total \<phi>\<^sub>1 (pid,vs)"
    have "q = Abs_posreal (mp\<^sub>1 (pid,vs))" and
         "nm' = (mp\<^sub>1 (pid,vs) / mp (pid,vs)) *\<^sub>s (snd (the (fnm (pid,vs))))"
      using lpm[unfolded \<open>\<phi>\<^sub>1 = _\<close> \<open>nm\<^sub>1 = _\<close>, simplified, simplified fnm\<^sub>1]
      by (cases "mp\<^sub>1 (pid,vs) = 0"; simp)+

    have "mp (pid,vs) \<ge> mp\<^sub>1 (pid,vs)"
      by (meson IH.hyps(2) le_funD split_implies_le(1))
    then obtain q\<^sub>a nm'\<^sub>a where "Some (q\<^sub>a,nm'\<^sub>a) = get_fnm_total \<phi> (pid,vs)"
      by (metis IH.prems(2) \<open>mp\<^sub>1 = _\<close> get_fnm_total.simps get_mp_0_implies_fnm_None get_mp_total.simps linorder_not_less lpm obtain_lpm_from_mp preal_not_0_gt_0)

    hence extcons\<^sub>a: "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm'\<^sub>a \<rparr>) (pid,vs) (Rep_posreal q\<^sub>a)"
      by (metis IH.prems(5) consistent_external.cases)

    have the_eq: "snd (the (fnm (pid,vs))) = nm'\<^sub>a"
      by (metis \<open>Some (q\<^sub>a,nm'\<^sub>a) = _\<close> fnm option.sel sndI)

    have q_pos: "mp\<^sub>1 (pid,vs) > 0"
      using lpm preal_not_0_gt_0 \<open>mp\<^sub>1 = get_mp_total \<phi>\<^sub>1\<close> get_mp_0_implies_fnm_None
      by fastforce

    have "Rep_posreal q\<^sub>a = mp (pid,vs)"
      by (metis IH.prems(2) \<open>Some (q\<^sub>a,nm'\<^sub>a) =_\<close> \<open>mp\<^sub>1 (pid, vs) \<le> mp (pid, vs)\<close> get_fnm_total.simps get_mp_total.simps mem_Collect_eq obtain_lpm_from_mp option.sel order_less_le_trans posreal_to_preal(8) prod.sel(1) q_pos)

    show "consistent_external_wrt_ploc ctxt (\<phi>\<^sub>1\<lparr> get_nm_total := nm' \<rparr>) (pid,vs) (Rep_posreal q)"
      unfolding \<open>\<phi>\<^sub>1 = _\<close> \<open>nm' = _\<close> the_eq \<open>q = _\<close> Abs_posreal_inverse[of "mp\<^sub>1 (pid,vs)", simplified, OF q_pos]
      using fraction_consistent_external(1)[OF CtxtPredSynWf extcons\<^sub>a, of "mp\<^sub>1 (pid, vs) / mp (pid, vs)", unfolded \<open>Rep_posreal q\<^sub>a = _\<close>, simplified]
      apply simp
      by (metis (mono_tags, lifting) IH.prems(2) \<open>Some (q\<^sub>a,nm'\<^sub>a) = _\<close> get_fnm_total.simps get_mp_0_implies_fnm_None get_mp_total.simps nonzero_eq_divide_eq option.discI preal_to_real(10) preal_to_real(12) preal_to_real(9) zero_preal.abs_eq)
  qed

  have \<phi>\<^sub>2_extcons: "consistent_external ctxt \<phi>\<^sub>2"
  proof
    fix pid vs q nm'
    assume lpm: "Some (q,nm') = get_fnm_total \<phi>\<^sub>2 (pid,vs)"
    have "q = Abs_posreal (mp\<^sub>2 (pid,vs))" and
         "nm' = (mp\<^sub>2 (pid,vs) / mp (pid,vs)) *\<^sub>s (snd (the (fnm (pid,vs))))"
      using lpm[unfolded \<open>\<phi>\<^sub>2 = _\<close> \<open>nm\<^sub>2 = _\<close>, simplified, simplified fnm\<^sub>2]
      by (cases "mp\<^sub>2 (pid,vs) = 0"; simp)+

    have "mp (pid,vs) \<ge> mp\<^sub>2 (pid,vs)"
      by (meson IH.hyps(2) le_funD split_implies_le(2))
    then obtain q\<^sub>a nm'\<^sub>a where "Some (q\<^sub>a,nm'\<^sub>a) = get_fnm_total \<phi> (pid,vs)"
      by (metis IH.prems(2) \<open>mp\<^sub>2 = _\<close> get_fnm_total.simps get_mp_0_implies_fnm_None get_mp_total.simps linorder_not_less lpm obtain_lpm_from_mp preal_not_0_gt_0)

    hence extcons\<^sub>a: "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm'\<^sub>a \<rparr>) (pid,vs) (Rep_posreal q\<^sub>a)"
      by (metis IH.prems(5) consistent_external.cases)

    have the_eq: "snd (the (fnm (pid,vs))) = nm'\<^sub>a"
      by (metis \<open>Some (q\<^sub>a,nm'\<^sub>a) = _\<close> fnm option.sel sndI)

    have q_pos: "mp\<^sub>2 (pid,vs) > 0"
      using lpm preal_not_0_gt_0 \<open>mp\<^sub>2 = get_mp_total \<phi>\<^sub>2\<close> get_mp_0_implies_fnm_None
      by fastforce

    have "Rep_posreal q\<^sub>a = mp (pid,vs)"
      by (metis IH.prems(2) \<open>Some (q\<^sub>a,nm'\<^sub>a) =_\<close> \<open>mp\<^sub>2 (pid, vs) \<le> mp (pid, vs)\<close> get_fnm_total.simps get_mp_total.simps mem_Collect_eq obtain_lpm_from_mp option.sel order_less_le_trans posreal_to_preal(8) prod.sel(1) q_pos)

    show "consistent_external_wrt_ploc ctxt (\<phi>\<^sub>2\<lparr> get_nm_total := nm' \<rparr>) (pid,vs) (Rep_posreal q)"
      unfolding \<open>\<phi>\<^sub>2 = _\<close> \<open>nm' = _\<close> the_eq \<open>q = _\<close> Abs_posreal_inverse[of "mp\<^sub>2 (pid,vs)", simplified, OF q_pos]
      using fraction_consistent_external(1)[OF CtxtPredSynWf extcons\<^sub>a, of "mp\<^sub>2 (pid, vs) / mp (pid, vs)", unfolded \<open>Rep_posreal q\<^sub>a = _\<close>, simplified]
      apply simp
      by (metis (mono_tags, lifting) IH.prems(2) \<open>Some (q\<^sub>a,nm'\<^sub>a) = _\<close> get_fnm_total.simps get_mp_0_implies_fnm_None get_mp_total.simps nonzero_eq_divide_eq option.discI preal_to_real(10) preal_to_real(12) preal_to_real(9) zero_preal.abs_eq)
  qed

  have "nm\<^sub>1 + nm\<^sub>2 = get_nm_total \<phi>"
    unfolding plus_nested_mask_def nm\<^sub>1_def nm\<^sub>2_def
    apply simp
    apply (rule nested_mask_equality)
    using IH.hyps(1) IH.prems(1)
     apply auto[1]
    unfolding fnm[simplified, symmetric]
    apply simp
    apply standard
    apply (rename_tac lp)
    apply (case_tac "fnm\<^sub>1 lp"; case_tac "fnm\<^sub>2 lp"; simp add: pfun_comb_def)
    subgoal for lp
      apply (subgoal_tac "mp lp = 0")
      apply (metis IH.prems(2) fnm get_fnm_total.simps get_mp_0_implies_fnm_None get_mp_total.simps)
      apply (subgoal_tac "mp\<^sub>1 lp = 0 \<and> mp\<^sub>2 lp = 0")
      using IH(2)[simplified, THEN fun_cong, of lp, simplified add_masks_def]
       apply fastforce
      using fnm\<^sub>1[of lp] fnm\<^sub>2[of lp]
      by (metis option.distinct(1))
    subgoal for lp lpm\<^sub>2
      apply (subgoal_tac "mp\<^sub>1 lp = 0 \<and> mp\<^sub>2 lp = mp lp \<and> mp\<^sub>2 lp > 0")
      using fnm\<^sub>2[of lp, simplified]
       apply (smt (verit, ccfv_SIG) IH.prems(2) PosReal.ppos.rep_eq \<open>get_fnm_nm (get_nm_total \<phi>) = fnm\<close> divide_preal.rep_eq divide_self_if get_mp_total.simps gr_0_is_ppos obtain_lpm_from_mp one_preal.rep_eq option.distinct(1) option.sel preal_semimodule_class.scale_one preal_to_real(12) prod.sel(2))
      using IH(2)[simplified, THEN fun_cong, of lp, simplified add_masks_def]
      by (metis add.commute fnm\<^sub>1 fnm\<^sub>2 option.distinct(1) padd_pnone preal_not_0_gt_0)
    subgoal for lp lpm\<^sub>1
      apply (subgoal_tac "mp\<^sub>2 lp = 0 \<and> mp\<^sub>1 lp = mp lp \<and> mp\<^sub>1 lp > 0")
      using fnm\<^sub>2[of lp, simplified]
       apply (metis IH.prems(2) \<open>get_fnm_nm (get_nm_total \<phi>) = fnm\<close> divide_preal.rep_eq divide_self_if fnm\<^sub>1 get_mp_total.simps obtain_lpm_from_mp one_preal.rep_eq option.distinct(1) option.sel preal_semimodule_class.scale_one preal_to_real(12) prod.sel(2) zero_preal.abs_eq)
      using IH(2)[simplified, THEN fun_cong, of lp, simplified add_masks_def]
      by (metis fnm\<^sub>1 fnm\<^sub>2 option.distinct(1) padd_pnone preal_not_0_gt_0)
    subgoal for lp lpm\<^sub>1 lpm\<^sub>2
    proof -
      assume "fnm\<^sub>1 lp = Some lpm\<^sub>1"
        and "fnm\<^sub>2 lp = Some lpm\<^sub>2"
      have "Rep_posreal (fst lpm\<^sub>1) = mp\<^sub>1 lp"
        using \<open>fnm\<^sub>1 lp = Some lpm\<^sub>1\<close> \<open>mp\<^sub>1 = _\<close> nm\<^sub>1_def
        unfolding \<open>\<phi>\<^sub>1 = _\<close>
        by auto
      have "Rep_posreal (fst lpm\<^sub>2) = mp\<^sub>2 lp"
        using \<open>fnm\<^sub>2 lp = Some lpm\<^sub>2\<close> \<open>mp\<^sub>2 = _\<close> nm\<^sub>2_def
        unfolding \<open>\<phi>\<^sub>2 = _\<close>
        by auto
      have "mp lp > 0"
        by (metis IH.hyps(2) \<open>fnm\<^sub>1 lp = Some lpm\<^sub>1\<close> fnm\<^sub>1 le_funD option.distinct(1) order_less_imp_not_less order_less_le preal_not_0_gt_0 split_implies_le(1))
      hence 1: "fnm lp = Some (Abs_posreal (mp lp), snd (the (fnm lp)))"
        by (metis IH.prems(2) \<open>get_fnm_nm (get_nm_total \<phi>) = fnm\<close> get_mp_total.simps obtain_lpm_from_mp option.sel split_pairs)
      have 2: "snd lpm\<^sub>1 = (mp\<^sub>1 lp / mp lp) *\<^sub>s snd (the (fnm lp))"
        by (metis \<open>fnm\<^sub>1 lp = Some lpm\<^sub>1\<close> fnm\<^sub>1 option.discI option.sel split_pairs)
      have 3: "snd lpm\<^sub>2 = (mp\<^sub>2 lp / mp lp) *\<^sub>s snd (the (fnm lp))"
        by (metis \<open>fnm\<^sub>2 lp = Some lpm\<^sub>2\<close> fnm\<^sub>2 option.discI option.sel split_pairs)
      show "Some (fst lpm\<^sub>1 + fst lpm\<^sub>2, nested_mask_merge (snd lpm\<^sub>1) (snd lpm\<^sub>2)) = fnm lp"
        apply (subst 1)
        apply standard+
         apply (rule Rep_posreal_inject[THEN iffD1])
        unfolding plus_posreal.rep_eq
         apply (metis Abs_posreal_inject IH.hyps(2) Rep_posreal Rep_posreal_inverse \<open>Rep_posreal (fst lpm\<^sub>1) = mp\<^sub>1 lp\<close> \<open>Rep_posreal (fst lpm\<^sub>2) = mp\<^sub>2 lp\<close> \<open>pos_perm_class.pnone < mp lp\<close> add_masks_def mem_Collect_eq mp_split.simps)
        unfolding plus_nested_mask_def[symmetric] 2 3
        unfolding preal_semimodule_class.scale_add_left[symmetric]
        using preal_semimodule_class.scale_one IH(2)[simplified, THEN fun_cong, of lp, simplified add_masks_def]
        by (metis PosReal.field_divide_inverse PosReal.field_inverse PosReal.pmult_comm \<open>pos_perm_class.pnone < mp lp\<close> distrib_right preal_not_0_gt_0)
    qed
    done

  define \<omega>\<^sub>A where "\<omega>\<^sub>A = add_to_nm_total_full \<omega>\<^sub>0 nm\<^sub>1"
  have 1: "add_to_nm_total_full \<omega>\<^sub>A nm\<^sub>2 = add_to_nm_total_full \<omega>\<^sub>0 (get_nm_total \<phi>)"
    apply (rule full_total_state.equality; simp_all add: IH \<omega>\<^sub>A_def)
    apply (rule total_state.equality; simp_all add: IH \<omega>\<^sub>A_def)
    using \<open>nm\<^sub>1 + nm\<^sub>2 = _\<close> ab_semigroup_add_class.add_ac(1)
    by metis

  have "add_to_nm_total_full \<omega>\<^sub>0 (get_nm_total \<phi>) \<succeq> add_to_nm_total_full \<omega>\<^sub>0 nm\<^sub>1"
    apply (simp add: greater_def)
    apply (rule exI[of _ "upd_nm_total_full \<omega>\<^sub>0 nm\<^sub>2"])
    apply (simp add: plus_full_total_state_ext_def plus_total_state_ext_def)
    apply standard+
     apply (simp add: \<open>nm\<^sub>1 + nm\<^sub>2 = get_nm_total \<phi>\<close> ab_semigroup_add_class.add_ac(1))
    by (simp add: defined_def plus_total_state_ext_def)

  hence A_mask_intcons: "StateCons (add_to_nm_total_full \<omega>\<^sub>0 nm\<^sub>1)"
    using ConsMono IH.prems(4) mono_prop_downwardD
    by auto

  have *: "add_to_nm_total \<phi>\<^sub>1 (get_nm_total_full \<omega>\<^sub>0) \<le> add_to_nm_total \<phi> (get_nm_total_full \<omega>\<^sub>0)"
    by (smt (verit) \<open>nm\<^sub>1 + nm\<^sub>2 = get_nm_total \<phi>\<close> \<phi>\<^sub>1_def add_to_nm_total.simps less_eq_total_state_ext_def nm_plus_mono nm_sum_is_bigger total_state.ext_inject total_state.surjective total_state.update_convs(2))

  have **: "add_to_nm_total \<phi>\<^sub>2 (get_nm_total_full \<omega>\<^sub>A) = add_to_nm_total \<phi> (get_nm_total_full \<omega>\<^sub>0)"
    apply (rule total_state.equality; simp)
    unfolding \<open>\<phi>\<^sub>2 = _\<close> \<open>\<omega>\<^sub>A = _\<close>
     apply simp_all
    by (metis \<open>nm\<^sub>1 + nm\<^sub>2 = get_nm_total \<phi>\<close> add.commute add.left_commute)

  have inhA: "red_inhale ctxt StateCons A \<omega>\<^sub>0 (RNormal (add_to_nm_total_full \<omega>\<^sub>0 nm\<^sub>1))"
    apply (rule extcons_state_can_be_inhaled_assertion[where hh="get_hh_total \<phi>"])
               apply fact
              apply (simp add: nm\<^sub>1_def)
             apply (simp add: \<open>mp\<^sub>1 = get_mp_total \<phi>\<^sub>1\<close> \<phi>\<^sub>1_def)
            apply (metis (full_types) \<phi>\<^sub>1_def \<phi>\<^sub>1_extcons old.unit.exhaust total_state.surjective total_state.update_convs(2))
    using IH.prems(8,9)
           apply auto[1]
    using IH.prems(9)
          apply auto[1]
         apply (simp add: IH.prems(7))
    using IH.prems(3) assertion_framing_star
        apply blast
    using IH.prems(12)
       apply force
    using IH.prems(11)
      apply auto[1]
    using A_mask_intcons
      apply auto[1]
    by fact+

  show ?case
    apply (rule SatStar)
       apply fact
      apply fact
     apply (rule IH.IH(1)[where \<phi>=\<phi>\<^sub>1 and \<omega>\<^sub>0=\<omega>\<^sub>0 and hh=hh])
                apply (simp add: \<phi>\<^sub>1_def nm\<^sub>1_def)
               apply (simp add: \<open>mp\<^sub>1 = get_mp_total \<phi>\<^sub>1\<close>)
    using IH.prems(3) assertion_framing_star
              apply blast
    using A_mask_intcons \<phi>\<^sub>1_def
             apply force
            apply fact
    using * IH.prems(6) differ_only_in_0_perm_locs_hh_smaller
           apply blast
          apply fact+
    using IH.prems(9) \<open>\<phi>\<^sub>1 = _\<close>
        apply auto[1]
    using IH.prems(10)
       apply auto[1]
    using IH.prems(11)
      apply auto[1]
    using IH.prems(12)
     apply auto[1]
    apply (rule IH.IH(2)[where \<phi>=\<phi>\<^sub>2 and \<omega>\<^sub>0=\<omega>\<^sub>A and hh=hh])
               apply (simp add: \<phi>\<^sub>2_def nm\<^sub>2_def)
              apply (simp add: \<open>mp\<^sub>2 = get_mp_total \<phi>\<^sub>2\<close>)
    using IH.prems(3) \<omega>\<^sub>A_def inhA assertion_framing_star
             apply blast
    using 1 IH.prems(4) \<phi>\<^sub>2_def
            apply force
           apply fact
    using ** IH.prems(6)
          apply presburger
    unfolding \<open>\<omega>\<^sub>A = _\<close>
         apply (simp add: IH.prems(7))
    using IH.prems(8)
        apply auto[1]
    using IH.prems(9) \<open>\<phi>\<^sub>2 = _\<close>
       apply auto[1]
    using IH.prems(10)
      apply auto[1]
    using IH.prems(11)
     apply auto[1]
    using IH.prems(12)
    apply auto[1]
    done
next
  case IH: (SatImpTrue e mh mp A)
  have "red_pure_exps_total ctxt None [e] \<omega>' (Some [VBool True])" and
       "red_pure_exps_total ctxt (Some \<omega>\<^sub>0) [e] \<omega>\<^sub>0 (Some [VBool True])"
    by (rule framed_sat_irrelevant_perm_0_locs_helper; (rule IH)?; simp add: IH.hyps(1-2) list_all2_red_pure_exps_total)+
  hence "ctxt, None \<turnstile> \<langle>e;\<omega>'\<rangle> [\<Down>]\<^sub>t Val (VBool True)" and
        "ctxt, Some \<omega>\<^sub>0 \<turnstile> \<langle>e;\<omega>\<^sub>0\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
    by (fastforce elim: red_exp_list_normal_elim)+
  show ?case
    apply (rule SatImpTrue)
     apply fact
    apply (rule IH.IH[where \<omega>\<^sub>0=\<omega>\<^sub>0])
               prefer 3
               apply (rule assertion_framing_imp[OF IH.prems(3)])
               apply fact
              apply (rule IH)+
    using IH.prems(12)
    by auto
next
  case IH: (SatImpFalse e mh mp A)
  have "red_pure_exps_total ctxt None [e] \<omega>' (Some [VBool False])"
    by (rule framed_sat_irrelevant_perm_0_locs_helper(1); (rule IH)?; simp add: IH.hyps(1-2) list_all2_red_pure_exps_total)
  hence "ctxt, None \<turnstile> \<langle>e;\<omega>'\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    by (fastforce elim: red_exp_list_normal_elim)
  show ?case
    apply (rule SatImpFalse)
    by fact+
next
  case IH: (SatCondTrue e mh mp A B)
  have "red_pure_exps_total ctxt None [e] \<omega>' (Some [VBool True])" and
       "red_pure_exps_total ctxt (Some \<omega>\<^sub>0) [e] \<omega>\<^sub>0 (Some [VBool True])"
    by (rule framed_sat_irrelevant_perm_0_locs_helper; (rule IH)?; simp add: IH.hyps(1-2) list_all2_red_pure_exps_total)+
  hence "ctxt, None \<turnstile> \<langle>e;\<omega>'\<rangle> [\<Down>]\<^sub>t Val (VBool True)" and
        "ctxt, Some \<omega>\<^sub>0 \<turnstile> \<langle>e;\<omega>\<^sub>0\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
    by (fastforce elim: red_exp_list_normal_elim)+
  show ?case
    apply (rule SatCondTrue)
     apply fact
    apply (rule IH.IH[where \<omega>\<^sub>0=\<omega>\<^sub>0])
               prefer 3
               apply (rule assertion_framing_cond_assert_true[OF IH.prems(3)])
               apply fact
              apply (rule IH)+
    using IH.prems(12)
    by auto
next
  case IH: (SatCondFalse e mh mp B A)
  have "red_pure_exps_total ctxt None [e] \<omega>' (Some [VBool False])" and
       "red_pure_exps_total ctxt (Some \<omega>\<^sub>0) [e] \<omega>\<^sub>0 (Some [VBool False])"
    by (rule framed_sat_irrelevant_perm_0_locs_helper; (rule IH)?; simp add: IH.hyps(1-2) list_all2_red_pure_exps_total)+
  hence "ctxt, None \<turnstile> \<langle>e;\<omega>'\<rangle> [\<Down>]\<^sub>t Val (VBool False)" and
        "ctxt, Some \<omega>\<^sub>0 \<turnstile> \<langle>e;\<omega>\<^sub>0\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    by (fastforce elim: red_exp_list_normal_elim)+
  show ?case
    apply (rule SatCondFalse)
     apply fact
    apply (rule IH.IH[where \<omega>\<^sub>0=\<omega>\<^sub>0])
               prefer 3
               apply (rule assertion_framing_cond_assert_false[OF IH.prems(3)])
               apply fact
              apply (rule IH)+
    using IH.prems(12)
    by auto
qed


lemma ctxt_pred_self_framing_inh_implies_extcons_irrelevant_perm_0_locs:
  assumes SFinh: "ctxt_pred_self_framing_inh ctxt StateCons"
      and ConsMonoSub: "mono_prop_downward_sub_mask_total StateCons_t"
      and ConsMono: "mono_prop_downward StateCons"
      and ConsCons_t: "\<forall>\<omega>. StateCons \<omega> \<longleftrightarrow> (StateCons_t (get_total_full \<omega>) \<and> (\<forall>lbl \<phi>. get_trace_total \<omega> lbl = Some \<phi> \<longrightarrow> StateCons_t \<phi>))"
      and CtxtSynWf: "ctxt_pred_syn_wf ctxt"
      and "StateCons_t \<phi>"
      and "differ_only_in_0_perm_locs \<phi> \<phi>'"
    shows "consistent_external_wrt_ploc ctxt \<phi> (pid,vs) p \<Longrightarrow>
           consistent_external_wrt_ploc ctxt \<phi>' (pid,vs) p"
      and "consistent_external ctxt \<phi> \<Longrightarrow>
           consistent_external ctxt \<phi>'"
  using assms(6-)
proof (induction arbitrary: \<phi>' and \<phi>' rule: consistent_external_wrt_ploc_consistent_external.inducts)
  case IH: (SatStep pid pdecl vs pbody p \<phi>)
  note diff_only_0_locs = IH.prems(2)[unfolded differ_only_in_0_perm_locs_def]
  define \<omega>\<^sub>b where "\<omega>\<^sub>b = \<lparr> get_store_total = Map.empty, get_trace_total = Map.empty, get_total_full = \<phi>\<lparr> get_nm_total := 0 \<rparr> \<rparr>"
  define \<omega>\<^sub>0 where "\<omega>\<^sub>0 = update_store_total \<omega>\<^sub>b (nth_option vs)"
  show ?case
    apply (rule SatStep)
         apply fact+
    using diff_only_0_locs IH.hyps(2)
      apply argo
     apply (rule framed_sat_irrelevant_perm_0_locs[where \<omega>\<^sub>0=\<omega>\<^sub>0 and \<phi>=\<phi> and hh="get_hh_total \<phi>'"])
    using diff_only_0_locs IH.IH(3)
                   apply simp
                  apply (simp add: diff_only_0_locs)
                 apply (simp add: diff_only_0_locs)
    unfolding \<open>\<omega>\<^sub>0 = _\<close>
    using SFinh[unfolded ctxt_pred_self_framing_inh_def
                assertion_self_framing_def
                assertion_self_framing_store_def,
                THEN spec[of _ pid], THEN spec[of _ pdecl], THEN spec[of _ pbody],
                THEN mp, THEN mp, THEN spec[of _ vs], THEN spec[of _ "Rep_preal p"],
                THEN mp, THEN spec[of _ \<omega>\<^sub>b]] IH
                apply blast
    unfolding \<open>\<omega>\<^sub>b = _\<close>
               apply simp
               apply (simp add: ConsCons_t IH.prems(1))
              apply (simp add: IH.IH(4))
             apply simp
    using diff_only_0_locs differ_only_in_0_perm_locs_hh_def
             apply blast
            apply simp
           apply simp
          apply simp
         apply simp
        apply simp
    using CtxtSynWf IH(1) IH(6) ctxt_pred_syn_wf_def prat_non_negative syntactic_mult_supported
       apply blast
      apply (rule CtxtSynWf)
     apply (rule ConsMono)
    by (simp add: IH.IH(5) IH.prems(1,2))

next
  case IH: (SatAll \<phi>)
  note diff_only_0_locs = IH.prems(2)[unfolded differ_only_in_0_perm_locs_def]
  show ?case
    apply (rule SatAll)
    apply (rule IH(2))
    using diff_only_0_locs
      apply simp
    using ConsMonoSub[unfolded mono_prop_downward_sub_mask_total_def] IH.prems(1) diff_only_0_locs
     apply simp
    by (simp add: IH.prems(2) diff_only_0_locs differ_only_in_0_perm_locs_submask)
qed


\<^cancel>\<open>
lemma inhale_perm_0_locs_irrelevant:
  assumes "red_inhale ctxt StateCons A \<omega>\<^sub>0 (RNormal \<omega>\<^sub>i)"
      and "get_store_total \<omega>\<^sub>0 = get_store_total \<omega>\<^sub>0'"
      and "get_trace_total \<omega>\<^sub>0 = get_trace_total \<omega>\<^sub>0'"
      and "get_nm_total_full \<omega>\<^sub>0 = get_nm_total_full \<omega>\<^sub>0'"
      and "get_store_total \<omega>\<^sub>i = get_store_total \<omega>\<^sub>i'"
      and "get_trace_total \<omega>\<^sub>i = get_trace_total \<omega>\<^sub>i'"
      and "differ_only_in_0_perm_locs (get_total_full \<omega>\<^sub>i) (get_total_full \<omega>\<^sub>i')"
      and "get_hh_total_full \<omega>\<^sub>0' = get_hh_total_full \<omega>\<^sub>i'"
      and ConsHeapIrrelevant:
            "\<And>\<omega> \<omega>'. get_trace_total \<omega> = get_trace_total \<omega>' \<Longrightarrow>
                     get_nm_total_full \<omega> = get_nm_total_full \<omega>' \<Longrightarrow>
                     StateCons \<omega> \<Longrightarrow> StateCons \<omega>'"
    shows "red_inhale ctxt StateCons A \<omega>\<^sub>0' (RNormal \<omega>\<^sub>i')"
  using assms(1-8)
proof (induction A arbitrary: \<omega>\<^sub>0 \<omega>\<^sub>i \<omega>\<^sub>0' \<omega>\<^sub>i')
  case (Atomic atm)
  show ?case
  proof (cases atm)
    case (Pure e)
    have "ctxt, Some \<omega>\<^sub>0 \<turnstile> \<langle>e;\<omega>\<^sub>0\<rangle> [\<Down>]\<^sub>t Val (VBool True)" and "\<omega>\<^sub>0 = \<omega>\<^sub>i"
      using Atomic(1)[unfolded Pure]
      by (metis InhPure_case result_total.distinct(3) result_total.distinct(5) result_total.inject)+
    hence "ctxt, Some \<omega>\<^sub>0' \<turnstile> \<langle>e;\<omega>\<^sub>0'\<rangle> [\<Down>]\<^sub>t Val (VBool True)"
      using eval_perm_0_locs_irrelevant(1)[of \<omega>\<^sub>0 \<omega>\<^sub>0' \<omega>\<^sub>0 \<omega>\<^sub>0']
      by (metis Atomic.prems(1-4,7,8) differ_only_in_0_perm_locs_smaller extended_val.simps(3) inhale_mono)
    moreover have "\<omega>\<^sub>0' = \<omega>\<^sub>i'"
      by (metis (mono_tags) Atomic.prems(2-8) \<open>\<omega>\<^sub>0 = \<omega>\<^sub>i\<close> differ_only_in_0_perm_locs_def full_total_state.surjective get_hh_total_full.simps get_nm_total_full.elims old.unit.exhaust total_state.surjective)
    ultimately show ?thesis
      unfolding Pure
      using red_inhale.InhPure
      by fastforce
  next
    case (Acc e_r f perm)
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      from Atomic(1)[unfolded Acc PureExp] obtain r p W where
        eval_r: "ctxt, Some \<omega>\<^sub>0 \<turnstile> \<langle>e_r;\<omega>\<^sub>0\<rangle> [\<Down>]\<^sub>t Val (VRef r)" and
        eval_p: "ctxt, Some \<omega>\<^sub>0 \<turnstile> \<langle>e_p;\<omega>\<^sub>0\<rangle> [\<Down>]\<^sub>t Val (VPerm p)" and
        "W = (if r = Null then {\<omega>\<^sub>0} else inhale_perm_single StateCons \<omega>\<^sub>0 (the_address r,f) (Some (Abs_preal p)))" and
        res: "th_result_rel (p \<ge> 0) (W \<noteq> {} \<and> (p > 0 \<longrightarrow> r \<noteq> Null)) W (RNormal \<omega>\<^sub>i)"
        by (auto elim: InhAcc_case)
      have "ctxt, Some \<omega>\<^sub>0' \<turnstile> \<langle>e_r;\<omega>\<^sub>0'\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
        apply (rule eval_perm_0_locs_irrelevant(1)[of \<omega>\<^sub>0 \<omega>\<^sub>0', OF _ _ _ _ _ _ _ _ _ _ eval_r])
        using Atomic
                  apply auto
        by (metis Atomic.prems(4,8) differ_only_in_0_perm_locs_smaller inhale_mono inhale_only_changes_mask)
      have "ctxt, Some \<omega>\<^sub>0' \<turnstile> \<langle>e_p;\<omega>\<^sub>0'\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
        apply (rule eval_perm_0_locs_irrelevant(1)[of \<omega>\<^sub>0 \<omega>\<^sub>0', OF _ _ _ _ _ _ _ _ _ _ eval_p])
        using Atomic
                  apply auto
        by (metis Atomic.prems(4,8) differ_only_in_0_perm_locs_smaller inhale_mono inhale_only_changes_mask)

      define W' where "W' = (if r = Null then {\<omega>\<^sub>0'} else inhale_perm_single StateCons \<omega>\<^sub>0' (the_address r,f) (Some (Abs_preal p)))"
      have "\<omega>\<^sub>i' \<in> W'"
        unfolding \<open>W' = _\<close>
      proof (auto split: if_split)
        assume "r = Null"
        hence "\<omega>\<^sub>i = \<omega>\<^sub>0"
          using \<open>W = _\<close> res th_result_rel_normal
          by auto
        thus "\<omega>\<^sub>i' = \<omega>\<^sub>0'"
          by (metis (mono_tags) Atomic.prems(2-8) differ_only_in_0_perm_locs_def full_total_state.equality get_hh_total_full.simps get_nm_total_full.simps old.unit.exhaust total_state.surjective)
      next
        assume "r \<noteq> Null"
        hence "\<omega>\<^sub>i \<in> inhale_perm_single StateCons \<omega>\<^sub>0 (the_address r, f) (Some (Abs_preal p))"
          using \<open>W = _\<close> res th_result_rel_normal
          by auto
        hence "\<omega>\<^sub>i = upd_mh_loc_total_full \<omega>\<^sub>0 (the_address r, f) (get_mh_total_full \<omega>\<^sub>0 (the_address r, f) + Abs_preal p)"
          unfolding inhale_perm_single_def
          by fastforce
        show "\<omega>\<^sub>i' \<in> inhale_perm_single StateCons \<omega>\<^sub>0' (the_address r, f) (Some (Abs_preal p))"
          unfolding inhale_perm_single_def
          apply (rule CollectI)
          apply (rule exI[of _ \<omega>\<^sub>i'])
          apply (rule exI[of _ "Abs_preal p"])
          apply (intro conjI)
             apply simp
            apply simp
           apply (rule full_total_state.equality)
              prefer 4
          using inhale_only_changes_mask[OF Atomic(1)] Atomic
              apply (simp, simp, simp)
           apply (rule total_state.equality)
             prefer 3
          using inhale_only_changes_mask[OF Atomic(1)] Atomic
             apply (simp, simp)
          using \<open>\<omega>\<^sub>i = _\<close> Atomic
           apply (simp add: differ_only_in_0_perm_locs_def)
          apply (rule ConsHeapIrrelevant[of \<omega>\<^sub>i])
          using Atomic Atomic(7)[unfolded differ_only_in_0_perm_locs_def] \<open>\<omega>\<^sub>i \<in> _\<close>[unfolded inhale_perm_single_def]
          by auto
      qed

      show ?thesis
        unfolding Acc PureExp
        apply (rule InhAcc)
           apply fact+
        by (metis (full_types) THResultNormal_alt \<open>\<omega>\<^sub>i' \<in> W'\<close> res all_not_in_conv th_result_rel_normal)
    next
      case Wildcard
      from Atomic(1)[unfolded Acc Wildcard] obtain r W where
        eval_r: "ctxt, Some \<omega>\<^sub>0 \<turnstile> \<langle>e_r;\<omega>\<^sub>0\<rangle> [\<Down>]\<^sub>t Val (VRef r)" and
        "W = inhale_perm_single StateCons \<omega>\<^sub>0 (the_address r,f) None" and
        res: "th_result_rel True (W \<noteq> {} \<and> r \<noteq> Null) W (RNormal \<omega>\<^sub>i)"
        by (auto elim: InhAccWildcard_case)
      have "ctxt, Some \<omega>\<^sub>0' \<turnstile> \<langle>e_r;\<omega>\<^sub>0'\<rangle> [\<Down>]\<^sub>t Val (VRef r)"
        apply (rule eval_perm_0_locs_irrelevant(1)[of \<omega>\<^sub>0 \<omega>\<^sub>0', OF _ _ _ _ _ _ _ _ _ _ eval_r])
        using Atomic
                  apply auto
        by (metis Atomic.prems(4,8) differ_only_in_0_perm_locs_smaller inhale_mono inhale_only_changes_mask)

      define W' where "W' = inhale_perm_single StateCons \<omega>\<^sub>0' (the_address r,f) None"
      have "\<omega>\<^sub>i' \<in> W'"
        unfolding \<open>W' = _\<close>
      proof -
        have "\<omega>\<^sub>i \<in> inhale_perm_single StateCons \<omega>\<^sub>0 (the_address r, f) None"
          using \<open>W = _\<close> res th_result_rel_normal
          by auto
        then obtain q where
          "option_fold ((=) q) (q \<noteq> 0) None" and
          "\<omega>\<^sub>i = upd_mh_loc_total_full \<omega>\<^sub>0 (the_address r, f) (get_mh_total_full \<omega>\<^sub>0 (the_address r, f) + q)" and
          "StateCons \<omega>\<^sub>i"
          using inhale_perm_single_def
          by blast
        show "\<omega>\<^sub>i' \<in> inhale_perm_single StateCons \<omega>\<^sub>0' (the_address r, f) None"
          unfolding inhale_perm_single_def
          apply (rule CollectI)
          apply (rule exI[of _ \<omega>\<^sub>i'])
          apply (rule exI[of _ q])
          apply (intro conjI)
             apply simp
            apply fact
           apply (rule full_total_state.equality)
              prefer 4
          using inhale_only_changes_mask[OF Atomic(1)] Atomic
              apply (simp, simp, simp)
           apply (rule total_state.equality)
             prefer 3
          using inhale_only_changes_mask[OF Atomic(1)] Atomic
             apply (simp, simp)
          using \<open>\<omega>\<^sub>i = _\<close> Atomic
           apply (simp add: differ_only_in_0_perm_locs_def)
          apply (rule ConsHeapIrrelevant[of \<omega>\<^sub>i])
          using Atomic Atomic(7)[unfolded differ_only_in_0_perm_locs_def] \<open>\<omega>\<^sub>i \<in> _\<close>[unfolded inhale_perm_single_def]
          by auto
      qed

      show ?thesis
        unfolding Acc Wildcard
        apply (rule InhAccWildcard)
          apply fact+
        by (metis (mono_tags, opaque_lifting) THResultNormal_alt \<open>\<omega>\<^sub>i' \<in> W'\<close> emptyE res th_result_rel_normal)
    qed
  next
    case (AccPredicate pid e_args perm)
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      from Atomic(1)[unfolded AccPredicate PureExp] obtain vs p W where
        eval_vs: "red_pure_exps_total ctxt (Some \<omega>\<^sub>0) e_args \<omega>\<^sub>0 (Some vs)" and
        eval_p: "ctxt, Some \<omega>\<^sub>0 \<turnstile> \<langle>e_p;\<omega>\<^sub>0\<rangle> [\<Down>]\<^sub>t Val (VPerm p)" and
        "W = inhale_perm_single_pred ctxt StateCons \<omega>\<^sub>0 (pid,vs) (Some (Abs_preal p))" and
        res: "th_result_rel (p \<ge> 0) (W \<noteq> {}) W (RNormal \<omega>\<^sub>i)"
        by (auto elim: InhAccPredPerm_case)
      have "red_pure_exps_total ctxt (Some \<omega>\<^sub>0') e_args \<omega>\<^sub>0' (Some vs)"
        apply (rule eval_perm_0_locs_irrelevant(2)[of \<omega>\<^sub>0 \<omega>\<^sub>0', OF _ _ _ _ _ _ _ _ _ _ eval_vs])
        using Atomic
                  apply auto
        by (metis Atomic.prems(4,8) differ_only_in_0_perm_locs_smaller inhale_mono inhale_only_changes_mask)
      have "ctxt, Some \<omega>\<^sub>0' \<turnstile> \<langle>e_p;\<omega>\<^sub>0'\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
        apply (rule eval_perm_0_locs_irrelevant(1)[of \<omega>\<^sub>0 \<omega>\<^sub>0', OF _ _ _ _ _ _ _ _ _ _ eval_p])
        using Atomic
                  apply auto
        by (metis Atomic.prems(4,8) differ_only_in_0_perm_locs_smaller inhale_mono inhale_only_changes_mask)

      define W' where "W' = inhale_perm_single_pred ctxt StateCons \<omega>\<^sub>0' (pid,vs) (Some (Abs_preal p))"
      have "\<omega>\<^sub>i' \<in> W'"
        unfolding \<open>W' = _\<close>
      proof -
        have "\<omega>\<^sub>i \<in> inhale_perm_single_pred ctxt StateCons \<omega>\<^sub>0 (pid,vs) (Some (Abs_preal p))"
          using \<open>W = _\<close> res th_result_rel_normal
          by auto
        then obtain q \<phi>_inh where
          "option_fold ((=) q) (q \<noteq> 0) (Some (Abs_preal p))" and
          "consistent_external_wrt_ploc ctxt \<phi>_inh (pid,vs) q" and
          \<phi>_inh_hh: "get_hh_total \<phi>_inh = get_hh_total_full \<omega>\<^sub>0" and
          "\<omega>\<^sub>i = (if q = 0 then \<omega>\<^sub>0 else add_to_lpm_nonzero_total_full \<omega>\<^sub>0 (pid,vs) (Abs_posreal q) (get_nm_total \<phi>_inh))"
          "StateCons \<omega>\<^sub>i"
          using inhale_perm_single_pred_def
          by blast
        show "\<omega>\<^sub>i' \<in> inhale_perm_single_pred ctxt StateCons \<omega>\<^sub>0' (pid,vs) (Some (Abs_preal p))"
          unfolding inhale_perm_single_pred_def
          apply (rule CollectI)
          apply (rule exI[of _ \<omega>\<^sub>i'])
          apply (rule exI[of _ "\<phi>_inh\<lparr> get_hh_total := get_hh_total_full \<omega>\<^sub>0' \<rparr>"])
          apply (rule exI[of _ q])
          apply (intro conjI)
               apply simp
              apply fact
            (* unprovable *)
          done
      qed

      show ?thesis
        unfolding AccPredicate PureExp
        apply (rule InhAccPred)
          apply fact+
        by (metis (mono_tags, opaque_lifting) THResultNormal_alt \<open>\<omega>\<^sub>i' \<in> W'\<close> emptyE res th_result_rel_normal)
    next
      case Wildcard
      then show ?thesis done
    qed
  qed

next
  case IH: (Imp e A)

  have "\<omega>\<^sub>0 \<le> \<omega>\<^sub>i"
    using IH.prems(1) inhale_mono
    by blast
  hence diff_only_0_locs: "differ_only_in_0_perm_locs (get_total_full \<omega>\<^sub>0) (get_total_full \<omega>\<^sub>0')"
    using IH.prems(4,7,8) differ_only_in_0_perm_locs_smaller less_eq_full_total_stateD_2
    by blast

  from IH consider (True) "ctxt, Some \<omega>\<^sub>0 \<turnstile> \<langle>e;\<omega>\<^sub>0\<rangle> [\<Down>]\<^sub>t Val (VBool True)" |
                  (False) "ctxt, Some \<omega>\<^sub>0 \<turnstile> \<langle>e;\<omega>\<^sub>0\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    by (auto elim: InhImp_case)
  then show ?case
  proof cases
    case True
    hence *: "red_inhale ctxt StateCons A \<omega>\<^sub>0 (RNormal \<omega>\<^sub>i)"
      by (metis IH.prems(1) InhImp_case ValueAndBasicState.val.inject(2) eval_is_deterministic_single extended_val.inject result_total.distinct(5))
    show ?thesis
      apply (rule InhImpTrue)
       apply (metis IH.prems(2-4) True diff_only_0_locs eval_perm_0_locs_irrelevant(1) extended_val.distinct(1))
      apply (rule IH(1))
             apply (rule *)
      using IH
      by auto
  next
    case False
    hence "\<omega>\<^sub>i = \<omega>\<^sub>0"
      by (metis (full_types) IH.prems(1) InhImp_case ValueAndBasicState.val.inject(2) eval_is_deterministic_single extended_val.inject result_total.distinct(5) result_total.inject)
    show ?thesis
      apply (rule InhImpFalse)
       apply (metis False IH.prems(2-4) diff_only_0_locs eval_perm_0_locs_irrelevant(1) extended_val.distinct(1))
      using IH \<open>\<omega>\<^sub>i = \<omega>\<^sub>0\<close>
      by (simp add: differ_only_in_0_perm_locs_def)
  qed

next
  case IH: (CondAssert e A B)

  have "\<omega>\<^sub>0 \<le> \<omega>\<^sub>i"
    using IH.prems(1) inhale_mono
    by blast
  hence diff_only_0_locs: "differ_only_in_0_perm_locs (get_total_full \<omega>\<^sub>0) (get_total_full \<omega>\<^sub>0')"
    using IH.prems(4,7,8) differ_only_in_0_perm_locs_smaller less_eq_full_total_stateD_2
    by blast

  from IH consider (True) "ctxt, Some \<omega>\<^sub>0 \<turnstile> \<langle>e;\<omega>\<^sub>0\<rangle> [\<Down>]\<^sub>t Val (VBool True)" |
                  (False) "ctxt, Some \<omega>\<^sub>0 \<turnstile> \<langle>e;\<omega>\<^sub>0\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    by (auto elim: red_inhale.cases)
  then show ?case
  proof cases
    case True
    hence *: "red_inhale ctxt StateCons A \<omega>\<^sub>0 (RNormal \<omega>\<^sub>i)"
      by (metis IH.prems(1) InhCondAssert ValueAndBasicState.val.inject(2) eval_is_deterministic_single extended_val.inject result_total.simps(7))
    show ?thesis
      apply (rule InhCondAssertTrue)
       apply (metis IH.prems(2-4) True diff_only_0_locs eval_perm_0_locs_irrelevant(1) extended_val.distinct(1))
      apply (rule IH(1))
             apply (rule *)
      using IH
      by auto
  next
    case False
    hence *: "red_inhale ctxt StateCons B \<omega>\<^sub>0 (RNormal \<omega>\<^sub>i)"
      by (metis IH.prems(1) InhCondAssert ValueAndBasicState.val.inject(2) eval_is_deterministic_single extended_val.inject result_total.simps(7))
    show ?thesis
      apply (rule InhCondAssertFalse)
       apply (metis IH.prems(2-4) False diff_only_0_locs eval_perm_0_locs_irrelevant(1) extended_val.distinct(1))
      apply (rule IH(2))
             apply (rule *)
      using IH
      by auto
  qed

next
  case IH: (Star A B)
  then obtain \<omega>'' where
    inhA: "red_inhale ctxt StateCons A \<omega>\<^sub>0 (RNormal \<omega>'')" and
    inhB: "red_inhale ctxt StateCons B \<omega>'' (RNormal \<omega>\<^sub>i)"
    by (blast elim: InhStar_case)
  define \<omega>''' where "\<omega>''' = upd_hh_total_full \<omega>'' (get_hh_total_full \<omega>\<^sub>0')"
  hence "\<omega>'' \<le> \<omega>\<^sub>i"
    using inhB
    by (simp add: inhale_mono)
  have "differ_only_in_0_perm_locs (get_total_full \<omega>'') (get_total_full \<omega>''')"
    apply (rule differ_only_in_0_perm_locs_smaller[OF IH(9)])
    unfolding \<open>\<omega>''' = _\<close>
       apply simp
    using \<open>\<omega>'' \<le> \<omega>\<^sub>i\<close> less_eq_full_total_stateD_2
      apply blast
     apply simp
    using IH.prems(8)
     apply auto[1]
    by fact

  show ?case
    apply (rule InhStarNormal)
     apply (rule IH(1)[OF inhA, of \<omega>\<^sub>0' "\<omega>'''"])
           apply (simp add: IH.prems(2))
          apply (simp add: IH.prems(3))
    using IH.prems(4)
         apply auto[1]
        apply (simp add: \<open>\<omega>''' = _\<close>)
       apply (simp add: \<open>\<omega>''' = _\<close>)
      apply fact
     apply (simp add: \<open>\<omega>''' = _\<close>)
    apply (rule IH(2)[OF inhB])
          apply (simp add: \<open>\<omega>''' = _\<close>)
         apply (simp add: \<open>\<omega>''' = _\<close>)
        apply (simp add: \<open>\<omega>''' = _\<close>)
       apply fact
      apply fact
     apply fact
    unfolding \<open>\<omega>''' = _\<close>
    apply simp
    using IH.prems(8)
    by auto
qed (auto elim: red_inhale.cases)
\<close>


\<comment> \<open>Unused\<close>
lemma inhale_sat:
  assumes "red_inhale ctxt StateCons A \<omega> (RNormal \<omega>')"
      and "(\<lambda>l. get_mh_total_full \<omega> l + mh l) = get_mh_total_full \<omega>'"
      and "(\<lambda>l. get_mp_total_full \<omega> l + mp l) = get_mp_total_full \<omega>'"
    shows "sat ctxt \<omega> mh mp A"
  oops


lemma ctxt_pred_self_framing_inh_implies_sat:
  assumes CtxtPredSynWf: "ctxt_pred_syn_wf ctxt"
      and ConsMonoSub: "mono_prop_downward_sub_mask_total StateCons_t"
      and MonoCons: "mono_prop_downward StateCons"
      and ConsCons_t: "\<forall>\<omega>. StateCons \<omega> \<longleftrightarrow> (StateCons_t (get_total_full \<omega>) \<and> (\<forall>lbl \<phi>. get_trace_total \<omega> lbl = Some \<phi> \<longrightarrow> StateCons_t \<phi>))"
      and CtxtPredSFinh: "ctxt_pred_self_framing_inh ctxt StateCons"
    shows "ctxt_pred_self_framing_sat ctxt StateCons_t"
  unfolding ctxt_pred_self_framing_sat_def pred_self_framing_def
  using ConsCons_t ConsMonoSub CtxtPredSFinh CtxtPredSynWf MonoCons ctxt_pred_self_framing_inh_implies_extcons_irrelevant_perm_0_locs(1)
  by blast



end
