section \<open>Key Properties of THSem\<close>

theory TotalSemanticsProperties
  imports TotalSemProperties TotalExtConsProps
begin


subsection \<open>Predicate Body Manipulation\<close>

lemma syntactic_mult_supported:
  assumes "supported_pred_body A"
    shows "supported_pred_body (syntactic_mult p A)"
  sorry


subsection \<open>Expression Evaluation Properties\<close>

lemma eval_with_None:
  assumes "ctxt, Some \<omega>\<^sub>0 \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"
    shows "ctxt, None \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"
  sorry

lemma eval_with_no_nm:
  assumes "ctxt, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"
      and "no_perm_pure_exp e"
    shows "ctxt, \<omega>_def \<turnstile> \<langle>e; upd_nm_total_full \<omega> empty_nm\<rangle> [\<Down>]\<^sub>t Val v"
  sorry

lemma eval_with_no_trace:
  assumes "ctxt, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"
      and "no_old_pure_exp e"
    shows "ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<lparr> get_trace_total := Map.empty \<rparr>\<rangle> [\<Down>]\<^sub>t Val v"
  sorry

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
          using shift_up_exists[of "get_mp_total_full \<omega>\<^sub>0\<^sub>2 (pred_id, vs) / Abs_preal 2" "get_nm_total_full \<omega>\<^sub>0\<^sub>2" pred_id vs, simplified,
                OF 1[of "get_mp_total_full \<omega>\<^sub>0\<^sub>2 (pred_id, vs)", simplified] 2[OF False[simplified]]]
                \<open>vs\<^sub>2 = vs\<close>
          by blast
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
          using shift_up_exists[of "get_mp_total_full \<omega>\<^sub>0\<^sub>2 (pred_id, vs) / Abs_preal 2" "get_nm_total_full \<omega>\<^sub>0\<^sub>2" pred_id vs, simplified,
                OF 1[of "get_mp_total_full \<omega>\<^sub>0\<^sub>2 (pred_id, vs)", simplified] 2[OF False[simplified]]]
                \<open>vs\<^sub>2 = vs\<close>
          by blast
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


subsection \<open>Exhale Properties\<close>

lemma exhale_fraction:
  assumes "red_exhale ctxt R \<omega>\<^sub>0 A \<omega> (RNormal \<omega>')"
  shows "get_nm_loc_total_full \<omega>' ploc =
         nested_mask_multiply_option (get_nm_loc_total_full \<omega> ploc)
                                     (get_mp_total_full \<omega>' ploc / get_mp_total_full \<omega> ploc)"
  sorry


\<comment> \<open>Helper lemmas\<close>

lemma eval_exhale_sat_helper:
  assumes "ctxt, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"
      and "no_perm_pure_exp e"
      and "no_old_pure_exp e"
    shows "ctxt, None \<turnstile> \<langle>e; \<lparr> get_store_total = get_store_total \<omega>,
                              get_trace_total = \<lambda>x. None,
                              get_total_full = get_total_full \<omega>\<lparr> get_nm_total := empty_nm \<rparr> \<rparr>\<rangle>
           [\<Down>]\<^sub>t Val v"
  sorry

lemma eval_multi_exhale_sat_helper:
  assumes "red_pure_exps_total ctxt \<omega>_def es \<omega> (Some vs)"
  shows "red_pure_exps_total ctxt None es
           \<lparr> get_store_total = get_store_total \<omega>,
             get_trace_total = \<lambda>x. None,
             get_total_full = get_total_full \<omega>\<lparr> get_nm_total := empty_nm \<rparr> \<rparr>
         (Some vs)"
  sorry

lemma exhale_mh_diff:
  shows "field_mask_sub (get_mh_total_full \<omega>)
                        (get_mh_total_full (exhale_pred \<omega> ploc p)) =
         zero_mh"
  apply (simp add: exhale_pred_def Let_def)
  using same_mh_diff
  by auto

lemma exhale_mp_diff:
  assumes "p \<le> get_mp_total_full \<omega> ploc"
  shows "predicate_mask_sub (get_mp_total_full \<omega>)
                            (get_mp_total_full (exhale_pred \<omega> ploc p)) =
         singleton_mp ploc p"
proof -
  have 1: "get_mp_total_full (exhale_pred \<omega> ploc p) = get_mp_total_full (upd_mp_loc_total_full \<omega> ploc (get_mp_total_full \<omega> ploc - p))"
    by (metis exhale_pred_def mult_nm_loc_total_full_mp_eq)
  have 2: "get_mp_total_full \<omega> ploc - (get_mp_total_full \<omega> ploc - p) = p"
    using assms minus_preal_gte by auto
  show ?thesis
    apply (simp add: 1 exhale_pred_def Let_def)
    using 2 minus_preal.abs_eq zero_preal.abs_eq
    by fastforce
qed

\<comment> \<open>already proved elsewhere, but need adjustment\<close>
lemma exhale_smaller:
  assumes "red_exhale ctxt R \<omega>_def A \<omega> (RNormal \<omega>')"
    shows "\<And>x. get_mh_total_full \<omega> x \<ge> get_mh_total_full \<omega>' x"
      and "\<And>x. get_mp_total_full \<omega> x \<ge> get_mp_total_full \<omega>' x"
  sorry

lemma mh_sub_twice:
  assumes "\<And>x. mh0 x \<ge> mh1 x"
      and "\<And>x. mh1 x \<ge> mh2 x"
    shows "mh_split (field_mask_sub mh0 mh2)
                    (field_mask_sub mh0 mh1)
                    (field_mask_sub mh1 mh2)"
  apply simp
  apply standard
  apply (simp add: add_masks_def preal_to_real)
  using assms less_eq_preal.rep_eq
  by auto

lemma mp_sub_twice:
  assumes "\<And>x. mp0 x \<ge> mp1 x"
      and "\<And>x. mp1 x \<ge> mp2 x"
    shows "mp_split (predicate_mask_sub mp0 mp2)
                    (predicate_mask_sub mp0 mp1)
                    (predicate_mask_sub mp1 mp2)"
  apply simp
  apply standard
  apply (simp add: add_masks_def preal_to_real)
  using assms less_eq_preal.rep_eq
  by auto


\<comment> \<open>Relation between exhale and sat\<close>

lemma exhale_diff_sat:
  assumes "consistent_external ctxt (get_total_full \<omega>)"
      and "red_exhale ctxt R \<omega>\<^sub>0 A \<omega> res" and "res = RNormal \<omega>'"
      and "supported_pred_body A"
    shows "sat ctxt (\<lparr> get_store_total = get_store_total \<omega>,
                       get_trace_total = Map.empty,
                       get_total_full = get_total_full \<omega>\<lparr> get_nm_total := empty_nm \<rparr> \<rparr>)
               (field_mask_sub (get_mh_total_full \<omega>) (get_mh_total_full \<omega>'))
               (predicate_mask_sub (get_mp_total_full \<omega>) (get_mp_total_full \<omega>'))
               A"
  using assms(2,3,4)
proof (induction arbitrary: \<omega>')
  case IH: (ExhAcc mh \<omega> e_r r e_p p a f)
  have 1: "0 \<le> p \<and> (if r = Null then p = 0 else Abs_preal p \<le> mh (a, f))"
   and \<omega>': "\<omega>' = (if r = Null then \<omega> else upd_mh_loc_total_full \<omega> (a, f) (mh (a, f) - Abs_preal p))"
    using exh_if_total_normal[OF IH(5)] exh_if_total_normal_2[OF IH(5)]
    by blast+
  show ?case
    apply standard
    using IH eval_exhale_sat_helper
         apply fastforce+
    using 1
      apply blast
     apply (cases r)
      apply (simp add: If_def \<omega>')
    using "1" IH.hyps(1) IH.hyps(4) mh_upd_loc_diff minus_preal_gte psub_smaller
      apply auto[1]
    using "1" \<omega>' same_mh_diff
     apply force
    by (metis IH.hyps(1) \<omega>' dec_mh_mp_diff same_mp_diff)
next
  case IH: (ExhAccWildcard mh \<omega> e_r r a f q)
  have 1: "mh (a,f) \<noteq> 0 \<and> r \<noteq> Null"
   and \<omega>': "\<omega>' = upd_mh_loc_total_full \<omega> (a, f) (mh (a,f) - q)"
    using IH.prems(1) exh_if_total_normal exh_if_total_normal_2
    by blast+
  show ?case
    apply standard
    using IH(2,5,6) eval_exhale_sat_helper
        apply fastforce+
    using IH(1,4) dec_mh_mh_diff 1 IH.hyps(3) \<omega>' is_singleton_mh.simps
     apply blast
    using \<omega>' IH.hyps(1) dec_mh_mp_diff
    by blast
next
  case IH: (ExhAccPred mp \<omega> e_args v_args e_p p pred_id)
  have 1: "0 \<le> p \<and> Abs_preal p \<le> mp (pred_id, v_args)"
   and \<omega>': "\<omega>' = exhale_pred \<omega> (pred_id, v_args) (Abs_preal p)"
    using IH.prems(1) exh_if_total_normal exh_if_total_normal_2
    by blast+
  show ?case
    apply standard
    using eval_multi_exhale_sat_helper[OF IH(2)]
        apply blast
    using IH(5) eval_exhale_sat_helper[OF IH(3)]
       apply simp
      apply (simp add: 1)
    using IH.hyps(1) \<omega>' exhale_mh_diff
     apply blast
    using IH.hyps(1) \<omega>' exhale_mp_diff 1
    by blast
next
  case IH: (ExhAccPredWildcard mp \<omega> e_args v_args pred_id q)
  have 1: "mp (pred_id, v_args) \<noteq> 0"
   and 2: "q > 0 \<and> mp (pred_id, v_args) > q"
   and \<omega>': "\<omega>' = exhale_pred \<omega> (pred_id, v_args) q"
    using IH.prems(1) IH.hyps(3) exh_if_total_normal exh_if_total_normal_2
    by blast+
  show ?case
    apply standard
    using eval_multi_exhale_sat_helper[OF IH(2)]
      apply blast
    using IH.hyps(1) \<omega>' exhale_mh_diff
     apply blast
    using 1 2 IH.hyps(1) IH.hyps(3) \<omega>' exhale_mp_diff is_singleton_mp.simps order_less_imp_le
    by blast
next
  case IH: (ExhPure e \<omega> b)
  show ?case
    apply standard
    using eval_exhale_sat_helper[OF IH(1)] IH.prems(1) IH.prems(2) exh_if_total_normal
      apply fastforce
    using IH.prems(1) exh_if_total_normal_2 same_mh_diff
     apply blast
    using IH.prems(1) exh_if_total_normal_2 same_mp_diff
    by blast
next
  case IH: (ExhStarNormal A \<omega> \<omega>_int B res)
  show ?case
  proof
    define mh\<^sub>A where "mh\<^sub>A = field_mask_sub (get_mh_total_full \<omega>) (get_mh_total_full \<omega>_int)"
    define mp\<^sub>A where "mp\<^sub>A = predicate_mask_sub (get_mp_total_full \<omega>) (get_mp_total_full \<omega>_int)"
    define mh\<^sub>B where "mh\<^sub>B = field_mask_sub (get_mh_total_full \<omega>_int) (get_mh_total_full \<omega>')"
    define mp\<^sub>B where "mp\<^sub>B = predicate_mask_sub (get_mp_total_full \<omega>_int) (get_mp_total_full \<omega>')"
    show "mh_split (field_mask_sub (get_mh_total_full \<omega>) (get_mh_total_full \<omega>')) mh\<^sub>A mh\<^sub>B"
      by (metis IH.hyps(1) IH.hyps(2) IH.prems(1) exhale_smaller(1) mh\<^sub>A_def mh\<^sub>B_def mh_sub_twice)
    show "mp_split (predicate_mask_sub (get_mp_total_full \<omega>) (get_mp_total_full \<omega>')) mp\<^sub>A mp\<^sub>B"
      by (metis IH.hyps(1) IH.hyps(2) IH.prems(1) exhale_smaller(2) mp\<^sub>A_def mp\<^sub>B_def mp_sub_twice)
    show "sat ctxt \<lparr> get_store_total = get_store_total \<omega>,
                     get_trace_total = \<lambda>x. None,
                     get_total_full = get_total_full \<omega>\<lparr> get_nm_total := empty_nm \<rparr> \<rparr>
              (field_mask_sub (get_mh_total_full \<omega>) (get_mh_total_full \<omega>_int))
              (predicate_mask_sub (get_mp_total_full \<omega>) (get_mp_total_full \<omega>_int))
              A"
      using IH.IH(1) IH.prems(2) by fastforce
    show "sat ctxt \<lparr> get_store_total = get_store_total \<omega>,
                     get_trace_total = \<lambda>x. None,
                     get_total_full = get_total_full \<omega>\<lparr> get_nm_total := empty_nm \<rparr> \<rparr>
              (field_mask_sub (get_mh_total_full \<omega>_int) (get_mh_total_full \<omega>'))
              (predicate_mask_sub (get_mp_total_full \<omega>_int) (get_mp_total_full \<omega>'))
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
    using IH.hyps IH.prems(2) eval_exhale_sat_helper apply force
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

lemma eval_framed_state_helper:
  assumes "es = direct_sub_expressions_assertion A"
      and "red_pure_exps_total ctxt None es \<omega>\<^sub>0 (Some vs)"
      and "assertion_framing_state ctxt (\<lambda>_. True) A \<omega>"
      and "supported_pred_body A"
    shows "red_pure_exps_total ctxt (Some \<omega>) es \<omega> (Some vs)"
  sorry

lemma red_pure_exps_totalI_helper:
  assumes "length es = length vs"
      and "\<And>i. 0 \<le> i \<Longrightarrow> i < length es \<Longrightarrow> ctxt, \<omega>_def \<turnstile> \<langle>es ! i; \<omega>\<rangle> [\<Down>]\<^sub>t Val (vs ! i)"
    shows "red_pure_exps_total ctxt \<omega>_def es \<omega> (Some vs)"
  sorry

lemma red_pure_exps_totalE_helper:
  assumes "length es = length vs"
      and "red_pure_exps_total ctxt \<omega>_def es \<omega> (Some vs)"
    shows "\<And>i. 0 \<le> i \<Longrightarrow> i < length es \<Longrightarrow> ctxt, \<omega>_def \<turnstile> \<langle>es ! i; \<omega>\<rangle> [\<Down>]\<^sub>t Val (vs ! i)"
  sorry

lemma singleton_set_helper:
  assumes "a = b"
    shows "a \<in> {b}"
  using assms
  by blast

lemma extcons_state_can_be_inhaled_assertion:
  assumes Sat: "sat ctxt \<omega>\<^sub>0 mh mp A"
      and mh_nm: "mh = get_mh_nm nm"
      and mp_nm: "mp = get_mp_nm nm"
      and ExtCons: "consistent_external ctxt \<lparr> get_hh_total = hh, get_nm_total = nm \<rparr>"
      and \<omega>hh: "get_hh_total_full \<omega> = hh"
      and \<omega>\<^sub>0hh: "get_hh_total_full \<omega>\<^sub>0 = hh"
      and SameStore: "get_store_total \<omega> = get_store_total \<omega>\<^sub>0"
      and Framed: "assertion_framing_state ctxt (\<lambda>_. True) A \<omega>"
      and SupPred: "supported_pred_body A"
    shows "red_inhale ctxt (\<lambda>_. True) A \<omega> (RNormal (add_to_nm_total_full \<omega> nm))"

  using Sat mh_nm mp_nm ExtCons \<omega>hh SameStore Framed SupPred
proof (induction A arbitrary: \<omega> nm)

  case IH: (SatAcc e_r r e_p p a mh f mp)
  hence "supported_pred_expr e_r" and "supported_pred_expr e_p"
    by simp+

  have "red_pure_exps_total ctxt None [e_r, e_p] \<omega>\<^sub>0 (Some [VRef r, VPerm p])"
    by (metis (no_types, lifting) IH.hyps(1) IH.hyps(2) add.right_neutral add_Suc_right less_Suc0 less_Suc_eq list.size(3) list.size(4) nth_Cons_0 nth_Cons_Suc red_pure_exps_totalI_helper)
  hence "red_pure_exps_total ctxt (Some \<omega>) [e_r, e_p] \<omega> (Some [VRef r, VPerm p])"
    using IH(1,2,12,13) eval_framed_state_helper
    by (metis direct_sub_expressions_assertion.simps(1) sub_expressions_atomic.simps(2) sub_expressions_exp_or_wildcard.simps(1))

  have eval_e_r: "ctxt, Some \<omega> \<turnstile> \<langle>e_r;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r)" and
       eval_e_p: "ctxt, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
    using \<open>red_pure_exps_total ctxt (Some \<omega>) [e_r, e_p] \<omega> (Some [VRef r, VPerm p])\<close> red_exp_list_normal_elim
     apply fastforce
    by (smt (verit, best) \<open>red_pure_exps_total ctxt (Some \<omega>) [e_r, e_p] \<omega> (Some [VRef r, VPerm p])\<close> list.discI list.inject red_exp_list_normal_elim)

  define W where "W = (if r = Null
                       then {\<omega>}
                       else inhale_perm_single (\<lambda>_. True) \<omega> (the_address r, f) (Some (Abs_preal p)))"

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
    have "nm = empty_nm"
      apply (rule nested_mask_equality)
        apply (simp_all add: empty_nm_def)
      using IH.hyps(5) IH.prems(1) True
        apply auto[1]
      using IH.hyps(6) IH.prems(2)
        apply auto[1]
      using zero_mask_def
        apply fastforce
      using IH.hyps(6) IH.prems(2) zero_mask_def
       apply fastforce
      by (metis IH.hyps(6) IH.prems(2) IH.prems(3) SatAll_case prod.exhaust total_state.select_convs(2) zero_mp.simps)
    show "th_result_rel (0 \<le> p) (W \<noteq> {} \<and> (0 < p \<longrightarrow> r \<noteq> Null)) W (RNormal (add_to_nm_total_full \<omega> nm))"
      apply (simp add: \<open>p = 0\<close> \<open>W = {\<omega>}\<close> True th_result_rel.simps)
      by (simp add: \<open>nm = empty_nm\<close> add_empty_nm)
  next
    case False
    have mh: "get_mh_nm nm = singleton_mh (a, f) (Abs_preal p)"
      using False IH.hyps(5) IH.prems(1) by presburger
    have fnm: "get_fnm_nm nm = (\<lambda>_. None)"
      by (metis IH.hyps(6) IH.prems(2) IH.prems(3) SatAll_case surj_pair total_state.select_convs(2) zero_mp.simps)
    show "th_result_rel (0 \<le> p) (W \<noteq> {} \<and> (0 < p \<longrightarrow> r \<noteq> Null)) W (RNormal (add_to_nm_total_full \<omega> nm))"
      apply (simp add: IH(4) W_def inhale_perm_single_def False)
      apply (rule THResultNormal)
      apply (rule singleton_set_helper)
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
       apply (metis IH.hyps(6) IH.prems(2) add_masks_self_zero_mask add_masks_zero_mask mp_split.elims(3) mp_split_zero)
      apply (simp add: fnm)
      apply (metis add_empty_nm empty_nm_def get_fnm_nm.simps get_fnm_nm__merge)
      done
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

  define W where "W = inhale_perm_single (\<lambda>_. True) \<omega> (the_address r, f) None"

  have "is_singleton_mh (a,f) (get_mh_nm nm)"
    using IH.hyps(4) IH.prems(1)
    by auto
  have "get_mp_nm nm = zero_mp"
    using IH.hyps(5) IH.prems(2)
    by presburger
  hence "get_fnm_nm nm = (\<lambda>_. None)"
    using IH(8) SatAll_case
    by fastforce

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
    apply (simp add: \<open>get_mp_nm nm = zero_mp\<close>)
    by (simp add: \<open>get_fnm_nm nm = (\<lambda>_. None)\<close> pfun_comb_def)
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
  case IH: (SatAccPred e_args v_args e_p p mh mp pred_id)

  hence e_args_sup: "list_all supported_pred_expr e_args" and
        e_p_sup: "supported_pred_expr e_p"
    by (simp add: list_all_length)+
  then obtain r_vs r_p where
    e_args_res: "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> r_vs" and
    e_p_res: "ctxt, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t r_p"
    using eval_ok_no_type_error IH(1,2,9,10) \<omega>\<^sub>0hh
    by (metis (full_types))
  have e_args_ok: "\<And>res. red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> res \<Longrightarrow> res \<noteq> None" and
          e_p_ok: "\<And>res. ctxt, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t res \<Longrightarrow> res \<noteq> VFailure"
     apply (metis IH.prems(6) assertion_framing_state_sub_exps_not_failure red_pure_exps_total_append_failure sub_expressions_atomic.simps(3))
    by (metis IH.prems(6) RedExpListFailure e_args_res assertion_framing_state_sub_exps_not_failure red_pure_exps_total_append_failure red_pure_exps_total_append_failure_2 split_option_ex sub_expressions_atomic.simps(3) sub_expressions_exp_or_wildcard.simps(1))
  have e_args_eval: "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some v_args)" and
          e_p_eval: "ctxt, Some \<omega> \<turnstile> \<langle>e_p;\<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)"
    using IH(1) eval_with_same_store_same_hh(2)[OF IH(1)]
    apply (metis IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh e_args_sup not_Some_eq e_args_ok e_args_res)
    by (metis IH(2) IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh e_p_res e_p_ok e_p_sup eval_with_same_store_same_hh(1) extended_val.exhaust)

  define W where "W = inhale_perm_single_pred ctxt (\<lambda>_. True) \<omega> (pred_id,v_args) (Some (Abs_preal p))"

  have "get_mh_nm nm = zero_mh"
    using IH.hyps(4) IH.prems(1) by auto
  have "get_mp_nm nm = singleton_mp (pred_id,v_args) (Abs_preal p)"
    using IH.hyps(5) IH.prems(2) by auto
  hence "get_mp_nm nm (pred_id,v_args) = Abs_preal p"
    by simp

  have sat: "sat ctxt \<omega>\<^sub>0 mh mp (Atomic (AccPredicate pred_id e_args (PureExp e_p)))"
    using IH
    by (meson SatAccPred)

  show ?case
  proof (cases "p = 0")
    case True
    hence "get_fnm_nm nm = (\<lambda>_. None)"
      by (metis IH.hyps(5) IH.prems(2) IH.prems(3) SatAll_case prod.exhaust singleton_mp.simps total_state.select_convs(2) zero_preal_def)
    have "nm = empty_nm"
      apply (rule nested_mask_equality; standard, simp_all add: empty_nm_def zero_mask_def)
      using \<open>get_mh_nm nm = zero_mh\<close> zero_mask_def
        apply fastforce
       apply (simp add: True \<open>get_mp_nm nm = singleton_mp (pred_id, v_args) (Abs_preal p)\<close> zero_preal.abs_eq)
      using \<open>get_fnm_nm nm = (\<lambda>_. None)\<close>
      by fastforce

    hence "add_to_nm_total_full \<omega> nm = \<omega>"
      by (simp add: add_empty_nm)

    have "\<omega> \<in> W"
      apply (simp add: W_def inhale_perm_single_pred_def)
      apply (rule exI[of _ "\<lparr> get_hh_total = hh, get_nm_total = empty_nm \<rparr>"])
      apply (intro conjI)
       apply standard
       apply simp_all
      using IH.prems(4)
       apply auto[1]
      using True zero_preal_def
      by presburger

    show ?thesis
      apply (rule InhAccPred[where ?W'=W])
      using e_args_eval e_p_eval
         apply (simp, simp)
      using W_def
       apply blast
      by (metis (full_types) IH.hyps(3) THResultNormal_alt \<open>\<omega> \<in> W\<close> \<open>add_to_nm_total_full \<omega> nm = \<omega>\<close> equals0D)
  next
    case False
    obtain nm_pred where nm_pred: "Some nm_pred = get_fnm_nm nm (pred_id,v_args)" and
      nm_pred_cons: "consistent_external_wrt_ploc ctxt \<lparr> get_hh_total = hh, get_nm_total = nm_pred \<rparr> (pred_id,v_args) (Abs_preal p)"
      using SatAll_case[OF IH(8), simplified]
      by (metis False IH.hyps(3) \<open>get_mp_nm nm (pred_id, v_args) = Abs_preal p\<close> linorder_not_less not_Some_eq order_antisym_conv positive_real_preal)

    have "add_to_nm_total_full \<omega> nm \<in> W"
      apply (simp add: W_def inhale_perm_single_pred_def)
      apply (rule exI[of _ "\<lparr> get_hh_total = hh, get_nm_total = nm_pred \<rparr>"])
      apply (intro conjI)
      using False IH.hyps(3) positive_real_preal
       apply force
      apply standard
      apply (intro conjI)
      using nm_pred_cons
        apply force
      using IH.prems(4)
       apply auto[1]
      apply (rule full_total_state.equality, simp_all)
      apply (rule total_state.equality, simp_all)
      apply (rule nested_mask_equality, simp_all; standard)
        apply (simp_all add: add_masks_def)
        apply (simp add: \<open>get_mh_nm nm = zero_mh\<close>)
       apply (simp add: \<open>get_mp_nm nm = singleton_mp (pred_id, v_args) (Abs_preal p)\<close>)
      by (metis (no_types, lifting) IH.prems(3) SatAll_case \<open>get_mp_nm nm = singleton_mp (pred_id, v_args) (Abs_preal p)\<close> combine_options_simps(2) nm_pred old.prod.exhaust pfun_comb_def singleton_mp.elims total_state.select_convs(2))
    hence "W \<noteq> {}"
      by blast

    show ?thesis
      apply (rule InhAccPred[where ?W'=W])
      using e_args_eval e_p_eval
         apply simp+
      using W_def
       apply force
      using IH.hyps(3) THResultNormal \<open>W \<noteq> {}\<close> \<open>add_to_nm_total_full \<omega> nm \<in> W\<close>
      by auto
  qed

next
  case IH: (SatAccPredWildcard e_args v_args mh pred_id mp)

  hence e_args_sup: "list_all supported_pred_expr e_args"
    by (simp add: list_all_length)
  then obtain r_vs where
    e_args_res: "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> r_vs"
    using eval_ok_no_type_error(2) IH(1,7,8,10) \<omega>\<^sub>0hh
    by (metis (no_types, lifting))
  have e_args_ok: "\<And>res. red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> res \<Longrightarrow> res \<noteq> None"
    by (metis IH.prems(6) assertion_framing_state_sub_exps_not_failure red_pure_exps_total_append_failure sub_expressions_atomic.simps(3))
  have e_args_eval: "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some v_args)"
    using IH(1) eval_with_same_store_same_hh(2)[OF IH(1)]
    by (metis IH.prems(4) IH.prems(5) \<omega>\<^sub>0hh e_args_sup not_Some_eq e_args_ok e_args_res)

  define W where "W = inhale_perm_single_pred ctxt (\<lambda>_. True) \<omega> (pred_id,v_args) None"

  have "get_mh_nm nm = zero_mh"
    using IH.hyps(2) IH.prems(1) by auto
  have "is_singleton_mp (pred_id,v_args) (get_mp_nm nm)"
    using IH.hyps(3) IH.prems(2) by auto
  then obtain p where p: "get_mp_nm nm = singleton_mp (pred_id,v_args) p" and "p > 0"
    by auto

  have sat: "sat ctxt \<omega>\<^sub>0 mh mp (Atomic (AccPredicate pred_id e_args Wildcard))"
    using IH
    by (meson SatAccPredWildcard)

  obtain nm_pred where nm_pred: "Some nm_pred = get_fnm_nm nm (pred_id,v_args)" and
    nm_pred_cons: "consistent_external_wrt_ploc ctxt \<lparr> get_hh_total = hh, get_nm_total = nm_pred \<rparr> (pred_id,v_args) p"
    using SatAll_case[OF IH(6), simplified]
    by (metis p \<open>p > 0\<close> \<open>get_mp_nm nm = singleton_mp (pred_id, v_args) p\<close> option.exhaust_sel preal_not_0_gt_0 singleton_mp.elims)

  have "add_to_nm_total_full \<omega> nm \<in> W"
    apply (simp add: W_def inhale_perm_single_pred_def)
    apply (rule exI[of _ "\<lparr> get_hh_total = hh, get_nm_total = nm_pred \<rparr>"])
    apply (rule exI[of _ p])
    apply (intro conjI)
    using \<open>p > 0\<close> IH.hyps(3) positive_real_preal
     apply force
    apply standard
    apply (intro conjI)
    using nm_pred_cons
      apply force
    using IH.prems(4)
     apply auto[1]
    apply (rule full_total_state.equality, simp_all)
    apply (rule total_state.equality, simp_all)
    apply (rule nested_mask_equality, simp_all; standard)
      apply (simp_all add: add_masks_def)
      apply (simp add: \<open>get_mh_nm nm = zero_mh\<close>)
     apply (simp add: \<open>get_mp_nm nm = singleton_mp (pred_id, v_args) p\<close>)
    by (metis (no_types, lifting) IH.prems(3) SatAll_case \<open>get_mp_nm nm = singleton_mp (pred_id, v_args) p\<close> combine_options_simps(2) nm_pred old.prod.exhaust pfun_comb_def singleton_mp.elims total_state.select_convs(2))
  hence "W \<noteq> {}"
    by blast

  show ?case
    apply (rule InhAccPredWildcard[where ?W'=W])
    using e_args_eval
      apply simp
    using W_def
     apply force
    using IH.hyps(3) THResultNormal \<open>W \<noteq> {}\<close> \<open>add_to_nm_total_full \<omega> nm \<in> W\<close>
    by auto

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
    have "nm = empty_nm"
      apply (rule nested_mask_equality)
        apply (metis IH.hyps(2) IH.prems(1) all_pos empty_nm_def get_mh_nm.simps le_fun_def order_antisym_conv zero_mask_less_eq_mask zero_mh.simps)
       apply (metis IH.hyps(3) IH.prems(2) add_masks_self_zero_mask empty_nm_def get_mp_nm.simps mp_split.elims(3) mp_split_zero)
      apply (simp add: empty_nm_def)
      by (metis IH(3) IH(6) IH.prems(2) SatAll_case surj_pair total_state.select_convs(2) zero_mp.elims)
    hence "add_to_nm_total_full \<omega> nm = \<omega>"
      apply simp
      by (simp add: add_empty_nm)
    then show ?thesis
      by (metis Val \<omega>_eval \<open>v = VBool True\<close> inh_pure_normal)
  next
    case VFailure
    then show ?thesis
      using IH.prems(6) RedExpListFailure \<omega>_eval assertion_framing_state_sub_exps_not_failure by fastforce
  qed

next
  case (SatStar mh mh\<^sub>1 mh\<^sub>2 mp mp\<^sub>1 mp\<^sub>2 A B)
  then show ?case sorry

next
  case (SatImpTrue e mh mp A)
  then show ?case sorry
next
  case (SatImpFalse e mh mp A)
  then show ?case sorry
next
  case (SatCondTrue e mh mp A B)
  then show ?case sorry
next
  case (SatCondFalse e mh mp B A)
  then show ?case sorry
qed


lemma extcons_state_can_be_inhaled:
  assumes PredDecl: "ViperLang.predicates (program_total ctxt) pid = Some pdecl"
      and PredBody: "ViperLang.predicate_decl.body pdecl = Some pbody"
      and SupPred: "supported_pred_body pbody"
      and SelfFraming: "\<And>q. assertion_framing_state ctxt (\<lambda>_. True) (syntactic_mult q pbody) \<omega>"
      and ExtCons: "consistent_external_wrt_ploc ctxt \<lparr> get_hh_total = hh, get_nm_total = nm \<rparr> (pid,vs) p"
      and \<omega>hh: "get_hh_total_full \<omega> = hh"
      and \<omega>Store: "get_store_total \<omega> = nth_option vs"
    shows "red_inhale ctxt (\<lambda>_. True) (syntactic_mult (Rep_preal p) pbody) \<omega> (RNormal (add_to_nm_total_full \<omega> nm))"
proof -
  have "sat ctxt \<lparr> get_store_total = nth_option vs,
                   get_trace_total = Map.empty,
                   get_total_full = \<lparr> get_hh_total = hh, get_nm_total = empty_nm \<rparr> \<rparr>
            (get_mh_nm nm) (get_mp_nm nm)
            (syntactic_mult (Rep_preal p) pbody)" and
    "consistent_external ctxt \<lparr> get_hh_total = hh, get_nm_total = nm \<rparr>"
    using SatStep_case PredDecl PredBody ExtCons by fastforce+
  moreover have "assertion_framing_state ctxt (\<lambda>_. True) (syntactic_mult (Rep_preal p) pbody) \<omega>"
    using SelfFraming by auto
  ultimately show ?thesis
    using \<omega>Store \<omega>hh extcons_state_can_be_inhaled_assertion
    by (metis SupPred full_total_state.select_convs(1) full_total_state.select_convs(3) get_hh_total_full.simps syntactic_mult_supported total_state.select_convs(1))
qed


subsection \<open>Inhale Simulates Unfold\<close>

lemma inhale_simulates_unfold:
  assumes Unfold: "unfold_rel ctxt pid vs p \<phi> \<phi>'"
      and ExtCons: "consistent_external ctxt \<phi>"
      and PredDecl: "ViperLang.predicates (program_total ctxt) pid = Some pdecl"
      and PredBody: "ViperLang.predicate_decl.body pdecl = Some pbody"
      and SupPred: "supported_pred_body pbody" \<comment> \<open>change name\<close>
      and SelfFraming: "\<And>q. assertion_self_framing_store ctxt (\<lambda>_. True) (syntactic_mult q pbody) (nth_option vs)"
      and "\<phi>\<^sub>d = rm_from_mp_loc_total (mult_rm_nm_loc_total \<phi> (pid,vs) p) (pid,vs) p"
    shows "red_inhale ctxt (\<lambda>_. True) (syntactic_mult (Rep_preal p) pbody)
                      \<lparr> get_store_total = nth_option vs, get_trace_total = trace, get_total_full = \<phi>\<^sub>d \<rparr>
             (RNormal \<lparr> get_store_total = nth_option vs, get_trace_total = trace, get_total_full = \<phi>' \<rparr>)"
proof -
  from assms(1)
  obtain nm nm' where
    "shift_up pid vs p nm nm'"
    "get_nm_total \<phi> = nm"
    "get_nm_total \<phi>' = nm'"
    "get_hh_total \<phi>' = get_hh_total \<phi>"
    by (blast elim: unfold_rel.cases)

  then obtain mh mp fnm pnm' pp mp' fnm' nm\<^sub>d where
    "nm = NM mh mp fnm" and
    "pnm' = fnm (pid,vs)" and
    "pp = mp (pid,vs)" and
    "p \<le> pp" and
    "p \<noteq> 0" and
    mp': "mp' = mp( (pid,vs) := pp - p )" and
    fnm': "fnm' = fnm( (pid,vs) := nested_mask_multiply_option pnm' ((pp - p) / pp) )" and
    nm\<^sub>d: "nm\<^sub>d = NM mh mp' fnm'" and
    nm': "Some nm' = nested_mask_merge_option (Some nm\<^sub>d) (nested_mask_multiply_option pnm' (p / pp))"
    by (blast elim: shift_up.cases)

  then obtain pnm where "Some pnm = pnm'"
    by (metis ExtCons SatAll_case \<open>get_nm_total \<phi> = nm\<close> all_pos get_fnm_nm.simps get_mp_nm.simps nested_mask_multiply_option.elims order_antisym)
  hence "Some pnm = fnm (pid, vs)"
    by (simp add: \<open>pnm' = fnm (pid, vs)\<close>)
  have "\<not> p / pp = pos_perm_class.pnone"
    using \<open>p \<le> pp\<close> \<open>p \<noteq> pos_perm_class.pnone\<close> divide_preal.rep_eq preal_not_0_gt_0 preal_to_real(10) zero_preal.rep_eq
    by auto
  hence nm'_direct: "nm' = nested_mask_merge nm\<^sub>d (nested_mask_multiply pnm (p / pp))"
    using nm'
    by (simp add: combine_options_def \<open>Some pnm = pnm'\<close>[symmetric])

  define nm\<^sub>s where "nm\<^sub>s = nested_mask_multiply pnm (p / pp)"

  \<comment> \<open>The shifted part is external consistent w.r.t. the predicate.\<close>
  have pnm_cons: "consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := pnm \<rparr>) (pid,vs) pp"
    using ExtCons SatAll_case \<open>Some pnm = fnm (pid, vs)\<close> \<open>get_nm_total \<phi> = nm\<close> \<open>nm = NM mh mp fnm\<close> \<open>pp = mp (pid, vs)\<close> get_fnm_nm.simps
    by fastforce
  have "0 < p / pp"
    using \<open>p \<le> pp\<close> \<open>p \<noteq> 0\<close>
    apply (simp add: preal_to_real)
    by (metis divide_pos_pos order_antisym order_le_imp_less_or_eq prat_non_negative)
  moreover hence "p / pp * pp = p"
    apply (simp add: preal_to_real)
    using divide_preal.rep_eq less_preal.rep_eq times_preal.rep_eq zero_preal.rep_eq
    by auto
  moreover have "\<lparr> get_hh_total = get_hh_total \<phi>, get_nm_total = nm\<^sub>s \<rparr> = \<phi>\<lparr> get_nm_total := nm\<^sub>s \<rparr>"
    by simp
  ultimately have
    ShiftExtCons: "consistent_external_wrt_ploc ctxt \<lparr>get_hh_total = get_hh_total \<phi>, get_nm_total = nm\<^sub>s\<rparr> (pid, vs) p"
    using fraction_consistent_external(1)[of "p / pp", OF _ pnm_cons] nm\<^sub>s_def
    by (metis mult_nm_total.elims total_state.ext_inject total_state.surjective total_state.update_convs(2))

  have "fnm (pid,vs) = Some pnm"
    using \<open>Some pnm = fnm (pid, vs)\<close>
    by force
  have "get_nm_total \<phi>\<^sub>d = nm\<^sub>d"
    apply (simp add: assms(5) nm\<^sub>d \<open>get_nm_total \<phi> = nm\<close> \<open>nm = NM mh mp fnm\<close> fnm' \<open>pp = mp (pid,vs)\<close>)
    apply (simp add: mp' \<open>pp = mp (pid,vs)\<close> \<open>fnm (pid,vs) = Some pnm\<close>)
    apply (rule nested_mask_equality)
      apply simp_all
      apply (simp add: \<open>get_nm_total \<phi> = nm\<close> \<open>nm = NM mh mp fnm\<close> assms(7))+
    using PosReal.field_divide_inverse \<open>fnm (pid, vs) = Some pnm\<close> \<open>pnm' = fnm (pid, vs)\<close> minus_preal.abs_eq zero_preal_def
    by force

  have 1: "add_to_nm_total_full
          \<lparr> get_store_total = nth_option vs, get_trace_total = trace, get_total_full = \<phi>\<^sub>d \<rparr> nm\<^sub>s =
          \<lparr> get_store_total = nth_option vs, get_trace_total = trace, get_total_full = \<phi>' \<rparr>"
    apply simp
    apply (rule total_state.equality)
      apply (simp add: \<open>get_hh_total \<phi>' = get_hh_total \<phi>\<close> assms(5))
      apply (simp add: assms(7))
     apply (rule nested_mask_equality)
       apply simp_all
    by (simp add: \<open>get_nm_total \<phi>' = nm'\<close> \<open>get_nm_total \<phi>\<^sub>d = nm\<^sub>d\<close> nm'_direct nm\<^sub>s_def)+

  have Framed: "\<And>q. assertion_framing_state ctxt (\<lambda>_. True) (syntactic_mult q pbody)
                      \<lparr> get_store_total = nth_option vs, get_trace_total = trace, get_total_full = \<phi>\<^sub>d \<rparr>"
    using assertion_self_framing_store_def SelfFraming
    by (metis full_total_state.update_convs(1) update_store_total.simps)

  have 2: "get_hh_total_full \<lparr>get_store_total = nth_option vs, get_trace_total = trace, get_total_full = \<phi>'\<rparr> = get_hh_total \<phi>"
    apply simp
    using \<open>get_hh_total \<phi>' = get_hh_total \<phi>\<close> by auto

  show ?thesis
    using extcons_state_can_be_inhaled[OF PredDecl PredBody SupPred Framed ShiftExtCons] 1 2 assms(7)
    by auto
qed


end
