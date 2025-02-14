theory TotalIntConsPreservation
  imports TotalInternalConsistency TotalSemantics
begin


subsection \<open>Lemma\<close>

lemma intcons_preserved_by_update_store:
  assumes "consistent_internal_total_full \<omega>"
  shows "consistent_internal_total_full (\<omega>\<lparr> get_store_total := \<sigma> \<rparr>)"
  using assms
  unfolding consistent_internal_total_full_def
  by simp


subsection \<open>Preservation\<close>

lemma intcons_preserved_by_red_inhale:
  assumes "consistent_internal_total_full \<omega>"
      and "red_inhale ctxt consistent_internal_total_full A \<omega> (RNormal \<omega>')"
    shows "consistent_internal_total_full \<omega>'"
  using assms
proof (induction A arbitrary: \<omega> \<omega>')
  case (Atomic atm)
  show ?case
  proof (cases atm)
    case (Pure e)
    show ?thesis
      using Atomic(1) Atomic(2)[unfolded Pure]
      by (metis red_inhale_elims(3) result_total.inject result_total.simps(5) result_total.simps(7))
  next
    case (Acc e_r f perm)
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      obtain W' r p where
        "W' = (if r = Null then {\<omega>} else inhale_perm_single consistent_internal_total_full \<omega> (the_address r,f) (Some (Abs_preal p)))" and
        "th_result_rel (p \<ge> 0) (W' \<noteq> {} \<and> (p > 0 \<longrightarrow> r \<noteq> Null)) W' (RNormal \<omega>')"
        using Atomic(2)[unfolded Acc PureExp]
        by (auto elim: InhAccPerm_case)
      hence "\<omega>' \<in> W'"
        using th_result_rel_normal
        by blast
      show ?thesis
        apply (cases "r = Null")
        using \<open>\<omega>' \<in> W'\<close> \<open>W' = _\<close> Atomic(1)
         apply force
        using \<open>W' = _\<close>[unfolded inhale_perm_single_def]
        apply simp
        using \<open>\<omega>' \<in> W'\<close> consistent_internal_total_def consistent_internal_total_full_def
        by blast
    next
      case Wildcard
      obtain W' r where
        "W' = inhale_perm_single consistent_internal_total_full \<omega> (the_address r,f) None" and
        "th_result_rel True (W' \<noteq> {} \<and> r \<noteq> Null) W' (RNormal \<omega>')"
        using Atomic(2)[unfolded Acc Wildcard]
        by (auto elim: InhAccWildcard_case)
      hence "\<omega>' \<in> W'"
        using th_result_rel_normal
        by blast
      then show ?thesis
        using \<open>W' = _\<close>[unfolded inhale_perm_single_def]
        apply simp
        using consistent_internal_total_def consistent_internal_total_full_def
        by blast
    qed
  next
    case (AccPredicate pid e_args perm)
    show ?thesis
    proof (cases perm)
      case (PureExp e_p)
      obtain W' v_args p where
        "W' = inhale_perm_single_pred ctxt consistent_internal_total_full \<omega> (pid,v_args) (Some (Abs_preal p))" and
        "th_result_rel (p \<ge> 0) (W' \<noteq> {}) W' (RNormal \<omega>')"
        using Atomic(2)[unfolded AccPredicate PureExp]
        by (auto elim: InhAccPredPerm_case)
      hence "\<omega>' \<in> W'"
        using th_result_rel_normal
        by blast
      then show ?thesis
        using \<open>W' = _\<close>[unfolded inhale_perm_single_pred_def]
        apply simp
        using consistent_internal_total_def consistent_internal_total_full_def
        by blast
    next
      case Wildcard
      obtain W' v_args where
        "W' = inhale_perm_single_pred ctxt consistent_internal_total_full \<omega> (pid,v_args) None" and
        "th_result_rel True (W' \<noteq> {}) W' (RNormal \<omega>')"
        using Atomic(2)[unfolded AccPredicate Wildcard]
        by (auto elim: InhAccPredWildcard_case)
      hence "\<omega>' \<in> W'"
        using th_result_rel_normal
        by blast
      then show ?thesis
        using \<open>W' = _\<close>[unfolded inhale_perm_single_pred_def]
        apply simp
        using consistent_internal_total_def consistent_internal_total_full_def
        by blast
    qed
  qed
qed (blast elim: red_inhale.cases)+


lemma intcons_preserved_by_red_inhale_stmt:
  assumes "consistent_internal_total_full \<omega>"
      and "red_stmt_total ctxt consistent_internal_total_full \<Lambda> (Inhale A) \<omega> (RNormal \<omega>')"
    shows "consistent_internal_total_full \<omega>'"
  using intcons_preserved_by_red_inhale assms
  by (blast elim: RedInhale_case)


lemma intcons_preserved_by_red_exhale_stmt:
  assumes "consistent_internal_total_full \<omega>"
      and "red_stmt_total ctxt consistent_internal_total_full \<Lambda> (Exhale A) \<omega> (RNormal \<omega>')"
    shows "consistent_internal_total_full \<omega>'"
  sorry


lemma intcons_preserved_by_red_stmt:
  assumes "consistent_internal_total_full \<omega>"
      and "red_stmt_total ctxt consistent_internal_total_full \<Lambda> stmt \<omega> (RNormal \<omega>')"
    shows "consistent_internal_total_full \<omega>'"
  using assms
proof (induction stmt arbitrary: \<Lambda> \<omega> \<omega>')
  case (Inhale A)
  then show ?case
    using intcons_preserved_by_red_inhale_stmt
    by blast
next
  case (Exhale x)
  then show ?case
    using intcons_preserved_by_red_exhale_stmt
    by blast
next
  case (If _ _ _)
  then show ?case
    by (meson RedIfNormal_case)
next
  case (Seq _ _)
  then show ?case
    by (meson RedSeqNormal_case)
next
  case (LocalAssign x1a x2a)
  then show ?case
    using RedLocalAssign_case[OF LocalAssign(2), simplified]
    unfolding consistent_internal_total_full_def
    by fastforce
next
  case (FieldAssign x1a x2a x3a)
  then show ?case
    using RedFieldAssign_case[OF FieldAssign(2), simplified]
    unfolding consistent_internal_total_full_def consistent_internal_total_def
    by fastforce
next
  case (Havoc x)
  then show ?case
    using RedHavoc_case[OF Havoc(2), simplified]
    unfolding consistent_internal_total_full_def consistent_internal_total_def
    by fastforce
next
  case IH: (MethodCall ys m es)
  obtain v_args mdecl v_rets resPre resPost where
    "red_pure_exps_total ctxt (Some \<omega>) es \<omega> (Some v_args)" and
    "program.methods (program_total ctxt) m = Some mdecl" and
    "vals_well_typed (absval_interp_total ctxt) v_args (method_decl.args mdecl)" and
    "list_all2 (\<lambda> y t. y = Some t) (map \<Lambda> ys) (method_decl.rets mdecl)" and
    "vals_well_typed (absval_interp_total ctxt) v_rets (method_decl.rets mdecl)" and
  red_exh:
    "red_stmt_total ctxt consistent_internal_total_full \<Lambda> (Exhale (method_decl.pre mdecl))
                    \<lparr> get_store_total = (shift_and_add_list_alt Map.empty v_args),
                      get_trace_total = [old_label \<mapsto> get_total_full \<omega>],
                      get_total_full = get_total_full \<omega> \<rparr>
                    resPre" and
    "resPre = RFailure \<or> resPre = RMagic \<Longrightarrow> RNormal \<omega>' = resPre" and
  red_inh:
    "\<And> \<omega>Pre. resPre = RNormal \<omega>Pre \<Longrightarrow>
        (red_stmt_total ctxt consistent_internal_total_full \<Lambda> (Inhale (method_decl.post mdecl))
                        \<lparr> get_store_total = (shift_and_add_list_alt Map.empty (v_args @ v_rets)),
                          get_trace_total = [old_label \<mapsto> get_total_full \<omega>],
                          get_total_full = get_total_full \<omega>Pre \<rparr>
                        resPost \<and>
        RNormal \<omega>' = map_result_total (reset_state_after_call ys v_rets \<omega>) resPost)"
    using RedMethodCall_case[OF IH(2)]
    by blast
  then obtain \<omega>Pre where "resPre = RNormal \<omega>Pre"
    by (metis result_total.exhaust)
  hence "consistent_internal_total_full \<omega>Pre"
    unfolding consistent_internal_total_full_def
    using intcons_preserved_by_red_exhale_stmt
    by (smt (verit, ccfv_SIG) IH.prems(1) consistent_internal_total_full_def full_total_state.select_convs(2) full_total_state.select_convs(3) map_upd_Some_unfold option.discI red_exh)
  obtain \<omega>Post where "resPost = RNormal \<omega>Post"
    by (metis \<open>resPre = RNormal \<omega>Pre\<close> map_result_total.elims red_inh)
  hence "consistent_internal_total_full \<omega>Post"
    by (smt (verit) IH.prems(1) \<open>consistent_internal_total_full \<omega>Pre\<close> \<open>resPre = RNormal \<omega>Pre\<close> consistent_internal_total_full_def full_total_state.select_convs(2) full_total_state.select_convs(3) fun_upd_def intcons_preserved_by_red_inhale_stmt option.discI option.simps(1) red_inh)
  then show ?case
    by (metis IH.prems(1) \<open>resPost = RNormal \<omega>Post\<close> \<open>resPre = RNormal \<omega>Pre\<close> consistent_internal_total_full_def full_total_state.select_convs(2) full_total_state.select_convs(3) map_result_total.simps(1) red_inh reset_state_after_call_def result_total.inject)
next
  case (Unfold _ _ _)
  show ?case
    using red_stmt_total.cases[OF Unfold(2), simplified] unfold_preserves_internal_consistency_total Unfold(1)
    unfolding consistent_internal_total_full_def
    by (metis full_total_state.select_convs(2) full_total_state.select_convs(3) full_total_state.surjective full_total_state.update_convs(3))
next
  case (Fold _ _ perm)
  show ?case
  proof (cases perm)
    case (PureExp x1)
    show ?thesis
      using red_stmt_total.cases[OF Fold(2)[unfolded PureExp], simplified]
      by (metis Fold.prems(1) intcons_preserved_by_fold_rel)
  next
    case Wildcard
    show ?thesis
      using red_stmt_total.cases[OF Fold(2)[unfolded Wildcard], simplified]
      by blast
  qed
next
  case (Label lbl)
  show ?case
    apply (cases "get_trace_total \<omega> lbl")
    using red_stmt_total.cases[OF Label(2), simplified] Label.prems(1)
     apply (simp add: consistent_internal_total_full_def)
     apply (smt (z3) full_total_state.cases_scheme full_total_state.select_convs(2) full_total_state.select_convs(3) full_total_state.update_convs(2) map_upd_Some_unfold)
    using red_stmt_total.cases[OF Label(2), simplified] Label.prems(1)
    by auto
next
  case IH: (Scope \<tau> scopeBody)
  then obtain v res where
    "get_type (absval_interp_total ctxt) v = \<tau>" and
    red: "red_stmt_total ctxt consistent_internal_total_full (shift_and_add \<Lambda> \<tau>) scopeBody (shift_and_add_state_total \<omega> v) res" and
    map: "RNormal \<omega>' = map_result_total (unshift_state_total 1) res"
    using RedScope_case[OF IH(3)]
    by (metis One_nat_def shift_and_add_state_total.elims sub_expressions.simps(17) update_store_total.simps)

  have *: "consistent_internal_total_full (shift_and_add_state_total \<omega> v)"
    by (simp add: IH.prems(1) intcons_preserved_by_update_store)
  obtain \<omega>\<^sub>m where "res = RNormal \<omega>\<^sub>m"
    by (metis map map_result_total.elims)
  have "consistent_internal_total_full \<omega>\<^sub>m"
    using IH(1)[OF * red[simplified \<open>res = _\<close>]]
    by blast

  then show ?case
    using \<open>res = RNormal \<omega>\<^sub>m\<close> map intcons_preserved_by_update_store
    by auto
qed (blast elim: red_stmt_total.cases)+

end
