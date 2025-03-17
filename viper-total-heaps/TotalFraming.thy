section \<open>Framed Assertions\<close>

theory TotalFraming
  imports TotalInhaleExhale NestedMaskProperties
begin


text \<open>We have two definitions of self-framing at the moment. We need to prove their equivalence eventually.\<close>


subsection \<open>Self-Framing Assertion Definition Based on \<^const>\<open>red_inhale\<close>\<close>

definition assertion_framing_state :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> bool"
  where
    "assertion_framing_state ctxt StateCons A \<omega> \<equiv>
      \<forall> res. red_inhale ctxt StateCons A \<omega> res \<longrightarrow> res \<noteq> RFailure"

definition assertion_self_framing_store :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> assertion \<Rightarrow> 'a store \<Rightarrow> bool"
  where
    "assertion_self_framing_store ctxt StateCons A \<sigma> \<equiv>
      \<forall> \<omega>. assertion_framing_state ctxt StateCons A (update_store_total \<omega> \<sigma>)"

lemma assertion_framing_star: 
  assumes "assertion_framing_state ctxt StateCons (A1 && A2) \<omega>" 
  shows "assertion_framing_state ctxt StateCons A1 \<omega> \<and>
        (\<forall> \<omega>'. red_inhale ctxt StateCons A1 \<omega> (RNormal \<omega>') \<longrightarrow> assertion_framing_state ctxt StateCons A2 \<omega>')" (is "?Goal1 \<and> ?Goal2")
proof 
  show "assertion_framing_state ctxt StateCons A1 \<omega>"
    unfolding assertion_framing_state_def
  proof (rule allI | rule impI)+
    fix res
    assume "red_inhale ctxt StateCons A1 \<omega> res"

    thus "res \<noteq> RFailure"
      using assms InhStarFailureMagic assertion_framing_state_def
      by blast
  qed
next
  show ?Goal2
  proof (rule allI | rule impI)+
    fix \<omega>' 
    assume InhA1: "red_inhale ctxt StateCons A1 \<omega> (RNormal \<omega>')"
    show "assertion_framing_state ctxt StateCons A2 \<omega>'"
      unfolding assertion_framing_state_def
      using InhA1 InhStarNormal assertion_framing_state_def assms by blast
  qed
qed

lemma assertion_framing_imp: 
  assumes "assertion_framing_state ctxt StateCons (Imp e A) \<omega>"
     and "ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool True))"  
   shows "assertion_framing_state ctxt StateCons A \<omega>"
  using assms
  unfolding assertion_framing_state_def
  by (auto intro: InhImpTrue)

lemma assertion_framing_cond_assert_true:
  assumes "assertion_framing_state ctxt StateCons (CondAssert e A B) \<omega>"
      and "ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool True))"
    shows "assertion_framing_state ctxt StateCons A \<omega>"
  using assms
  unfolding assertion_framing_state_def
  by (auto intro: InhCondAssertTrue)

lemma assertion_framing_cond_assert_false:
  assumes "assertion_framing_state ctxt StateCons (CondAssert e A B) \<omega>"
      and "ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool False))"
    shows "assertion_framing_state ctxt StateCons B \<omega>"
  using assms
  unfolding assertion_framing_state_def
  by (auto intro: InhCondAssertFalse)

definition assertion_self_framing :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> assertion \<Rightarrow> vtyp list \<Rightarrow> bool"
  where
    "assertion_self_framing ctxt StateCons A tys \<equiv> \<forall>vs p. vals_well_typed (absval_interp_total ctxt) vs tys \<longrightarrow>
       assertion_self_framing_store ctxt StateCons (syntactic_mult p A) (nth_option vs)"



subsection \<open>Self-Framing Predicate Definition Based on \<^const>\<open>sat\<close>\<close>


definition well_typed_store :: "vtyp list \<Rightarrow> ('a \<Rightarrow> abs_type) \<Rightarrow> 'a store \<Rightarrow> bool"
  where
    "well_typed_store tys \<Delta> st \<equiv> \<forall>i. i < length tys \<longrightarrow> (\<exists>v. st i = Some v \<and> get_type \<Delta> v = tys ! i)"


definition differ_only_in_0_perm_locs where
  "differ_only_in_0_perm_locs \<phi> \<phi>' \<equiv>
     (\<forall>loc. get_hh_total \<phi> loc \<noteq> get_hh_total \<phi>' loc \<longrightarrow> nm_loc_sum loc (get_nm_total \<phi>) 0) \<and>
     get_nm_total \<phi> = get_nm_total \<phi>'"


definition pred_self_framing :: "'a total_context \<Rightarrow> ('a total_state \<Rightarrow> bool) \<Rightarrow> predicate_ident \<Rightarrow> bool"
  where
    "pred_self_framing ctxt StateCons_t pid \<equiv>
       \<forall>(\<omega>::'a full_total_state) (\<omega>'::'a full_total_state) (\<phi>::'a total_state) (\<phi>'::'a total_state) vs frac.
          frac > 0 \<longrightarrow>
          get_store_total \<omega> = get_store_total \<omega>' \<longrightarrow>
          differ_only_in_0_perm_locs \<phi> \<phi>' \<longrightarrow>
          get_hh_total_full \<omega> = get_hh_total \<phi> \<longrightarrow>
          get_hh_total_full \<omega>' = get_hh_total \<phi>' \<longrightarrow>
          consistent_external_wrt_ploc ctxt \<phi> (pid,vs) frac \<longrightarrow>
          StateCons_t \<phi> \<longrightarrow>
          consistent_external_wrt_ploc ctxt \<phi>' (pid,vs) frac"

(*
lemma pred_self_framing_subst:
  assumes "pred_self_framing ctxt pred_decl"
      and "predicate_decl.body pred_decl = Some pred_body"
      and "get_store_total \<omega> = get_store_total \<omega>'"
      and "\<forall>l. mh l > 0 \<longrightarrow> get_hh_total_full \<omega> l = get_hh_total_full \<omega>' l"
      and "sat ctxt \<omega> mh mp (syntactic_mult p pred_body)"
    shows "sat ctxt \<omega>' mh mp (syntactic_mult p pred_body)"
  using assms(1) assms(2) assms(3) assms(4) assms(5) pred_self_framing_def
  by blast
*)


subsection \<open>Context All Predicates Self-Framing\<close>

definition ctxt_pred_self_framing_sat :: "'a total_context \<Rightarrow> ('a total_state \<Rightarrow> bool) \<Rightarrow> bool" where
  "ctxt_pred_self_framing_sat ctxt StateCons_t \<equiv> \<forall>pid.
     pred_self_framing ctxt StateCons_t pid"

definition ctxt_pred_self_framing_inh :: "'a total_context \<Rightarrow> ('a full_total_state \<Rightarrow> bool) \<Rightarrow> bool" where
  "ctxt_pred_self_framing_inh ctxt StateCons \<equiv> \<forall>pid pdecl pbody.
     ViperLang.predicates (program_total ctxt) pid = Some pdecl \<longrightarrow>
     predicate_decl.body pdecl = Some pbody \<longrightarrow>
     assertion_self_framing ctxt StateCons pbody (predicate_decl.args pdecl)"


end
