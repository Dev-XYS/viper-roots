theory TotalSemanticsProperties
  imports TotalSemProperties
begin


lemma eval_with_None:
  assumes "ctxt, Some \<omega>\<^sub>0 \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"
  shows "ctxt, None \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"
  sorry

lemma eval_with_no_nm:
  assumes "ctxt, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"
      and "no_perm_pure_exp e"
    shows "ctxt, \<omega>_def \<turnstile> \<langle>e; update_nm_total_full \<omega> empty_nm\<rangle> [\<Down>]\<^sub>t Val v"
  sorry

lemma eval_with_no_trace:
  assumes "ctxt, \<omega>_def \<turnstile> \<langle>e;\<omega>\<rangle> [\<Down>]\<^sub>t Val v"
      and "no_old_pure_exp e"
    shows "ctxt, \<omega>_def \<turnstile> \<langle>e; \<omega>\<lparr> get_trace_total := Map.empty \<rparr>\<rangle> [\<Down>]\<^sub>t Val v"
  sorry


\<comment> \<open>Properties on \<^const>\<open>red_exhale\<close>\<close>

lemma exhale_fraction:
  assumes "red_exhale ctxt \<omega>\<^sub>0 A \<omega> (RNormal \<omega>')"
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

lemma same_mh_diff:
  shows "field_mask_sub (get_mh_total_full \<omega>)
                        (get_mh_total_full \<omega>) =
         zero_mh"
  apply standard
  apply simp
  using minus_preal.abs_eq zero_preal_def
  by force

lemma same_mp_diff:
  shows "predicate_mask_sub (get_mp_total_full \<omega>)
                            (get_mp_total_full \<omega>) =
         zero_mp"
  apply standard
  apply simp
  using minus_preal.abs_eq zero_preal_def
  by force

lemma dec_mh_mh_diff:
  assumes "p < get_mh_total_full \<omega> loc"
  shows "field_mask_sub (get_mh_total_full \<omega>)
                        (get_mh_total_full (update_mh_loc_total_full \<omega> loc (get_mh_total_full \<omega> loc - p))) =
         singleton_mh loc p"
proof -
  have "get_mh_total_full \<omega> loc - (get_mh_total_full \<omega> loc - p) = p"
    using assms minus_preal_gte by auto
  thus ?thesis
    by (metis assms mh_upd_loc_diff order_less_imp_le psub_smaller update_mh_loc_total_full_mh_rel)
qed

lemma dec_mh_mp_diff:
  shows "predicate_mask_sub (get_mp_total_full \<omega>)
                            (get_mp_total_full (update_mh_loc_total_full \<omega> loc (get_mh_total_full \<omega> loc - p))) =
         zero_mp"
  by (metis same_mp_diff update_mh_loc_total_full_mp_eq)

lemma exhale_mh_diff:
  shows "field_mask_sub (get_mh_total_full \<omega>)
                        (get_mh_total_full (exhale_pred \<omega> ploc p)) =
         zero_mh"
  by (metis exhale_pred_def mult_nm_loc_total_full_mh_eq same_mh_diff update_mp_loc_total_full_mh_eq)

lemma exhale_mp_diff:
  assumes "p \<le> get_mp_total_full \<omega> ploc"
  shows "predicate_mask_sub (get_mp_total_full \<omega>)
                            (get_mp_total_full (exhale_pred \<omega> ploc p)) =
         singleton_mp ploc p"
proof -
  have 1: "get_mp_total_full (exhale_pred \<omega> ploc p) = get_mp_total_full (update_mp_loc_total_full \<omega> ploc (get_mp_total_full \<omega> ploc - p))"
    by (metis exhale_pred_def mult_nm_loc_total_full_mp_eq)
  have 2: "get_mp_total_full \<omega> ploc - (get_mp_total_full \<omega> ploc - p) = p"
    using assms minus_preal_gte by auto
  show ?thesis
    apply (simp only: 1)
    by (metis 2 assms mp_upd_loc_diff psub_smaller update_mp_loc_total_full_mp_rel)
qed

\<comment> \<open>already proved elsewhere, but need adjustment\<close>
lemma exhale_smaller:
  assumes "red_exhale ctxt \<omega>_def A \<omega> (RNormal \<omega>')"
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
  apply (simp add: fun_comb_def preal_to_real)
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
  apply (simp add: fun_comb_def preal_to_real)
  using assms less_eq_preal.rep_eq
  by auto


\<comment> \<open>Relation between exhale and sat\<close>

lemma exhale_diff_sat:
  assumes "consistent_external ctxt (get_total_full \<omega>)"
      and "red_exhale ctxt \<omega>\<^sub>0 A \<omega> res" and "res = RNormal \<omega>'"
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
   and \<omega>': "\<omega>' = (if r = Null then \<omega> else update_mh_loc_total_full \<omega> (a, f) (mh (a, f) - Abs_preal p))"
    using exh_if_total_normal[OF IH(5)] exh_if_total_normal_2[OF IH(5)]
    by blast+
  show ?case
    apply standard
    using IH eval_exhale_sat_helper
         apply fastforce+
    using 1
      apply blast
     apply (metis "1" IH.hyps(1) IH.hyps(4) \<omega>' mh_upd_loc_diff minus_preal_gte psub_smaller update_mh_loc_total_full_mh_rel)
    by (metis IH.hyps(1) \<omega>' dec_mh_mp_diff same_mp_diff)
next
  case IH: (ExhAccWildcard mh \<omega> e_r r a f q)
  have 1: "mh (a,f) \<noteq> 0 \<and> r \<noteq> Null"
   and \<omega>': "\<omega>' = update_mh_loc_total_full \<omega> (a, f) (mh (a,f) - q)"
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


end
