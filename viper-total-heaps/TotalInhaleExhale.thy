section \<open>Semantics for Inhale and Exhale\<close>

theory TotalInhaleExhale
  imports ViperCommon.ViperLang ViperCommon.ValueAndBasicState ViperCommon.Binop ViperCommon.DeBruijn ViperCommon.PredicatesUtil
          TotalViperState TotalStateUtil TotalResult TotalExpressions TotalExternalConsistency
begin


subsection \<open>Inhale\<close>

(* The general question is, if we put consistent checks inside inhale or inside statement reduction. *)

definition inhale_perm_single :: "'a full_total_state \<Rightarrow> heap_loc \<Rightarrow> preal option \<Rightarrow> 'a full_total_state set"
  where "inhale_perm_single \<omega> lh p_opt =
    { \<omega>'| \<omega>' q.
            option_fold ((=) q) (q \<noteq> 0) p_opt \<and>
            get_mh_total_full \<omega> lh + q \<le> 1 \<and>  \<comment> \<open>There can be at most 1 field permission\<close>
               \<comment> \<open>Do we really need the check here? Or it is covered in consistency?\<close>
            \<omega>' = update_mh_loc_total_full \<omega> lh (get_mh_total_full \<omega> lh + q)
    }"

definition inhale_perm_single_pred :: "'a total_context \<Rightarrow> 'a full_total_state \<Rightarrow> 'a predicate_loc \<Rightarrow> preal option \<Rightarrow> 'a full_total_state set"
  where "inhale_perm_single_pred ctxt \<omega> lp p_opt =
    { \<omega>'| \<omega>' \<phi>_inh q.
            option_fold ((=) q) (q \<noteq> 0) p_opt \<and>
            consistent_external_wrt_ploc ctxt \<phi>_inh lp q \<and>
            get_hh_total \<phi>_inh = get_hh_total_full \<omega> \<and>
            \<omega>' = add_to_nm_loc_total_full (update_mp_loc_total_full \<omega> lp (get_mp_total_full \<omega> lp + q)) lp (get_nm_total \<phi>_inh)
    }"

inductive red_inhale :: "'a total_context \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> 'a result_total \<Rightarrow> bool" where
\<comment>\<open>Atomic inhale\<close>
  InhAcc:
  "\<lbrakk> ctxt, Some \<omega> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
     ctxt, Some \<omega> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p);
     W' = (if r = Null then {\<omega>} else inhale_perm_single \<omega> (the_address r,f) (Some (Abs_preal p)));
     th_result_rel (p \<ge> 0) (W' \<noteq> {} \<and> (p > 0 \<longrightarrow> r \<noteq> Null)) W' res
   \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (Atomic (Acc e_r f (PureExp e_p))) \<omega> res"
| InhAccPred:
  "\<lbrakk> red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some v_args);
     ctxt, Some \<omega> \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p);
     W' = inhale_perm_single_pred ctxt \<omega> (pred_id, v_args) (Some (Abs_preal p));
     th_result_rel (p \<ge> 0) (W' \<noteq> {}) W' res
   \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega> res"
| InhAccWildcard:
  "\<lbrakk> ctxt, Some \<omega> \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
     W' = inhale_perm_single \<omega> (the_address r,f) None;
     th_result_rel True (W' \<noteq> {} \<and> r \<noteq> Null) W' res
   \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (Atomic (Acc e_r f Wildcard)) \<omega> res"
| InhAccPredWildcard:
  "\<lbrakk> red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some v_args);
     W' = inhale_perm_single_pred ctxt \<omega> (pred_id, v_args) None;
     th_result_rel True (W' \<noteq> {}) W' res
   \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (Atomic (AccPredicate pred_id e_args Wildcard)) \<omega> res"
| InhPure:
  "\<lbrakk> ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool b) \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (Atomic (Pure e)) \<omega> (if b then RNormal \<omega> else RMagic)"

\<comment>\<open>Connectives inhale\<close>
| InhStarNormal:
  "\<lbrakk> red_inhale ctxt A \<omega> (RNormal \<omega>'');
     red_inhale ctxt B \<omega>'' res
   \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (A && B) \<omega> res"
| InhStarFailureMagic:
  "\<lbrakk> red_inhale ctxt A \<omega> resA;
     resA = RFailure \<or> resA = RMagic
   \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (A && B) \<omega> resA"
| InhImpTrue:
  "\<lbrakk> ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool True));
     red_inhale ctxt A \<omega> res
   \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (Imp e A) \<omega> res"
| InhImpFalse:
  "\<lbrakk> ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (Imp e A) \<omega> (RNormal \<omega>)"
| InhCondAssertTrue:
  "\<lbrakk> ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t (Val (VBool True));
     red_inhale ctxt A \<omega> res
   \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (CondAssert e A B) \<omega> res"
| InhCondAssertFalse:
  "\<lbrakk> ctxt, Some \<omega> \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False);
     red_inhale ctxt B \<omega> res
   \<rbrakk> \<Longrightarrow>
   red_inhale ctxt (CondAssert e A B) \<omega> res"

\<comment>\<open>If a \<^emph>\<open>direct\<close> subexpression is not well-defined, then this results in failure.\<close>
| InhSubExpFailure:
  "\<lbrakk> (direct_sub_expressions_assertion A) \<noteq> [];
     red_pure_exps_total ctxt (Some \<omega>) (direct_sub_expressions_assertion A) \<omega> None
   \<rbrakk> \<Longrightarrow>
   red_inhale ctxt A \<omega> RFailure"


subsection \<open>Exhale\<close>

fun exh_if_total :: "bool \<Rightarrow> 'a full_total_state \<Rightarrow> 'a result_total" where
  "exh_if_total False _ = RFailure"
| "exh_if_total True \<omega> = RNormal \<omega>"

definition exhale_pred :: "'a full_total_state \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> 'a full_total_state" where
  "exhale_pred \<omega> ploc p = (let perm = get_mp_total_full \<omega> ploc in
     mult_nm_loc_total_full (update_mp_loc_total_full \<omega> ploc (perm - p)) ploc ((perm - p) / perm))"

inductive red_exhale :: "'a total_context \<Rightarrow> 'a full_total_state \<Rightarrow> assertion \<Rightarrow> 'a full_total_state \<Rightarrow> 'a result_total \<Rightarrow> bool"
  for ctxt :: "'a total_context" and \<omega>0 :: "'a full_total_state" where

\<comment>\<open>exhale acc(e.f, p)\<close>
  ExhAcc:
  "\<lbrakk> mh = get_mh_total_full \<omega>;
     ctxt, (Some \<omega>0) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
     ctxt, (Some \<omega>0) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p);
     a = the_address r
   \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (Atomic (Acc e_r f (PureExp e_p))) \<omega>
     (exh_if_total (p \<ge> 0 \<and> (if r = Null then p = 0 else mh (a,f) \<ge> Abs_preal p))
                   (if r = Null then \<omega> else update_mh_loc_total_full \<omega> (a,f) ((mh (a,f)) - (Abs_preal p))))"

\<comment>\<open>Exhaling wildcard removes some non-zero permission that is less than the current permission held.\<close>
| ExhAccWildcard:
  "\<lbrakk> mh = get_mh_total_full \<omega>;
     ctxt, (Some \<omega>0) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
     a = the_address r;
     \<comment>\<open>\<^term>\<open>q\<close> satisfies the right-hand side if \<^prop>\<open>mh (a,f) \<noteq> 0\<close> (thm prat_exists_stricly_smaller_nonzero).
     If \<^prop>\<open>mh (a,f) \<noteq> 0\<close> does not hold, then the exhale fails and the value of q is irrelevant. \<close>
     mh (a,f) \<noteq> 0 \<and> r \<noteq> Null \<Longrightarrow> q > 0 \<and> mh (a,f) > q
   \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (Atomic (Acc e_r f Wildcard)) \<omega>
     (exh_if_total (mh (a,f) \<noteq> 0 \<and> r \<noteq> Null)
                   (update_mh_loc_total_full \<omega> (a,f) (mh (a,f) - q)))"

\<comment>\<open>exhale acc(P(es), p)\<close>
\<comment> \<open>TODO: remove the corresponding fraction of the nested mask when exhaling a predicate\<close>
| ExhAccPred:
  "\<lbrakk> mp = get_mp_total_full \<omega>;
     red_pure_exps_total ctxt (Some \<omega>0) e_args \<omega> (Some v_args);
     ctxt, (Some \<omega>0) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)
   \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (Atomic (AccPredicate pred_id e_args (PureExp e_p))) \<omega>
     (exh_if_total (p \<ge> 0 \<and> mp (pred_id, v_args) \<ge> Abs_preal p)
                   (exhale_pred \<omega> (pred_id, v_args) (Abs_preal p)))"
| ExhAccPredWildcard:
  "\<lbrakk> mp = get_mp_total_full \<omega>;
     red_pure_exps_total ctxt (Some \<omega>0) e_args \<omega> (Some v_args);
     \<comment>\<open>q satisfies the right-hand side if \<^prop>\<open>mp (pred_id, v_args) \<noteq> 0\<close> (thm prat_exists_strictly_smaller_nonzero).
     If \<^prop>\<open>mp (pred_id, v_args) \<noteq> 0\<close> does not hold, then the exhale fails and the value of q is irrelevant.\<close>
     mp (pred_id, v_args) \<noteq> 0 \<Longrightarrow> q > 0 \<and> mp (pred_id, v_args) > q
   \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (Atomic (AccPredicate pred_id e_args Wildcard)) \<omega>
     (exh_if_total (mp (pred_id, v_args) \<noteq> 0)
                   (exhale_pred \<omega> (pred_id, v_args) q))"

| ExhPure:
  "\<lbrakk> ctxt, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool b) \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (Atomic (Pure e)) \<omega> (exh_if_total b \<omega>)"

\<comment>\<open>exhale A && B\<close>
| ExhStarNormal:
  "\<lbrakk> red_exhale ctxt \<omega>0 A \<omega> (RNormal \<omega>');
     red_exhale ctxt \<omega>0 B \<omega>' res
   \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (A && B) \<omega> res"
| ExhStarFailure:
  "\<lbrakk> red_exhale ctxt \<omega>0 A \<omega> RFailure \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (A && B) \<omega> RFailure"

\<comment>\<open>exhale A \<longrightarrow> B\<close>
| ExhImpTrue:
  "\<lbrakk> ctxt, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True);
     red_exhale ctxt \<omega>0 A \<omega> res
   \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (Imp e A) \<omega> res"
| ExhImpFalse:
  "\<lbrakk> ctxt, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False) \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (Imp e A) \<omega> (RNormal \<omega>)"

\<comment>\<open>exhale e ? A : B\<close>
| ExhCondTrue:
  "\<lbrakk> ctxt, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True);
     red_exhale ctxt \<omega>0 A \<omega> res
   \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (CondAssert e A B) \<omega> res"
| ExhCondFalse:
  "\<lbrakk> ctxt, (Some \<omega>0) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False);
     red_exhale ctxt \<omega>0 B \<omega> res
   \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 (CondAssert e A B) \<omega> res"

\<comment>\<open>If a \<^emph>\<open>direct\<close> subexpression is not well-defined, then this results in failure.\<close>
| ExhSubExpFailure:
  "\<lbrakk> direct_sub_expressions_assertion A \<noteq> [];
     red_pure_exps_total ctxt (Some \<omega>0) (direct_sub_expressions_assertion A) \<omega> None
   \<rbrakk> \<Longrightarrow>
   red_exhale ctxt \<omega>0 A \<omega> RFailure"


inductive_cases ExhStar_case: "red_exhale ctxt \<omega>0 (A && B) m_pm res"


end
