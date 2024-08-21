section \<open>External Consistency\<close>

theory TotalExternalConsistency
  imports ViperCommon.ViperLang
          TotalContext TotalStateUtil TotalExpressions
begin


subsection \<open>Satisfiability\<close>

fun proportional_split :: "'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> bool" where
  "proportional_split \<omega> \<omega>\<^sub>1 \<omega>\<^sub>2 = ((\<forall>l. get_mh_total_full \<omega>\<^sub>1 l + get_mh_total_full \<omega>\<^sub>2 l = get_mh_total_full \<omega> l) \<and>
    (\<forall>pl. get_mp_total_full \<omega>\<^sub>1 pl + get_mp_total_full \<omega>\<^sub>2 pl = get_mp_total_full \<omega> pl \<and>
      get_nm_loc_total_full \<omega>\<^sub>1 pl = nested_mask_multiply_option (get_nm_loc_total_full \<omega> pl)
        (get_mp_total_full \<omega>\<^sub>1 pl / get_mp_total_full \<omega> pl) \<and>
      get_nm_loc_total_full \<omega>\<^sub>2 pl = nested_mask_multiply_option (get_nm_loc_total_full \<omega> pl)
        (get_mp_total_full \<omega>\<^sub>2 pl / get_mp_total_full \<omega> pl)))"

fun mh_split :: "field_mask \<Rightarrow> field_mask \<Rightarrow> field_mask \<Rightarrow> bool" where
  "mh_split mh mh\<^sub>1 mh\<^sub>2 = (mh = (mh\<^sub>1 +\<lbrakk>(+)\<rbrakk>+ mh\<^sub>2))"

fun mp_split :: "'a predicate_mask \<Rightarrow> 'a predicate_mask \<Rightarrow> 'a predicate_mask \<Rightarrow> bool" where
  "mp_split mp mp\<^sub>1 mp\<^sub>2 = (mp = (mp\<^sub>1 +\<lbrakk>(+)\<rbrakk>+ mp\<^sub>2))"

inductive sat :: "'a total_context \<Rightarrow> 'a full_total_state \<Rightarrow> field_mask \<Rightarrow> 'a predicate_mask \<Rightarrow> assertion \<Rightarrow> bool"
  for ctxt :: "'a total_context" where

\<comment>\<open>sat acc(e.f, p)
  The mask must have exactly p amount of permission.\<close>
  SatAcc:
  "\<lbrakk> ctxt, None \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
     ctxt, None \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p);
     a = the_address r;
     p \<ge> 0;
     if r = Null then p = 0 else mh = singleton_mh (a,f) (Abs_preal p);
     mp = zero_mp
   \<rbrakk> \<Longrightarrow>
   sat ctxt \<omega> mh mp (Atomic (Acc e_r f (PureExp e_p)))"

\<comment>\<open>A wildcard permission accepts any positive amount of permission.\<close>
| SatAccWildcard:
  "\<lbrakk> ctxt, None \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef r);
     a = the_address r;
     \<comment>\<open>\<^term>\<open>q\<close> satisfies the right-hand side if \<^prop>\<open>mh (a,f) \<noteq> 0\<close> (thm prat_exists_stricly_smaller_nonzero).
     If \<^prop>\<open>mh (a,f) \<noteq> 0\<close> does not hold, then the exhale fails and the value of q is irrelevant. \<close>
     r \<noteq> Null;
     is_singleton_mh (a,f) mh;
     mp = zero_mp
   \<rbrakk> \<Longrightarrow>
   sat ctxt \<omega> mh mp (Atomic (Acc e_r f Wildcard))"

\<comment>\<open>sat acc(P(es), p)\<close>
| SatAccPred:
  "\<lbrakk> red_pure_exps_total ctxt None e_args \<omega> (Some v_args);
     ctxt, None \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p);
     p \<ge> 0;
     mh = zero_mh;
     mp = singleton_mp (pred_id,v_args) (Abs_preal p)
   \<rbrakk> \<Longrightarrow>
   sat ctxt \<omega> mh mp (Atomic (AccPredicate pred_id e_args (PureExp e_p)))"

| SatAccPredWildcard:
  "\<lbrakk> red_pure_exps_total ctxt None e_args \<omega> (Some v_args);
     mh = zero_mh;
     is_singleton_mp (pred_id,v_args) mp
   \<rbrakk> \<Longrightarrow>
   sat ctxt \<omega> mh mp (Atomic (AccPredicate pred_id e_args Wildcard))"

| SatPure:
  "\<lbrakk> ctxt, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True);
     mh = zero_mh;
     mp = zero_mp
   \<rbrakk> \<Longrightarrow>
   sat ctxt \<omega> mh mp (Atomic (Pure e))"

\<comment>\<open>sat A && B\<close>
| SatStar:
  "\<lbrakk> mh_split mh mh\<^sub>1 mh\<^sub>2;
     mp_split mp mp\<^sub>1 mp\<^sub>2;
     sat ctxt \<omega> mh\<^sub>1 mp\<^sub>1 A;
     sat ctxt \<omega> mh\<^sub>2 mp\<^sub>2 B
   \<rbrakk> \<Longrightarrow>
   sat ctxt \<omega> mh mp (A && B)"

\<comment>\<open>sat A \<longrightarrow> B\<close>
| SatImpTrue:
  "\<lbrakk> ctxt, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True);
     sat ctxt \<omega> mh mp A
   \<rbrakk> \<Longrightarrow>
   sat ctxt \<omega> mh mp (Imp e A)"
| SatImpFalse:
  "\<lbrakk> ctxt, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False);
     mh = zero_mh;
     mp = zero_mp
   \<rbrakk> \<Longrightarrow>
   sat ctxt \<omega> mh mp (Imp e A)"

\<comment>\<open>sat e ? A : B\<close>
| SatCondTrue:
  "\<lbrakk> ctxt, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True);
     sat ctxt \<omega> mh mp A
   \<rbrakk> \<Longrightarrow>
   sat ctxt \<omega> mh mp (CondAssert e A B)"
| SatCondFalse:
  "\<lbrakk> ctxt, None \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False);
     sat ctxt \<omega> mh mp B
   \<rbrakk> \<Longrightarrow>
   sat ctxt \<omega> mh mp (CondAssert e A B)"


inductive_cases SatAtomic_case: "sat ctxt \<omega> mh mp (Atomic x)"
inductive_cases SatAcc_case: "sat ctxt \<omega> mh mp (Atomic (Acc e_r f (PureExp e_p)))"
inductive_cases SatAccWildcard_case: "sat ctxt \<omega> mh mp (Atomic (Acc e_r f Wildcard))"
inductive_cases SatAccPred_case: "sat ctxt \<omega> mh mp (Atomic (AccPredicate pred_id e_args (PureExp e_p)))"
inductive_cases SatAccPredWildcard_case: "sat ctxt \<omega> mh mp (Atomic (AccPredicate pred_id e_args Wildcard))"
inductive_cases SatImp_case: "sat ctxt \<omega> mh mp (Imp e A)"
inductive_cases SatCond_case: "sat ctxt \<omega> mh mp (CondAssert e A B)"
inductive_cases SatImpureAnd_case: "sat ctxt \<omega> mh mp (ImpureAnd A B)"
inductive_cases SatImpureOr_case: "sat ctxt \<omega> mh mp (ImpureOr A B)"
inductive_cases SatWand_case: "sat ctxt \<omega> mh mp (A --* B)"
inductive_cases SatForAll_case: "sat ctxt \<omega> mh mp (ForAll ty A)"
inductive_cases SatExists_case: "sat ctxt \<omega> mh mp (Exists ty A)"
inductive_cases SatStar_case: "sat ctxt \<omega> mh mp (A && B)"


subsection \<open>External Consistency\<close>

inductive consistent_external_wrt_ploc :: "'a total_context \<Rightarrow> 'a total_state \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> bool" and
          consistent_external :: "'a total_context \<Rightarrow> 'a total_state \<Rightarrow> bool"
          for ctxt :: "'a total_context" where
  SatStep:
  "\<lbrakk> ViperLang.predicates (program_total ctxt) pred_id = Some pred_decl;
     ViperLang.predicate_decl.body pred_decl = Some pred_body;
     sat ctxt
         \<lparr> get_store_total = nth_option vs, get_trace_total = Map.empty, get_total_full = \<phi>\<lparr> get_nm_total := empty_nm \<rparr> \<rparr>
         (get_mh_total \<phi>) (get_mp_total \<phi>)
         (syntactic_mult (Rep_preal p) pred_body);
     consistent_external ctxt \<phi>;
     p > 0
   \<rbrakk> \<Longrightarrow>
   consistent_external_wrt_ploc ctxt \<phi> (pred_id,vs) p"
| SatAll:
  "\<lbrakk> \<And>pred_id vs q. get_mp_total \<phi> (pred_id,vs) = q \<Longrightarrow> (q = 0) = (get_nm_loc_total \<phi> (pred_id,vs) = None);
     \<And>pred_id vs q nm'. get_mp_total \<phi> (pred_id,vs) = q \<Longrightarrow>
       Some nm' = get_nm_loc_total \<phi> (pred_id,vs) \<Longrightarrow>
       consistent_external_wrt_ploc ctxt (\<phi>\<lparr> get_nm_total := nm' \<rparr>) (pred_id,vs) q
   \<rbrakk> \<Longrightarrow>
   consistent_external ctxt \<phi>"

inductive_cases SatStep_case: "consistent_external_wrt_ploc ctxt \<phi> (pred_id,vs) p"
inductive_cases SatAll_case: "consistent_external ctxt \<phi>"

\<comment> \<open>Using inductive might be better than using a function.
    The generated @{thm consistent_external_wrt_ploc.simps} is equivalent to the function definition below.
    And the inductive definition gives us more?
    Question: How does the inductive definition prove termination? Or does it even prove it?
    "\<not> P \<Longrightarrow> P" is not accepted as a valid inductive definition.
    "\<not> P n \<Longrightarrow> P (Suc n) is also not accepted as a valid inductive definition. \<close>


end
