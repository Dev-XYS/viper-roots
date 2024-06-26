theory TotalConsistencyProperties
  imports TotalSemanticsCore TotalSemantics
begin


\<comment> \<open>Local variable assignment preserves internal state consistency.\<close>

lemma var_assignment_preserves_internal_consistency:
  assumes "get_total_full \<omega> = \<phi>"
      and "total_heap_consistent \<phi>"
      and "red_stmt_total ctxt R \<Lambda> (LocalAssign x e) \<omega> (RNormal \<omega>')"
      and "get_total_full \<omega>' = \<phi>'"
    shows "total_heap_consistent \<phi>'"
proof -
  obtain v where "\<omega>' = update_var_total \<omega> x v" using assms(3) red_stmt_total.simps by blast
  hence "\<phi> = \<phi>'" using assms(1,4) by force
  thus ?thesis using assms(2) by auto
qed


\<comment> \<open>Unfold statement preserves internal state consistency.\<close>

lemma unfold_preserves_internal_consistency:
  assumes "get_total_full \<omega> = \<phi>"
      and "total_heap_consistent \<phi>"
      and "red_stmt_total ctxt R \<Lambda> (Unfold pred_id e_args (PureExp e_p)) \<omega> (RNormal \<omega>')"
      and "get_total_full \<omega>' = \<phi>'"
    shows "total_heap_consistent \<phi>'"
proof -
  obtain vs p where
    vs: "red_pure_exps_total ctxt (Some \<omega>) e_args \<omega> (Some vs)" and
    p: "ctxt, (Some \<omega>) \<turnstile> \<langle>e_p; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VPerm p)" and
    result: "th_result_rel (p > 0 \<and> p \<le> Rep_preal (get_mp_total_full \<omega> (pred_id, vs))) True {\<omega>'. \<exists>\<phi>'. \<omega>' = \<omega>\<lparr> get_total_full := \<phi>' \<rparr> \<and> unfold_rel ctxt pred_id vs (Abs_preal p) (get_total_full \<omega>) \<phi>'} (RNormal \<omega>')"
    using assms(3) RedUnfold_case by force
  define W' where W': "W' = {\<omega>'. \<exists>\<phi>'. \<omega>' = \<omega>\<lparr> get_total_full := \<phi>' \<rparr> \<and> unfold_rel ctxt pred_id vs (Abs_preal p) (get_total_full \<omega>) \<phi>'}"
  with result have "th_result_rel (p > 0 \<and> p \<le> Rep_preal (get_mp_total_full \<omega> (pred_id, vs))) True W' (RNormal \<omega>')" by blast
  with W' have "\<omega>' \<in> W'" using th_result_rel_normal by blast
  show "total_heap_consistent \<phi>'"
  proof (simp add: total_heap_consistent_def, standard)
    fix n
    from assms(2) have "total_heap_consistent_unfold_n (get_nm_total \<phi>) (Suc n)"
      by (simp add: total_heap_consistent_def)
    moreover have "unfold_rel ctxt pred_id vs (Abs_preal p) (get_total_full \<omega>) \<phi>'"
      using W' \<open>\<omega>' \<in> W'\<close> assms(4) by force
    ultimately show "total_heap_consistent_unfold_n (get_nm_total \<phi>') n"
      by (smt (z3) Abs_preal_inverse UnfoldStep_cases assms(1) get_mp_total.simps get_mp_total_full.simps less_eq_preal.rep_eq less_preal.rep_eq mem_Collect_eq result th_result_rel_normal unfold_rel.cases zero_preal.rep_eq)
  qed
qed


\<comment> \<open>Field assignment preserves internal state consistency.\<close>

lemma field_assignment_preserves_internal_consistency:
  assumes "get_total_full \<omega> = \<phi>"
      and "total_heap_consistent \<phi>"
      and "red_stmt_total ctxt R \<Lambda> (FieldAssign e_r f e) \<omega> (RNormal \<omega>')"
      and "get_total_full \<omega>' = \<phi>'"
    shows "total_heap_consistent \<phi>'"
proof -
  obtain addr v where "ctxt, (Some \<omega>) \<turnstile> \<langle>e_r; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VRef (Address addr))" and
    "\<omega>' = update_hh_loc_total_full \<omega> (addr,f) v"
    using assms(3) red_stmt_total.simps by blast (* This is quite slow. Any better method? *)
  hence "get_nm_total \<phi> = get_nm_total \<phi>'"
    using assms(1,4) by force
  thus ?thesis using assms(2)
    by (simp add: total_heap_consistent_def)
qed


\<comment> \<open>Combinability of fractional resources.\<close>

lemma fraction_combinability:
  assumes "sat ctxt \<phi> mh\<^sub>1 mp\<^sub>1 (syntactic_mult (Rep_preal p) A)"
      and "sat ctxt \<phi> mh\<^sub>2 mp\<^sub>2 (syntactic_mult (Rep_preal q) A)"
      and "mh_split mh mh\<^sub>1 mh\<^sub>2"
      and "mp_split mp mp\<^sub>1 mp\<^sub>2"
  shows "sat ctxt \<phi> mh mp (syntactic_mult (Rep_preal (p + q)) A)"
  oops


\<comment> \<open>A fraction of the mask satisfies the syntactic multiplication of the assertion.\<close>

inductive_cases SatImp_case: "sat ctxt \<omega> mh mp (Imp e A)"

lemma fractionability:
    fixes p q :: preal
    shows "sat ctxt \<omega> mh mp (syntactic_mult (Rep_preal p) A) \<Longrightarrow> sat ctxt \<omega> (field_mask_multiply mh q) (predicate_mask_multiply mp q) (syntactic_mult (Rep_preal (q * p)) A)"
  sorry
(* proof (induct A)
  case (Atomic x)
  then show ?case sorry
next
  case IH: (Imp e A)
  then consider (True) "ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool True)" |
               (False) "ctxt, (Some \<omega>) \<turnstile> \<langle>e; \<omega>\<rangle> [\<Down>]\<^sub>t Val (VBool False)"
    by (smt (verit) assert.sel(2) assert.simps(11) assert.simps(27) assert.simps(33) sat.simps syntactic_mult.simps(4))
    (* Needs a better way *)
  then show ?case
  proof (cases)
    case True
    then show ?thesis sorry
  next
    case False
    then show ?thesis using IH
    proof -
      from IH False have "mh = zero_mh" and "mp = zero_mp"
        sorry
    qed
  qed
next
  case (CondAssert x1a A1 A2)
  then show ?case sorry
next
  case (ImpureAnd A1 A2)
  then show ?case sorry
next
  case (ImpureOr A1 A2)
  then show ?case sorry
next
  case (Star A1 A2)
  then show ?case sorry
next
  case (Wand A1 A2)
  then show ?case sorry
next
  case (ForAll x1a A)
  then show ?case sorry
next
  case (Exists x1a A)
  then show ?case sorry
qed *)


\<comment> \<open>The total state \<phi> we give to \<^const>\<open>sat\<close> does not matter.\<close>

lemma sat_\<phi>_does_not_matter:
  fixes frac :: preal
  assumes "frac > 0"
      and "sat ctxt \<omega> mh mp A"
    shows "sat ctxt (update_nm_total_full \<omega> (nested_mask_multiply (get_nm_total_full \<omega>) frac)) mh mp A"
  sorry


\<comment> \<open>Helper lemmas on \<^const>\<open>nested_mask_multiply\<close>\<close>

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


\<comment> \<open>Other helper lemmas\<close>

lemma total_state_update_nm_read:
  shows "get_nm_total (\<phi>\<lparr> get_nm_total := nm \<rparr>) = nm"
  by simp

\<comment> \<open>A fraction of a consistent total state is external consistent.\<close>

thm consistent_external_wrt_ploc_consistent_external.inducts

lemma fraction_consistent_external':
  fixes frac :: preal
  assumes "0 < frac \<and> frac < 1"
    shows "(consistent_external_wrt_ploc ctxt \<phi> (pred_id,vs) p \<Longrightarrow>
            consistent_external_wrt_ploc ctxt
              (\<phi>\<lparr> get_nm_total := nested_mask_multiply (get_nm_total \<phi>) frac \<rparr>)
              (pred_id,vs) (frac * p))"
      and "(consistent_external ctxt \<phi> \<Longrightarrow>
            consistent_external ctxt
              (\<phi>\<lparr> get_nm_total := nested_mask_multiply (get_nm_total \<phi>) frac \<rparr>))"
proof (induction rule: consistent_external_wrt_ploc_consistent_external.inducts)
  case IH: (SatStep pred_id pred_decl pred_body vs \<phi> p)
  show ?case
    apply (rule SatStep)
       defer 3
    using IH apply blast+
    apply (simp del: field_mask_multiply.simps predicate_mask_multiply.simps)
    apply (rule fractionability)
    using IH sat_\<phi>_does_not_matter assms by fastforce
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
    assume perm: "get_mp_total (\<phi>\<lparr>get_nm_total := nested_mask_multiply (get_nm_total \<phi>) frac\<rparr>) (pred_id,vs) = q"
       and nm': "Some nm' = get_nm_loc_total (\<phi>\<lparr>get_nm_total := nested_mask_multiply (get_nm_total \<phi>) frac\<rparr>) (pred_id,vs)"
    hence "get_mp_total \<phi> (pred_id,vs) = q / frac" using nm_multiply_back
      by (metis assms get_mp_total.simps total_state.simps(2) total_state.surjective total_state.update_convs(2))
    moreover from nm' have "Some nm' = get_nm_loc_nm (nested_mask_multiply (get_nm_total \<phi>) frac) (pred_id,vs)"
      using get_nm_loc_total_multiply by auto
    hence "Some (nested_mask_multiply nm' (1 / frac)) = get_nm_loc_total \<phi> (pred_id,vs)" using nm_multiply_back_nm sorry
    moreover note IH(3)
    ultimately have "consistent_external_wrt_ploc ctxt
                       (\<phi>\<lparr> get_nm_total := nested_mask_multiply (get_nm_total (\<phi>\<lparr> get_nm_total := (nested_mask_multiply nm' (1 / frac)) \<rparr>)) frac \<rparr>)
                       (pred_id,vs) q"
      using perm by force
    moreover have "\<phi>\<lparr> get_nm_total := nested_mask_multiply (get_nm_total (\<phi>\<lparr> get_nm_total := (nested_mask_multiply nm' (1 / frac)) \<rparr>)) frac \<rparr>
                   = \<phi>\<lparr> get_nm_total := nm' \<rparr>"
      by (metis assms mult.commute nm_multiply_back_nm nm_multiply_twice total_state_update_nm_read)
    ultimately show "consistent_external_wrt_ploc ctxt
                       (\<phi>\<lparr> get_nm_total := nested_mask_multiply (get_nm_total \<phi>) frac, get_nm_total := nm' \<rparr>)
                       (pred_id,vs) q"
      by fastforce
  qed
qed

lemma fraction_consistent_external:
    fixes frac :: preal
  assumes "consistent_external_wrt_ploc ctxt \<phi> (pred_id,vs) p"
      and "0 < frac \<and> frac < 1"
      and "nm = nested_mask_multiply (get_nm_total \<phi>) frac"
    shows "consistent_external_wrt_ploc ctxt (update_nm_total \<phi> nm) (pred_id,vs) (p * frac)"
  oops


\<comment> \<open>Unfold statement preserves external state consistency.\<close>

lemma unfold_preserves_external_consistency:
  assumes "consistent_external ctxt \<phi>"
      and "get_total_full \<omega> = \<phi>"
      and "red_stmt_total ctxt R \<Lambda> (Unfold pred_id e_args (PureExp e_p)) \<omega> (RNormal \<omega>')"
      and "get_total_full \<omega>' = \<phi>'"
    shows "consistent_external ctxt \<phi>'"
  oops

end
