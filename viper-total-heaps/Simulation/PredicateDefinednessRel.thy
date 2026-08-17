theory PredicateDefinednessRel
  imports ViperBoogieEndToEnd TotalViperSemantics.TotalFramingIndep
    TotalViperSemantics.SyntacticMultVarBridge
begin

text \<open>Scaling by a positive literal fraction does not change which variables an assertion reads.
  Positivity matters: for a negative factor \<open>real_mult_permexpr\<close> maps \<open>Wildcard\<close> to \<open>undefined\<close>.\<close>
lemma free_var_atomic_assert_real_mult_permexpr:
  assumes "0 < p"
  shows "free_var_atomic_assert (Acc e_r f (real_mult_permexpr p e_p)) =
           free_var_atomic_assert (Acc e_r f e_p)"
    and "free_var_atomic_assert (AccPredicate pid es (real_mult_permexpr p e_p)) =
           free_var_atomic_assert (AccPredicate pid es e_p)"
  using assms by (cases e_p; simp)+

text \<open>A supported assertion has no wildcard/predicate accesses, so scaling only rewrites the
  \<open>PureExp\<close> permission amounts and preserves supportedness.\<close>
lemma supported_atomic_assert_real_mult_permexpr:
  assumes "supported_atomic_assert (Acc e_r f e_p)"
      and "atomic_assert_pred_rec not_supported_exp_no_rec (Acc e_r f e_p)"
    shows "supported_atomic_assert (Acc e_r f (real_mult_permexpr p e_p)) \<and>
           atomic_assert_pred_rec not_supported_exp_no_rec (Acc e_r f (real_mult_permexpr p e_p))"
  using assms by (cases e_p; simp add: real_to_expr.simps)

lemma syntactic_mult_supported_assertion:
  assumes "supported_assertion A"
  shows "supported_assertion (syntactic_mult p A)"
  using assms
  by (induction A rule: syntactic_mult.induct)
     (auto dest: supported_atomic_assert_real_mult_permexpr)

lemma free_var_assertion_syntactic_mult:
  assumes "0 < p"
  shows "free_var_assertion (syntactic_mult p A) = free_var_assertion A"
  using assms
  by (induction A rule: syntactic_mult.induct)
     (simp_all add: free_var_atomic_assert_real_mult_permexpr)

text \<open>Steps through the \<open>assume definednessPerm > 0\<close> that ends a definedness check's fixed prefix.
  The assumed condition is not proved from anything on the Viper side: it is exactly the \<open>Success\<close>
  relation's own constraint, so the states where it fails are the ones \<open>Success\<close> already excludes
  (there the assume goes to \<^const>\<open>Magic\<close>). The fraction stays existentially bound.\<close>
lemma rel_general_assume_perm_pos:
  assumes StoreRel: "\<And>\<omega> ns. R0 \<omega> ns \<Longrightarrow> store_rel A (var_context ctxt) var_tr \<omega> ns"
      and VarTr: "var_tr n = Some var_bpl"
      \<comment>\<open>Boogie's \<open>0.0\<close> literal parses as \<open>0 / 10\<close>, so do not demand the numeral \<open>0\<close> syntactically\<close>
      and ZeroEq: "zero_lit = (0::real)"
      and Rel: "rel_general R0 R1
                  (\<lambda>\<omega> \<omega>'. \<omega>' = \<omega> \<and> (\<exists>q. get_store_total \<omega> n = Some (VPerm q) \<and> 0 < q))
                  (\<lambda>_. False) P ctxt (BigBlock name cs str tr, cont) \<gamma>'"
    shows "rel_general R0 R1
             (\<lambda>\<omega> \<omega>'. \<omega>' = \<omega> \<and> (\<exists>q. get_store_total \<omega> n = Some (VPerm q) \<and> 0 < q))
             (\<lambda>_. False) P ctxt
             (BigBlock name (Lang.Assume (expr.Var var_bpl \<guillemotleft>Lang.binop.Gt\<guillemotright> Lit (LReal zero_lit)) # cs) str tr, cont)
             \<gamma>'"
  unfolding ZeroEq
proof (rule rel_propagate_pre_assume[OF _ Rel])
  fix \<omega> ns \<omega>'
  assume R0Holds: "R0 \<omega> ns"
     and "(\<omega>' = \<omega> \<and> (\<exists>q. get_store_total \<omega> n = Some (VPerm q) \<and> 0 < q)) \<or> False"
  then obtain q where StoreVal: "get_store_total \<omega> n = Some (VPerm q)" and PermPos: "0 < q"
    by blast
  from StoreRel[OF R0Holds] VarTr StoreVal
  have Lookup: "lookup_var (var_context ctxt) ns var_bpl = Some (RealV q)"
    using store_rel_var_rel by (metis option.inject val_rel_vpr_bpl.simps(5))
  show "red_expr_bpl ctxt (expr.Var var_bpl \<guillemotleft>Lang.binop.Gt\<guillemotright> Lit (LReal 0)) ns (BoolV True) \<and> True"
    using PermPos
    by (auto intro!: RedBinOp RedVar[OF Lookup] RedLit simp: binop_eval.simps)
qed

text \<open>Analogue of @{thm [source] end_to_end_vpr_method_correct_partial} for a predicate's
  \<open>#definedness\<close> check procedure. Its Boogie body starts with a fixed prefix -- zero the mask,
  assume the state is good, assume the fresh permission-scaling local is positive -- and only the
  commands after that prefix encode \<^term>\<open>Inhale (var_mult n pbody)\<close>. Given that the Boogie
  procedure verifies, the predicate's body is self-framing.

  No fraction appears as a variable of this lemma: the scaling amount is whatever the Viper store
  happens to hold at \<open>n\<close>, existentially bound in the \<open>Success\<close> relation of \<open>InitRel\<close> (states where
  it is not positive send the last assume to \<^const>\<open>Magic\<close>, so nothing is required of them), and
  universally bound inside the \<^const>\<open>assertion_self_framing\<close> conclusion.\<close>

lemma predicate_definedness_check_correct:
  assumes Boogie_correct: "proc_is_correct (vbpl_absval_ty (TyRep :: 'a ty_repr_bpl)) fun_decls constants unique_consts global_vars axioms (proc_bpl :: ast procedure)
                  (Ast.proc_body_satisfies_spec :: (('a vbpl_absval, ast) proc_body_satisfies_spec_ty))"
      and WfTyRep: "wf_ty_repr_bpl TyRep"
      and WfConsistency: "wf_total_consistency ctxt_vpr StateCons StateCons_t"
      and DomainType: "domain_type TyRep = absval_interp_total ctxt_vpr"

\<comment>\<open>Viper properties\<close>
      and SupPred: "supported_pred_body pbody"
      and SupAssertion: "supported_assertion pbody"
\<comment>\<open>needed to lift framing from the empty state to an arbitrary state, see
   @{thm [source] assertion_self_framing_of_empty_state}\<close>
      and NoUnfolding: "no_unfolding_assertion pbody"
      and ConsMono: "mono_prop_downward_ord StateCons"
      and OnlyArgsInBody: "\<And>x. x \<in> free_var_assertion pbody \<Longrightarrow> x < length tys"
      and LambdaEq: "\<Lambda> = nth_option (tys @ [TPerm])"
      and NEq: "n = length tys"

\<comment>\<open>Boogie properties\<close>
      and FunInterp: "fun_interp_wf (vbpl_absval_ty TyRep) fun_decls (fun_interp ctxt)"
      and TypeInterpEq: "type_interp ctxt = vbpl_absval_ty TyRep"
      and RtypeInterpEmpty: "rtype_interp ctxt = []"
      and VarCtxtEq: "var_context ctxt = (constants @ global_vars, proc_args proc_bpl @ locals_bpl @ proc_rets proc_bpl)"
      and ProcPresEmpty: "proc_pres proc_bpl = []"
      and ProcTyArgsEmpty: "proc_ty_args proc_bpl = 0"
      and ProcBodySome: "proc_body proc_bpl = Some (locals_bpl, proc_body_bpl)"

\<comment>\<open>the fixed prefix of a definedness check's Boogie body: zero the mask, assume the state is good,
   assume the fresh permission-scaling local is positive\<close>
      and ProcBodyStart:
            "convert_ast_to_program_point proc_body_bpl =
               (BigBlock name (Assign mvar e_zero_mask #
                               Assume e_good_state #
                               Assume (Lang.Var perm_var_bpl \<guillemotleft>Lang.binop.Gt\<guillemotright> Lit (LReal 0)) #
                               cs) str tr_bpl, cont)"

\<comment>\<open>predicate rel: the fixed prefix of a definedness check is simulated, and the commands after it
   encode the (variable-scaled) inhale of the predicate body\<close>
\<comment>\<open>A single premise, like @{term method_rel} in @{thm [source] end_to_end_vpr_method_correct_partial}:
   the intermediate configuration (where the prefix ends and the inhale's encoding begins) is
   existentially bound, and obtained inside this proof. Stating it as two separate premises would
   force the caller to name that configuration explicitly.\<close>
\<comment>\<open>One premise rather than two, so that the configuration between them -- where the prefix ends and
   the inhale's encoding begins -- is shared. The generated relational proof discharges this with a
   single `rule`, which keeps `\<gamma>0` consistent across both conjuncts.\<close>
      and PredicateRel: "rel_general (state_rel_empty (state_rel_well_def_same ctxt (program_total ctxt_vpr) StateCons (TyRep :: 'a ty_repr_bpl) Tr AuxPred)) R1
               (\<lambda>\<omega> \<omega>'. \<omega>' = \<omega> \<and> (\<exists>q. get_store_total \<omega> n = Some (VPerm q) \<and> 0 < q))
               (\<lambda>_. False)
               proc_body_bpl ctxt
               (convert_ast_to_program_point proc_body_bpl)
               \<gamma>0
             \<and> stmt_rel R1 R2 ctxt_vpr StateCons \<Lambda> proc_body_bpl ctxt
               (Inhale (var_mult n pbody)) \<gamma>0 \<gamma>1"

\<comment>\<open>construct initial state\<close>
      and InitialStateRel: "\<And>\<omega>.
                       vpr_store_well_typed (absval_interp_total ctxt_vpr) \<Lambda> (get_store_total \<omega>) \<Longrightarrow>
                       total_heap_well_typed (program_total ctxt_vpr) (absval_interp_total ctxt_vpr) (get_hh_total_full \<omega>) \<Longrightarrow>
                       is_empty_total_full \<omega> \<Longrightarrow>
                       StateCons \<omega> \<Longrightarrow>
                       \<exists>ns ls gs.
                           ns = \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> \<and>
\<comment>\<open>as in @{thm [source] end_to_end_vpr_method_correct_partial}, the well-typedness of the Boogie
   state follows from the state relation and is therefore not required here\<close>
                           (state_rel_empty (state_rel_well_def_same ctxt (program_total ctxt_vpr) StateCons (TyRep :: 'a ty_repr_bpl) Tr AuxPred)) \<omega> ns \<and>
                           unique_constants_distinct gs unique_consts \<and>
                           axioms_sat (vbpl_absval_ty TyRep) (constants, []) (fun_interp ctxt) (global_to_nstate (state_restriction gs constants)) axioms"
    shows "assertion_self_framing ctxt_vpr StateCons pbody tys"
proof (rule assertion_self_framing_of_empty_state[OF SupPred NoUnfolding ConsMono])
  fix vs and p :: real and tr hh
  assume WtVs: "vals_well_typed (absval_interp_total ctxt_vpr) vs tys"
     and PermPos: "0 < p"
     and HeapWt: "total_heap_well_typed (program_total ctxt_vpr) (absval_interp_total ctxt_vpr) hh"
     and ConsPlain: "StateCons \<lparr> get_store_total = nth_option vs, get_trace_total = tr,
                                 get_total_full = \<lparr> get_hh_total = hh, get_nm_total = 0 \<rparr> \<rparr>"

  let ?\<omega>p = "\<lparr> get_store_total = nth_option (vs @ [VPerm p]), get_trace_total = tr,
               get_total_full = \<lparr> get_hh_total = hh, get_nm_total = 0 \<rparr> \<rparr>"
  let ?\<omega> = "\<lparr> get_store_total = nth_option vs, get_trace_total = tr,
              get_total_full = \<lparr> get_hh_total = hh, get_nm_total = 0 \<rparr> \<rparr>"

  have LenVs: "length vs = length tys"
    using WtVs vals_well_typed_same_lengthD by blast

  have StoreN: "get_store_total ?\<omega>p n = Some (VPerm p)"
    using NEq LenVs by (simp add: nth_append)

  have StoreWt: "vpr_store_well_typed (absval_interp_total ctxt_vpr) \<Lambda> (get_store_total ?\<omega>p)"
    unfolding LambdaEq vpr_store_well_typed_def
  proof (rule allI | rule impI)+
    fix x t
    assume "nth_option (tys @ [TPerm]) x = Some t"
    hence XLt: "x < length tys + 1" and TEq: "(tys @ [TPerm]) ! x = t"
      by (auto split: if_splits)
    show "map_option (\<lambda>v. get_type (absval_interp_total ctxt_vpr) v)
            (get_store_total ?\<omega>p x) = Some t"
    proof (cases "x < length tys")
      case True
      hence "(vs @ [VPerm p]) ! x = vs ! x" and "(tys @ [TPerm]) ! x = tys ! x"
        using LenVs by (auto simp: nth_append)
      moreover have "tys ! x = get_type (absval_interp_total ctxt_vpr) (vs ! x)"
        using WtVs True LenVs unfolding vals_well_typed_def by (metis nth_map)
      ultimately show ?thesis
        using True TEq LenVs by simp
    next
      case False
      hence "x = length tys" using XLt by simp
      thus ?thesis
        using TEq LenVs by (simp add: nth_append)
    qed
  qed

  have Empty: "is_empty_total_full ?\<omega>p"
    by (simp add: is_empty_total_full_def is_empty_total_def)

  text \<open>Consistency depends only on the heap/mask and the trace, not on the store
    (see @{thm [source] wf_total_consistency_def}), so it transfers from the plain state.\<close>
  have ConsIff: "\<And>\<omega> :: 'a full_total_state. StateCons \<omega> \<longleftrightarrow>
        (StateCons_t (get_total_full \<omega>) \<and>
         (\<forall>lbl \<phi>. get_trace_total \<omega> lbl = Some \<phi> \<longrightarrow> StateCons_t \<phi>))"
    using WfConsistency unfolding wf_total_consistency_def by blast
  have Cons: "StateCons ?\<omega>p"
    using ConsPlain ConsIff[of ?\<omega>p] ConsIff[of ?\<omega>] by simp

  from InitialStateRel[OF StoreWt _ Empty Cons] HeapWt
  obtain ns ls gs where
    NsEq: "ns = \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr>" and
    StateRelInitial: "(state_rel_empty (state_rel_well_def_same ctxt (program_total ctxt_vpr) StateCons (TyRep :: 'a ty_repr_bpl) Tr AuxPred)) ?\<omega>p ns" and
    UniqueConstants: "unique_constants_distinct gs unique_consts" and
    AxiomsSat: "axioms_sat (vbpl_absval_ty TyRep) (constants, []) (fun_interp ctxt) (global_to_nstate (state_restriction gs constants)) axioms"
    by auto

  from StateRelInitial
  have StateRel: "state_rel (program_total ctxt_vpr) StateCons TyRep Tr AuxPred ctxt ?\<omega>p ?\<omega>p ns"
    by (simp add: state_rel_empty_def)

  have
    GlobalsWf: "state_typ_wf (vbpl_absval_ty TyRep) [] gs (constants @ global_vars)" and
    LocalsWf: "state_typ_wf (vbpl_absval_ty TyRep) [] ls (proc_args proc_bpl @ locals_bpl @ proc_rets proc_bpl)"
    using state_rel_state_well_typed[OF StateRel] NsEq VarCtxtEq TypeInterpEq
    unfolding state_well_typed_def
    by auto

  let ?abs = "vbpl_absval_ty TyRep"

  have ProcBodyBplCorrect:
      "(Ast.proc_body_satisfies_spec :: (('a vbpl_absval, ast) proc_body_satisfies_spec_ty)) ?abs [] (constants@global_vars, (proc_args proc_bpl)@(locals_bpl@(proc_rets proc_bpl))) (fun_interp ctxt) []
                                       (proc_all_pres proc_bpl) (proc_checked_posts proc_bpl) proc_body_bpl
                                       \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr>"
  proof (rule proc_is_correct_elim[OF Boogie_correct ProcBodySome])
    show "\<forall>t. closed t \<longrightarrow> (\<exists>v. type_of_vbpl_val TyRep v = t)"
      by (simp add: closed_types_inhabited)
  next
    show "\<forall>v. closed (type_of_vbpl_val TyRep v)"
    proof (rule allI)
      fix v
      show "closed (type_of_vbpl_val TyRep v)"
      proof (cases v)
        case (LitV x1)
        then show ?thesis by simp
      next
        case (AbsV x2)
        then show ?thesis
          using vbpl_absval_ty_closed[OF WfTyRep]
          by fastforce
      qed
    qed
  next
    show "fun_interp_wf (vbpl_absval_ty TyRep) fun_decls (fun_interp ctxt)"
      by (rule FunInterp)
  next
    show "list_all closed [] \<and> length [] = proc_ty_args proc_bpl"
      by (simp add: ProcTyArgsEmpty)
  next
    show "state_typ_wf (vbpl_absval_ty TyRep) [] gs (constants @ global_vars)"
      by (rule GlobalsWf)
  next
    show "state_typ_wf (vbpl_absval_ty TyRep) [] ls (proc_args proc_bpl @ locals_bpl @ proc_rets proc_bpl)"
      by (rule LocalsWf)
  next
    show "unique_constants_distinct gs unique_consts"
      by (rule UniqueConstants)
  next
    show "axioms_sat (vbpl_absval_ty TyRep) (constants, []) (fun_interp ctxt) (global_to_nstate (state_restriction gs constants)) axioms"
      by (rule AxiomsSat)
  qed

  text \<open>The prefix is simulated: its \<open>Success\<close> holds at \<open>?\<omega>p\<close> because the store's scaling slot is
    positive, which gives us the post-prefix Boogie state.\<close>
  obtain ns1 where
    RedInit: "red_ast_bpl proc_body_bpl ctxt (convert_ast_to_program_point proc_body_bpl, Normal ns)
                (\<gamma>0, Normal ns1)" and
    R1Holds: "R1 ?\<omega>p ns1"
    using rel_success_elim[OF PredicateRel[THEN conjunct1] StateRelInitial] StoreN PermPos
    by blast

  have NoFailVarMult: "\<And>res. red_inhale ctxt_vpr StateCons (var_mult n pbody) ?\<omega>p res \<Longrightarrow> res \<noteq> RFailure"
  proof -
    fix res
    assume RedInh: "red_inhale ctxt_vpr StateCons (var_mult n pbody) ?\<omega>p res"
    show "res \<noteq> RFailure"
    proof
      assume "res = RFailure"
      with RedInh have "red_stmt_total ctxt_vpr StateCons \<Lambda> (Inhale (var_mult n pbody)) ?\<omega>p RFailure"
        by (auto intro: TotalSemantics.RedInhale)

      with stmt_rel_failure_elim[OF PredicateRel[THEN conjunct2] R1Holds]
      obtain c' where
        FailureConfig: "snd c' = Failure" and
        RedBplRest: "red_ast_bpl proc_body_bpl ctxt (\<gamma>0, Normal ns1) c'"
        by blast

      from red_ast_bpl_transitive[OF RedInit RedBplRest]
      have RedBpl: "red_ast_bpl proc_body_bpl ctxt (convert_ast_to_program_point proc_body_bpl, Normal ns) c'" .

      have "snd c' \<noteq> Failure"
        using red_ast_bpl_proc_body_sat_spec[OF RedBpl, where ?pres="(Ast.proc_all_pres proc_bpl)"]
              ProcPresEmpty ProcBodyBplCorrect
        unfolding expr_all_sat_def
        by (simp add: VarCtxtEq TypeInterpEq RtypeInterpEmpty NsEq)

      thus False
        using FailureConfig by simp
    qed
  qed

  have FramingExt: "assertion_framing_state ctxt_vpr StateCons (syntactic_mult p pbody) ?\<omega>p"
    unfolding assertion_framing_state_def
    using NoFailVarMult red_inhale_var_mult_eq_syntactic_mult[OF StoreN PermPos]
    by blast

  show "assertion_framing_state ctxt_vpr StateCons (syntactic_mult p pbody) ?\<omega>"
  proof (rule assertion_framing_store_same_on_free_var[OF WfConsistency FramingExt])
    fix x
    assume "x \<in> free_var_assertion (syntactic_mult p pbody)"
    hence "x \<in> free_var_assertion pbody"
      using free_var_assertion_syntactic_mult[OF PermPos] by simp
    hence "x < length vs"
      using OnlyArgsInBody LenVs by simp
    thus "get_store_total ?\<omega>p x = get_store_total ?\<omega> x"
      by (simp add: nth_append)
  next
    show "get_trace_total ?\<omega>p = get_trace_total ?\<omega> \<and> get_total_full ?\<omega>p = get_total_full ?\<omega>"
      by simp
  next
    show "supported_assertion (syntactic_mult p pbody)"
      by (rule syntactic_mult_supported_assertion[OF SupAssertion])
  qed
qed

end
