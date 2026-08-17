theory TotalFramingIndep
  imports TotalFraming TotalStateProperties TotalExtConsProps
begin

text \<open>Carbon only checks well-definedness of a predicate body from the empty state (zero heap
  mask, zero predicate mask, an otherwise arbitrary well-typed heap), scaled by an arbitrary
  positive fraction. \<^const>\<open>assertion_self_framing\<close> demands well-definedness from every well-typed,
  consistent state (only the store is fixed). This lemma bridges the two.\<close>

text \<open>\<^const>\<open>syntactic_mult\<close> only rewrites permission amounts, so it introduces no
  \<^const>\<open>Unfolding\<close>. The bound on \<open>p\<close> is needed for \<^const>\<open>Wildcard\<close>, which a negative factor
  maps to \<^const>\<open>undefined\<close>.\<close>
lemma no_unfolding_syntactic_mult:
  assumes "no_unfolding_assertion A"
      and "0 \<le> p"
  shows "no_unfolding_assertion (syntactic_mult p A)"
  using assms
  apply (induction A rule: syntactic_mult.induct)
             apply simp_all
   apply (case_tac e_p; simp add: real_to_expr.simps)
  apply (case_tac e_p; simp add: real_to_expr.simps)
  done

text \<open>The zero-mask state is below every state with the same heap
  (@{thm [source] less_eq_total_state_ext_def} forces heaps to be equal), so
  @{thm [source] assertion_framing_state_mono} transfers framing upwards. The two hypotheses of
  \<open>EmptyFraming\<close> that the empty state does not supply on its own -- a well-typed heap and
  \<^term>\<open>StateCons\<close> -- are exactly the ones \<^const>\<open>assertion_self_framing\<close> demands of the target
  state; without them the statement is false, since inhaling \<open>acc(x.f) && x.f > 0\<close> fails when the
  heap is ill-typed at \<open>x.f\<close>.\<close>
lemma assertion_self_framing_of_empty_state:
  assumes SupPred: "supported_pred_body A"
      and NoUnfolding: "no_unfolding_assertion A"
      and ConsMono: "mono_prop_downward_ord StateCons"
      and EmptyFraming: "\<And>vs p tr hh.
             vals_well_typed (absval_interp_total ctxt) vs tys \<Longrightarrow>
             0 < p \<Longrightarrow>
             total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) hh \<Longrightarrow>
             StateCons \<lparr> get_store_total = nth_option vs, get_trace_total = tr, get_total_full = \<lparr> get_hh_total = hh, get_nm_total = 0 \<rparr> \<rparr> \<Longrightarrow>
             assertion_framing_state ctxt StateCons (syntactic_mult p A)
               \<lparr> get_store_total = nth_option vs, get_trace_total = tr, get_total_full = \<lparr> get_hh_total = hh, get_nm_total = 0 \<rparr> \<rparr>"
    shows "assertion_self_framing ctxt StateCons A tys"
  unfolding assertion_self_framing_def
proof (rule allI | rule impI)+
  fix vs and p :: real and \<omega>
  assume WtVs: "vals_well_typed (absval_interp_total ctxt) vs tys"
     and PermPos: "0 < p"
     and HeapWt: "total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) (get_hh_total_full \<omega>)"
     and Cons: "StateCons (update_store_total \<omega> (nth_option vs))"

  let ?\<omega>s = "update_store_total \<omega> (nth_option vs)"
  let ?\<omega>0 = "\<lparr> get_store_total = nth_option vs, get_trace_total = get_trace_total \<omega>,
               get_total_full = \<lparr> get_hh_total = get_hh_total_full \<omega>, get_nm_total = 0 \<rparr> \<rparr>"

  have Leq: "?\<omega>0 \<le> ?\<omega>s"
    by (rule less_eq_full_total_stateI) (simp_all add: less_eq_total_stateI nm_0_le_any)

  have ConsEmpty: "StateCons ?\<omega>0"
    using ConsMono Cons Leq
    unfolding mono_prop_downward_ord_def
    by blast

  have "assertion_framing_state ctxt StateCons (syntactic_mult p A) ?\<omega>0"
    using EmptyFraming[OF WtVs PermPos _ ConsEmpty] HeapWt
    by simp

  thus "assertion_framing_state ctxt StateCons (syntactic_mult p A) ?\<omega>s"
    using assertion_framing_state_mono[OF ConsMono _ Leq] SupPred NoUnfolding PermPos
          syntactic_mult_supported no_unfolding_syntactic_mult
    by simp
qed

end

