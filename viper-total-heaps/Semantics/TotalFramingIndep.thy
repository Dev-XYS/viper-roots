theory TotalFramingIndep
  imports TotalFraming TotalStateProperties
begin

declare [[quick_and_dirty]]

text \<open>Carbon only checks well-definedness of a predicate body from the empty state (zero heap
  mask, zero predicate mask, an otherwise arbitrary heap), scaled by an arbitrary positive
  fraction. \<^const>\<open>assertion_self_framing\<close> demands well-definedness from every state (only the
  store is fixed). This lemma is the (currently unproven) bridge between the two: well-definedness
  from the empty state, for every positive fraction, transfers to well-definedness from any state.\<close>

lemma assertion_self_framing_of_empty_state:
  assumes SupPred: "supported_pred_body A"
      and EmptyFraming: "\<And>vs p tr hh.
             vals_well_typed (absval_interp_total ctxt) vs tys \<Longrightarrow>
             0 < p \<Longrightarrow>
             total_heap_well_typed (program_total ctxt) (absval_interp_total ctxt) hh \<Longrightarrow>
             StateCons \<lparr> get_store_total = nth_option vs, get_trace_total = tr, get_total_full = \<lparr> get_hh_total = hh, get_nm_total = 0 \<rparr> \<rparr> \<Longrightarrow>
             assertion_framing_state ctxt StateCons (syntactic_mult p A)
               \<lparr> get_store_total = nth_option vs, get_trace_total = tr, get_total_full = \<lparr> get_hh_total = hh, get_nm_total = 0 \<rparr> \<rparr>"
    shows "assertion_self_framing ctxt StateCons A tys"
  sorry

end

