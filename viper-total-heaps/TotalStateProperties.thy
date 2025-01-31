section \<open>Basic State Properties and Instantiations\<close>

theory TotalStateProperties
  imports TotalStateUtil TotalStateInst
begin


subsection \<open>General Helper Lemmas\<close>

lemma add_masks_minus:
  assumes "m1 = add_masks (m2 :: ('a, preal) abstract_mask) m3"
  shows "m3 = m1 - m2"
  unfolding fun_diff_def
proof
  fix x

  have "m1 x = (m2 x) + (m3 x)"
    using assms
    by (simp add: add_masks_def)

  thus "m3 x = m1 x - m2 x"
    by (simp add: Rep_preal_inverse minus_preal.abs_eq plus_preal.rep_eq pos_perm_class.sum_larger)
qed

lemma minus_masks_empty:
 "m - (m :: ('a, preal) abstract_mask) = zero_mask"
  unfolding fun_diff_def
proof
  fix x
  show "m x - m x = zero_mask x"
    unfolding minus_preal_def zero_mask_def
    by (simp add: zero_preal_def)
qed

lemma minus_preal_gte:
  assumes "p \<ge> (q :: preal)"
  shows "p - (p - q) = q"
  using assms Rep_preal_inject minus_preal.rep_eq psub_smaller by fastforce

lemma mask_plus_Some:
  shows "(m1 :: ('a, preal) abstract_mask) \<oplus> m2 = Some (add_masks m1 m2)"
  unfolding plus_fun_def add_masks_def
  by (simp split: if_split add: SepAlgebra.plus_preal_def compatible_fun_def)

lemma add_masks_self_zero_mask:
  assumes "m1 = add_masks m1 m2"
  shows "m2 = zero_mask"
  using assms
  unfolding add_masks_def
  by (metis (full_types) add.commute add_0 le_fun_def order_class.order_eq_iff pos_perm_class.padd_cancellative zero_mask_def)

lemma succ_maskI:
  assumes "(m :: ('a, preal) abstract_mask) \<ge> m'"
  shows "m \<succeq> m'"
  unfolding greater_def
proof
  let ?\<Delta> = "\<lambda>l. (m l) \<ominus> (m' l)"

  have "m = add_masks m' ?\<Delta>"
    unfolding add_masks_def
  proof
    fix l

    from assms have "m l \<ge> m' l"
      by (simp add: le_funD)

    from this obtain p where "m l = padd (m' l) p"
      using preal_gte_padd
      by blast

    hence "Some (m l) = (m' l) \<oplus> p"
      unfolding plus_preal_def
      by simp

    thus "m l = padd (m' l) (m l \<ominus> m' l)"
      by (metis SepAlgebra.plus_preal_def add.commute greater_equiv minus_equiv_def option.inject)
  qed

  thus "Some m = m' \<oplus> ?\<Delta>"
    by (metis (mono_tags, lifting) SepAlgebra.plus_preal_def add_masks_def plus_funI)
qed


subsection \<open>Empty States\<close>

lemma is_empty_total_wf_mask: "is_empty_total_full \<omega> \<Longrightarrow> wf_mask_simple (get_mh_total_full \<omega>)"
  unfolding is_empty_total_full_def is_empty_total_def
  by (simp add: wf_zero_mask zero_nested_mask_def)

lemma is_empty_total_less_eq:
  assumes "is_empty_total \<phi>" and
    "get_hh_total \<phi> = get_hh_total \<phi>'" and
    "total_state.more \<phi> = total_state.more \<phi>'"
  shows "\<phi> \<le> \<phi>'"
  unfolding less_eq_total_state_ext_def
  apply (intro conjI)
    defer 2
    apply (simp_all add: assms(2,3))
  unfolding less_eq_nested_mask_def
  apply (cases "get_nm_total \<phi>"; cases "get_nm_total \<phi>'")
  using assms(1)[simplified is_empty_total_def zero_nested_mask_def] zero_mask_less_eq_mask
  by auto

lemma is_empty_total_full_less_eq:
  assumes "is_empty_total_full \<omega>" and
          "get_store_total \<omega> = get_store_total \<omega>'" and
          "get_trace_total \<omega> = get_trace_total \<omega>'" and
          "get_hh_total_full \<omega> = get_hh_total_full \<omega>'" and
          "full_total_state.more \<omega> = full_total_state.more \<omega>'"
        shows "\<omega> \<le> \<omega>'"
proof -
  have "get_total_full \<omega> \<le> get_total_full \<omega>'"
    using is_empty_total_less_eq assms
    unfolding is_empty_total_full_def
    by fastforce

  thus ?thesis
    using assms
    unfolding less_eq_full_total_state_ext_def
    by auto
qed

definition empty_full_total_state :: "'a store \<Rightarrow> 'a total_trace \<Rightarrow> 'a total_heap \<Rightarrow> 'a full_total_state"
  where "empty_full_total_state \<sigma> t hh =
   \<lparr> get_store_total = \<sigma>,
     get_trace_total = t,
     get_total_full = \<lparr> get_hh_total = hh, get_nm_total = 0 \<rparr>
   \<rparr>"

lemma get_store_empty_full_total_state [simp]: "get_store_total (empty_full_total_state \<sigma> t hh) = \<sigma>"
  by (simp add: empty_full_total_state_def)

lemma get_trace_empty_full_total_state [simp]: "get_trace_total (empty_full_total_state \<sigma> t hh) = t"
  by (simp add: empty_full_total_state_def)

lemma is_empty_empty_full_total_state: "is_empty_total_full (empty_full_total_state \<sigma> t hh)"
  unfolding is_empty_total_full_def is_empty_total_def empty_full_total_state_def
  by simp


subsection \<open>Trace Update Properties\<close>

lemma update_trace_total_store_same: "get_store_total (update_trace_total \<omega> \<pi>) = get_store_total \<omega>"
  by simp

lemma update_trace_total_hm_same: "get_total_full (update_trace_total \<omega> \<pi>) = get_total_full \<omega>"
  by simp

lemma update_trace_total_heap_same: "get_hh_total_full (update_trace_total \<omega> \<pi>) = get_hh_total_full \<omega>"
  by simp

lemma update_trace_total_mask_same: "get_mh_total_full (update_trace_total \<omega> \<pi>) = get_mh_total_full \<omega>"
  by simp


subsection \<open>Simplification Lemmas on State Update\<close>


subsubsection \<open>Nested Masks\<close>

lemma upd_mh_nm__mp_rel [simp]:
  shows "get_mp_nm (upd_mh_nm nm mh) = get_mp_nm nm"
  by (cases nm, fastforce)

lemma upd_mh_nm__mh_rel [simp]:
  shows "get_mh_nm (upd_mh_nm nm mh) = mh"
  by (cases nm, fastforce)

lemma upd_mh_nm__fnm_rel [simp]:
  shows "get_fnm_nm (upd_mh_nm nm mh) = get_fnm_nm nm"
  by (cases nm, fastforce)

(*
lemma upd_mh_loc_nm__mh_rel [simp]:
  shows "get_mh_nm (upd_mh_loc_nm nm l p) = (get_mh_nm nm)( l := p )"
  by (cases nm, fastforce)

lemma upd_mh_loc_nm__mp_rel [simp]:
  shows "get_mp_nm (upd_mh_loc_nm nm l p) = get_mp_nm nm"
  by (cases nm, fastforce)

lemma upd_mh_loc_nm__fnm_rel [simp]:
  shows "get_fnm_nm (upd_mh_loc_nm nm l p) = get_fnm_nm nm"
  by (cases nm, fastforce)
*)

(*
lemma upd_mp_nm__mh_rel [simp]:
  shows "get_mh_nm (upd_mp_nm nm mp) = get_mh_nm nm"
  by (cases nm, fastforce)

lemma upd_mp_nm__mp_rel [simp]:
  shows "get_mp_nm (upd_mp_nm nm mp) = mp"
  by (cases nm, fastforce)

lemma upd_mp_nm__fnm_rel [simp]:
  shows "get_fnm_nm (upd_mp_nm nm mp) = get_fnm_nm nm"
  by (cases nm, fastforce)

lemma upd_mp_loc_nm__mh_rel [simp]:
  shows "get_mh_nm (upd_mp_loc_nm nm lp p) = get_mh_nm nm"
  by (cases nm, fastforce)

lemma upd_mp_loc_nm__mp_rel [simp]:
  shows "get_mp_nm (upd_mp_loc_nm nm lp p) = (get_mp_nm nm)( lp := p )"
  by (cases nm, fastforce)

lemma upd_mp_loc_nm__fnm_rel [simp]:
  shows "get_fnm_nm (upd_mp_loc_nm nm lp p) = get_fnm_nm nm"
  by (cases nm, fastforce)
*)

lemma upd_fnm_nm__mh_rel [simp]:
  shows "get_mh_nm (upd_fnm_nm nm fnm) = get_mh_nm nm"
  by (cases nm, fastforce)

(*
lemma upd_fnm_nm__mp_rel [simp]:
  shows "get_mp_nm (upd_fnm_nm nm fnm) = get_mp_nm nm"
  by (cases nm, fastforce)
*)

lemma upd_fnm_nm__fnm_rel [simp]:
  shows "get_fnm_nm (upd_fnm_nm nm fnm) = fnm"
  by (cases nm, fastforce)

(*
lemma upd_nm_loc_opt_nm__mh_rel [simp]:
  shows "get_mh_nm (upd_nm_loc_opt_nm nm lp nm') = get_mh_nm nm"
  by (cases nm, fastforce)

lemma upd_nm_loc_opt_nm__mp_rel [simp]:
  shows "get_mp_nm (upd_nm_loc_opt_nm nm lp nm') = get_mp_nm nm"
  by (cases nm, fastforce)
*)

(*
lemma inc_mp_loc_nm__mh_rel [simp]:
  shows "get_mh_nm (inc_mp_loc_nm nm lp p) = get_mh_nm nm"
  by (cases nm, fastforce)

lemma inc_mp_loc_nm__mp_rel [simp]:
  shows "get_mp_nm (inc_mp_loc_nm nm lp p) = (get_mp_nm nm)( lp := get_mp_nm nm lp + p )"
  by (cases nm, fastforce)

lemma inc_mp_loc_nm__fnm_rel [simp]:
  shows "get_fnm_nm (inc_mp_loc_nm nm lp p) = get_fnm_nm nm"
  by (cases nm, fastforce)

lemma dec_mh_loc_nm__mh_rel [simp]:
  shows "get_mh_nm (dec_mh_loc_nm nm l p) = (get_mh_nm nm)( l := get_mh_nm nm l - p )"
  by (cases nm, fastforce)

lemma dec_mh_loc_nm__mp_rel [simp]:
  shows "get_mp_nm (dec_mh_loc_nm nm l p) = get_mp_nm nm"
  by (cases nm, fastforce)

lemma dec_mh_loc_nm__fnm_rel [simp]:
  shows "get_fnm_nm (dec_mh_loc_nm nm l p) = get_fnm_nm nm"
  by (cases nm, fastforce)

lemma dec_mp_loc_nm__mh_rel [simp]:
  shows "get_mh_nm (dec_mp_loc_nm nm lp p) = get_mh_nm nm"
  by (cases nm, fastforce)

lemma dec_mp_loc_nm__mp_rel [simp]:
  shows "get_mp_nm (dec_mp_loc_nm nm lp p) = (get_mp_nm nm)( lp := get_mp_nm nm lp - p )"
  by (cases nm, fastforce)

lemma add_to_nm_loc_nm__mh_rel [simp]:
  shows "get_mh_nm (add_to_nm_loc_nm nm lp nm') = get_mh_nm nm"
  by (cases nm, fastforce)

lemma add_to_nm_loc_nm__mp_rel [simp]:
  shows "get_mp_nm (add_to_nm_loc_nm nm lp nm') = get_mp_nm nm"
  by (cases nm, fastforce)

lemma add_to_nm_loc_nm__fnm_rel [simp]:
  shows "get_fnm_nm (add_to_nm_loc_nm nm lp nm') = (get_fnm_nm nm)( lp := get_fnm_nm nm lp + Some nm' )"
  by (cases nm, fastforce)

lemma mult_nm_loc_nm__mh_rel [simp]:
  shows "get_mh_nm (mult_nm_loc_nm nm lp p) = get_mh_nm nm"
  by (cases nm, fastforce)

lemma mult_nm_loc_nm__mp_rel [simp]:
  shows "get_mp_nm (mult_nm_loc_nm nm lp p) = get_mp_nm nm"
  by (cases nm, fastforce)

lemma mult_rm_nm_loc_nm__mh_rel [simp]:
  shows "get_mh_nm (mult_rm_nm_loc_nm nm lp p) = get_mh_nm nm"
  by (cases nm, fastforce)

lemma mult_rm_nm_loc_nm__mp_rel [simp]:
  shows "get_mp_nm (mult_rm_nm_loc_nm nm lp p) = get_mp_nm nm"
  by (cases nm, fastforce)
*)


subsubsection \<open>Total States\<close>

lemma mult_nm_total__nm_rel [simp]:
  shows "get_nm_total (mult_nm_total \<phi> p) = p *\<^sub>s (get_nm_total \<phi>)"
  by simp

(*
lemma mult_rm_nm_loc_total__nm_rel [simp]:
  shows "get_nm_total (mult_rm_nm_loc_total \<phi> lp f) = mult_rm_nm_loc_nm (get_nm_total \<phi>) lp f"
  by simp

lemma dec_mp_loc_total__nm_rel [simp]:
  shows "get_nm_total (dec_mp_loc_total \<phi> lp p) = dec_mp_loc_nm (get_nm_total \<phi>) lp p"
  by simp
*)


subsubsection \<open>Full Total States\<close>

(*
lemma upd_mh_loc_total_full_mh_rel:
  shows "get_mh_total_full (upd_mh_loc_total_full \<omega> l p) = (get_mh_total_full \<omega>)( l := p )"
  by simp

lemma upd_mh_loc_total_full_mp_eq:
  shows "get_mp_total_full \<omega> = get_mp_total_full (upd_mh_loc_total_full \<omega> l p)"
  by simp

lemma upd_mp_loc_total_full_mh_eq:
  shows "get_mh_total_full \<omega> = get_mh_total_full (upd_mp_loc_total_full \<omega> lp p)"
  by simp

lemma upd_mp_loc_total_full_mp_rel:
  shows "get_mp_total_full (upd_mp_loc_total_full \<omega> lp p) = (get_mp_total_full \<omega>)( lp := p )"
  using upd_mp_nm_mp_rel by auto

lemma mult_nm_loc_total_full_mh_eq:
  shows "get_mh_total_full \<omega> = get_mh_total_full (mult_nm_loc_total_full \<omega> lp p)"
  by simp

lemma mult_nm_loc_total_full_mp_eq:
  shows "get_mp_total_full \<omega> = get_mp_total_full (mult_nm_loc_total_full \<omega> lp p)"
  by simp
*)


subsection \<open>Lemmas on Mask Diff\<close>

lemma mh_upd_loc_diff:
  assumes "p \<le> mh l"
  shows "mh - (mh( l := p )) = singleton_mh l (mh l - p)"
  by (standard, simp)

lemma mp_upd_loc_diff:
  assumes "p \<le> mp lp"
  shows "mp - (mp( lp := p )) = singleton_mp lp (mp lp - p)"
  by (standard, simp)

lemma same_mh_diff:
  shows "get_mh_total_full \<omega> - get_mh_total_full \<omega> = zero_mask"
  apply standard
  by (simp add: zero_mask_def)

lemma same_mp_diff:
  shows "get_mp_total_full \<omega> - get_mp_total_full \<omega> = zero_mask"
  apply standard
  by (simp add: zero_mask_def)

lemma dec_mh_mh_diff:
  assumes "p < get_mh_total_full \<omega> loc"
  shows "get_mh_total_full \<omega> - get_mh_total_full (upd_mh_loc_total_full \<omega> loc (get_mh_total_full \<omega> loc - p)) =
         singleton_mh loc p"
proof -
  have "get_mh_total_full \<omega> loc - (get_mh_total_full \<omega> loc - p) = p"
    using assms minus_preal_gte by auto
  thus ?thesis
    apply simp
    using assms mh_upd_loc_diff psub_smaller
    by auto
qed

lemma dec_mh_mp_diff:
  shows "get_mp_total_full \<omega> - get_mp_total_full (upd_mh_loc_total_full \<omega> loc (get_mh_total_full \<omega> loc - p)) =
         zero_mask"
  apply simp
  using same_mp_diff
  by auto


subsection \<open>Helper Lemmas for Mask Multiplication\<close>

lemma singleton_mh_multiply:
  shows "singleton_mh loc (q * p) = ((*) q) \<circ> singleton_mh loc p"
  by (standard, simp)

lemma singleton_mp_multiply:
  shows "singleton_mp loc (q * p) = ((*) q) \<circ> singleton_mp loc p"
  by (standard, simp)

lemma zero_mh_multiply:
  fixes frac :: preal
  shows "mul_mask frac zero_mask = zero_mask"
  by (standard, simp add: mul_mask_def zero_mask_def)

lemma zero_mp_multiply:
  fixes frac :: preal
  shows "mul_mask frac zero_mask = zero_mask"
  by (standard, simp add: mul_mask_def zero_mask_def)

lemma get_mh_multiply [simp]:
  fixes frac :: preal
  shows "get_mh_nm (frac *\<^sub>s get_nm_total \<phi>) = mul_mask frac (get_mh_total \<phi>)"
  by (metis (no_types, lifting) get_fnm_nm.simps get_mh_nm.simps get_mh_total.elims nested_mask_equality nested_mask_multiply.simps scale_nested_mask_def)

lemma get_mp_multiply [simp]:
  fixes frac :: preal
  shows "get_mp_nm (frac *\<^sub>s get_nm_total \<phi>) = mul_mask frac (get_mp_total \<phi>)"
proof
  fix lp
  show "get_mp_nm (frac *\<^sub>s get_nm_total \<phi>) lp = mul_mask frac (get_mp_total \<phi>) lp"
  proof (cases "get_fnm_total \<phi> lp")
    case None
    then show ?thesis
      apply (simp add: mul_mask_def scale_nested_mask_def)
      apply (cases "get_nm_total \<phi>")
      by simp
  next
    case (Some a)
    then show ?thesis
      apply (simp add: mul_mask_def scale_nested_mask_def)
      apply (cases "get_nm_total \<phi>")
      apply (cases "frac = 0")
       apply simp_all
      apply (simp add: pos2p_def)
      apply (simp add: preal_to_real posreal_to_real)
      by (smt (verit, del_insts) Abs_posreal_inverse Rep_posreal Rep_preal_inject mem_Collect_eq mult.commute prat_non_negative preal_to_real(12) times_posreal.rep_eq times_preal.rep_eq zero_preal.rep_eq)
  qed
qed

(*
lemma get_nm_loc_total_multiply [simp]:
  fixes frac :: preal
  shows "get_nm_loc_total (\<phi>\<lparr> get_nm_total := frac *\<^sub>s get_nm_total \<phi> \<rparr>) loc =
         get_nm_loc_nm (frac *\<^sub>s get_nm_total \<phi>) loc"
  by (metis TotalStateUtil.get_nm_loc_total.simps get_fnm_nm.simps get_fnm_total.simps get_nm_loc_nm.simps nested_mask_multiply.elims total_state.simps(2) total_state.simps(5) total_state.surjective)
*)

\<^cancel>\<open>
lemma get_nm_loc_nm_multiply:
  fixes frac :: preal
  shows "get_nm_loc_nm (frac *\<^sub>s nm) loc =
         map_option (\<lambda>m. frac *\<^sub>s m) (get_nm_loc_nm nm loc)"
  apply (cases nm)
  apply (cases "get_nm_loc_nm nm loc")
   apply (simp add: scale_nested_mask_def)
  apply (cases "frac = 0")
proof -
  fix mh fnm nm'
  assume "nm = NM mh fnm"
     and "get_nm_loc_nm nm loc = Some nm'"
     and "frac = 0"
  have "frac *\<^sub>s nm = 0"
    apply (simp add: scale_nested_mask_def \<open>frac = 0\<close> \<open>nm = NM mh fnm\<close> mul_mask_def zero_nested_mask_def comp_def)
    using zero_mask_def by force
  hence "get_nm_loc_nm (frac *\<^sub>s nm) loc = None"
    by (simp add: zero_nested_mask_def)
  moreover have "map_option ((*\<^sub>s) frac) (get_nm_loc_nm nm loc) = None"
    apply (simp only: \<open>get_nm_loc_nm nm loc = Some nm'\<close>)
    apply simp
\<close>

(*
lemma get_mp_total_full_multiply:
  fixes frac :: preal
  assumes "get_mp_total_full \<omega> loc = p"
  shows "get_mp_total_full (mult_nm_total_full \<omega> frac) loc = p * frac"
  apply (simp add: mul_mask_def)
  using PosReal.pmult_comm assms
  by fastforce
*)

lemma get_hh_total_full_multiply:
  fixes frac :: preal
  assumes "get_hh_total_full \<omega> loc = v"
  shows "get_hh_total_full (mult_nm_total_full \<omega> frac) loc = v"
  apply simp
  using assms by force

lemma get_valid_locs_multiply:
  fixes frac :: preal
  assumes "frac > 0"
  shows "get_valid_locs \<omega> = get_valid_locs (mult_nm_total_full \<omega> frac)"
  apply (simp add: get_valid_locs_def)
  apply (rule Set.Collect_cong)
  apply standard
  using PosReal.pgt.rep_eq assms preal_pnone_pgt times_preal.rep_eq zero_preal.rep_eq less_preal.rep_eq
   apply (simp add: mul_mask_def)
  by (metis comp_apply mul_mask_def mult_zero_right preal_not_0_gt_0)

lemma nm_multiply_none:
    fixes frac :: preal
  assumes "frac > 0"
    shows "(get_nm_loc_nm nm loc = None) = (get_nm_loc_nm (frac *\<^sub>s nm) loc = None)"
  by (smt (verit) assms get_fnm_nm.simps get_nm_loc_nm.simps nested_mask_multiply.elims o_apply option.map_disc_iff preal_not_0_gt_0 scale_nested_mask_def)

lemma nm_multiply_mp_value:
  fixes frac
  shows "get_mp_nm (frac *\<^sub>s nm) loc = frac * get_mp_nm nm loc"
  by (metis get_mp_multiply get_mp_total.elims o_def mul_mask_def total_state.select_convs(2))

lemma nm_multiply_back:
    fixes frac :: preal
  assumes "frac > 0"
      and "get_mp_nm (frac *\<^sub>s nm) loc = q"
    shows "get_mp_nm nm loc = q / frac"
  by (metis Rep_preal_inverse assms(1) assms(2) divide_preal.rep_eq dual_order.refl linorder_not_less nm_multiply_mp_value nonzero_mult_div_cancel_left times_preal.rep_eq zero_preal.rep_eq)

(* lemma nm_multiply_back_nm:
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
qed *)

lemma mh_split_multiply:
  fixes frac :: preal
  assumes "mh_split mh mh\<^sub>1 mh\<^sub>2"
  shows "mh_split (mul_mask frac mh) (mul_mask frac mh\<^sub>1) (mul_mask frac mh\<^sub>2)"
  apply simp
  apply standard
  apply (simp add: add_masks_def mul_mask_def)
  by (metis PosReal.pmult_distr add_masks_def assms mh_split.elims(2))

lemma mp_split_multiply:
  fixes frac :: preal
  assumes "mp_split mp mp\<^sub>1 mp\<^sub>2"
  shows "mp_split (mul_mask frac mp) (mul_mask frac mp\<^sub>1) (mul_mask frac mp\<^sub>2)"
  apply simp
  apply standard
  using assms
  apply (simp add: add_masks_def mul_mask_def)
  using distrib_left
  by blast

lemma mh_split_zero:
  assumes "mh_split mh zero_mask zero_mask"
  shows "mh = zero_mask"
  apply standard
  apply (simp add: zero_mask_def)
  by (metis add_masks_zero_mask assms mh_split.elims(2) zero_mask_def)

lemma mp_split_zero:
  assumes "mp_split mp zero_mask zero_mask"
  shows "mp = zero_mask"
  apply standard
  apply (simp add: zero_mask_def)
  by (metis add_masks_zero_mask assms mp_split.elims(2) zero_mask_def)

lemma mh_split_twice:
  assumes "mh_split s a b"
      and "mh_split a a1 a2"
      and "mh_split b b1 b2"
      and "mh_split s1 a1 b1"
      and "mh_split s2 a2 b2"
    shows "mh_split s s1 s2"
  apply simp
  apply standard
  apply (simp add: add_masks_def)
proof -
  fix x
  have "s1 x = a1 x + b1 x"
    by (metis assms(4) add_masks_def mh_split.elims(1))
  moreover have "s2 x = a2 x + b2 x"
    by (metis assms(5) add_masks_def mh_split.elims(1))
  ultimately show "s x = s1 x + s2 x"
    by (metis add.assoc add.left_commute add_masks_def assms(1) assms(2) assms(3) mh_split.simps)
qed

lemma mp_split_twice:
  assumes "mp_split s a b"
      and "mp_split a a1 a2"
      and "mp_split b b1 b2"
      and "mp_split s1 a1 b1"
      and "mp_split s2 a2 b2"
    shows "mp_split s s1 s2"
  apply simp
  apply standard
  apply (simp add: add_masks_def)
proof -
  fix x
  have "s1 x = a1 x + b1 x"
    by (metis assms(4) add_masks_def mp_split.elims(1))
  moreover have "s2 x = a2 x + b2 x"
    by (metis assms(5) add_masks_def mp_split.elims(1))
  ultimately show "s x = s1 x + s2 x"
    by (metis add.assoc add.left_commute add_masks_def assms(1) assms(2) assms(3) mp_split.simps)
qed


subsection \<open>Simplification Lemmas for Nested Mask Merge\<close>

lemma get_mh_nm__plus [simp]:
  shows "get_mh_nm (nm1 + nm2) = add_masks (get_mh_nm nm1) (get_mh_nm nm2)"
  apply (cases nm1, cases nm2)
  apply standard
  by (simp add: plus_nested_mask_def add_masks_def)

(*
lemma get_mp_nm__plus [simp]:
  shows "get_mp_nm (nm1 + nm2) = add_masks (get_mp_nm nm1) (get_mp_nm nm2)"
  apply (cases nm1, cases nm2)
  apply standard
  by (simp add: plus_nested_mask_def add_masks_def)

lemma get_fnm_nm__plus [simp]:
  shows "get_fnm_nm (nm1 + nm2) = ((get_fnm_nm nm1) +\<lparr>(+)\<rparr>+ (get_fnm_nm nm2))"
  apply (cases nm1, cases nm2)
  by (simp add: plus_nested_mask_def)
*)

lemma get_mh_nm__merge [simp]:
  shows "get_mh_nm (nested_mask_merge nm1 nm2) = add_masks (get_mh_nm nm1) (get_mh_nm nm2)"
  by (cases nm1, cases nm2, simp)

(*
lemma get_mp_nm__merge [simp]:
  shows "get_mp_nm (nested_mask_merge nm1 nm2) = add_masks (get_mp_nm nm1) (get_mp_nm nm2)"
  by (cases nm1, cases nm2, simp)

lemma get_fnm_nm__merge [simp]:
  shows "get_fnm_nm (nested_mask_merge nm1 nm2) = pfun_comb (get_fnm_nm nm1) nested_mask_merge (get_fnm_nm nm2)"
  by (cases nm1, cases nm2, simp)
*)


subsection \<open>Properties of Nested Mask Shift\<close>

lemma mp_non_zero_implies_some:
  assumes "get_mp_nm nm lp > 0"
  shows "\<not> Option.is_none (get_nm_loc_nm nm lp)"
  using assms
  apply (cases nm)
  apply simp
  by (metis Option.is_none_def option_fold.simps(2) preal_not_0_gt_0)

lemma mp_non_zero_obtain_nm_loc:
  assumes "get_mp_nm nm lp > 0"
  obtains nm' where "get_nm_loc_nm nm lp = Some nm'"
  by (metis Option.is_none_def assms mp_non_zero_implies_some not_None_eq)

lemma shift_up_exists:
  assumes "q \<le> get_mp_nm nm (pid,vs)"
    shows "\<exists>nm'. shift_up pid vs q nm nm'"
proof (cases "q = 0")
  case True
  then show ?thesis
    using ShiftZero by blast
next
  case False
  then obtain mh fnm where
    1: "mh = get_mh_nm nm" and
    2: "fnm = get_fnm_nm nm"
    by auto
  from assms(1) have *: "get_mp_nm nm (pid,vs) > 0"
    using False preal_not_0_gt_0
    by fastforce
  obtain p\<^sub>p pnm where
    3: "Some (p\<^sub>p, pnm) = fnm (pid, vs)"
    using mp_non_zero_obtain_nm_loc[OF *] 2
    by fastforce
  obtain p where
    4: "p = pos2p p\<^sub>p"
    by auto
  have 5: "q > 0"
    using False preal_not_0_gt_0
    by blast
  have "p = get_mp_nm nm (pid,vs)"
    apply simp
    by (metis "2" "3" "4" comp_apply fst_conv option_fold.simps(1))
  hence 6: "q \<le> p"
    using assms
    by (simp add: pos2p_def)
  show ?thesis
    using ShiftNonZero[OF 1 2 3 4 5 6]
    by blast
qed

lemma shift_up_exists_obtain:
  assumes "q \<le> get_mp_nm nm (pid,vs)"
      and "q \<noteq> 0"
  obtains nm' where "shift_up pid vs q nm nm'"
  using assms(1) assms(2) shift_up_exists
  by blast

lemma shift_up_frac:
    fixes frac :: preal
  assumes "frac > 0"
      and "shift_up pid vs q nm nm'"
    shows "shift_up pid vs (frac * q) (frac *\<^sub>s nm) (frac *\<^sub>s nm')"
  sorry


subsection \<open>Shifting stores\<close>

fun shift_and_add_state_total :: "'a full_total_state \<Rightarrow> 'a val \<Rightarrow> 'a full_total_state"
  where
    "shift_and_add_state_total \<omega> v = update_store_total \<omega> (shift_and_add (get_store_total \<omega>) v)"

fun unshift_state_total :: "nat \<Rightarrow> 'a full_total_state \<Rightarrow> 'a full_total_state"
  where
   "unshift_state_total n \<omega> = update_store_total \<omega> (unshift_2 n (get_store_total \<omega>))"

fun shift_state_total
  where "shift_state_total n \<omega> = update_store_total \<omega> (DeBruijn.shift n (get_store_total \<omega>))"

lemma shift_1_shift_and_add_total:
  "shift_and_add_state_total \<omega> y = update_var_total (shift_state_total 1 \<omega>) 0 y"
  apply (simp add: shift_and_add_def)
  apply (rule full_total_state.equality)
  unfolding DeBruijn.shift_def
  by auto


subsection \<open>Well-typed states\<close>

definition total_heap_well_typed :: "program \<Rightarrow> ('a \<Rightarrow> abs_type) \<Rightarrow> 'a total_heap \<Rightarrow> bool"
  where "total_heap_well_typed Pr \<Delta> h \<equiv>
           \<forall>loc \<tau>. declared_fields Pr (snd loc) = Some \<tau> \<longrightarrow> has_type \<Delta> \<tau> (h loc)"


subsubsection \<open>Lemmas\<close>

lemma plus_mask_zero_mask_neutral: "(m :: ('a, preal) abstract_mask) \<oplus> zero_mask = Some m"
proof -
  have "compatible_fun m zero_mask"
    by (simp add: SepAlgebra.plus_preal_def compatible_funI)

  thus ?thesis
  unfolding plus_fun_def
  by (simp add: SepAlgebra.plus_preal_def zero_mask_def)
qed

lemma core_mask_zero_mask: "zero_mask = |m :: ('a, preal) abstract_mask|"
proof
  fix x
  show "zero_mask x = |m| x"
    unfolding zero_mask_def
    by (simp add: core_fun core_preal_def)
qed

lemma total_state_plus_defined:
  assumes "a \<oplus> b = Some c"
  shows "get_hh_total a = get_hh_total b \<and> total_state.more a = total_state.more b \<and>
         get_hh_total a = get_hh_total c \<and> total_state.more a = total_state.more c"
  using assms
  unfolding plus_total_state_ext_def
  by (clarsimp split: if_split_asm )

(*
lemma plus_Some_total_state_eq:
  assumes "\<phi> \<oplus> \<phi>' = Some \<phi>sum"
  shows "\<phi>sum = \<phi> \<lparr> get_mh_total := add_masks (get_mh_total \<phi>) (get_mh_total \<phi>'),
                    get_mp_total := add_masks (get_mp_total \<phi>) (get_mp_total \<phi>') \<rparr>"
  using assms
  unfolding plus_total_state_ext_def
  by (simp split: if_split_asm add: mask_plus_Some)
*

lemma plus_Some_full_total_state_eq:
  assumes "\<omega> \<oplus> \<omega>' = Some \<omega>sum"
  shows "\<omega>sum = update_m_total_full \<omega> (add_masks (get_mh_total_full \<omega>) (get_mh_total_full \<omega>'))
                                      (add_masks (get_mp_total_full \<omega>) (get_mp_total_full \<omega>'))"
  using assms
  unfolding plus_full_total_state_ext_def defined_def
  by (fastforce split: if_split_asm dest: plus_Some_total_state_eq)

lemma plus_Some_full_total_state_total_state:
  assumes "Some a = b \<oplus> x"
  shows "Some (get_total_full a) = (get_total_full b) \<oplus> (get_total_full x)"
  using assms
  unfolding plus_full_total_state_ext_def defined_def
  by (auto split: if_split_asm)
*)

lemma plus_total_state_zero_mask:
  assumes "get_hh_total \<phi> = get_hh_total \<phi>' \<and> total_state.more \<phi> = total_state.more \<phi>'" and
          "get_nm_total \<phi>' = 0"
    shows "\<phi>' \<oplus> \<phi> = Some \<phi>"
  using assms
  unfolding plus_total_state_ext_def
  by simp

lemma plus_full_total_state_zero_mask:
  assumes "get_store_total \<omega> = get_store_total \<omega>' \<and> get_trace_total \<omega> = get_trace_total \<omega>' \<and>
           get_hh_total_full \<omega> = get_hh_total_full \<omega>' \<and>
           full_total_state.more \<omega> = full_total_state.more \<omega>'" and
          "get_nm_total_full \<omega>' = 0"
        shows "\<omega>' \<oplus> \<omega> = Some \<omega>"
proof -
  have "get_total_full \<omega>' \<oplus> get_total_full \<omega> = Some (get_total_full \<omega>)"
    apply (rule plus_total_state_zero_mask)
    using assms
    by simp_all

  thus ?thesis
    unfolding plus_full_total_state_ext_def defined_def
    using plus_total_state_zero_mask assms
    by simp
qed

lemma full_total_state_greater_only_mask_changed:
  assumes "\<omega> \<succeq> \<omega>'"
  shows "get_store_total \<omega> = get_store_total \<omega>' \<and>
         get_trace_total \<omega> = get_trace_total \<omega>' \<and>
         get_hh_total_full \<omega> = get_hh_total_full \<omega>' \<and>
         full_total_state.more \<omega> = full_total_state.more \<omega>'"
  using assms
  unfolding greater_def
  unfolding plus_full_total_state_ext_def defined_def plus_total_state_ext_def
  by (force split: if_split if_split_asm)

(*
lemma succ_total_stateI:
  assumes "get_mh_total \<phi> \<succeq> get_mh_total \<phi>'"  (is "?mh \<succeq> ?mh'")
      and "get_mp_total \<phi> \<succeq> get_mp_total \<phi>'"  (is "?mp \<succeq> ?mp'")
      and "get_hh_total \<phi> = get_hh_total \<phi>'"
      and "get_hp_total \<phi> = get_hp_total \<phi>'"
      and "total_state.more \<phi> = total_state.more \<phi>'"
    shows "\<phi> \<succeq> \<phi>'"
proof -
  from assms(1-2) obtain mh_diff mp_diff where
    Eqns: "?mh' \<oplus> mh_diff = Some ?mh" "?mp' \<oplus> mp_diff = Some ?mp"
    by (auto simp: greater_def)

  have "\<phi>' \<oplus> (update_m_total \<phi>' (mh_diff,mp_diff)) = Some \<phi>"
    unfolding plus_total_state_ext_def
    apply (simp add: Eqns)
    apply (rule total_state.equality)
    using assms
    by auto

  thus ?thesis
    unfolding greater_def
    by metis
qed

lemma succ_full_total_stateI:
  assumes "get_mh_total_full \<omega> \<succeq> get_mh_total_full \<omega>'"
      and "get_mp_total_full \<omega> \<succeq> get_mp_total_full \<omega>'"
      and "get_h_total_full \<omega> = get_h_total_full \<omega>'"
      and "get_store_total \<omega> = get_store_total \<omega>'"
      and "get_trace_total \<omega> = get_trace_total \<omega>'"
      and "full_total_state.more \<omega> = full_total_state.more \<omega>'"
    shows "\<omega> \<succeq> \<omega>'"
proof -
  have "get_total_full \<omega> \<succeq> get_total_full \<omega>'" (is "?\<phi> \<succeq> ?\<phi>'")
    apply (rule succ_total_stateI)
    using assms
    by auto

  from this obtain \<phi>_diff where *: "?\<phi>' \<oplus> \<phi>_diff = Some ?\<phi>"
    by (auto simp: greater_def)

  have "Some \<omega> = \<omega>' \<oplus> (\<omega> \<lparr> get_total_full := \<phi>_diff \<rparr>)"
    unfolding plus_full_total_state_ext_def defined_def
    apply (clarsimp split: if_split)
    apply (intro conjI)
  proof -
    show "\<exists>y. get_total_full \<omega>' \<oplus> \<phi>_diff = Some y"
      by (metis * )
  next
    fix A \<comment>\<open>LHS irrelevant\<close>
    show "A \<longrightarrow> \<omega> = \<omega>'\<lparr>get_total_full := the (get_total_full \<omega>' \<oplus> \<phi>_diff)\<rparr>"
    proof (rule impI, simp add: * )
      show "\<omega> = \<omega>'\<lparr>get_total_full := get_total_full \<omega>\<rparr>"
        apply (rule full_total_state.equality)
        using assms by auto
    qed
  qed (insert assms, simp_all)

  thus ?thesis
    by (auto simp add: greater_def)
qed
*)

lemma greater_full_total_state_total_state:
  assumes "\<omega> \<succeq> \<omega>'"
  shows "get_total_full \<omega> \<succeq> get_total_full \<omega>'"
  using assms
  unfolding greater_def plus_full_total_state_ext_def
  by (metis defined_def full_total_state.select_convs(3) full_total_state.surjective full_total_state.update_convs(3) option.distinct(1) option.exhaust_sel option.sel)


lemma total_state_greater_mask:
  assumes "\<phi> \<succeq> \<phi>'"
  shows "get_mh_total \<phi> \<succeq> get_mh_total \<phi>' \<and> get_mp_total \<phi> \<succeq> get_mp_total \<phi>'"
  sorry
(*
proof -

  from assms obtain \<phi>a where "\<phi>' \<oplus> \<phi>a = Some \<phi>"
    unfolding greater_def
    by auto

  hence "get_mh_total \<phi> = add_masks (get_mh_total \<phi>') (get_mh_total \<phi>a)" and
        "get_mp_total \<phi> = add_masks (get_mp_total \<phi>') (get_mp_total \<phi>a)"
    using plus_Some_total_state_eq
    by fastforce+

  thus ?thesis
    using mask_plus_Some
    unfolding greater_def
    by metis
qed
*)

lemma full_total_state_greater_mask:
  assumes "\<omega> \<succeq> \<omega>'"
  shows "get_mh_total_full \<omega> \<succeq> get_mh_total_full \<omega>' \<and> get_mp_total_full \<omega> \<succeq> get_mp_total_full \<omega>'"
  using greater_full_total_state_total_state[OF assms] total_state_greater_mask
  by auto

lemma total_state_greater_equiv:
  shows "(\<omega> :: 'a total_state) \<succeq> \<omega>' \<longleftrightarrow> \<omega> \<ge> \<omega>'"
  sorry
(*
proof
  assume "\<omega> \<succeq> \<omega>'"

  from this obtain \<omega>2 where Sum: "\<omega>' \<oplus> \<omega>2 = Some \<omega>"
    by (auto simp add: greater_def)

  show "\<omega> \<ge> \<omega>'"
    unfolding plus_Some_total_state_eq[OF Sum]
    by (rule less_eq_total_stateI) (simp_all add: less_eq_add_masks)
next
  assume *: "\<omega> \<ge> \<omega>'"

  let ?mh2 = "\<lambda>l. get_mh_total \<omega> l - get_mh_total \<omega>' l"
  let ?mp2 = "\<lambda>l. get_mp_total \<omega> l - get_mp_total \<omega>' l"

  have MhEq: "get_mh_total \<omega> = add_masks (get_mh_total \<omega>') ?mh2"
    unfolding add_masks_def
  proof
    fix hl
    have "get_mh_total \<omega> hl \<ge> get_mh_total \<omega>' hl"
    using less_eq_total_stateD[OF *]
    by (simp add: le_funD)

    thus "get_mh_total \<omega> hl = padd (get_mh_total \<omega>' hl) (get_mh_total \<omega> hl - get_mh_total \<omega>' hl)"
      by (simp add:Rep_preal_inject[symmetric] minus_preal.rep_eq plus_preal.rep_eq)
  qed

  have MpEq: "get_mp_total \<omega> = add_masks (get_mp_total \<omega>') ?mp2"
    unfolding add_masks_def
  proof
    fix hl
    have "get_mp_total \<omega> hl \<ge> get_mp_total \<omega>' hl"
    using less_eq_total_stateD[OF *]
    by (simp add: le_funD)

    thus "get_mp_total \<omega> hl = padd (get_mp_total \<omega>' hl) (get_mp_total \<omega> hl - get_mp_total \<omega>' hl)"
      by (simp add:Rep_preal_inject[symmetric] minus_preal.rep_eq plus_preal.rep_eq)
  qed

  have "Some \<omega> = \<omega>' \<oplus> (\<omega> \<lparr> get_mh_total := ?mh2, get_mp_total := ?mp2 \<rparr>)"
    unfolding plus_total_state_ext_def
    using MhEq MpEq less_eq_total_stateD[OF *]
    by (auto simp: mask_plus_Some)

  thus "\<omega> \<succeq> \<omega>'"
    by (auto simp add: greater_def)
qed
*)

lemma full_total_state_succ_implies_gte:
  assumes "(\<omega> :: 'a full_total_state) \<succeq> \<omega>'"
  shows "\<omega> \<ge> \<omega>'"
  sorry
(*
proof -
  from assms obtain \<omega>2 where Sum: "\<omega>' \<oplus> \<omega>2 = Some \<omega>"
    by (auto simp add: greater_def)

  show "\<omega> \<ge> \<omega>'"
    unfolding plus_Some_full_total_state_eq[OF Sum]
    apply (rule less_eq_full_total_stateI)
       apply simp
      apply simp
    using less_eq_add_masks plus_Some_full_total_state_eq[OF Sum] \<open>\<omega> \<succeq> \<omega>'\<close>
          greater_full_total_state_total_state total_state_greater_equiv
     apply blast
    by simp
qed
*)

lemma full_total_state_gte_implies_succ:
  assumes "\<omega> \<ge> \<omega>'"
      and TraceEq: "get_trace_total \<omega> = get_trace_total \<omega>'"
    shows "(\<omega> :: 'a full_total_state) \<succeq> \<omega>'"
  sorry
(*
proof -
  from \<open>\<omega> \<ge> \<omega>'\<close> have "get_total_full \<omega> \<ge> get_total_full \<omega>'"
    using less_eq_full_total_state_ext_def
    by auto

  hence "get_total_full \<omega> \<succeq> get_total_full \<omega>'"
    by (simp add: total_state_greater_equiv)

  thus "\<omega> \<succeq> \<omega>'"
    using TraceEq less_eq_full_total_stateD
    using assms(1) less_eq_full_total_stateD_2 succ_full_total_stateI total_state_greater_mask
    by fastforce
qed
*)

subsection \<open>Partial commutative monoid with core instantiation\<close>

instantiation total_state_ext :: (type,type) pcm_with_core
begin

definition core_total_state_ext :: "('a,'b) total_state_ext \<Rightarrow> ('a, 'b) total_state_ext"
  where "core_total_state_ext \<phi> = (upd_nm_total \<phi> 0)"

instance
  sorry
(*
proof
  fix a b c x y :: "('a,'b) total_state_ext"

  show "Some x = x \<oplus> |x|"
    unfolding core_total_state_ext_def plus_total_state_ext_def
    by simp

  show "Some |x| = |x| \<oplus> |x|"
    unfolding core_total_state_ext_def plus_total_state_ext_def
    by simp

  show "Some x = x \<oplus> c \<Longrightarrow> \<exists>r. Some |x| = c \<oplus> r" (is "?lhs \<Longrightarrow> ?rhs")
  proof -
    assume ?lhs

    have "get_nm_total c = 0" \<comment> \<open>Todo: This is actually incorrect. \<open>c\<close> might be something equivalent to \<open>empty_nm\<close>.\<close>
      by ..

    thus ?thesis
      by (metis \<open>Some x = x \<oplus> c\<close> \<open>Some x = x \<oplus> |x|\<close> plus_total_state_zero_mask total_state_plus_defined)
  qed

  show "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|"
    unfolding core_total_state_ext_def plus_total_state_ext_def
    by (clarsimp split: if_split if_split_asm simp: plus_mask_zero_mask_neutral)

  show "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y" (is "?A \<Longrightarrow> ?B \<Longrightarrow> _ \<Longrightarrow> _")
    \<comment>\<open>\<^prop>\<open>|x| = |y|\<close> is not needed, since it is always the case if he heap of \<^term>\<open>x\<close> and \<^term>\<open>y\<close>
       are the same, which it must be because of the first two assumptions\<close>
  proof -
    assume ?A and ?B

    from \<open>?A\<close> have Eqx1: "a = b \<lparr> get_mh_total := add_masks (get_mh_total b) (get_mh_total x),
                            get_mp_total := add_masks (get_mp_total b) (get_mp_total x) \<rparr>"
      using plus_Some_total_state_eq
      by metis

    from \<open>?B\<close> have Eqy1: "a = b \<lparr> get_mh_total := add_masks (get_mh_total b) (get_mh_total y),
                            get_mp_total := add_masks (get_mp_total b) (get_mp_total y) \<rparr>"
      using plus_Some_total_state_eq
      by metis

    from Eqx1 have Eqx2: "get_mh_total a = add_masks (get_mh_total b) (get_mh_total x) \<and>
                    get_mp_total a = add_masks (get_mp_total b) (get_mp_total x)"
      by simp

    from Eqy1 have Eqy2: "get_mh_total a = add_masks (get_mh_total b) (get_mh_total y) \<and>
                    get_mp_total a = add_masks (get_mp_total b) (get_mp_total y)"
      by simp

    have "get_mh_total x = get_mh_total y \<and> get_mp_total x = get_mp_total y"
      unfolding add_masks_def
       \<comment>\<open>one could instead do a proof here that does not unfold \<^term>\<open>add_masks\<close> and instead uses the properties
        of the mask core instantiation (but the current proof is more straightforward)\<close>
      by (metis Eqx2 Eqy2 add_masks_minus)

    thus ?thesis
      by (metis \<open>?A\<close> \<open>?B\<close> total_state.equality total_state_plus_defined)
  qed
qed
*)

end


instantiation full_total_state_ext :: (type,type) pcm_with_core
begin

text \<open>In the following, we do not take the core of the trace, because the addition of states is
      defined only if the traces are the same.\<close>

definition core_full_total_state_ext :: "('a,'b) full_total_state_ext \<Rightarrow> ('a, 'b) full_total_state_ext"
  where "core_full_total_state_ext \<omega> =
            \<omega> \<lparr> get_total_full := |get_total_full \<omega>| \<rparr>"
instance sorry (* proof
  fix a b c x y :: "('a,'b) full_total_state_ext"

  let ?at = "get_total_full a"
  let ?bt = "get_total_full b"
  let ?ct = "get_total_full c"
  let ?xt = "get_total_full x"
  let ?yt = "get_total_full y"


  show "Some x = x \<oplus> |x|"
  proof -
    from core_is_smaller[where ?x = ?xt]
    show ?thesis
      unfolding core_full_total_state_ext_def plus_full_total_state_ext_def defined_def
      using option.sel
      by (fastforce split: if_split_asm)
  qed

  show "Some |x| = |x| \<oplus> |x|"
  proof -
    from core_is_pure[where ?x = ?xt]
    show ?thesis
      unfolding core_full_total_state_ext_def plus_full_total_state_ext_def defined_def
      using option.sel
      by (fastforce split: if_split_asm)
  qed

  show "Some x = x \<oplus> c \<Longrightarrow> \<exists>r. Some |x| = c \<oplus> r" (is "?A \<Longrightarrow> _")
  proof -
    assume ?A
    hence "Some ?xt = ?xt \<oplus> ?ct"
      by (blast intro: plus_Some_full_total_state_total_state)

    from core_max[OF plus_Some_full_total_state_total_state[OF \<open>?A\<close>]] obtain rt where Eq_xt: "Some |?xt| = ?ct \<oplus> rt"
      by blast

    let ?r = "x \<lparr> get_total_full := rt \<rparr>"

    have "Some |x| = c \<oplus> ?r"
      using \<open>?A\<close>
      unfolding core_full_total_state_ext_def plus_full_total_state_ext_def defined_def
      apply (simp split: if_split_asm if_split)
      using Eq_xt
      by (metis full_total_state.surjective full_total_state.update_convs(3) option.sel)

    thus ?thesis
      by blast
  qed


  show "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|" (is "?A \<Longrightarrow> _")
  proof -
    assume "?A"
    hence *: "Some ?ct = ?at \<oplus> ?bt"
      by (blast intro: plus_Some_full_total_state_total_state)

    show ?thesis
      unfolding core_full_total_state_ext_def plus_full_total_state_ext_def defined_def
      apply (simp split: if_split_asm if_split)
      using core_sum[OF *]
      by (metis (no_types, lifting) \<open>?A\<close> full_total_state.surjective full_total_state.update_convs(3) option.distinct(1) option.sel plus_full_total_state_ext_def)
  qed


  show "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y" (is "?A \<Longrightarrow> ?B \<Longrightarrow> ?C \<Longrightarrow> _")
  proof -
    assume "?A" and "?B" and "?C"

    from \<open>?A\<close> have "Some ?at = ?bt \<oplus> ?xt"
      by (blast intro: plus_Some_full_total_state_total_state)

    moreover from \<open>?B\<close> have "Some ?at = ?bt \<oplus> ?yt"
      by (blast intro: plus_Some_full_total_state_total_state)

    moreover from \<open>?C\<close> have "|?xt| = |?yt|"
      unfolding core_full_total_state_ext_def
      by (metis full_total_state.select_convs(3) full_total_state.surjective full_total_state.update_convs(3))

    ultimately have "?xt = ?yt"
      using cancellative by blast

    thus ?thesis
      by (metis Some_Some_ifD \<open>?A\<close> \<open>?B\<close> full_total_state.surjective plus_full_total_state_ext_def)
  qed
qed
*)

end


subsubsection \<open>Lemmas\<close>

lemma total_state_defined_core_same:
  assumes "(\<phi> :: 'a total_state) ## \<phi>'"
  shows "|\<phi>| = |\<phi>'|"
  using assms
  unfolding defined_def plus_total_state_ext_def core_total_state_ext_def
  by (simp split: if_split_asm)

lemma full_total_state_defined_core_same:
  assumes "(\<omega> :: 'a full_total_state) ## \<omega>'"
  shows "|\<omega>| = |\<omega>'|"
  using assms total_state_defined_core_same
  unfolding defined_def plus_full_total_state_ext_def core_full_total_state_ext_def
  by (fastforce split: if_split_asm)

lemma full_total_state_defined_core_same_2:
  assumes "(\<omega> :: 'a full_total_state) \<oplus> \<omega>' = Some \<omega>''"
  shows "|\<omega>| = |\<omega>'|"
  using assms full_total_state_defined_core_same
  unfolding defined_def
  by fast

(*
lemma minus_total_state:
  assumes "\<phi> \<succeq> \<phi>'"
  shows "\<phi> \<ominus> \<phi>' = \<phi> \<lparr> get_mh_total := get_mh_total \<phi> - get_mh_total \<phi>',
                      get_mp_total := get_mp_total \<phi> - get_mp_total \<phi>' \<rparr>" (is "_ = ?\<Delta>")
proof -
  from assms minus_exists obtain \<phi>m
    where PlusSome: "Some \<phi> = \<phi>' \<oplus> \<phi>m" and "\<phi>m \<succeq> |\<phi>|"
    by blast

  hence "\<phi>m = \<phi> \<ominus> \<phi>'"
    using minusI by auto

  from PlusSome have
     PlusMh: "get_mh_total \<phi> = add_masks (get_mh_total \<phi>') (get_mh_total \<phi>m)" and
     PlusMp: "get_mp_total \<phi> = add_masks (get_mp_total \<phi>') (get_mp_total \<phi>m)"
    unfolding plus_total_state_ext_def
    by (auto split: if_split_asm simp: mask_plus_Some)

  have "get_mh_total \<phi>m = get_mh_total \<phi> - get_mh_total \<phi>'"
    using add_masks_minus PlusMh
    by blast

  moreover have "get_mp_total \<phi>m = get_mp_total \<phi> - get_mp_total \<phi>'"
    using add_masks_minus PlusMp
    by blast

  moreover from PlusSome have "get_hh_total \<phi> = get_hh_total \<phi>m \<and>
                               get_hp_total \<phi> = get_hp_total \<phi>m \<and>
                               total_state.more \<phi> = total_state.more \<phi>m"
    by (metis total_state_plus_defined)
  ultimately have "\<phi>m = ?\<Delta>"
    by simp
  thus ?thesis
    using \<open>\<phi>m = \<phi> \<ominus> \<phi>'\<close>
    by argo
qed
*)

lemma minus_full_total_state_only_mask_different:
  shows "get_store_total (\<omega> \<ominus> \<omega>') = get_store_total \<omega> \<and>
         get_trace_total (\<omega> \<ominus> \<omega>') = get_trace_total \<omega> \<and>
         get_hh_total_full (\<omega> \<ominus> \<omega>') = get_hh_total_full \<omega>"
  using full_total_state_greater_only_mask_changed minus_default minus_smaller
  by metis

lemma minus_full_total_state_only_mask_different_2:
  assumes "\<omega>_inh \<oplus> (\<omega> \<ominus> \<omega>') = Some \<omega>_inh'"
  shows
    "get_store_total \<omega>_inh = get_store_total \<omega> \<and>
     get_trace_total \<omega>_inh = get_trace_total \<omega> \<and>
     get_hh_total_full \<omega>_inh = get_hh_total_full \<omega>"
  by (metis assms full_total_state_greater_only_mask_changed greater_def minus_bigger minus_full_total_state_only_mask_different)

lemma minus_full_total_state:
  assumes "\<omega> \<succeq> \<omega>'"
  shows "\<omega> \<ominus> \<omega>' = \<omega> \<lparr> get_total_full := get_total_full \<omega> \<ominus> get_total_full \<omega>' \<rparr>" (is "_ = ?\<Delta>")
  sorry
(*
proof -
  from assms minus_exists obtain \<omega>m
    where PlusSome: "\<omega>' \<oplus> \<omega>m = Some \<omega>" and "\<omega>m \<succeq> |\<omega>|"
    by force

  hence "\<omega>m = \<omega> \<ominus> \<omega>'"
    using minusI
    by metis

  from plus_Some_full_total_state_eq[OF PlusSome] have
     PlusMh: "get_mh_total_full \<omega> = add_masks (get_mh_total_full \<omega>') (get_mh_total_full \<omega>m)" and
     PlusMp: "get_mp_total_full \<omega> = add_masks (get_mp_total_full \<omega>') (get_mp_total_full \<omega>m)"
    by simp_all


  have "get_mh_total_full \<omega>m = get_mh_total_full \<omega> - get_mh_total_full \<omega>'"
    using add_masks_minus PlusMh
    by blast

  moreover have "get_mp_total_full \<omega>m = get_mp_total_full \<omega> - get_mp_total_full \<omega>'"
    using add_masks_minus PlusMp
    by blast

  moreover from PlusSome have "get_store_total \<omega> = get_store_total \<omega>m \<and>
                               get_trace_total \<omega> = get_trace_total \<omega>m \<and>
                               get_h_total_full \<omega> = get_h_total_full \<omega>m \<and>
                               full_total_state.more \<omega> = full_total_state.more \<omega>m"
    by (metis \<open>\<omega>m = \<omega> \<ominus> \<omega>'\<close> core_is_smaller minus_equiv_def_any_elem minus_full_total_state_only_mask_different option.discI plus_full_total_state_ext_def)

  ultimately have "\<omega>m = ?\<Delta>"
    using minus_total_state[OF greater_full_total_state_total_state[OF assms]]
    by simp
  thus ?thesis
    using \<open>\<omega>m = \<omega> \<ominus> \<omega>'\<close>
    by argo
qed
*)

lemma minus_full_total_state_mask:
  assumes "\<omega> \<succeq> \<omega>'"
  shows "get_mh_total_full (\<omega> \<ominus> \<omega>') = get_mh_total_full \<omega> - get_mh_total_full \<omega>' \<and>
         get_mp_total_full (\<omega> \<ominus> \<omega>') = get_mp_total_full \<omega> - get_mp_total_full \<omega>'"
  sorry
(*
proof -
  from minus_full_total_state[OF assms]
  have "get_total_full (\<omega> \<ominus> \<omega>') = get_total_full \<omega> \<ominus> get_total_full \<omega>'" (is "_ = ?\<phi> \<ominus> ?\<phi>'")
    by simp

  thus ?thesis
  using greater_full_total_state_total_state[OF assms, THEN minus_total_state]
  by simp
qed
*)

subsection \<open>Monotonicity relationship\<close>

text \<open>The following lemma shows for \<^typ>\<open>'a full_total_state\<close> that downwards monotonicity w.r.t.
the order type class is at least as strong as downwards monotoncity w.r.t. order defined via the pcm
addition. The converse is not true, because the order type class instantiation is a larger relation
(since traces need not be equal as opposed to the pcm addition case where traces must be equal).\<close>

lemma mono_prop_downward_ord_implies_mono_prop_downward:
  assumes "mono_prop_downward_ord (StateCons :: 'a full_total_state \<Rightarrow> bool)"
  shows "mono_prop_downward StateCons"
  using assms full_total_state_succ_implies_gte
  unfolding mono_prop_downward_ord_def mono_prop_downward_def
  by blast

subsection \<open>valid mask (TODO: move to ViperLang?)\<close>

abbreviation valid_heap_mask :: "preal mask \<Rightarrow> bool"
  where "valid_heap_mask \<equiv> wf_mask_simple"

lemma valid_heap_maskD:
  assumes "valid_heap_mask m"
  shows "pgte pwrite (m l)"
  using assms
  unfolding wf_mask_simple_def
  apply transfer
  by blast

lemma valid_heap_mask_downward_mono:
  assumes "valid_heap_mask m0" and "m0 \<succeq> m1"
  shows "valid_heap_mask m1"
proof -
  from \<open>m0 \<succeq> m1\<close> obtain m2 where "m0 = add_masks m1 m2"
    unfolding greater_def
    using mask_plus_Some
    by (metis option.sel)

  show "valid_heap_mask m1"
    unfolding wf_mask_simple_def
  proof
    fix l
    have "m0 l = padd (m1 l) (m2 l)"
      using \<open>m0 = _\<close>
      by (simp add: add_masks_def)

    thus "pwrite \<ge> (m1 l)"
      using valid_heap_maskD[of m0 l, OF assms(1)] \<open>m0 = add_masks m1 m2\<close> assms(1) wf_mask_simple_def wf_mask_simple_false_preserved
      by blast
  qed
qed


end
