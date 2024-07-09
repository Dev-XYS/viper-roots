theory NestedMaskProperties
  imports TotalSemanticsCore HOL.Groups_Big "HOL-Analysis.Infinite_Sum"
begin


fun domain :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set" where
  "domain f = {x . True}"

abbreviation has_sumA (infixr "has'_sumA" 46) where
  "(f has_sumA S) \<equiv> (f has_sum S) (domain f)"

function (sequential) nm_loc_sum :: "heap_loc \<Rightarrow> 'a nested_mask \<Rightarrow> preal \<Rightarrow> bool" where
  "nm_loc_sum loc (NM mh mp fnm) p =
     (mh loc \<le> p \<and>
      (\<exists>pf. pf has_sumA (p - mh loc) \<and>
            (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf ploc)) (pf ploc = 0) (fnm ploc))))"
  by (pat_completeness) auto
termination
  apply (relation "{} <*lex*> nested_mask_rel <*lex*> {}")
  using wf_nested_mask_rel
   apply blast
  by (metis (mono_tags, lifting) in_lex_prod mem_Collect_eq)


lemma nm_loc_sum_add:
  assumes "nm_loc_sum loc nm\<^sub>1 p"
      and "nm_loc_sum loc nm\<^sub>2 q"
    shows "nm_loc_sum loc (nested_mask_merge nm\<^sub>1 nm\<^sub>2) (p + q)"
  using assms
proof (induct arbitrary: p q rule: nested_mask_merge.induct[of _ nm\<^sub>1 nm\<^sub>2])
  case IH: (1 mh\<^sub>1 mp\<^sub>1 fnm\<^sub>1 mh\<^sub>2 mp\<^sub>2 fnm\<^sub>2)
  show ?case
    (* apply (simp del: nm_loc_sum.simps) *)
  proof -
    from IH have "mh\<^sub>1 loc \<le> p" and "mh\<^sub>2 loc \<le> q"
      by (metis get_mh_nm.simps nm_loc_sum.elims(1))+
    from IH(2) obtain pf\<^sub>1 where pf\<^sub>1: "pf\<^sub>1 has_sumA (p - mh\<^sub>1 loc) \<and>
      (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf\<^sub>1 ploc)) (pf\<^sub>1 ploc = 0) (fnm\<^sub>1 ploc))"
      by (metis nm_loc_sum.simps)
    from IH(3) obtain pf\<^sub>2 where pf\<^sub>2: "pf\<^sub>2 has_sumA (q - mh\<^sub>2 loc) \<and>
      (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf\<^sub>2 ploc)) (pf\<^sub>2 ploc = 0) (fnm\<^sub>2 ploc))" 
      by (metis nm_loc_sum.simps)
    define pf where "pf = (pf\<^sub>1 +\<lbrakk>(+)\<rbrakk>+ pf\<^sub>2)"
    hence "domain pf = domain pf\<^sub>1" and "domain pf = domain pf\<^sub>2" by auto+
    hence has_sum: "pf has_sumA ((p - mh\<^sub>1 loc) + (q - mh\<^sub>2 loc))"
      using has_sum_add[of pf\<^sub>1 "domain pf" "p - mh\<^sub>1 loc" pf\<^sub>2 "q - mh\<^sub>2 loc"] fun_comb_def
      by (metis (no_types, lifting) pf\<^sub>1 pf\<^sub>2 has_sum_cong pf_def)
    define fnm where "fnm = (fnm\<^sub>1 +\<lparr>nested_mask_merge\<rparr>+ fnm\<^sub>2)"
    have all_sub: "\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf ploc)) (pf ploc = 0) (fnm ploc)"
    proof
      fix ploc
      show "option_fold (\<lambda>m. nm_loc_sum loc m (pf ploc)) (pf ploc = 0) (fnm ploc)"
      proof (cases "fnm\<^sub>1 ploc")
        case c1N: None
        show ?thesis
        proof (cases "fnm\<^sub>2 ploc")
          case c2N: None
          show ?thesis
            apply (simp del: nm_loc_sum.simps add: fnm_def pfun_comb_def combine_options_def option_fold_def)
            apply (simp del: nm_loc_sum.simps add: c1N c2N)
            by (metis (full_types) add_0 c1N c2N fun_comb_def option_fold.simps(2) pf\<^sub>1 pf\<^sub>2 pf_def)
        next
          case c2S: (Some a)
          show ?thesis
            apply (simp del: nm_loc_sum.simps add: fnm_def pfun_comb_def combine_options_def option_fold_def)
            apply (simp del: nm_loc_sum.simps add: c1N c2S)
            by (metis (mono_tags, lifting) add_0 c1N c2S fun_comb_def option_fold.simps(1) option_fold.simps(2) pf\<^sub>1 pf\<^sub>2 pf_def)
        qed
      next
        case c1S: (Some a)
        show ?thesis
        proof (cases "fnm\<^sub>2 ploc")
          case c2N: None
          show ?thesis
            apply (simp del: nm_loc_sum.simps add: fnm_def pfun_comb_def combine_options_def option_fold_def)
            apply (simp del: nm_loc_sum.simps add: c1S c2N)
            by (metis (mono_tags, lifting) add.right_neutral c1S c2N fun_comb_def option_fold.simps(1) option_fold.simps(2) pf\<^sub>1 pf\<^sub>2 pf_def)
        next
          case c2S: (Some a)
          show ?thesis
            apply (simp del: nm_loc_sum.simps add: fnm_def pfun_comb_def combine_options_def option_fold_def)
            apply (simp del: nm_loc_sum.simps add: c1S c2S)
            by (metis (mono_tags, lifting) IH.hyps c1S c2S fun_comb_def option_fold.simps(1) pf\<^sub>1 pf\<^sub>2 pf_def)
        qed
      qed
    qed
    define mh where "mh = field_mask_merge mh\<^sub>1 mh\<^sub>2"
    define mp where "mp = predicate_mask_merge mp\<^sub>1 mp\<^sub>2"
    have "mh loc \<le> p + q"
      by (simp add: PosReal.padd_mono \<open>mh\<^sub>1 loc \<le> p\<close> \<open>mh\<^sub>2 loc \<le> q\<close> fun_comb_def mh_def)
    moreover from has_sum all_sub have
      "\<exists>pf. pf has_sumA ((p - mh\<^sub>1 loc) + (q - mh\<^sub>2 loc)) \<and>
            (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf ploc)) (pf ploc = 0) (fnm ploc))"
      by metis
    moreover have "mh loc = mh\<^sub>1 loc + mh\<^sub>2 loc"
      by (simp add: fun_comb_def mh_def)
    have "p + q \<ge> mh\<^sub>1 loc + mh\<^sub>2 loc"
      using PosReal.padd_mono \<open>mh\<^sub>1 loc \<le> p\<close> \<open>mh\<^sub>2 loc \<le> q\<close> by presburger
    moreover hence "(p - mh\<^sub>1 loc) + (q - mh\<^sub>2 loc) = (p + q) - (mh\<^sub>1 loc + mh\<^sub>2 loc)"
      using \<open>mh\<^sub>1 loc \<le> p\<close> \<open>mh\<^sub>2 loc \<le> q\<close> Rep_preal_inject minus_preal.rep_eq plus_preal.rep_eq
      by fastforce
    moreover have "nested_mask_merge (NM mh\<^sub>1 mp\<^sub>1 fnm\<^sub>1) (NM mh\<^sub>2 mp\<^sub>2 fnm\<^sub>2) = NM mh mp fnm"
      by (simp add: fnm_def mh_def mp_def)
    ultimately show "nm_loc_sum loc (nested_mask_merge (NM mh\<^sub>1 mp\<^sub>1 fnm\<^sub>1) (NM mh\<^sub>2 mp\<^sub>2 fnm\<^sub>2)) (p + q)"
      by (simp add: \<open>mh loc = PosReal.padd (mh\<^sub>1 loc) (mh\<^sub>2 loc)\<close>)
  qed
qed

thm nested_mask_multiply.induct
lemma nm_loc_sum_mult:
    fixes frac :: preal
  assumes "frac > 0"
      and "nm_loc_sum loc nm p"
    shows "nm_loc_sum loc (nested_mask_multiply nm frac) (p * frac)"
  using assms(2)
proof (induct arbitrary: p rule: nested_mask_multiply.induct[of _ nm p])
  case IH: (1 mh mp fnm p)
  define mh' where "mh' = field_mask_multiply mh frac"
  define mp' where "mp' = predicate_mask_multiply mp frac"
  define fnm' where "fnm' = (map_option (\<lambda>nm. nested_mask_multiply nm frac)) \<circ> fnm"
  have "mh' loc \<le> p * frac"
    apply (simp add: mh'_def)
    using IH(2)
    by (simp add: less_eq_preal.rep_eq mult.commute mult_left_mono prat_non_negative times_preal.rep_eq)
  from IH(2) obtain pf where pf: "pf has_sumA (p - mh loc) \<and>
      (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf ploc)) (pf ploc = 0) (fnm ploc))"
    using nm_loc_sum.simps by blast
  define pf' where "pf' = ((*) frac) \<circ> pf"
  moreover hence "domain pf' = domain pf" by simp
  moreover have "frac * p - mh' loc = frac * p - frac * mh loc"
    by (simp add: mh'_def)
  moreover hence "frac * p - mh' loc = frac * (p - mh loc)"
    by (smt (verit, ccfv_threshold) IH.prems PosReal.pmult_comm Rep_preal_inverse \<open>mh' loc \<le> PosReal.pmult p frac\<close> comp_apply field_mask_multiply.simps mh'_def minus_preal.rep_eq nm_loc_sum.simps right_diff_distrib times_preal.rep_eq)
  ultimately have "pf' has_sumA (frac * p - mh' loc)"
    using has_sum_cmult_right[of pf "domain pf" "p - mh loc" frac] pf pf'_def
    by (metis (no_types, lifting) comp_apply has_sum_cong)
  moreover have "(\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf' ploc)) (pf' ploc = 0) (fnm' ploc))"
  proof
    fix ploc
    show "option_fold (\<lambda>m. nm_loc_sum loc m (pf' ploc)) (pf' ploc = PosReal.pnone) (fnm' ploc)"
    proof (cases "fnm ploc")
      case None
      then show ?thesis
        by (metis (mono_tags, lifting) comp_apply fnm'_def mult_zero_right option.simps(8) option_fold.simps(2) pf pf'_def)
    next
      case (Some nm)
      hence "fnm' ploc = Some (nested_mask_multiply nm frac)"
        using fnm'_def by simp
      then show ?thesis
        apply simp
        using IH(1)[of "fnm ploc" nm]
        by (metis Some comp_apply mult.commute option_fold.simps(1) pf pf'_def rangeI)
    qed
  qed
  ultimately show ?case
    using PosReal.pmult_comm \<open>mh' loc \<le> PosReal.pmult p frac\<close> fnm'_def mh'_def by auto
qed


end
