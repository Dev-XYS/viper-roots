theory NestedMaskProperties
  imports TotalSemanticsCore HOL.Groups_Big "HOL-Analysis.Infinite_Sum"
begin


fun domain :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set" where
  "domain f = {x . True}"

function (sequential) nm_loc_sum :: "heap_loc \<Rightarrow> 'a nested_mask \<Rightarrow> preal \<Rightarrow> bool" where
  "nm_loc_sum loc nm p =
     ((get_mh_nm nm loc \<le> p) \<and>
      (\<exists>pf. HAS_SUM pf (domain pf) (p - get_mh_nm nm loc) \<and>
           (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf ploc)) (pf ploc = 0) (get_nm_loc_nm nm ploc))))"
  by (pat_completeness) auto
termination
  apply (relation "{} <*lex*> nested_mask_rel <*lex*> {}")
  using wf_nested_mask_rel
   apply blast
  by (metis (mono_tags, lifting) get_nm_loc_nm.elims in_lex_prod mem_Collect_eq)


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
    from IH(2) obtain pf\<^sub>1 where pf\<^sub>1: "HAS_SUM pf\<^sub>1 (domain pf\<^sub>1) (p - mh\<^sub>1 loc) \<and>
      (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf\<^sub>1 ploc)) (pf\<^sub>1 ploc = 0) (fnm\<^sub>1 ploc))"
      by (metis get_mh_nm.simps get_nm_loc_nm.simps nm_loc_sum.simps)
    from IH(3) obtain pf\<^sub>2 where pf\<^sub>2: "HAS_SUM pf\<^sub>2 (domain pf\<^sub>2) (q - mh\<^sub>2 loc) \<and>
      (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf\<^sub>2 ploc)) (pf\<^sub>2 ploc = 0) (fnm\<^sub>2 ploc))" 
      by (metis get_mh_nm.simps get_nm_loc_nm.simps nm_loc_sum.simps)
    define pf where "pf = (pf\<^sub>1 +\<lbrakk>(+)\<rbrakk>+ pf\<^sub>2)"
    hence "domain pf = domain pf\<^sub>1" and "domain pf = domain pf\<^sub>2" by auto+
    hence has_sum: "HAS_SUM pf (domain pf) ((p - mh\<^sub>1 loc) + (q - mh\<^sub>2 loc))"
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
    define nm where "nm = nested_mask_merge (NM mh\<^sub>1 mp\<^sub>1 fnm\<^sub>1) (NM mh\<^sub>2 mp\<^sub>2 fnm\<^sub>2)"
    have "get_mh_nm nm loc \<le> p + q"
      by (simp add: PosReal.padd_mono \<open>mh\<^sub>1 loc \<le> p\<close> \<open>mh\<^sub>2 loc \<le> q\<close> fun_comb_def nm_def)
    moreover from has_sum all_sub have
      "\<exists>pf. HAS_SUM pf (domain pf) ((p - mh\<^sub>1 loc) + (q - mh\<^sub>2 loc)) \<and>
            (\<forall>ploc. option_fold (\<lambda>m. nm_loc_sum loc m (pf ploc)) (pf ploc = 0) (get_nm_loc_nm nm ploc))"
      by (metis fnm_def get_nm_loc_nm.simps nested_mask_merge_combine_options nm_def)
    moreover have "get_mh_nm nm loc = mh\<^sub>1 loc + mh\<^sub>2 loc"
      by (simp add: fun_comb_def nm_def)
    have "p + q \<ge> mh\<^sub>1 loc + mh\<^sub>2 loc"
      using PosReal.padd_mono \<open>mh\<^sub>1 loc \<le> p\<close> \<open>mh\<^sub>2 loc \<le> q\<close> by presburger
    moreover hence "(p - mh\<^sub>1 loc) + (q - mh\<^sub>2 loc) = (p + q) - (mh\<^sub>1 loc + mh\<^sub>2 loc)"
      using \<open>mh\<^sub>1 loc \<le> p\<close> \<open>mh\<^sub>2 loc \<le> q\<close>
      by (smt (verit, best) Rep_preal_inject minus_preal.rep_eq plus_preal.rep_eq)
    ultimately show "nm_loc_sum loc (nested_mask_merge (NM mh\<^sub>1 mp\<^sub>1 fnm\<^sub>1) (NM mh\<^sub>2 mp\<^sub>2 fnm\<^sub>2)) (p + q)"
      by (metis \<open>get_mh_nm nm loc = PosReal.padd (mh\<^sub>1 loc) (mh\<^sub>2 loc)\<close> nm_def nm_loc_sum.simps)
  qed
qed

end
