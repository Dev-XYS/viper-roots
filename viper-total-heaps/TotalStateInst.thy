section \<open>Total State Instantiations\<close>

theory TotalStateInst
  imports HOL.Groups TotalStateUtil NestedMaskInst
begin


subsection \<open>Order Instantiation\<close>

lemma zero_mask_less_eq_mask: "zero_mask \<le> m"
  unfolding zero_mask_def le_fun_def
  by (simp add: all_pos)


instantiation total_state_ext :: (type,type) order
begin

definition less_eq_total_state_ext :: "('a,'b) total_state_ext \<Rightarrow> ('a,'b) total_state_ext \<Rightarrow> bool"
  where "\<phi>1 \<le> \<phi>2 \<equiv> 
         get_hh_total \<phi>1 = get_hh_total \<phi>2 \<and>
         get_nm_total \<phi>1 \<le> get_nm_total \<phi>2 \<and>
         total_state.more \<phi>1 = total_state.more \<phi>2"

definition less_total_state_ext :: "('a,'b) total_state_ext \<Rightarrow> ('a,'b) total_state_ext \<Rightarrow> bool"
  where "\<phi>1 < \<phi>2 \<equiv> 
         get_hh_total \<phi>1 = get_hh_total \<phi>2 \<and>
         get_nm_total \<phi>1 < get_nm_total \<phi>2 \<and>
         total_state.more \<phi>1 = total_state.more \<phi>2"
instance
proof
  fix x y z :: "('a,'b) total_state_ext"

  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
  proof
    assume "x < y"
    show "x \<le> y \<and> \<not> y \<le> x"
    proof (rule conjI)
      show "x \<le> y"
        using \<open>x < y\<close> 
        unfolding less_total_state_ext_def less_eq_total_state_ext_def
        by auto
    next
      show "\<not> y \<le> x"
      using \<open>x < y\<close> 
      unfolding less_total_state_ext_def less_eq_total_state_ext_def
      by auto
    qed
  next
    assume *: "x \<le> y \<and> \<not> y \<le> x"
    thus "x < y"
      unfolding less_total_state_ext_def less_eq_total_state_ext_def
      by force        
  qed

  show "x \<le> x"
    unfolding less_eq_total_state_ext_def
    by blast

  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    unfolding less_eq_total_state_ext_def
    by auto
  
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    unfolding less_eq_total_state_ext_def
    by auto
qed

end

instantiation full_total_state_ext :: (type,type) order
begin

definition less_eq_full_total_state_ext :: "('a,'b) full_total_state_ext \<Rightarrow> ('a,'b) full_total_state_ext \<Rightarrow> bool"
  where "\<omega>1 \<le> \<omega>2 \<equiv> 
         get_store_total \<omega>1 = get_store_total \<omega>2 \<and>
         dom (get_trace_total \<omega>1) = dom (get_trace_total \<omega>2) \<and>
         (\<forall>lbl \<phi> \<phi>'. (get_trace_total \<omega>1 lbl = Some \<phi> \<and> 
                      get_trace_total \<omega>2 lbl = Some \<phi>') \<longrightarrow> \<phi> \<le> \<phi>') \<and>
         get_total_full \<omega>1 \<le> get_total_full \<omega>2 \<and>
         full_total_state.more \<omega>1 = full_total_state.more \<omega>2"

definition less_full_total_state_ext :: "('a,'b) full_total_state_ext \<Rightarrow> ('a,'b) full_total_state_ext \<Rightarrow> bool"
  where "\<omega>1 < \<omega>2 \<equiv> 
           \<omega>1 \<le> \<omega>2 \<and> 
           (get_total_full \<omega>1 < get_total_full \<omega>2 \<or>
           (\<exists>lbl \<phi> \<phi>'. get_trace_total \<omega>1 lbl = Some \<phi> \<and> get_trace_total \<omega>2 lbl = Some \<phi>' \<and>
                        \<phi> < \<phi>'))"

instance
proof
  fix x y z :: "('a,'b) full_total_state_ext"

  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
  proof
    assume "x < y"
    show "x \<le> y \<and> \<not> y \<le> x"
    proof (rule conjI)
      show "x \<le> y"
        using \<open>x < y\<close> 
        unfolding less_full_total_state_ext_def
        by simp
    next
      from \<open>x < y\<close> consider "get_total_full x < get_total_full y" |
                            "(\<exists>lbl \<phi> \<phi>'. get_trace_total x lbl = Some \<phi> \<and> get_trace_total y lbl = Some \<phi>' \<and>
                                         \<phi> < \<phi>')"
        unfolding less_full_total_state_ext_def
        by blast
      thus "\<not> y \<le> x"
        by (metis less_eq_full_total_state_ext_def leD)
    qed
  next
    assume "x \<le> y \<and> \<not> y \<le> x"
    thus "x < y"
      unfolding less_full_total_state_ext_def less_eq_full_total_state_ext_def
      by fastforce
  qed

  show "x \<le> x"
    unfolding less_eq_full_total_state_ext_def
    by auto

  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  proof -
    assume Leqs: "x \<le> y" "y \<le> z"

    show "x \<le> z"
      unfolding less_eq_full_total_state_ext_def
    proof (intro conjI)
      show "\<forall>lbl \<phi> \<phi>'. get_trace_total x lbl = Some \<phi> \<and> get_trace_total z lbl = Some \<phi>' \<longrightarrow> \<phi> \<le> \<phi>'"
        using Leqs
        unfolding less_eq_full_total_state_ext_def
        by (metis (mono_tags, opaque_lifting) domIff dual_order.trans not_None_eq)
    qed (insert Leqs[simplified less_eq_full_total_state_ext_def], auto)
  qed

  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  proof -
    assume "x \<le> y" and "y \<le> x"

    show ?thesis
    proof (rule full_total_state.equality)
      show "get_store_total x = get_store_total y"
        using \<open>x \<le> y\<close> less_eq_full_total_state_ext_def by blast
    
      show "get_trace_total x = get_trace_total y"
      proof -
        have *: "\<And> lbl \<phi> \<phi>'. get_trace_total x lbl = Some \<phi> \<Longrightarrow> get_trace_total y lbl = Some \<phi>' \<Longrightarrow> \<phi> = \<phi>'"
          using \<open>x \<le> y\<close> \<open>y \<le> x\<close> less_eq_full_total_state_ext_def
          by fastforce
        have DomEq: "dom (get_trace_total x) = dom (get_trace_total y)"
          using \<open>x \<le> y\<close> less_eq_full_total_state_ext_def by blast
        show ?thesis
          apply (rule HOL.ext)
          using * DomEq
          by (metis domIff not_None_eq)
      qed

      show "get_total_full x = get_total_full y"
        using \<open>x \<le> y\<close> \<open>y \<le> x\<close> less_eq_full_total_state_ext_def
        by auto

      show "full_total_state.more x = full_total_state.more y "
        using \<open>x \<le> y\<close> less_eq_full_total_state_ext_def by blast
    qed
  qed         
qed

end


lemma less_eq_nested_maskD: "nm1 \<le> nm2 \<Longrightarrow>
         get_mh_nm nm1 \<le> get_mh_nm nm2 \<and>
         get_mp_nm nm1 \<le> get_mp_nm nm2"
  unfolding less_eq_nested_mask_def
  apply (cases nm1, cases nm2)
  by simp

lemma less_eq_total_stateI:
  " get_hh_total \<phi>1 = get_hh_total \<phi>2 \<Longrightarrow>
     get_nm_total \<phi>1 \<le> get_nm_total \<phi>2 \<Longrightarrow>
    total_state.more \<phi>1 = total_state.more \<phi>2 \<Longrightarrow>
    \<phi>1 \<le> \<phi>2"
  unfolding less_eq_total_state_ext_def
  by blast

lemma less_eq_total_stateD: "\<phi>1 \<le> \<phi>2 \<Longrightarrow>
         get_hh_total \<phi>1 = get_hh_total \<phi>2 \<and>
         get_nm_total \<phi>1 \<le> get_nm_total \<phi>2 \<and>
         total_state.more \<phi>1 = total_state.more \<phi>2"
  unfolding less_eq_total_state_ext_def
  by blast

lemma less_eq_total_stateE:
  assumes "\<phi>1 \<le> \<phi>2" and
          "get_hh_total \<phi>1 = get_hh_total \<phi>2 \<Longrightarrow>
           get_nm_total \<phi>1 \<le> get_nm_total \<phi>2 \<Longrightarrow>
           total_state.more \<phi>1 = total_state.more \<phi>2 \<Longrightarrow> P"
        shows P
  using assms 
  by (auto dest: less_eq_total_stateD)

lemma less_eq_full_total_stateI:
    "get_store_total \<omega>1 = get_store_total \<omega>2 \<Longrightarrow>
     get_trace_total \<omega>1 = get_trace_total \<omega>2 \<Longrightarrow>
     get_total_full \<omega>1 \<le> get_total_full \<omega>2 \<Longrightarrow>
     full_total_state.more \<omega>1 = full_total_state.more \<omega>2 \<Longrightarrow>
     \<omega>1 \<le> \<omega>2"
  unfolding less_eq_full_total_state_ext_def
  by auto

lemma less_eq_full_total_stateI2:
    "get_store_total \<omega>1 = get_store_total \<omega>2 \<Longrightarrow>
     dom (get_trace_total \<omega>1) = dom (get_trace_total \<omega>2) \<Longrightarrow>
     (\<forall>lbl \<phi> \<phi>'. (get_trace_total \<omega>1 lbl = Some \<phi> \<and> 
                      get_trace_total \<omega>2 lbl = Some \<phi>') \<longrightarrow> \<phi> \<le> \<phi>') \<Longrightarrow>
     get_total_full \<omega>1 \<le> get_total_full \<omega>2 \<Longrightarrow>
     full_total_state.more \<omega>1 = full_total_state.more \<omega>2 \<Longrightarrow>
     \<omega>1 \<le> \<omega>2"
  unfolding less_eq_full_total_state_ext_def
  by auto

lemma less_eq_full_total_stateD:
  assumes "\<omega>1 \<le> \<omega>2"
  shows "get_store_total \<omega>1 = get_store_total \<omega>2 \<and>
         dom (get_trace_total \<omega>1) = dom (get_trace_total \<omega>2) \<and>      
         (\<forall>lbl \<phi> \<phi>'. (get_trace_total \<omega>1 lbl = Some \<phi> \<and> 
                      get_trace_total \<omega>2 lbl = Some \<phi>') \<longrightarrow> \<phi> \<le> \<phi>') \<and>   
         get_total_full \<omega>1 \<le> get_total_full \<omega>2 \<and>
         full_total_state.more \<omega>1 = full_total_state.more \<omega>2"
  using assms
  unfolding less_eq_full_total_state_ext_def
  by argo

lemma less_eq_full_total_stateE:
  assumes "\<omega>1 \<le> \<omega>2" and
          "get_store_total \<omega>1 = get_store_total \<omega>2 \<Longrightarrow>
           dom (get_trace_total \<omega>1) = dom (get_trace_total \<omega>2) \<Longrightarrow>   
           (\<forall>lbl \<phi> \<phi>'. (get_trace_total \<omega>1 lbl = Some \<phi> \<and> 
                        get_trace_total \<omega>2 lbl = Some \<phi>') \<longrightarrow> \<phi> \<le> \<phi>') \<Longrightarrow>
           get_total_full \<omega>1 \<le> get_total_full \<omega>2 \<Longrightarrow>
           full_total_state.more \<omega>1 = full_total_state.more \<omega>2 \<Longrightarrow> P"
  shows P
  using assms
  unfolding less_eq_full_total_state_ext_def
  by blast


subsection \<open>Ordering lemmas\<close>

lemma less_eq_full_total_stateD_2:
  assumes "\<omega>1 \<le> \<omega>2"
  shows "get_hh_total_full \<omega>1 = get_hh_total_full \<omega>2 \<and>
         get_nm_total_full \<omega>1 \<le> get_nm_total_full \<omega>2"
  using assms
  by (fastforce dest: less_eq_full_total_stateD less_eq_total_stateD)

lemma update_mh_loc_nm_mono:
  assumes "nm1 \<le> nm2" and "p1 \<le> p2"
  shows "upd_mh_loc_nm nm1 l p1 \<le> upd_mh_loc_nm nm2 l p2"
  apply (cases nm1, cases nm2)
  apply (simp add: less_eq_nested_mask_def)
  using assms(1)[simplified less_eq_nested_mask_def]
  by (simp add: assms(2) le_funD le_funI)

lemma update_mp_loc_nm_mono:
  assumes "nm1 \<le> nm2" and "p1 \<le> p2"
  shows "upd_mp_loc_nm nm1 lp p1 \<le> upd_mp_loc_nm nm2 lp p2"
  apply (cases nm1, cases nm2)
  apply (simp add: less_eq_nested_mask_def)
  using assms(1)[simplified less_eq_nested_mask_def]
  by (simp add: assms(2) le_funD le_funI)

lemma update_mh_loc_total_mono:
  assumes "\<phi>1 \<le> \<phi>2" and "p1 \<le> p2"
  shows "upd_mh_loc_total \<phi>1 l p1 \<le> upd_mh_loc_total \<phi>2 l p2"
  apply (rule less_eq_total_stateI)
    apply (insert assms)
    apply (auto dest: less_eq_total_stateD)
  by (simp add: less_eq_total_stateD update_mh_loc_nm_mono)

lemma update_mp_loc_total_mono:
  assumes "\<omega>1 \<le> \<omega>2" and "p1 \<le> p2"
  shows "upd_mp_loc_total \<omega>1 l p1 \<le> upd_mp_loc_total \<omega>2 l p2"
  apply (rule less_eq_total_stateI)
    apply (insert assms)
    apply (auto dest: less_eq_total_stateD)
  by (simp add: less_eq_total_stateD update_mp_loc_nm_mono)

lemma update_mh_loc_total_full_mono:
  assumes "\<omega>1 \<le> \<omega>2" and "p1 \<le> p2"
  shows "upd_mh_loc_total_full \<omega>1 l p1 \<le> upd_mh_loc_total_full \<omega>2 l p2"
proof -
  have *: "upd_mh_loc_total (get_total_full \<omega>1) l p1 \<le> upd_mh_loc_total (get_total_full \<omega>2) l p2"
    using assms update_mh_loc_total_mono less_eq_full_total_state_ext_def
    by blast

  show ?thesis
    apply (insert assms * )
    apply (rule less_eq_full_total_stateI2)
    by (fastforce dest: less_eq_full_total_stateD)+
qed

lemma update_mp_loc_total_full_mono:
  assumes "\<omega>1 \<le> \<omega>2" and "p1 \<le> p2"
  shows "upd_mp_loc_total_full \<omega>1 l p1 \<le> upd_mp_loc_total_full \<omega>2 l p2"
proof -
  have *: "upd_mp_loc_total (get_total_full \<omega>1) l p1 \<le> upd_mp_loc_total (get_total_full \<omega>2) l p2"
    using assms update_mp_loc_total_mono less_eq_full_total_state_ext_def
    by blast

  show ?thesis
    apply (insert assms * )
    apply (rule less_eq_full_total_stateI2)
    by (fastforce dest: less_eq_full_total_stateD)+
qed

lemma less_eq_add_masks: "m1 \<le> add_masks m1 m2"
  unfolding add_masks_def le_fun_def
proof
  fix x
  show "m1 x \<le> (m1 x) + (m2 x)"
    by (simp add: padd_pgte)
qed


subsection \<open>Partial Commutative Monoid Instantiation\<close>

lemma plus_masks_defined: "(m1 :: ('a, preal) abstract_mask) ## m2"
  unfolding defined_def
  by (simp add: SepAlgebra.plus_preal_def compatible_funI plus_fun_def)


instantiation total_state_ext :: (type,type) pcm
begin

definition plus_total_state_ext :: "('a,'b) total_state_ext \<Rightarrow> ('a,'b) total_state_ext \<Rightarrow> ('a,'b) total_state_ext option"
  where "plus_total_state_ext \<phi>1 \<phi>2 \<equiv>
           if get_hh_total \<phi>1 = get_hh_total \<phi>2 \<and> total_state.more \<phi>1 = total_state.more \<phi>2
           then Some (\<phi>1\<lparr> get_nm_total := get_nm_total \<phi>1 + get_nm_total \<phi>2 \<rparr>)
           else None"

instance proof
  fix a b ab c bc :: "('a,'b) total_state_ext"

  let ?mh_a = "get_mh_total a"
  let ?mp_a = "get_mp_total a"
  let ?mh_b = "get_mh_total b"
  let ?mp_b = "get_mp_total b"
  let ?mh_c = "get_mh_total c"
  let ?mp_c = "get_mp_total c"

  obtain mh_ab where MhEqAB: "?mh_a \<oplus> ?mh_b = Some mh_ab"
    using plus_masks_defined
    unfolding defined_def
    by blast

  obtain mp_ab where MpEqAB: "?mp_a \<oplus> ?mp_b = Some mp_ab"
    using plus_masks_defined
    unfolding defined_def
    by blast

  note MEqAB = MhEqAB MpEqAB

  obtain mh_bc where MhEqBC: "?mh_b \<oplus> ?mh_c = Some mh_bc"
    using plus_masks_defined
    unfolding defined_def
    by blast

  obtain mp_bc where MpEqBC: "?mp_b \<oplus> ?mp_c = Some mp_bc"
    using plus_masks_defined
    unfolding defined_def
    by blast

  note MEqBC = MhEqBC MpEqBC

  show "a \<oplus> b = b \<oplus> a"
    unfolding plus_total_state_ext_def
    by (simp add: add.commute)

  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
  proof -
    have *: "mh_ab \<oplus> get_mh_total c = get_mh_total a \<oplus> mh_bc"
      using MEqAB MEqBC asso1
      by blast

    have **: "mp_ab \<oplus> get_mp_total c = get_mp_total a \<oplus> mp_bc"
      using MEqAB MEqBC asso1
      by blast

    assume "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc"
    thus ?thesis
      unfolding plus_total_state_ext_def
      apply simp
      by (metis (no_types, lifting) add.assoc option.distinct(1) option.inject total_state.ext_inject total_state.surjective total_state.update_convs(2))
      \<comment> \<open>Todo: Needs a better proof.\<close>
  qed

  show "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"
  unfolding plus_total_state_ext_def
  by (clarsimp split: if_split if_split_asm)

  show "a \<oplus> b = Some c \<Longrightarrow> Some c = c \<oplus> c \<Longrightarrow> Some a = a \<oplus> a"
    sorry  \<comment> \<open>Is positivity ever used?\<close>
  (*
  proof -
    assume A: "a \<oplus> b = Some c" and B: "Some c = c \<oplus> c"

    obtain mh_cc where MhEqCC: "?mh_c \<oplus> ?mh_c = Some mh_cc"
    using plus_masks_defined
    unfolding defined_def
    by blast

    obtain mp_cc where MpEqCC: "?mp_c \<oplus> ?mp_c = Some mp_cc"
    using plus_masks_defined
    unfolding defined_def
    by blast

    note MEqCC = MhEqCC MpEqCC

    from B have *: "?mh_c \<oplus> ?mh_c = Some ?mh_c \<and> ?mp_c \<oplus> ?mp_c = Some ?mp_c"
      unfolding plus_total_state_ext_def
    proof (clarsimp simp: MEqCC split: if_split if_split_asm)
      assume "c = c\<lparr>get_mh_total := mh_cc, get_mp_total := mp_cc\<rparr>"
      have "get_mh_total c = mh_cc"
        apply (subst \<open>c = _\<close>)
        by simp
      moreover have "get_mp_total c = mp_cc"
        apply (subst \<open>c = _\<close>)
        by simp
      ultimately show "mh_cc = get_mh_total c \<and> mp_cc = get_mp_total c"
        by simp
    qed

    moreover from * A have "?mh_a \<oplus> ?mh_b = Some ?mh_c \<and> ?mp_a \<oplus> ?mp_b = Some ?mp_c"
      unfolding plus_total_state_ext_def
      by (clarsimp simp: MEqAB split: if_split if_split_asm)

    ultimately have "?mh_a \<oplus> ?mh_a = Some ?mh_a \<and> ?mp_a \<oplus> ?mp_a = Some ?mp_a"
      using positivity
      by metis

    thus ?thesis
      unfolding plus_total_state_ext_def
      by (clarsimp simp: MEqAB MEqBC split: if_split if_split_asm)
  qed
  *)
qed

end


instantiation full_total_state_ext :: (type,type) pcm
begin

\<comment>\<open>In the following definitions, traces must be the same. A different design decision would be to add the traces.
   Since our setting, elements of a trace once initialised are never modified it seems natural to force
   the traces to be the same.\<close>

definition plus_full_total_state_ext :: "('a,'b) full_total_state_ext \<Rightarrow> ('a,'b) full_total_state_ext \<Rightarrow> ('a,'b) full_total_state_ext option"
  where "plus_full_total_state_ext \<omega>1 \<omega>2 =
            (if get_store_total \<omega>1 = get_store_total \<omega>2 \<and>
                get_trace_total \<omega>1 = get_trace_total \<omega>2 \<and>
                get_total_full \<omega>1 ## get_total_full \<omega>2 \<and>
                full_total_state.more \<omega>1 = full_total_state.more \<omega>2 then
                Some (\<omega>1\<lparr>get_total_full := the (get_total_full \<omega>1 \<oplus> get_total_full \<omega>2) \<rparr>)
            else
                None)"

instance

proof
  fix a b c ab bc :: "('a,'b) full_total_state_ext"

  show "a \<oplus> b = b \<oplus> a"
    unfolding plus_full_total_state_ext_def
    by (simp add: commutative defined_def)

  show "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"
    unfolding plus_full_total_state_ext_def
    by (metis (no_types, lifting) asso2 defined_def full_total_state.ext_inject full_total_state.surjective full_total_state.update_convs(3) option.collapse option.discI option.inject)

  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc" (is "?A \<Longrightarrow> _")
  proof -
    let ?at = "get_total_full a"
    let ?bt = "get_total_full b"
    let ?ct = "get_total_full c"
    let ?abt = "get_total_full ab"
    let ?bct = "get_total_full bc"

    assume ?A

    hence "?at \<oplus> ?bt = Some ?abt \<and> ?bt \<oplus> ?ct = Some ?bct"
      unfolding plus_full_total_state_ext_def defined_def
      by (auto split: if_split if_split_asm)

    hence "?abt \<oplus> ?ct = ?at \<oplus> ?bct"
      using asso1 by blast

    with \<open>?A\<close>
    show ?thesis
      unfolding plus_full_total_state_ext_def defined_def
      by (auto split: if_split if_split_asm)
  qed

  show "a \<oplus> b = Some c \<Longrightarrow> Some c = c \<oplus> c \<Longrightarrow> Some a = a \<oplus> a" (is "?A \<Longrightarrow> ?B \<Longrightarrow> _")
  proof -
    let ?at = "get_total_full a"
    let ?bt = "get_total_full b"
    let ?ct = "get_total_full c"
    assume ?A and ?B

    from \<open>?A\<close> have "?at \<oplus> ?bt = Some ?ct"
      unfolding plus_full_total_state_ext_def defined_def
      by (auto split: if_split if_split_asm)

    moreover from \<open>?B\<close> have "Some ?ct = ?ct \<oplus> ?ct"
      unfolding plus_full_total_state_ext_def defined_def
      apply (simp split: if_split if_split_asm)
      by (metis full_total_state.select_convs(3) full_total_state.surjective full_total_state.update_convs(3))

    ultimately have "Some ?at = ?at \<oplus> ?at"
      using positivity by blast

    thus ?thesis
      unfolding plus_full_total_state_ext_def defined_def
      by (metis full_total_state.surjective full_total_state.update_convs(3) option.discI option.sel)
  qed
qed

end


end
