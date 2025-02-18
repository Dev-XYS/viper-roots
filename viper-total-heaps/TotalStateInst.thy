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
  apply standard
   apply simp
  apply (rule iffD2[OF le_fun_def])
proof
  fix mh\<^sub>1 fnm\<^sub>1 mh\<^sub>2 fnm\<^sub>2 lp
  assume "nested_mask_le nm1 nm2"
     and [simp]: "nm1 = NM mh\<^sub>1 fnm\<^sub>1"
     and [simp]: "nm2 = NM mh\<^sub>2 fnm\<^sub>2"
  hence mple: "option_fold (\<lambda>lpm\<^sub>1. option_fold (\<lambda>lpm\<^sub>2. fst lpm\<^sub>1 \<le> fst lpm\<^sub>2 \<and> nested_mask_le (snd lpm\<^sub>1) (snd lpm\<^sub>2)) False (fnm\<^sub>2 lp)) True (fnm\<^sub>1 lp)"
    using nested_mask_le.simps
    by blast
  show "get_mp_nm nm1 lp \<le> get_mp_nm nm2 lp"
    apply (cases "fnm\<^sub>1 lp"; cases "fnm\<^sub>2 lp")
       apply simp_all
      apply (simp add: all_pos)
    using mple
     apply auto[1]
    apply (insert mple)
    apply (simp add: less_eq_preal_def)
    apply (insert Abs_preal_inverse)
    by (simp add: less_eq_posreal.rep_eq less_eq_preal.rep_eq)
qed

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

(*
lemma update_mp_loc_nm_mono:
  assumes "nm1 \<le> nm2" and "p1 \<le> p2"
  shows "upd_mp_loc_nm nm1 lp p1 \<le> upd_mp_loc_nm nm2 lp p2"
  apply (cases nm1, cases nm2)
  apply (simp add: less_eq_nested_mask_def)
  using assms(1)[simplified less_eq_nested_mask_def]
  by (simp add: assms(2) le_funD le_funI)
*)

lemma update_mh_loc_total_mono:
  assumes "\<phi>1 \<le> \<phi>2" and "p1 \<le> p2"
  shows "upd_mh_loc_total \<phi>1 l p1 \<le> upd_mh_loc_total \<phi>2 l p2"
  apply (rule less_eq_total_stateI)
    apply (insert assms)
    apply (auto dest: less_eq_total_stateD)
  by (metis less_eq_total_state_ext_def upd_mh_loc_nm.elims update_mh_loc_nm_mono)

(*
lemma update_mp_loc_total_mono:
  assumes "\<omega>1 \<le> \<omega>2" and "p1 \<le> p2"
  shows "upd_mp_loc_total \<omega>1 l p1 \<le> upd_mp_loc_total \<omega>2 l p2"
  apply (rule less_eq_total_stateI)
    apply (insert assms)
    apply (auto dest: less_eq_total_stateD)
  by (simp add: less_eq_total_stateD update_mp_loc_nm_mono)
*)

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

(*
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
*)

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

  show "a \<oplus> b = b \<oplus> a"
    unfolding plus_total_state_ext_def
    by (simp add: add.commute)

  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
  proof -
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
  proof -
    assume a_b: "a \<oplus> b = Some c"
    assume c_c: "Some c = c \<oplus> c"
    define a_nm where "a_nm = get_nm_total a"
    define b_nm where "b_nm = get_nm_total b"
    define c_nm where "c_nm = get_nm_total c"

    have "c_nm = 0"
    proof (rule ccontr)
      assume c_not_0: "c_nm \<noteq> 0"
      then consider (mh_non_0) "get_mh_nm c_nm \<noteq> zero_mask" | (fnm_non_0) "get_fnm_nm c_nm \<noteq> Map.empty"
        by (metis nm_get_eq zero_nested_mask_def)
      then show False
      proof cases
        case mh_non_0
        then obtain l where "get_mh_nm c_nm l \<noteq> 0"
          using zero_mask_def
          by fastforce
        hence "Some c \<noteq> c \<oplus> c"
          apply (simp add: plus_total_state_ext_def plus_nested_mask_def c_nm_def[symmetric])
          apply (rule neq_by_fun[of get_mh_total])
          apply (rule neq_by_fun[of "\<lambda>f. f l"])
          apply (cases c_nm)
          apply simp
          by (metis Rep_preal_inject add_cancel_left_left add_masks_def c_nm_def get_mh_nm.simps plus_preal.rep_eq zero_preal.rep_eq)
        thus ?thesis
          using c_c
          by contradiction
      next
        case fnm_non_0
        then obtain lp p nm_p where "get_fnm_nm c_nm lp = Some (p, nm_p)"
          by (metis option.collapse prod.collapse)
        hence "Some c \<noteq> c \<oplus> c"
          apply (simp add: plus_total_state_ext_def plus_nested_mask_def c_nm_def[symmetric])
          apply (rule neq_by_fun[of get_fnm_total])
          apply (rule neq_by_fun[of "\<lambda>f. f lp"])
          apply (cases c_nm)
          apply (simp add: pfun_comb_def c_nm_def[symmetric])
          by (simp add: order_less_imp_not_eq posreal_add_greater)
        thus ?thesis
          using c_c
          by contradiction
      qed
    qed

    have "a_nm = 0"
    proof (rule ccontr)
      assume c_not_0: "a_nm \<noteq> 0"
      then consider (mh_non_0) "get_mh_nm a_nm \<noteq> zero_mask" | (fnm_non_0) "get_fnm_nm a_nm \<noteq> Map.empty"
        by (metis nm_get_eq zero_nested_mask_def)
      then show False
      proof cases
        case mh_non_0
        then obtain l where "get_mh_nm a_nm l \<noteq> 0"
          using zero_mask_def
          by fastforce
        hence "a \<oplus> b \<noteq> Some c"
          apply (simp add: plus_total_state_ext_def plus_nested_mask_def a_nm_def[symmetric])
          apply standard
          apply (rule neq_by_fun[of get_mh_total])
          apply (rule neq_by_fun[of "\<lambda>f. f l"])
          apply (cases a_nm)
          apply (cases b_nm)
          apply (cases c_nm)
          apply simp
          by (metis (no_types, lifting) \<open>c_nm = 0\<close> add_masks_def b_nm_def c_nm_def get_mh_nm.simps padd_pos zero_mask_def zero_nested_mask_def)
        thus ?thesis
          using a_b
          by contradiction
      next
        case fnm_non_0
        then obtain lp p nm_p where "get_fnm_nm a_nm lp = Some (p, nm_p)"
          by (metis option.collapse prod.collapse)
        hence "a \<oplus> b \<noteq> Some c"
          apply (simp add: plus_total_state_ext_def plus_nested_mask_def a_nm_def[symmetric])
          apply standard
          apply (rule neq_by_fun[of get_fnm_total])
          apply (rule neq_by_fun[of "\<lambda>f. f lp"])
          apply (cases a_nm)
          apply (cases b_nm)
          apply (cases c_nm)
          apply (simp add: pfun_comb_def a_nm_def[symmetric] b_nm_def[symmetric] c_nm_def[symmetric])
          by (metis (no_types, lifting) \<open>c_nm = 0\<close> combine_options_simps(2) combine_options_simps(3) get_fnm_nm.simps not_None_eq zero_nested_mask_def)
        thus ?thesis
          using a_b
          by contradiction
      qed
    qed

    show "Some a = a \<oplus> a"
      apply (simp add: plus_total_state_ext_def plus_nested_mask_def)
      apply (rule total_state.equality; simp_all)
      apply (simp add: a_nm_def[symmetric] \<open>a_nm = 0\<close>)
      by (metis add_0 plus_nested_mask_def)
  qed
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


subsection \<open>Partial Commutative Monoid with Core\<close>

subsubsection \<open>Lemmas\<close>

lemma total_state_plus_defined:
  assumes "a \<oplus> b = Some c"
  shows "get_hh_total a = get_hh_total b \<and> total_state.more a = total_state.more b \<and>
         get_hh_total a = get_hh_total c \<and> total_state.more a = total_state.more c"
  using assms
  unfolding plus_total_state_ext_def
  by (clarsimp split: if_split_asm)

lemma plus_mask_zero_mask_neutral: "(m :: ('a, preal) abstract_mask) \<oplus> zero_mask = Some m"
proof -
  have "compatible_fun m zero_mask"
    by (simp add: SepAlgebra.plus_preal_def compatible_funI)

  thus ?thesis
  unfolding plus_fun_def
  by (simp add: SepAlgebra.plus_preal_def zero_mask_def)
qed

lemma plus_Some_full_total_state_total_state:
  assumes "Some a = b \<oplus> x"
  shows "Some (get_total_full a) = (get_total_full b) \<oplus> (get_total_full x)"
  using assms
  unfolding plus_full_total_state_ext_def defined_def
  by (auto split: if_split_asm)


subsubsection \<open>Instantiation\<close>

instantiation total_state_ext :: (type,type) pcm_with_core
begin

definition core_total_state_ext :: "('a,'b) total_state_ext \<Rightarrow> ('a, 'b) total_state_ext"
  where "core_total_state_ext \<phi> = (upd_nm_total \<phi> 0)"

instance
proof
  fix a b c x y :: "('a,'b) total_state_ext"

  show "Some x = x \<oplus> |x|"
    unfolding core_total_state_ext_def plus_total_state_ext_def
    by simp

  show "Some |x| = |x| \<oplus> |x|"
    unfolding core_total_state_ext_def plus_total_state_ext_def
    by simp

  show "Some x = x \<oplus> c \<Longrightarrow> \<exists>r. Some |x| = c \<oplus> r" (is "?lhs \<Longrightarrow> ?rhs")
  proof
    assume x_c: "Some x = x \<oplus> c"

    hence "get_hh_total x = get_hh_total c \<and> total_state.more x = total_state.more c"
      by (metis total_state_plus_defined)

    moreover have "get_nm_total c = 0"
    proof (rule ccontr)
      assume c_not_0: "get_nm_total c \<noteq> 0"
      then consider (mh_non_0) "get_mh_total c \<noteq> zero_mask" | (fnm_non_0) "get_fnm_total c \<noteq> Map.empty"
        by (metis get_fnm_total.simps get_mh_total.simps nm_get_eq zero_nested_mask_def)
      then show False
      proof cases
        case mh_non_0
        then obtain l where "get_mh_total c l \<noteq> 0"
          using zero_mask_def
          by fastforce
        have "Some x \<noteq> x \<oplus> c"
          apply (simp add: plus_total_state_ext_def plus_nested_mask_def)
          apply standard
          apply (rule neq_by_fun[of get_mh_total])
          apply (rule neq_by_fun[of "\<lambda>f. f l"])
          apply (subst nm_get_eq)
          apply (simp add: add_masks_def)
          by (metis PosReal.padd_cancellative \<open>get_mh_total c l \<noteq> pos_perm_class.pnone\<close> add.commute add_0 get_mh_total.simps)
        thus ?thesis
          using x_c
          by contradiction
      next
        case fnm_non_0
        then obtain lp p nm_p where "get_fnm_total c lp = Some (p, nm_p)"
          by (metis option.collapse prod.collapse)
        hence "Some x \<noteq> x \<oplus> c"
          apply (simp add: plus_total_state_ext_def plus_nested_mask_def)
          apply standard
          apply (rule neq_by_fun[of get_fnm_total])
          apply (rule neq_by_fun[of "\<lambda>f. f lp"])
          apply (subst nm_get_eq)
          apply (subst nm_get_eq[of "get_nm_total c"])
          apply (simp add: pfun_comb_def)
          apply (cases "get_fnm_total x lp")
           apply simp_all
          by (metis fst_conv nless_le posreal_add_greater)
        thus ?thesis
          using x_c
          by contradiction
      qed
    qed

    ultimately show "Some |x| = c \<oplus> c\<lparr> get_nm_total := 0 \<rparr>"
      unfolding core_total_state_ext_def plus_total_state_ext_def
      by simp
  qed

  show "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|"
    unfolding core_total_state_ext_def plus_total_state_ext_def
    by (clarsimp split: if_split if_split_asm simp: plus_mask_zero_mask_neutral)

  show "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y" (is "?A \<Longrightarrow> ?B \<Longrightarrow> _ \<Longrightarrow> _")
    \<comment>\<open>\<^prop>\<open>|x| = |y|\<close> is not needed, since it is always the case if he heap of \<^term>\<open>x\<close> and \<^term>\<open>y\<close>
       are the same, which it must be because of the first two assumptions\<close>
  proof -
    assume "?A" and "?B"
    hence b_x_eq: "get_hh_total b = get_hh_total x \<and> total_state.more b = total_state.more x" and
          b_y_eq: "get_hh_total b = get_hh_total y \<and> total_state.more b = total_state.more y"
      by (metis option.simps(3) plus_total_state_ext_def)+
    show "x = y"
      by (metis \<open>Some a = b \<oplus> x\<close> \<open>Some a = b \<oplus> y\<close> add_left_cancel b_x_eq b_y_eq option.sel plus_total_state_ext_def total_state.select_convs(2) total_state.surjective total_state.update_convs(2))
  qed
qed

end


instantiation full_total_state_ext :: (type,type) pcm_with_core
begin

text \<open>In the following, we do not take the core of the trace, because the addition of states is
      defined only if the traces are the same.\<close>

definition core_full_total_state_ext :: "('a,'b) full_total_state_ext \<Rightarrow> ('a, 'b) full_total_state_ext"
  where "core_full_total_state_ext \<omega> =
            \<omega> \<lparr> get_total_full := |get_total_full \<omega>| \<rparr>"

instance
proof
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

end


end
