section \<open>A state model for the Viper total heap semantics\<close>

theory TotalViperState
imports ViperCommon.ValueAndBasicState ViperCommon.PosReal
begin


text \<open> We use the following naming scheme:

hh: heap for heap locations
hp: heap for predicate locations (deprecated)
h: hh and hp together (e.g., (hh,hp)) (deprecated)

mh: permission mask for heap locations
mp: permission mask for predicate locations
m: mh and mp together (e.g., (mh,mp))

lh: heap location
lp: predicate location
\<close>


subsection \<open>Individual Masks and Heaps\<close>

type_synonym 'a total_heap = "heap_loc \<Rightarrow> 'a val"
type_synonym field_mask = "preal mask"
type_synonym 'a predicate_mask = "'a predicate_loc \<Rightarrow> preal"

text \<open>For each predicate instance, the state tracks the heap snapshot represented as a subset of
heap locations and predicate locations. The values of the heap locations are given by the 
corresponding total heap\<close>

type_synonym 'a predicate_heap = "'a predicate_loc \<Rightarrow> heap_loc set \<times> 'a predicate_loc set"

fun get_lhset_pheap :: "'a predicate_heap \<Rightarrow> 'a predicate_loc \<Rightarrow> heap_loc set"
  where "get_lhset_pheap hp lp = fst (hp lp)"

fun get_lpset_pheap :: "'a predicate_heap \<Rightarrow> 'a predicate_loc \<Rightarrow> 'a predicate_loc set"
  where "get_lpset_pheap hp lp = snd (hp lp)"


subsection \<open>Nested Mask\<close>

datatype 'a nested_mask = NM field_mask "'a predicate_mask" "('a predicate_loc \<rightharpoonup> 'a nested_mask)"

fun get_mh_nm :: "'a nested_mask \<Rightarrow> field_mask"
  where "get_mh_nm (NM mh _ _) = mh"

fun get_mp_nm :: "'a nested_mask \<Rightarrow> 'a predicate_mask"
  where "get_mp_nm (NM _ mp _) = mp"

fun get_fnm_nm :: "'a nested_mask \<Rightarrow> ('a predicate_loc \<rightharpoonup> 'a nested_mask)"
  where "get_fnm_nm (NM _ _ fnm) = fnm"

fun get_nm_loc_nm :: "'a nested_mask \<Rightarrow> 'a predicate_loc \<Rightarrow> 'a nested_mask option"
  where "get_nm_loc_nm (NM _ _ fnm) loc = fnm loc"

fun upd_mh_nm :: "'a nested_mask \<Rightarrow> field_mask \<Rightarrow> 'a nested_mask"
  where "upd_mh_nm (NM _ mp fnm) mh = NM mh mp fnm"

fun upd_mp_nm :: "'a nested_mask \<Rightarrow> 'a predicate_mask \<Rightarrow> 'a nested_mask"
  where "upd_mp_nm (NM mh _ fnm) mp = NM mh mp fnm"

fun upd_nm_loc_nm :: "'a nested_mask \<Rightarrow> 'a predicate_loc \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask"
  where "upd_nm_loc_nm (NM mh mp fnm) lp nm = NM mh mp (fnm( lp := Some nm ))"

fun upd_nm_loc_opt_nm :: "'a nested_mask \<Rightarrow> 'a predicate_loc \<Rightarrow> 'a nested_mask option \<Rightarrow> 'a nested_mask"
  where "upd_nm_loc_opt_nm (NM mh mp fnm) lp nm = NM mh mp (fnm( lp := nm ))"

fun add_to_mp_loc_nm :: "'a nested_mask \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> 'a nested_mask"
  where "add_to_mp_loc_nm (NM mh mp fnm) lp p = NM mh (mp( lp := mp lp + p )) fnm"

definition empty_nm :: "'a nested_mask"
  where "empty_nm = NM (\<lambda>_. 0) (\<lambda>_. 0) Map.empty"


subsection \<open>Total State\<close>

record 'a total_state =
   get_hh_total :: "'a total_heap"
   get_nm_total :: "'a nested_mask"

fun get_mh_total :: "('a, 'b) total_state_scheme \<Rightarrow> field_mask"
  where "get_mh_total \<phi> = get_mh_nm (get_nm_total \<phi>)"

fun mh_total_update :: "('a, 'b) total_state_scheme \<Rightarrow> field_mask \<Rightarrow> ('a, 'b) total_state_scheme"
  where "mh_total_update \<phi> mh = \<phi>\<lparr> get_nm_total := upd_mh_nm (get_nm_total \<phi>) mh \<rparr>"

fun get_mp_total :: "('a, 'b) total_state_scheme \<Rightarrow> 'a predicate_mask"
  where "get_mp_total \<phi> = get_mp_nm (get_nm_total \<phi>)"

fun mp_total_update :: "('a, 'b) total_state_scheme \<Rightarrow> 'a predicate_mask \<Rightarrow> ('a, 'b) total_state_scheme"
  where "mp_total_update \<phi> mp = \<phi>\<lparr> get_nm_total := upd_mp_nm (get_nm_total \<phi>) mp \<rparr>"

fun get_fnm_total :: "('a, 'b) total_state_scheme \<Rightarrow> ('a predicate_loc \<rightharpoonup> 'a nested_mask)"
  where "get_fnm_total \<phi> = get_fnm_nm (get_nm_total \<phi>)"

fun fnm_total_update :: "('a, 'b) total_state_scheme \<Rightarrow> ('a predicate_loc \<rightharpoonup> 'a nested_mask) \<Rightarrow> ('a, 'b) total_state_scheme"
  where "fnm_total_update \<phi> fnm = (case get_nm_total \<phi> of (NM mh mp _) \<Rightarrow> \<phi>\<lparr> get_nm_total := NM mh mp fnm \<rparr>)"

fun get_nm_loc_total :: "('a, 'b) total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> 'a nested_mask option"
  where "get_nm_loc_total \<phi> lp = get_fnm_total \<phi> lp"


subsection \<open>Full Total State\<close>

type_synonym 'a total_trace = "label \<rightharpoonup> 'a total_state"
type_synonym 'a store = "var \<rightharpoonup> 'a val" (* De Bruijn indices *)

record 'a full_total_state = (*= "'a store \<times> 'a total_trace \<times> 'a total_state"*)
  get_store_total :: "'a store"
  get_trace_total :: "'a total_trace"
  get_total_full :: "'a total_state"


(* subsection \<open>Order\<close>

lemma zero_mask_less_eq_mask: "zero_mask \<le> m"
  unfolding  zero_mask_def le_fun_def
  by (simp add: all_pos)
  

instantiation total_state_ext :: (type,type) order
begin

definition less_eq_total_state_ext :: "('a,'b) total_state_ext \<Rightarrow> ('a,'b) total_state_ext \<Rightarrow> bool"
  where "\<phi>1 \<le> \<phi>2 \<equiv> 
         get_hh_total \<phi>1 = get_hh_total \<phi>2 \<and>
         get_hp_total \<phi>1 = get_hp_total \<phi>2 \<and>
         (get_mh_total \<phi>1) \<le> (get_mh_total \<phi>2) \<and>
         (get_mp_total \<phi>1) \<le> (get_mp_total \<phi>2) \<and>
         total_state.more \<phi>1 = total_state.more \<phi>2"

definition less_total_state_ext :: "('a,'b) total_state_ext \<Rightarrow> ('a,'b) total_state_ext \<Rightarrow> bool"
  where "\<phi>1 < \<phi>2 \<equiv> 
         get_hh_total \<phi>1 = get_hh_total \<phi>2 \<and>
         get_hp_total \<phi>1 = get_hp_total \<phi>2 \<and>
         ( ((get_mh_total \<phi>1) < (get_mh_total \<phi>2) \<and> (get_mp_total \<phi>1) \<le> (get_mp_total \<phi>2)) \<or>
           ((get_mh_total \<phi>1) \<le> (get_mh_total \<phi>2) \<and> (get_mp_total \<phi>1) < (get_mp_total \<phi>2))) \<and>
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
        by (metis TotalViperState.less_eq_full_total_state_ext_def leD)
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

lemma less_eq_total_stateI:
  " get_hh_total \<phi>1 = get_hh_total \<phi>2 \<Longrightarrow>
    get_hp_total \<phi>1 = get_hp_total \<phi>2 \<Longrightarrow>
     (get_mh_total \<phi>1) \<le> (get_mh_total \<phi>2) \<Longrightarrow>
     (get_mp_total \<phi>1) \<le> (get_mp_total \<phi>2) \<Longrightarrow>
    total_state.more \<phi>1 = total_state.more \<phi>2 \<Longrightarrow>
    \<phi>1 \<le> \<phi>2"
  unfolding less_eq_total_state_ext_def
  by blast

lemma less_eq_total_stateD: "\<phi>1 \<le> \<phi>2 \<Longrightarrow>
         get_hh_total \<phi>1 = get_hh_total \<phi>2 \<and>
         get_hp_total \<phi>1 = get_hp_total \<phi>2 \<and>
         ((get_mh_total \<phi>1) \<le> (get_mh_total \<phi>2) \<and> (get_mp_total \<phi>1) \<le> (get_mp_total \<phi>2)) \<and>
         total_state.more \<phi>1 = total_state.more \<phi>2"
  unfolding less_eq_total_state_ext_def
  by blast

lemma less_eq_total_stateE:
  assumes "\<phi>1 \<le> \<phi>2" and
          "get_hh_total \<phi>1 = get_hh_total \<phi>2 \<Longrightarrow>
           get_hp_total \<phi>1 = get_hp_total \<phi>2 \<Longrightarrow>
           (get_mh_total \<phi>1) \<le> (get_mh_total \<phi>2) \<Longrightarrow>
           (get_mp_total \<phi>1) \<le> (get_mp_total \<phi>2) \<Longrightarrow>
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
  by blast *)

subsection \<open>Destructors \<close>

fun get_hh_total_full :: "('a,'b) full_total_state_scheme \<Rightarrow> 'a total_heap"
  where "get_hh_total_full \<omega> = get_hh_total (get_total_full \<omega>)"

fun get_nm_total_full :: "('a,'b) full_total_state_scheme \<Rightarrow> 'a nested_mask"
  where "get_nm_total_full \<omega> = get_nm_total (get_total_full \<omega>)"

fun get_mh_total_full :: "('a,'b) full_total_state_scheme \<Rightarrow> field_mask"
  where "get_mh_total_full \<omega> = get_mh_total (get_total_full \<omega>)"

fun get_mp_total_full :: "('a,'b) full_total_state_scheme \<Rightarrow> 'a predicate_mask"
  where "get_mp_total_full \<omega> = get_mp_total (get_total_full \<omega>)"

subsection \<open>Empty states\<close>

definition is_empty_total :: "('a,'b) total_state_scheme \<Rightarrow> bool"
  where "is_empty_total \<phi> \<equiv> get_mh_total \<phi> = zero_mask \<and> get_mp_total \<phi> = zero_mask"

definition is_empty_total_full :: "('a,'b) full_total_state_scheme \<Rightarrow> bool"
  where "is_empty_total_full \<omega> \<equiv> is_empty_total (get_total_full \<omega>)"

lemma is_empty_total_wf_mask: "is_empty_total_full \<omega> \<Longrightarrow> wf_mask_simple (get_mh_total_full \<omega>)"
  unfolding is_empty_total_full_def is_empty_total_def
  by (simp add: wf_zero_mask)

(* lemma is_empty_total_less_eq:
  assumes "is_empty_total \<phi>" and
          "get_hh_total \<phi> = get_hh_total \<phi>'" and
          "get_hp_total \<phi> = get_hp_total \<phi>'" and
          "total_state.more \<phi> = total_state.more \<phi>'"
        shows "\<phi> \<le> \<phi>'"
  using assms zero_mask_less_eq_mask
  unfolding less_eq_total_state_ext_def is_empty_total_def 
  by metis

lemma is_empty_total_full_less_eq:
  assumes "is_empty_total_full \<omega>" and
          "get_store_total \<omega> = get_store_total \<omega>'" and
          "get_trace_total \<omega> = get_trace_total \<omega>'" and
          "get_hh_total_full \<omega> = get_hh_total_full \<omega>'" and
          "get_hp_total_full \<omega> = get_hp_total_full \<omega>'" and
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

definition empty_full_total_state :: "'a store \<Rightarrow> 'a total_trace \<Rightarrow> 'a total_heap \<Rightarrow> 'a predicate_heap \<Rightarrow> 'a full_total_state"
  where "empty_full_total_state \<sigma> t hh hp =
   \<lparr> get_store_total = \<sigma>, 
     get_trace_total = t, 
     get_total_full = \<lparr> get_hh_total = hh, get_hp_total = hp, get_mh_total = zero_mask, get_mp_total = zero_mask \<rparr> 
   \<rparr>"

lemma get_store_empty_full_total_state [simp]: "get_store_total (empty_full_total_state \<sigma> t hh hp) = \<sigma>"
  by (simp add: empty_full_total_state_def)

lemma get_trace_empty_full_total_state [simp]: "get_trace_total (empty_full_total_state \<sigma> t hh hp) = t"
  by (simp add: empty_full_total_state_def)

lemma is_empty_empty_full_total_state: "is_empty_total_full (empty_full_total_state \<sigma> t hh hp)"
  unfolding is_empty_total_full_def is_empty_total_def empty_full_total_state_def
  by simp *)

end