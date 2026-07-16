section \<open>Utilities for Total Masks (Heap Mask, Predicate Mask, Nested Mask)\<close>

theory TotalMaskUtil
  imports TotalViperUtil TotalViperState
begin


subsection \<open>Well-foundness Relation for \<^typ>\<open>'a nested_mask\<close>\<close>

abbreviation nested_mask_rel :: "('a nested_mask \<times> 'a nested_mask) set"
  where "nested_mask_rel \<equiv> {(nm, (NM mh fnm)) | nm mh fnm lp. nm \<in> set_option (map_option snd (fnm lp))}"

lemma wf_nested_mask_rel: "wf nested_mask_rel"
  unfolding wf_def
  apply (rule allI | rule impI)+
  apply (rule nested_mask.induct)
  apply simp
  by (metis nested_mask.inject range_eqI snd_conv snds.intros)


subsection \<open>Mask Merge\<close>

function (sequential) nested_mask_merge :: "'a nested_mask \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask" where
  "nested_mask_merge (NM mh\<^sub>1 fnm\<^sub>1) (NM mh\<^sub>2 fnm\<^sub>2) =
     NM (add_masks mh\<^sub>1 mh\<^sub>2) (fnm\<^sub>1 +\<lparr>\<lambda>lpm\<^sub>1 lpm\<^sub>2. (fst lpm\<^sub>1 + fst lpm\<^sub>2, nested_mask_merge (snd lpm\<^sub>1) (snd lpm\<^sub>2))\<rparr>+ fnm\<^sub>2)"
  by (pat_completeness) auto
termination
   \<comment>\<open>"nested_mask_rel <*lex*> {}" would be sufficient here, since the first argument becomes smaller always\<close>
  apply (relation "nested_mask_rel <*lex*> nested_mask_rel")
  using wf_nested_mask_rel
   apply blast
  using Option.is_none_def
  by fastforce


subsection \<open>Mask Multiplication\<close>

function (sequential) nested_mask_multiply :: "preal \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask" where
  "nested_mask_multiply p (NM mh fnm) = NM (mul_mask p mh) ((\<lambda>nm. if p = 0 then None else (map_option (\<lambda>lpm. (fst lpm * Abs_posreal p, nested_mask_multiply p (snd lpm))) nm)) \<circ> fnm)"
  by (pat_completeness) auto
termination
  apply (relation "{} <*lex*> nested_mask_rel")
  using wf_nested_mask_rel
   apply blast
  apply simp
  by (metis image_iff prod.exhaust_sel)


subsection \<open>Mask Subtraction\<close>

(* Hopefully we will not need this. *)
(*
function (sequential) nested_mask_subtract :: "'a nested_mask \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask" where
  "nested_mask_subtract (NM mh\<^sub>1 fnm\<^sub>1) (NM mh\<^sub>2 fnm\<^sub>2) =
     NM (mh\<^sub>1 - mh\<^sub>2) (fnm\<^sub>1 +\<lparr>\<lambda>lpm\<^sub>1 lpm\<^sub>2. (fst lpm\<^sub>1 + fst lpm\<^sub>2, nested_mask_merge (snd lpm\<^sub>1) (snd lpm\<^sub>2))\<rparr>+ fnm\<^sub>2)"
  by (pat_completeness) auto
termination
  apply (relation "nested_mask_rel <*lex*> {}")
  using wf_nested_mask_rel
  by blast
*)


subsection \<open>Mask Ordering\<close>

function (sequential) nested_mask_le :: "'a nested_mask \<Rightarrow> 'a nested_mask \<Rightarrow> bool" where
  "nested_mask_le (NM mh\<^sub>1 fnm\<^sub>1) (NM mh\<^sub>2 fnm\<^sub>2) = (mh\<^sub>1 \<le> mh\<^sub>2 \<and>
     (\<forall>lp. option_fold (\<lambda>lpm\<^sub>1. option_fold (\<lambda>lpm\<^sub>2. lpm\<^sub>1 = lpm\<^sub>2 \<or> fst lpm\<^sub>1 < fst lpm\<^sub>2 \<and> nested_mask_le (snd lpm\<^sub>1) (snd lpm\<^sub>2)) False (fnm\<^sub>2 lp)) True (fnm\<^sub>1 lp)))"
  by (pat_completeness) auto
termination
  apply (relation "nested_mask_rel <*lex*> {}")
  using wf_nested_mask_rel
   apply blast
  by fastforce


subsection \<open>Mask Split\<close>

fun mh_split :: "field_mask \<Rightarrow> field_mask \<Rightarrow> field_mask \<Rightarrow> bool" where
  "mh_split mh mh\<^sub>1 mh\<^sub>2 = (mh = add_masks mh\<^sub>1 mh\<^sub>2)"

fun mp_split :: "'a predicate_mask \<Rightarrow> 'a predicate_mask \<Rightarrow> 'a predicate_mask \<Rightarrow> bool" where
  "mp_split mp mp\<^sub>1 mp\<^sub>2 = (mp = add_masks mp\<^sub>1 mp\<^sub>2)"


subsection \<open>Constant Masks\<close>

fun singleton_mh :: "heap_loc \<Rightarrow> preal \<Rightarrow> field_mask" where
  "singleton_mh loc p l = (if l = loc then p else 0)"

fun singleton_mp :: "'a predicate_loc \<Rightarrow> preal \<Rightarrow> 'a predicate_mask" where
  "singleton_mp ploc p pl = (if pl = ploc then p else 0)"

fun is_singleton_mh :: "heap_loc \<Rightarrow> field_mask \<Rightarrow> bool" where
  "is_singleton_mh loc mh = (\<exists>p > 0. mh = singleton_mh loc p)"

fun is_singleton_mp :: "'a predicate_loc \<Rightarrow> 'a predicate_mask \<Rightarrow> bool" where
  "is_singleton_mp ploc mp = (\<exists>p > 0. mp = singleton_mp ploc p)"


subsection \<open>The Most Basic Getters and Setters\<close>

fun get_mh_nm :: "'a nested_mask \<Rightarrow> field_mask"
  where "get_mh_nm (NM mh _) = mh"

fun get_fnm_nm :: "'a nested_mask \<Rightarrow> 'a predicate_nm_fun"
  where "get_fnm_nm (NM _ fnm) = fnm"

fun upd_mh_nm :: "'a nested_mask \<Rightarrow> field_mask \<Rightarrow> 'a nested_mask"
  where "upd_mh_nm (NM _ fnm) mh = NM mh fnm"

fun upd_fnm_nm :: "'a nested_mask \<Rightarrow> 'a predicate_nm_fun \<Rightarrow> 'a nested_mask"
  where "upd_fnm_nm (NM mh _) fnm = NM mh fnm"


subsection \<open>Nested Mask Equality\<close>

lemma nested_mask_equality:
  assumes "get_mh_nm nm1 = get_mh_nm nm2"
      and "get_fnm_nm nm1 = get_fnm_nm nm2"
    shows "nm1 = nm2"
  apply (cases nm1, cases nm2)
  using assms
  by auto

lemma nm_get_eq:
  shows "nm = NM (get_mh_nm nm) (get_fnm_nm nm)"
  by (simp add: nested_mask_equality)


end
