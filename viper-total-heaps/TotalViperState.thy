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

definition empty_nm :: "'a nested_mask"
  where "empty_nm = NM (\<lambda>_. 0) (\<lambda>_. 0) Map.empty"


subsection \<open>Total State\<close>

record 'a total_state =
   get_hh_total :: "'a total_heap"
   get_nm_total :: "'a nested_mask"


subsection \<open>Full Total State\<close>

type_synonym 'a total_trace = "label \<rightharpoonup> 'a total_state"
type_synonym 'a store = "var \<rightharpoonup> 'a val" (* De Bruijn indices *)

record 'a full_total_state = (*= "'a store \<times> 'a total_trace \<times> 'a total_state"*)
  get_store_total :: "'a store"
  get_trace_total :: "'a total_trace"
  get_total_full :: "'a total_state"


end