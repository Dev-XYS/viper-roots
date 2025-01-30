section \<open>Helper lemmas, instantiations, definitions for the total state\<close>

theory TotalStateUtil
  imports ViperCommon.SepAlgebra ViperCommon.DeBruijn TotalViperUtil NestedMaskInst
begin


subsection \<open>Nested Mask Getters and Setters\<close>

fun get_mp_nm :: "'a nested_mask \<Rightarrow> 'a predicate_mask"
  where "get_mp_nm nm = (option_fold (pos2p \<circ> fst) 0) \<circ> (get_fnm_nm nm)"

fun get_nm_loc_nm :: "'a nested_mask \<Rightarrow> 'a predicate_loc \<Rightarrow> 'a nested_mask option"
  where "get_nm_loc_nm nm loc = map_option snd (get_fnm_nm nm loc)"

fun upd_mh_loc_nm :: "'a nested_mask \<Rightarrow> heap_loc \<Rightarrow> preal \<Rightarrow> 'a nested_mask"
  where "upd_mh_loc_nm nm l p = upd_mh_nm nm ((get_mh_nm nm)( l := p ))"

fun add_to_lpm_nonzero_nm :: "'a nested_mask \<Rightarrow> 'a predicate_loc \<Rightarrow> posreal \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask"
  where "add_to_lpm_nonzero_nm nm lp p nm' = upd_fnm_nm nm ((get_fnm_nm nm)( lp :=
           Some (option_fold (\<lambda>lpm. (fst lpm + p, snd lpm + nm')) (p, nm') (get_fnm_nm nm lp)) ))"

fun add_to_lpm_nm :: "'a nested_mask \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask"
  where "add_to_lpm_nm nm lp p nm' = (if p = 0 then nm else add_to_lpm_nonzero_nm nm lp (p2pos p) nm')"

fun rm_from_lpm_nm :: "'a nested_mask \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> 'a nested_mask"
  where "rm_from_lpm_nm nm lp p = upd_fnm_nm nm ((get_fnm_nm nm)( lp :=
           option_fold (\<lambda>lpm. if p \<ge> pos2p (fst lpm) then None else Some (p2pos (pos2p (fst lpm) - p), (1 - pos2p (fst lpm) / p) *\<^sub>s snd lpm)) None (get_fnm_nm nm lp) ))"

(*
fun upd_mp_loc_nm :: "'a nested_mask \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> 'a nested_mask"
  where "upd_mp_loc_nm (NM mh mp fnm) lp p = NM mh (mp( lp := p )) fnm"

fun upd_nm_loc_nm :: "'a nested_mask \<Rightarrow> 'a predicate_loc \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask"
  where "upd_nm_loc_nm (NM mh mp fnm) lp nm = NM mh mp (fnm( lp := Some nm ))"

fun upd_nm_loc_opt_nm :: "'a nested_mask \<Rightarrow> 'a predicate_loc \<Rightarrow> 'a nested_mask option \<Rightarrow> 'a nested_mask"
  where "upd_nm_loc_opt_nm (NM mh mp fnm) lp nm = NM mh mp (fnm( lp := nm ))"

fun inc_mp_loc_nm :: "'a nested_mask \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> 'a nested_mask"
  where "inc_mp_loc_nm (NM mh mp fnm) lp p = NM mh (mp( lp := mp lp + p )) fnm"

fun dec_mh_loc_nm :: "'a nested_mask \<Rightarrow> heap_loc \<Rightarrow> preal \<Rightarrow> 'a nested_mask"
  where "dec_mh_loc_nm (NM mh mp fnm) l p = NM (mh( l := mh l - p )) mp fnm"

fun dec_mp_loc_nm :: "'a nested_mask \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> 'a nested_mask"
  where "dec_mp_loc_nm (NM mh mp fnm) lp p = NM mh (mp( lp := mp lp - p )) fnm"

fun add_to_nm_loc_nm :: "'a nested_mask \<Rightarrow> 'a predicate_loc \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask"
  where "add_to_nm_loc_nm (NM mh mp fnm) loc nm = NM mh mp (fnm( loc := fnm loc + Some nm ))"

fun mult_nm_loc_nm :: "'a nested_mask \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> 'a nested_mask"
  where "mult_nm_loc_nm (NM mh mp fnm) lp p = NM mh mp (fnm( lp := p *\<^sub>s fnm lp ))"

fun mult_rm_nm_loc_nm :: "'a nested_mask \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> 'a nested_mask"
  where "mult_rm_nm_loc_nm (NM mh mp fnm) lp p = NM mh mp (fnm( lp := if mp lp = p then None else ((mp lp - p) / mp lp) *\<^sub>s fnm lp) )"
*)


subsection \<open>Total State Getters and Setters\<close>

fun get_mh_total :: "('a, 'b) total_state_scheme \<Rightarrow> field_mask"
  where "get_mh_total \<phi> = get_mh_nm (get_nm_total \<phi>)"

fun get_mp_total :: "('a, 'b) total_state_scheme \<Rightarrow> 'a predicate_mask"
  where "get_mp_total \<phi> = get_mp_nm (get_nm_total \<phi>)"

fun get_fnm_total :: "('a, 'b) total_state_scheme \<Rightarrow> 'a predicate_nm_fun"
  where "get_fnm_total \<phi> = get_fnm_nm (get_nm_total \<phi>)"

(*
fun get_m_total :: "('a, 'b) total_state_scheme \<Rightarrow> field_mask \<times> 'a predicate_mask"
  where "get_m_total \<omega> = (get_mh_total \<omega>, get_mp_total \<omega>)"

fun get_nm_loc_total :: "('a, 'b) total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> 'a nested_mask option"
  where "get_nm_loc_total \<phi> lp = get_fnm_total \<phi> lp"
*)

fun upd_hh_total :: "('a, 'b) total_state_scheme \<Rightarrow> 'a total_heap \<Rightarrow> ('a, 'b) total_state_scheme"
  where "upd_hh_total \<omega> hh = \<omega>\<lparr> get_hh_total := hh \<rparr>"

fun upd_hh_loc_total :: "('a, 'b) total_state_scheme \<Rightarrow> heap_loc \<Rightarrow> 'a val \<Rightarrow> ('a, 'b) total_state_scheme"
  where "upd_hh_loc_total \<omega> l v = \<omega>\<lparr> get_hh_total := (get_hh_total \<omega>)(l := v) \<rparr>"

fun upd_mh_total :: "('a, 'b) total_state_scheme \<Rightarrow> field_mask \<Rightarrow> ('a, 'b) total_state_scheme"
  where "upd_mh_total \<phi> mh = \<phi>\<lparr> get_nm_total := upd_mh_nm (get_nm_total \<phi>) mh \<rparr>"

fun upd_mh_loc_total :: "('a, 'b) total_state_scheme \<Rightarrow> heap_loc \<Rightarrow> preal \<Rightarrow> ('a, 'b) total_state_scheme"
  where "upd_mh_loc_total \<phi> l p = \<phi>\<lparr> get_nm_total := upd_mh_loc_nm (get_nm_total \<phi>) l p \<rparr>"

(*
fun upd_mp_total :: "('a, 'b) total_state_scheme \<Rightarrow> 'a predicate_mask \<Rightarrow> ('a, 'b) total_state_scheme"
  where "upd_mp_total \<phi> mp = \<phi>\<lparr> get_nm_total := upd_mp_nm (get_nm_total \<phi>) mp \<rparr>"

fun upd_mp_loc_total :: "('a, 'b) total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> ('a, 'b) total_state_scheme"
  where "upd_mp_loc_total \<phi> lp p = \<phi>\<lparr> get_nm_total := upd_mp_loc_nm (get_nm_total \<phi>) lp p \<rparr>"

fun upd_m_total :: "('a, 'b) total_state_scheme \<Rightarrow> field_mask \<times> 'a predicate_mask \<Rightarrow> ('a, 'b) total_state_scheme"
  where "upd_m_total \<omega> m = upd_mp_total (upd_mh_total \<omega> (fst m)) (snd m)"

fun upd_fnm_total :: "('a, 'b) total_state_scheme \<Rightarrow> ('a predicate_loc \<rightharpoonup> 'a nested_mask) \<Rightarrow> ('a, 'b) total_state_scheme"
  where "upd_fnm_total \<phi> fnm = \<phi>\<lparr> get_nm_total := upd_fnm_nm (get_nm_total \<phi>) fnm \<rparr>"
*)

fun upd_nm_total :: "('a, 'b) total_state_scheme \<Rightarrow> 'a nested_mask \<Rightarrow> ('a, 'b) total_state_scheme"
  where "upd_nm_total \<phi> nm = \<phi>\<lparr> get_nm_total := nm \<rparr>"

(*
fun upd_nm_loc_total :: "('a, 'b) total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> 'a nested_mask \<Rightarrow> ('a, 'b) total_state_scheme"
  where "upd_nm_loc_total \<phi> lp nm = \<phi>\<lparr> get_nm_total := upd_nm_loc_nm (get_nm_total \<phi>) lp nm \<rparr>"

fun upd_nm_loc_opt_total :: "('a, 'b) total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> 'a nested_mask option \<Rightarrow> ('a, 'b) total_state_scheme"
  where "upd_nm_loc_opt_total \<phi> lp nm = \<phi>\<lparr> get_nm_total := upd_nm_loc_opt_nm (get_nm_total \<phi>) lp nm \<rparr>"
*)

fun add_to_nm_total :: "('a, 'b) total_state_scheme \<Rightarrow> 'a nested_mask \<Rightarrow> ('a, 'b) total_state_scheme"
  where "add_to_nm_total \<phi> nm = \<phi>\<lparr> get_nm_total := get_nm_total \<phi> + nm \<rparr>"

(*
fun add_to_nm_loc_total :: "('a, 'b) total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> 'a nested_mask \<Rightarrow> ('a, 'b) total_state_scheme"
  where "add_to_nm_loc_total \<phi> lp nm = \<phi>\<lparr> get_nm_total := add_to_nm_loc_nm (get_nm_total \<phi>) lp nm \<rparr>"

fun inc_mp_loc_total :: "('a, 'b) total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> ('a, 'b) total_state_scheme"
  where "inc_mp_loc_total \<phi> lp p = \<phi>\<lparr> get_nm_total := inc_mp_loc_nm (get_nm_total \<phi>) lp p \<rparr>"

fun dec_mh_loc_total :: "('a, 'b) total_state_scheme \<Rightarrow> heap_loc \<Rightarrow> preal \<Rightarrow> ('a, 'b) total_state_scheme"
  where "dec_mh_loc_total \<phi> l p = \<phi>\<lparr> get_nm_total := dec_mh_loc_nm (get_nm_total \<phi>) l p \<rparr>"

fun dec_mp_loc_total :: "('a, 'b) total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> ('a, 'b) total_state_scheme"
  where "dec_mp_loc_total \<phi> lp p = \<phi>\<lparr> get_nm_total := dec_mp_loc_nm (get_nm_total \<phi>) lp p \<rparr>"
*)

fun mult_nm_total :: "('a, 'b) total_state_scheme \<Rightarrow> preal \<Rightarrow> ('a, 'b) total_state_scheme"
  where "mult_nm_total \<phi> p = \<phi>\<lparr> get_nm_total := p *\<^sub>s get_nm_total \<phi> \<rparr>"

(*
fun mult_nm_loc_total :: "('a, 'b) total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> ('a, 'b) total_state_scheme"
  where "mult_nm_loc_total \<phi> lp p = \<phi>\<lparr> get_nm_total := mult_nm_loc_nm (get_nm_total \<phi>) lp p \<rparr>"

fun mult_rm_nm_loc_total :: "('a, 'b) total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> ('a, 'b) total_state_scheme"
  where "mult_rm_nm_loc_total \<phi> lp p = \<phi>\<lparr> get_nm_total := mult_rm_nm_loc_nm (get_nm_total \<phi>) lp p \<rparr>"
*)

fun add_to_lpm_total :: "('a, 'b) total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> posreal \<Rightarrow> 'a nested_mask \<Rightarrow> ('a, 'b) total_state_scheme"
  where "add_to_lpm_total \<phi> lp p nm' = upd_nm_total \<phi> (add_to_lpm_nonzero_nm (get_nm_total \<phi>) lp p nm')"

fun rm_from_lpm_total :: "('a, 'b) total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> ('a, 'b) total_state_scheme"
  where "rm_from_lpm_total \<phi> lp p = upd_nm_total \<phi> (rm_from_lpm_nm (get_nm_total \<phi>) lp p)"


subsection \<open>Full Total State Getters and Setters\<close>

fun get_hh_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> 'a total_heap"
  where "get_hh_total_full \<omega> = get_hh_total (get_total_full \<omega>)"

fun get_nm_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> 'a nested_mask"
  where "get_nm_total_full \<omega> = get_nm_total (get_total_full \<omega>)"

fun get_mh_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> field_mask"
  where "get_mh_total_full \<omega> = get_mh_total (get_total_full \<omega>)"

fun get_mp_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> 'a predicate_mask"
  where "get_mp_total_full \<omega> = get_mp_total (get_total_full \<omega>)"

(*
fun get_fnm_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> ('a predicate_loc \<rightharpoonup> 'a nested_mask)"
  where "get_fnm_total_full \<omega> = get_fnm_total (get_total_full \<omega>)"

fun get_nm_loc_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> 'a nested_mask option"
  where "get_nm_loc_total_full \<omega> lp = get_nm_loc_total (get_total_full \<omega>) lp"

fun get_m_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> field_mask \<times> 'a predicate_mask"
  where "get_m_total_full \<omega> = (get_mh_total_full \<omega>, get_mp_total_full \<omega>)"
*)

fun upd_hh_total_full ::  "('a, 'b) full_total_state_scheme \<Rightarrow> 'a total_heap \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "upd_hh_total_full \<omega> hh = \<omega>\<lparr> get_total_full := upd_hh_total (get_total_full \<omega>) hh \<rparr>"

fun upd_hh_loc_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> heap_loc \<Rightarrow> 'a val \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "upd_hh_loc_total_full \<omega> l v =
        \<omega>\<lparr> get_total_full := upd_hh_loc_total (get_total_full \<omega>) l v \<rparr>"

(*
fun upd_m_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> field_mask \<Rightarrow> 'a predicate_mask \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "upd_m_total_full \<omega> m pm = \<omega>\<lparr> get_total_full := upd_mp_total (upd_mh_total (get_total_full \<omega>) m) pm \<rparr>"
*)

fun upd_mh_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> field_mask \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "upd_mh_total_full \<omega> mh = \<omega>\<lparr> get_total_full :=  upd_mh_total (get_total_full \<omega>) mh \<rparr>"

(*
fun upd_mp_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> 'a predicate_mask \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "upd_mp_total_full \<omega> mp = \<omega>\<lparr> get_total_full := upd_mp_total (get_total_full \<omega>) mp \<rparr>"
*)

fun upd_mh_loc_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> heap_loc \<Rightarrow> preal \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "upd_mh_loc_total_full \<omega> l p =
        \<omega>\<lparr> get_total_full := upd_mh_loc_total (get_total_full \<omega>) l p \<rparr>"

(*
fun upd_mp_loc_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "upd_mp_loc_total_full \<omega> lp p =
        \<omega>\<lparr> get_total_full := upd_mp_loc_total (get_total_full \<omega>) lp p \<rparr>"

fun upd_fnm_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> ('a predicate_loc \<rightharpoonup> 'a nested_mask) \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "upd_fnm_total_full \<omega> fnm = \<omega>\<lparr> get_total_full := upd_fnm_total (get_total_full \<omega>) fnm \<rparr>"
*)

fun upd_nm_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> 'a nested_mask \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "upd_nm_total_full \<omega> nm = \<omega>\<lparr> get_total_full := (get_total_full \<omega>)\<lparr> get_nm_total := nm \<rparr> \<rparr>"

(*
fun upd_nm_loc_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> 'a nested_mask \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "upd_nm_loc_total_full \<omega> lp nm = \<omega>\<lparr> get_total_full := upd_nm_loc_total (get_total_full \<omega>) lp nm \<rparr>"

fun upd_nm_loc_opt_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> 'a nested_mask option \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "upd_nm_loc_opt_total_full \<omega> lp nm = \<omega>\<lparr> get_total_full := upd_nm_loc_opt_total (get_total_full \<omega>) lp nm \<rparr>"
*)

fun add_to_nm_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> 'a nested_mask \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "add_to_nm_total_full \<omega> nm =
        \<omega>\<lparr> get_total_full := add_to_nm_total (get_total_full \<omega>) nm \<rparr>"

(*
fun add_to_nm_loc_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> 'a nested_mask \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "add_to_nm_loc_total_full \<omega> lp nm =
        \<omega>\<lparr> get_total_full := add_to_nm_loc_total (get_total_full \<omega>) lp nm \<rparr>"

fun inc_mp_loc_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "inc_mp_loc_total_full \<omega> lp p =
        \<omega>\<lparr> get_total_full := inc_mp_loc_total (get_total_full \<omega>) lp p \<rparr>"

fun dec_mh_loc_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> heap_loc \<Rightarrow> preal \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "dec_mh_loc_total_full \<omega> l p =
        \<omega>\<lparr> get_total_full := dec_mh_loc_total (get_total_full \<omega>) l p \<rparr>"

fun dec_mp_loc_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "dec_mp_loc_total_full \<omega> lp p =
        \<omega>\<lparr> get_total_full := dec_mp_loc_total (get_total_full \<omega>) lp p \<rparr>"
*)

fun mult_nm_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> preal \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "mult_nm_total_full \<omega> p = \<omega>\<lparr> get_total_full := mult_nm_total (get_total_full \<omega>) p \<rparr>"

(*
fun mult_nm_loc_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "mult_nm_loc_total_full \<omega> lp p = \<omega>\<lparr> get_total_full := mult_nm_loc_total (get_total_full \<omega>) lp p \<rparr>"

fun mult_rm_nm_loc_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "mult_rm_nm_loc_total_full \<omega> lp p = \<omega>\<lparr> get_total_full := mult_rm_nm_loc_total (get_total_full \<omega>) lp p \<rparr>"
*)

fun add_to_lpm_nonzero_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> posreal \<Rightarrow> 'a nested_mask \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "add_to_lpm_nonzero_total_full \<omega> lp p nm' = upd_nm_total_full \<omega> (add_to_lpm_nonzero_nm (get_nm_total_full \<omega>) lp p nm')"

fun add_to_lpm_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> 'a nested_mask \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "add_to_lpm_total_full \<omega> lp p nm' = upd_nm_total_full \<omega> (add_to_lpm_nm (get_nm_total_full \<omega>) lp p nm')"

fun rm_from_lpm_total_full :: "('a, 'b) full_total_state_scheme \<Rightarrow> 'a predicate_loc \<Rightarrow> preal \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "rm_from_lpm_total_full \<phi> lp p = upd_nm_total_full \<phi> (rm_from_lpm_nm (get_nm_total_full \<phi>) lp p)"


subsection \<open>Empty States\<close>

definition is_empty_total :: "('a,'b) total_state_scheme \<Rightarrow> bool"
  where "is_empty_total \<phi> \<equiv> get_nm_total \<phi> = 0"

definition is_empty_total_full :: "('a,'b) full_total_state_scheme \<Rightarrow> bool"
  where "is_empty_total_full \<omega> \<equiv> is_empty_total (get_total_full \<omega>)"


subsection \<open>Store Update\<close>

fun update_var_total :: "'a full_total_state \<Rightarrow> var \<Rightarrow> 'a val \<Rightarrow> 'a full_total_state"
  where "update_var_total \<omega> x v = \<omega>\<lparr>get_store_total := (get_store_total \<omega>)(x \<mapsto> v)\<rparr>"

fun update_store_total :: "'a full_total_state \<Rightarrow> 'a store \<Rightarrow> 'a full_total_state"
  where "update_store_total \<omega> \<sigma> = \<omega>\<lparr>get_store_total := \<sigma>\<rparr>"


subsection \<open>Trace Update\<close>

fun update_trace_total :: "('a, 'b) full_total_state_scheme \<Rightarrow> 'a total_trace \<Rightarrow> ('a, 'b) full_total_state_scheme"
  where "update_trace_total \<omega> \<pi> = \<omega>\<lparr>get_trace_total := \<pi>\<rparr>"


subsection \<open>Readable and Writable Location Sets\<close>

definition get_valid_locs :: "'a full_total_state \<Rightarrow> heap_loc set"
  where "get_valid_locs \<omega> = {lh |lh. get_mh_total_full \<omega> lh > 0}"

definition get_writeable_locs :: "'a full_total_state \<Rightarrow> heap_loc set"
  where "get_writeable_locs \<omega> = {lh |lh. get_mh_total_full \<omega> lh = 1}"


subsection \<open>Full Total State Split\<close>

(*
fun proportional_split :: "'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> 'a full_total_state \<Rightarrow> bool" where
  "proportional_split \<omega> \<omega>\<^sub>1 \<omega>\<^sub>2 = ((\<forall>l. get_mh_total_full \<omega>\<^sub>1 l + get_mh_total_full \<omega>\<^sub>2 l = get_mh_total_full \<omega> l) \<and>
    (\<forall>pl. get_mp_total_full \<omega>\<^sub>1 pl + get_mp_total_full \<omega>\<^sub>2 pl = get_mp_total_full \<omega> pl \<and>
      get_nm_loc_total_full \<omega>\<^sub>1 pl = (get_mp_total_full \<omega>\<^sub>1 pl / get_mp_total_full \<omega> pl) *\<^sub>s (get_nm_loc_total_full \<omega> pl) \<and>
      get_nm_loc_total_full \<omega>\<^sub>2 pl = (get_mp_total_full \<omega>\<^sub>2 pl / get_mp_total_full \<omega> pl) *\<^sub>s (get_nm_loc_total_full \<omega> pl)))"
*)


subsection \<open>Nested Mask Shift Operations\<close>

text \<open>\<^term>\<open>shift_up\<close> only "unfolds" the specified predicate by one level.
      It does not check if the body of the predicate being unfolded is satisfied.\<close>

inductive shift_up :: "predicate_ident \<Rightarrow> ('a val list) \<Rightarrow> preal \<Rightarrow> 'a nested_mask \<Rightarrow> 'a nested_mask \<Rightarrow> bool" where
  ShiftNonZero:
  "\<lbrakk> mh = get_mh_nm nm;
     fnm = get_fnm_nm nm;
     Some (p\<^sub>p, pnm) = fnm (pred_id,vs);
     p = pos2p p\<^sub>p;
     q > 0;
     q \<le> p;
     fnm' = fnm( (pred_id,vs) := if p = q then None else Some (p2pos (p - q), ((p - q) / p) *\<^sub>s pnm) );
     nm'_sub = NM mh fnm';
     nm' = nm'_sub + (q / p) *\<^sub>s pnm \<rbrakk> \<Longrightarrow>
     shift_up pred_id vs q nm nm'"
| ShiftZero:
  "shift_up pred_id vs 0 nm nm"

inductive_cases shift_up_case: "shift_up pred_id vs q nm nm'"
inductive_simps shift_up_simp: "shift_up pred_id vs q nm nm'"


lemma shift_up_perm_sufficient:
  assumes "shift_up pid vs q nm nm'"
  shows "q \<le> get_mp_nm nm (pid,vs)"
  using assms[simplified shift_up.simps]
  apply simp
  by (metis (no_types, opaque_lifting) all_pos comp_def fst_conv option_fold.simps(1))


end