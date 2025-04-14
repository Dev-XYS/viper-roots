theory PredicatesUtil
imports ViperLang HOL.Real
begin
(*
fun real_to_expr :: "real \<Rightarrow> pure_exp"
  where "real_to_expr r = (let q = quotient_of r in 
                                  (Binop (ELit (LInt (fst q))) PermDiv (ELit (LInt (snd q)))))"
*)
fun real_to_expr :: "real \<Rightarrow> pure_exp" where
  "real_to_expr r = ELit (LPerm r)"

text \<open>Here multiplication of Wildcard with a negative amount gives wildcard\<close>
fun real_mult_permexpr :: "real \<Rightarrow> pure_exp exp_or_wildcard \<Rightarrow> pure_exp exp_or_wildcard"
  where 
    "real_mult_permexpr p Wildcard = (if p = 0 then PureExp (ELit NoPerm) else (if p > 0 then Wildcard else undefined))"
  | "real_mult_permexpr p (PureExp e) = PureExp (Binop (real_to_expr p) Mult e)"

fun syntactic_mult :: "real \<Rightarrow> assertion \<Rightarrow> assertion"
  where
    "syntactic_mult p (Atomic (Pure e)) = (Atomic (Pure e))"
  | "syntactic_mult p (Atomic (Acc e_r f e_p)) = (Atomic (Acc e_r f (real_mult_permexpr p e_p)))"
  | "syntactic_mult p (Atomic (AccPredicate pred_id e_args e_p)) = 
       (Atomic (AccPredicate pred_id e_args (real_mult_permexpr p e_p)))"
  | "syntactic_mult p (Imp e A) = (Imp e (syntactic_mult p A))"
  | "syntactic_mult p (Star A B) = Star (syntactic_mult p A) (syntactic_mult p B)"
  | "syntactic_mult p (ForAll ty A) = (ForAll ty (syntactic_mult p A))"
  | "syntactic_mult p (Exists ty A) = (Exists ty (syntactic_mult p A))"
  | "syntactic_mult p (ImpureAnd A B) = ImpureAnd (syntactic_mult p A) (syntactic_mult p B)"
  | "syntactic_mult p (ImpureOr A B) = ImpureOr (syntactic_mult p A) (syntactic_mult p B)"
  | "syntactic_mult p (A --* B) = (syntactic_mult p A) --* (syntactic_mult p B)"
  | "syntactic_mult p (CondAssert e A B) = CondAssert e (syntactic_mult p A) (syntactic_mult p B)"

hide_const predicate_decl.args function_decl.args method_decl.args
fun substitute_args_expr :: "pure_exp \<Rightarrow> pure_exp list \<Rightarrow> pure_exp" where
    "substitute_args_expr (Var x) args = (if x < length args then args ! x else DummyExpr)"  \<comment> \<open>Using \<^const>\<open>DummyExpr\<close> as the default value. Otherwise \<open>eval_with_substitution_rev\<close> is not provable.\<close>
  | "substitute_args_expr (Unop uop e) args = Unop uop (substitute_args_expr e args)"
  | "substitute_args_expr (Binop e1 bop e2) args = Binop (substitute_args_expr e1 args) bop (substitute_args_expr e2 args)"
  | "substitute_args_expr (CondExp cond e1 e2) args = CondExp (substitute_args_expr cond args) (substitute_args_expr e1 args) (substitute_args_expr e2 args)"
  | "substitute_args_expr (FieldAcc e f) args = FieldAcc (substitute_args_expr e args) f"
  | "substitute_args_expr (Old l e) args = Old l (substitute_args_expr e args)"
  | "substitute_args_expr (Perm e f) args = Perm (substitute_args_expr e args) f"
  | "substitute_args_expr (PermPred pid es) args = PermPred pid (map (\<lambda>e. substitute_args_expr e args) es)"
  | "substitute_args_expr (FunApp fid es) args = FunApp fid (map (\<lambda>e. substitute_args_expr e args) es)"
  | "substitute_args_expr (Unfolding pid es e) args = Unfolding pid (map (\<lambda>e. substitute_args_expr e args) es) (substitute_args_expr e args)"
  | "substitute_args_expr (Let e lbody) args = Let (substitute_args_expr e args) (substitute_args_expr lbody args)"
  | "substitute_args_expr (PExists ty e) args = PExists ty (substitute_args_expr e args)"
  | "substitute_args_expr (PForall ty e) args = PForall ty (substitute_args_expr e args)"
  | "substitute_args_expr e _ = e"

fun substitute_args_assertion :: "assertion \<Rightarrow> pure_exp list \<Rightarrow> assertion" where
    "substitute_args_assertion (Atomic (Pure e)) args = Atomic (Pure (substitute_args_expr e args))"
  | "substitute_args_assertion (Atomic (Acc e_r f (PureExp e_p))) args = Atomic (Acc (substitute_args_expr e_r args) f (PureExp (substitute_args_expr e_p args)))"
  | "substitute_args_assertion (Atomic (Acc e_r f Wildcard)) args = Atomic (Acc (substitute_args_expr e_r args) f Wildcard)"
  | "substitute_args_assertion (Atomic (AccPredicate pid e_args (PureExp e_p))) args = Atomic (AccPredicate pid (map (\<lambda>e. substitute_args_expr e args) e_args) (PureExp (substitute_args_expr e_p args)))"
  | "substitute_args_assertion (Atomic (AccPredicate pid e_args Wildcard)) args = Atomic (AccPredicate pid (map (\<lambda>e. substitute_args_expr e args) e_args) Wildcard)"
  | "substitute_args_assertion (Imp e A) args = Imp (substitute_args_expr e args) (substitute_args_assertion A args)"
  | "substitute_args_assertion (Star A B) args = Star (substitute_args_assertion A args) (substitute_args_assertion B args)"
  | "substitute_args_assertion (CondAssert e A B) args = CondAssert (substitute_args_expr e args) (substitute_args_assertion A args) (substitute_args_assertion B args)"
  | "substitute_args_assertion A _ = A"

lemma substitute_synmult_commute:
  assumes "p \<ge> 0"
  shows "substitute_args_assertion (syntactic_mult p A) args = syntactic_mult p (substitute_args_assertion A args)"
  using assms
  apply (induction A; simp?)
  apply (rename_tac atm)
  apply (case_tac atm; simp?)
   apply (rename_tac e_r f perm)
   apply (case_tac perm; simp?)
  apply (rename_tac pid e_args perm)
  apply (case_tac perm; simp?)
  done

end