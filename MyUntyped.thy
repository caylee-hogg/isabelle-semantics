theory MyUntyped
imports "Nominal-Utils" "FMap-Nominal-HOLCF" begin

atom_decl name

nominal_datatype lam = Lam x::"name" l::"lam" binds x in l | App lam lam | Var name

domain D = DFun "D \<rightarrow> D"

abbreviation dLam :: "(D \<Rightarrow> D) \<Rightarrow> D" (binder "\<Delta> " 10) where
"dLam f \<equiv> DFun\<cdot>(\<Lambda> x. f x)"

fixrec dApply :: "D \<rightarrow> D \<rightarrow> D" where
"dApply\<cdot>(DFun\<cdot>f)\<cdot>x = f\<cdot>x" |
"dApply\<cdot>\<bottom>\<cdot>x = \<bottom>"

abbreviation dapp :: "D \<Rightarrow> D \<Rightarrow> D" (infixl "\<diamond>" 900) where
"f\<diamond>x \<equiv> dApply\<cdot>f\<cdot>x"

instantiation D :: pure_cpo
begin
  definition "p \<bullet> (d :: D) = d"
instance 
  apply default 
  apply (auto simp add: permute_D_def)
  done
end

type_synonym 'a cenv = "name f\<rightharpoonup> 'a"

instantiation name :: discrete_cpo
begin
  definition  [simp]: "(x::name) \<sqsubseteq> y \<longleftrightarrow> x = y"
  instance by default simp
end

instance name :: cont_pt  by default auto

nominal_primrec lamDenote :: "lam \<Rightarrow> D cenv \<Rightarrow> D" where
"atom n \<sharp> \<sigma> \<Longrightarrow> lamDenote (Lam n l) \<sigma> = (\<Delta> x. lamDenote l (\<sigma>(n f\<mapsto> x)))" |
"lamDenote (Var n) \<sigma> = \<sigma> f! n" |
"lamDenote (App f a) \<sigma> = (lamDenote f \<sigma>)\<diamond>(lamDenote a \<sigma>)"
proof-  (* this was done by following the proof from the Denotational.thy file in the isa-launchbury development *)

case goal1 thus ?case
  unfolding eqvt_def lamDenote_graph_def
  by (rule, perm_simp, rule)
next
case (goal3 P x) 
  show ?case
  proof(cases x)
  case (Pair e \<rho>)
    show ?thesis 
      using Pair goal3 thm lam.exhaust(1)
      apply (rule_tac y=e in lam.exhaust(1))
      prefer 2
      apply (rule_tac y=e and c = \<rho> in lam.strong_exhaust(1), auto simp add: fresh_star_singleton,metis)[1]
      apply (rule_tac y=e and c = \<rho> in lam.strong_exhaust(1), auto simp add: fresh_star_singleton,metis)[1]
      apply auto[1]
      done
  qed
next

case (goal4 n \<sigma> l n' \<sigma>' l' )
  have all_fresh: "(atom n' \<rightleftharpoons> atom n) \<bullet> \<sigma>' = \<sigma>'" 
    using goal4
    by (auto simp add: swap_fresh_fresh)

  have tmp: "\<And> xa. lamDenote_sumC (l, (\<sigma>(n f\<mapsto> xa))) = lamDenote_sumC (l', (\<sigma>'(n' f\<mapsto> xa)))"
    using goal4
    apply (auto simp add: Abs1_eq_iff')

    apply (erule_tac x = xa in meta_allE)
    apply (erule_tac x = xa in meta_allE)
    apply (simp only: eqvt_at_def)
    apply auto

    apply (erule_tac x = "(atom n' \<rightleftharpoons> atom n)" in allE)
    apply (auto simp add: fmap_upd_eqvt permute_D_def all_fresh)
    done
   thus ?case by simp
next
qed auto

termination (eqvt) by lexicographic_order

lemma permute_lamDenote: "\<pi> \<bullet> lamDenote = lamDenote"
apply (perm_simp, rule)
done

lemma "cont (lamDenote l)"
apply (induct l rule: lam.strong_induct)
back
apply simp

definition aname where
"aname \<equiv> Abs_name (Atom (Sort ''MyUntyped.name'' []) 0)"
(*
definition Lam' :: "(name \<Rightarrow> lam) \<Rightarrow> lam" (binder "LAM " 10) where
"Lam' f = fresh_fun (\<lambda> x. Lam x (f x))" *)

definition Lam' :: "(name \<Rightarrow> lam) \<Rightarrow> lam" (binder "LAM " 10) where
"Lam' f = Lam aname (f aname)"

(* simple example of church encodings *)

definition C0 :: lam where
"C0 \<equiv> (LAM s z. (Var z))"

definition C1 :: lam where
"C1 \<equiv> (LAM s z. (App (Var s) (Var z)))"

definition CSucc :: lam where
"CSucc \<equiv> (LAM n s z.  (App (Var s) (App (App (Var z) (Var s)) (Var n))))"

lemma "lamDenote (App CSucc C0) f\<emptyset> = lamDenote C1 f\<emptyset>"
apply (simp add: CSucc_def C1_def C0_def Lam'_def)
(* doesn't actually reduce the lambda abstractions, is stuck on the FRESH binders *)
done