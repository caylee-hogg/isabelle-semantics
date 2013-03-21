theory Stlc 
imports Main begin

(* Well golly gee willikers since the simply typed lambda calculus has a 
   set theoretic semantics, one might hope we can write a denotation function
   without actually appealing to domain theory. Let's try! *)

datatype ty = TyNat | TyFun ty ty

datatype lam = LVar nat | LApp lam lam | LAbs nat ty lam | LNat nat
             | LPlus lam lam

(* Now what is the domain for our meaning function going to be? Well, we might consider defining a type 

   data V = VNat nat | VBool bool | VFun "V \<Rightarrow> V"


   The problem, of course, is that this is negatively recursive and has no
   meaning in Isabelle/HOL. Why? Because we can sneakily encode the Y-combinator
   into our language if we allow negative datatypes 
   TODO: add more textual examples of that

   So now we take a second approach that's a bit sneakier. What if we try
   an encoding where the functions are from terms to values?
*)

datatype V = VNat nat | VBool bool | VFun "lam \<Rightarrow> V"

(* Obviously this has no problems being accepted, but what about when we
   try to write the meaning function? *)

primrec fromFun :: "V \<Rightarrow> (lam \<Rightarrow> V)" where
"fromFun (VFun f) = f"

fun lamM :: "lam \<Rightarrow> (nat \<Rightarrow> V) \<Rightarrow> V" where
"lamM (LVar n) \<sigma> = \<sigma> n" |
"lamM (LNat n) \<sigma> = VNat n" |
"lamM (LApp l l') \<sigma> = fromFun (lamM l \<sigma>) l'" |
"lamM (LAbs n _ l) \<sigma> = VFun (\<lambda> a. lamM l (\<sigma>(n := lamM a \<sigma>)))"

(* Oops, this isn't necessarily terminating and there's no way to sneak in 
   what we need here, is there? there's no guarantee
   that 'a' is actually smaller. This is the price we pay for having such
   a weak type system that we cannot guarantee that the types work the
   way we could in Agda or Idris or Coq. *)