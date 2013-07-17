(*<*)
theory Pointy 
imports HOLCF Ideal Cenv CPER
"~~/src/HOL/HOLCF/Library/Bool_Discrete"
 begin (*>*)

section {* Pointed types *}

text {* Another example we will consider, motivated by the Habit language design (ref), comes from a paper by Launchbury and Patterson (ref). Motivated by issues of optimization and safe unboxing of types in Haskell, they introduced a typeclass to describe when a type has bottom as an element. For sake of example,
let us consider a lazy language with a pointed boolean type, an unpointed natural numbers type, and a function type. As this language is call by name, we will have the following instances for this typeclass.

   instance Pointed b => Pointed (a -> b)
and
   instance Pointed Bool
In words, we have that whenever the codomain of the function space is pointed then the entire function space must be pointed. In order to model this typeclass, we will add an inductively defined predicate to describe pointedness.

Here we present our types and terms, as before
*}

datatype ty = TyNat | TyFun ty ty | TyPBool

datatype lam = LVar nat | LApp lam lam | LLam nat ty lam | LNat nat
             | LPlus lam lam | LFix ty lam | LBool bool

text {* Here, we include the inductive pointedness relation on types *}

inductive pointed :: "ty \<Rightarrow> bool" where
pFun : "\<lbrakk>pointed t2\<rbrakk> \<Longrightarrow> pointed (TyFun t1 t2)" |
pBool : "pointed TyPBool"

type_synonym ty_env = "nat \<Rightarrow> ty"

text {* Now our typing relation is, mostly the same as before, but with the additional change that our fixed point operator is only defined
        on pointed types. This is equivalent to having the type of our fixed point operator be, in the Haskell
        world, something like @{text "fix : Pointed a \<Rightarrow> (a \<rightarrow> a) \<rightarrow> a"} *}

inductive lam_ty :: "ty_env \<Rightarrow> lam \<Rightarrow> ty \<Rightarrow> bool" where
  LVar : "\<lbrakk>tys n = ty\<rbrakk> \<Longrightarrow> lam_ty tys (LVar n) ty" |
  LPlus : "\<lbrakk>lam_ty tys l1 TyNat; lam_ty tys l2 TyNat\<rbrakk> \<Longrightarrow> lam_ty tys (LPlus l1 l2) TyNat" |
  LApp  : "\<lbrakk>lam_ty tys l1 (TyFun t1 t2); lam_ty tys l2 t1\<rbrakk> \<Longrightarrow> lam_ty tys (LApp l1 l2) t2" |
  LNat  : "lam_ty tys (LNat n) TyNat" |
  LLam  : "\<lbrakk>lam_ty (tys (n :=t1)) l1 t2\<rbrakk> \<Longrightarrow> lam_ty tys (LLam n t1 l1) (TyFun t1 t2)" |
  LFix  : "\<lbrakk>pointed t1; lam_ty tys l1 (TyFun t1 t1)\<rbrakk> \<Longrightarrow> lam_ty tys (LFix t1 l1) t1"

text {* We define our domain type very similarly as before but with the additon of a boolean constructor. *}

domain V = VNat (fromNat :: "nat u") | VFun (lazy "V \<rightarrow> V")
         | VBool (fromBool :: "bool u") | Wrong

(*<*) term V_take

class taken = pcpo + 
  fixes take :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes take_0 [simp]: "take 0 x = \<bottom>"
  assumes take_below [simp]: "take n x \<sqsubseteq> x"
  assumes take_take : "take m (take n x) = take (min m n) x"
  assumes take_reach : "(\<Squnion> i. take i x) = x"
  assumes take_chain : "chain (\<lambda> i. take i x)"

instantiation V :: taken
begin
definition "take_V = (\<lambda> i x. V_take i\<cdot>x)"
instance
apply (default, unfold take_V_def)
apply simp
apply (rule V.take_below)
apply (rule V.take_take)
apply (rule V.reach)
apply simp
done

instantiation "set" :: ("taken") cer
begin

definition "inCer A \<equiv> ideal A"

definition "rel i S T \<equiv> (\<forall> z. take i z \<in> S \<longleftrightarrow> take i z \<in> T)" 
instance
apply (default, unfold rel_set_def inCer_set_def)
apply (rule_tac x="UNIV" in exI)
apply (simp add: ideal_def)
apply simp
apply simp
apply simp
apply (simp add: ideal_bottom)

apply (rule allI)
apply (drule_tac x="take i z" in spec)
apply (subgoal_tac "take (Suc i) (take i z) = take i z")
apply simp 
apply (subgoal_tac "min (Suc i) i = i")
apply (force simp: take_take)
apply simp
apply (rule set_eqI, rename_tac z)
apply (subgoal_tac "(\<Squnion>i. take i z) \<in> x \<longleftrightarrow> (\<Squnion>i. take i z) \<in> y")
apply (simp add: take_reach)
apply (simp add: take_chain ideal_lub_iff)

 (*>*)
done
end

text {* Here we define that the meaning of the natural numbers type is the set of natural
        numbers, without bottom, wrapped up in the appropriate constructors *}

definition VNat_set :: "V set" ("[\<nat>]") where
  "[\<nat>] = (range (\<lambda>x. VNat\<cdot>(up\<cdot>x)))"

text {* Meanwhile, the booleans include bottom *}

definition VBool_set :: "V set" ("[2]") where
"[2] = {VBool\<cdot>(up\<cdot>True), VBool\<cdot>(up\<cdot>False), \<bottom>}"

text {* And as is needed, the booleans form an ideal *}

lemma VBool_ideal : "ideal [2]"
(*<*)
unfolding VBool_set_def
apply (rule idealI)
apply simp
apply (case_tac y, simp_all)
apply (case_tac x, simp_all)
apply (case_tac ua)
apply simp
apply simp
done(*>*)

text {* Our definition of functions is identical to previous definitions and, as expected, forms an ideal when the codomain is an ideal.  *}

(*<*)
fixrec vFix :: "V \<rightarrow> V" where
"vFix\<cdot>(VFun\<cdot>f) = fix\<cdot>f" |
"vFix\<cdot>(VBool\<cdot>(up\<cdot>b)) = Wrong" |
"vFix\<cdot>Wrong = Wrong" |
"vFix\<cdot>(VNat\<cdot>(up\<cdot>n)) = Wrong"

lemma [simp]: "vFix\<cdot>\<bottom> = \<bottom>"
apply fixrec_simp
done

fixrec vApply :: "V \<rightarrow> V \<rightarrow> V" where
"vApply\<cdot>(VNat\<cdot>(up\<cdot>n))\<cdot>x = Wrong" |
"vApply\<cdot>(VFun\<cdot>f)\<cdot>x = f\<cdot>x" |
"vApply\<cdot>(VBool\<cdot>(up\<cdot>b))\<cdot>x = Wrong" |
"vApply\<cdot>Wrong\<cdot>x = Wrong"

lemma [simp]: "vApply\<cdot>\<bottom>\<cdot>x = \<bottom>"
apply fixrec_simp
done

abbreviation vapp :: " V \<Rightarrow> V \<Rightarrow> V" (infixl "\<bullet>" 900) where
"f\<bullet>x \<equiv> vApply\<cdot>f\<cdot>x"

abbreviation vLam :: "(V \<Rightarrow> V) \<Rightarrow> V" (binder "\<Delta> " 10) where
"vLam f \<equiv> VFun\<cdot>(\<Lambda> x. f x)" (*>*)
(*<*)
definition VFun_set :: "V set \<Rightarrow> V set \<Rightarrow> V set" (infix "[\<rightarrow>]" 55)
where
     "S [\<rightarrow>] T = {f. \<forall> x \<in> S. f\<bullet>x \<in> T}"

lemma less_apply: "f \<sqsubseteq> g \<Longrightarrow> f\<bullet>x \<sqsubseteq> g\<bullet>x"
apply (cases f, simp_all)
apply (cases g, simp_all)
apply (case_tac ua, simp_all)
apply (case_tac u, simp_all)
apply (cases g, simp_all)
apply (rule monofun_cfun_fun)
apply simp
apply (cases g, simp_all)
apply (case_tac ua, simp_all)
apply (case_tac u, simp_all)
apply (case_tac g, simp_all)
done

lemma app_lub : "chain Y \<Longrightarrow> (\<Squnion> i. Y i) \<bullet> x = (\<Squnion> i. Y i \<bullet> x)"
apply (rule cont2contlubE, simp+)
done

lemma VFun_ideal : "\<lbrakk>ideal T\<rbrakk> \<Longrightarrow> ideal (S [\<rightarrow>] T)"
unfolding VFun_set_def
apply (rule idealI)
apply clarsimp
apply (rule ideal_bottom)
apply simp
apply clarsimp 
apply (rule_tac y="y\<bullet>xa" in ideal_downward)
apply simp
apply (erule less_apply)
apply simp
apply clarsimp
apply (rule adm_ball)
apply (rule admI)
apply (subgoal_tac "chain (\<lambda>i. Y i \<bullet> x)")
apply (subst app_lub)
apply simp
apply (subgoal_tac "adm (\<lambda>x. x\<in> T)")
apply (drule_tac Y="(\<lambda> i. Y i \<bullet> x)" in admD) 
apply simp
apply simp
apply simp
apply (rule ideal_adm, simp)
apply (rule chainI)
apply (rule less_apply)
apply (rule chainE)
apply simp
done
(*>*)

text {* We reuse our definitions for ideals and combinators of ideals from our demonstration of recursive types, but we don't, yet, bother with making a newtype for ideals. Rather, we have the meaning of our types be ordinary V-sets. *}

fun tyM :: "ty \<Rightarrow> V set" where
"tyM TyNat = [\<nat>]" |
"tyM (TyFun t1 t2) = (tyM t1) [\<rightarrow>] (tyM t2)" |
"tyM TyPBool = [2]"

text {* We can prove, though, that the meaning of a type is an ideal whenever it is pointed so, then, we can write our meaning funciton on terms identically as before and our proof for type soundness follows almost identically *}

lemma pointy_ideal : "pointed t \<Longrightarrow> ideal (tyM t)"
(*<*)
apply (induct t rule: pointed.induct)
apply simp
apply (erule VFun_ideal)
apply simp
apply (rule VBool_ideal)
done

fixrec vPlus :: "V \<rightarrow> V \<rightarrow> V" where
"vPlus\<cdot>(VNat\<cdot>(up\<cdot>n))\<cdot>(VNat\<cdot>(up\<cdot>n')) = VNat\<cdot>(up\<cdot>(n + n'))" |
"vPlus\<cdot>\<bottom>\<cdot>(VNat\<cdot>(up\<cdot>n)) = \<bottom>" |
"vPlus\<cdot>(VNat\<cdot>(up\<cdot>n))\<cdot>\<bottom> = \<bottom>" |
"vPlus\<cdot>(VNat\<cdot>(up\<cdot>n))\<cdot>(VFun\<cdot>f) = Wrong" |
"vPlus\<cdot>(VFun\<cdot>f)\<cdot>(VFun\<cdot>f') = Wrong" |
"vPlus\<cdot>(VFun\<cdot>f)\<cdot>(VNat\<cdot>(up\<cdot>n)) = Wrong" |
"vPlus\<cdot>Wrong\<cdot>(VFun\<cdot>f) = Wrong" |
"vPlus\<cdot>Wrong\<cdot>(VNat\<cdot>(up\<cdot>n)) = Wrong" |
"vPlus\<cdot>(VNat\<cdot>(up\<cdot>n))\<cdot>Wrong = Wrong" |
"vPlus\<cdot>(VFun\<cdot>f)\<cdot>Wrong = Wrong" |
"vPlus\<cdot>(VBool\<cdot>(up\<cdot>b))\<cdot>(VBool\<cdot>(up\<cdot>b)) = Wrong"

lemma [simp]: "vPlus\<cdot>\<bottom>\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma [simp]: "vPlus\<cdot>\<bottom>\<cdot>(VNat\<cdot>n) = \<bottom>"
apply fixrec_simp
done

lemma [simp]: "vPlus\<cdot>(VNat\<cdot>n)\<cdot>\<bottom> = \<bottom>"
apply (case_tac n)
apply fixrec_simp
apply fixrec_simp
done
(*>*)
fun lamM :: "lam \<Rightarrow> V cenv \<rightarrow> V" where
"lamM (LNat n) = (\<Lambda> \<sigma>. VNat\<cdot>(up\<cdot>n))" |
"lamM (LLam n _ e) = (\<Lambda> \<sigma>. (\<Delta> x. lamM e\<cdot>(sfun_upd\<cdot>\<sigma>\<cdot>n\<cdot>x)))" |
"lamM (LApp e1 e2) = (\<Lambda> \<sigma>. (lamM e1\<cdot>\<sigma>)\<bullet>(lamM e2\<cdot>\<sigma>))" |
"lamM (LPlus e1 e2) = (\<Lambda> \<sigma>. vPlus\<cdot>(lamM e1\<cdot>\<sigma>)\<cdot>(lamM e2\<cdot>\<sigma>))" |
"lamM (LVar n) = (\<Lambda> \<sigma>. slookup n\<cdot>\<sigma>)"|
"lamM (LFix _ f) = (\<Lambda> \<sigma>. vFix\<cdot>(lamM f\<cdot>\<sigma>))" |
"lamM (LBool b) = (\<Lambda> \<sigma>. VBool\<cdot>(up\<cdot>b))"
(*<*)
(* define compatibility between environments and \<sigma> *)

definition env_compat :: "ty_env \<Rightarrow> V cenv \<Rightarrow> bool" where
"env_compat tys \<sigma> \<equiv> \<forall> n. (slookup n\<cdot>\<sigma>) \<in> (tyM (tys n))"

lemma [simp] : "pointed t \<Longrightarrow> \<bottom> \<in> tyM t"
apply (rule ideal_bottom)
apply (erule pointy_ideal)
done

lemma [simp] : "pointed t \<Longrightarrow> adm (\<lambda> x. x \<in> tyM t)"
apply (rule ideal_adm)
apply (erule pointy_ideal)
done

lemma fixy: "\<lbrakk>\<forall> v \<in> P. f\<cdot>v \<in> P; adm (\<lambda> x. x \<in> P); \<bottom> \<in> P\<rbrakk> \<Longrightarrow> fix\<cdot>f \<in> P"
apply (rule fix_ind)
by simp+

lemma [simp] : "\<exists> x. x \<in> tyM t "
apply (induct t)
apply (force simp: VNat_set_def)
apply (simp add: VFun_set_def)
apply (erule exE)
apply (erule exE)
apply (rule_tac x="\<Delta> a. xa" in exI)
apply (rule ballI)
apply simp
apply (force simp: VBool_set_def)
done

lemma [simp] : "Wrong \<notin> tyM t"
apply (induct t)
apply (force simp: VNat_set_def)
apply (simp add: VFun_set_def)
apply (simp add: VBool_set_def)
done

(*<*)
lemma VNat_erule : "\<lbrakk>lamM l\<cdot>\<sigma> \<in> [\<nat>]; \<And> n. lamM l\<cdot>\<sigma> = VNat\<cdot>(up\<cdot>n) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
apply (case_tac "lamM l\<cdot>\<sigma>")
apply (force simp: VNat_set_def)
apply (case_tac u)
apply (force simp: VNat_set_def)
apply simp
apply (force simp: VFun_set_def VNat_set_def VBool_set_def)+
done

lemma VFun_erule : "\<lbrakk>lamM l\<cdot>\<sigma> \<in> (tyM t1 [\<rightarrow>] tyM t2); lamM l\<cdot>\<sigma> \<noteq> \<bottom>; \<And> f. lamM l\<cdot>\<sigma> = VFun\<cdot>f \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
apply (case_tac "lamM l\<cdot>\<sigma>")
apply simp
apply (case_tac u, simp)
apply (auto simp: VFun_set_def)
apply (case_tac u, simp)
apply (force simp: VFun_set_def)
done
(*>*) (*>*)


lemma "\<lbrakk>lam_ty tys l t; env_compat tys \<sigma>\<rbrakk> \<Longrightarrow> lamM l\<cdot>\<sigma> \<in> (tyM t)"
(*<*)
apply (induct arbitrary: \<sigma> rule: lam_ty.induct)
apply (force simp: env_compat_def)
apply simp
apply (subgoal_tac "lamM l1\<cdot>\<sigma> \<in> [\<nat>]")
apply (subgoal_tac "lamM l2\<cdot>\<sigma> \<in> [\<nat>]")
apply (erule VNat_erule)
apply (erule VNat_erule)
apply (simp add: VNat_set_def, assumption+)
apply (force simp: VFun_set_def)
apply (simp add: VNat_set_def)
apply (simp add: VFun_set_def env_compat_def)
apply simp
apply (subgoal_tac "lamM l1\<cdot>\<sigma> \<in> tyM t1 [\<rightarrow>] tyM t1")
apply (case_tac "lamM l1\<cdot>\<sigma> = \<bottom>")
apply simp
apply (erule VFun_erule, simp+)
apply (rule fixy)
apply (force simp: VFun_set_def, simp+)
done

end
(*>*)
(*>*)