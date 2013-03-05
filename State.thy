(*<*)theory State
imports HOLCF Cenv Ideal CER
"~~/src/HOL/HOLCF/Library/Nat_Discrete"
"~~/src/HOL/HOLCF/Library/Bool_Discrete"
 begin(*>*)

section {* Monadic Semantics *}

text {* As our final example, we will consider adding a store to our simply-typed
        lambda calculus and show that we can, without great difficulty, adjust our theory
        to show type soundness of the monadic semantics. 

        Here, we return the classic approach of Moggi (ref) and represent our effectful
        computation with a monad. We then extend our language of types to have
        an explicity internal monad for IO, since our primary concern is modelling
        languages such as Haskell or Habit that use monads in the object language
        to separate out effectful code from pure code. 

        We also, to our term language, add return and bind as well as the get and put
        operations for our store. In this case, we are presuming a store that holds
        a single item for simplicity but this can be extended to a store with many
        values and references as well. *}

datatype ty = TyNat | TyFun ty ty | TyM ty | TyUnit

datatype lam = LVar nat | LApp lam lam | LLam nat ty lam | LNat nat
             | LPlus lam lam | LFix ty lam | LGet | LPut lam | LBind lam lam
             | LReturn lam

type_synonym ty_env = "nat \<Rightarrow> ty"

inductive lam_ty :: "ty_env \<Rightarrow> lam \<Rightarrow> ty \<Rightarrow> bool" where
  LVar : "\<lbrakk>tys n = ty\<rbrakk> \<Longrightarrow> lam_ty tys (LVar n) ty" |
  LPlus : "\<lbrakk>lam_ty tys l1 TyNat; lam_ty tys l2 TyNat\<rbrakk> \<Longrightarrow> lam_ty tys (LPlus l1 l2) TyNat" |
  LApp  : "\<lbrakk>lam_ty tys l1 (TyFun t1 t2); lam_ty tys l2 t1\<rbrakk> \<Longrightarrow> lam_ty tys (LApp l1 l2) t2" |
  LNat  : "lam_ty tys (LNat n) TyNat" |
  LLam  : "\<lbrakk>lam_ty (tys (n :=t1)) l1 t2\<rbrakk> \<Longrightarrow> lam_ty tys (LLam n t1 l1) (TyFun t1 t2)" |
  LFix  : "\<lbrakk>lam_ty tys l1 (TyFun t1 t1)\<rbrakk> \<Longrightarrow> lam_ty tys (LFix t1 l1) t1" |
  LGet  : "lam_ty tys LGet (TyM TyNat)" |
  LPut  : "\<lbrakk>lam_ty tys l TyNat\<rbrakk> \<Longrightarrow> lam_ty tys (LPut l) (TyM TyUnit)" |
  LBind : "\<lbrakk>lam_ty tys l2 (TyFun t1 (TyM t2)); lam_ty tys l1 (TyM t1)\<rbrakk> \<Longrightarrow>
              lam_ty tys (LBind l1 l2) (TyM t2)" |
  LReturn : "\<lbrakk>lam_ty tys l t\<rbrakk> \<Longrightarrow> lam_ty tys (LReturn l) (TyM t)"

text {* On the domain theoretic side, we also introduce a new type synonym *}

type_synonym 'a State = "nat \<rightarrow> ('a \<otimes> (nat u))"

text {* Where, in this case, we are using the strict product instead of the ordinary
        Cartesian product because it more naturally fits the intended meaning of the 
        monad. We can also define the basic combinators for this monad as follows. *}

definition sReturn :: "'a \<rightarrow> 'a State" where
"sReturn \<equiv> \<Lambda> x. (\<Lambda> n. (:x, up\<cdot>n:))"

definition sJoin :: "('a State) State \<rightarrow> 'a State" where
"sJoin \<equiv> (\<Lambda> ss n. (\<Lambda> (:f,up\<cdot>n':). f\<cdot>n')\<cdot>(ss\<cdot>n))"

definition sBind :: "('a State) \<rightarrow> ('a \<rightarrow> 'b State) \<rightarrow> 'b State" where
"sBind \<equiv> (\<Lambda> s f n. (\<Lambda> (: a , up\<cdot>n' :). (f\<cdot>a)\<cdot>n')\<cdot>(s\<cdot>n))"

definition sMap :: "('a \<rightarrow> 'b) \<rightarrow> (('a State) \<rightarrow> ('b State))" where
"sMap \<equiv> (\<Lambda> f as n. (\<Lambda> (: a, up\<cdot>n' :). (:f\<cdot>a,up\<cdot>n':))\<cdot>(as\<cdot>n))"

text {* and we can prove laws we would expect to hold for this semantics if we've actually
        defined the monad correctly. *}

(*<*)
(* whhhhhy did I have to prove this what the heck is going on? *)
lemma [simp]: "x \<noteq> \<bottom> \<Longrightarrow> (\<Lambda> (n\<Colon>nat). (:x, up\<cdot>n:)) \<noteq> \<bottom>"
proof
assume 0: "x \<noteq> \<bottom>"
assume 1: "(\<Lambda> (n :: nat). (:x, up\<cdot>n:)) = \<bottom>"
then have "(\<Lambda> n. (:x, up\<cdot>n:))\<cdot>(0 :: nat) = \<bottom>\<cdot>(0 :: nat)" by simp
then have "(:x, up\<cdot>(0 :: nat):) = \<bottom>" by simp
thus False using 0 by simp
qed(*>*)

lemma [simp]: "sJoin\<cdot>((sMap\<cdot>sReturn)\<cdot>x) = x"(*<*)
apply (simp add: sJoin_def sMap_def sReturn_def)
apply (rule cfun_eqI)
apply simp
apply (subst Rep_cfun_inverse)
apply (subst Rep_cfun_inverse)
apply (case_tac "x\<cdot>xa")
apply simp
apply simp
apply (case_tac y)
apply simp
apply simp
done(*>*)

(*<*)
lemma [simp]: "sBind\<cdot>\<bottom>\<cdot>x = \<bottom>"
apply (simp add: sBind_def)
done(*>*)

(*<*)
lemma [simp] : "a \<noteq> \<bottom> \<Longrightarrow> sBind\<cdot>(sReturn\<cdot>a)\<cdot>f = f\<cdot>a"
apply (simp add: sBind_def sReturn_def)
apply (subst Rep_cfun_inverse)
apply simp
done(*>*)

lemma [simp] : "sJoin\<cdot>(sReturn\<cdot>x) = x"(*<*)
apply (simp add: sJoin_def sReturn_def)
apply (subst Rep_cfun_inverse)
apply (subst Rep_cfun_inverse)
apply (case_tac "x = \<bottom>")
apply simp
apply simp
apply (rule eta_cfun)
done (*>*)

text {* Our domain is similar to our previous examples, except that our function space has been modified
        as we are working in the Kleisli category that corresponds to the monad we are working with. *}

domain V = VNat (fromNat :: "nat u") | VFun (lazy "(V \<rightarrow> (V State))") | VUnit | 
         Wrong

text {* Given this definition for $V$, we can write our constants for the theory as we've done previously.
        The only truly new ones are the get and state operators. *}

definition sGet :: "V State"(*<*) where
"sGet \<equiv> (\<Lambda> s. (: VNat\<cdot>(up\<cdot>s), up\<cdot>s :))"(*>*)

fixrec sPut :: "V \<rightarrow> V State"(*<*) where
"sPut\<cdot>(VNat\<cdot>(up\<cdot>n))\<cdot>n' = (: VUnit, up\<cdot>n :)" |
"sPut\<cdot>\<bottom>\<cdot>n' = \<bottom>" |
"sPut\<cdot>VUnit\<cdot>n' = (: Wrong, up\<cdot>n' :)" |
"sPut\<cdot>(VFun\<cdot>f)\<cdot>n' = (: Wrong, up\<cdot>n' :)" (*>*)

(*<*)
typedef (open) ideal = "{S :: V set. ideal S}"
proof
   show "{\<bottom>} \<in> ?ideal"
     unfolding ideal_def by simp
qed

lemma Rep_ideal': "ideal (Rep_ideal S)"
  using Rep_ideal by simp

lemma Abs_ideal_inverse': "ideal S \<Longrightarrow> Rep_ideal (Abs_ideal S) = S"
  using Abs_ideal_inverse by simp

instantiation ideal :: cer 
begin

definition 
  "rel i S T \<equiv> (\<forall> z. V_take i\<cdot>z \<in> Rep_ideal S \<longleftrightarrow> V_take i\<cdot>z \<in> Rep_ideal T)"
instance
apply (default, unfold rel_ideal_def)
apply simp
apply simp
apply simp
apply (simp add: ideal_bottom [OF Rep_ideal'])
apply (rule allI)
apply (drule_tac x="V_take i\<cdot>z" in spec)
apply (simp add: V.take_take min_def)
apply (simp add: Rep_ideal_inject [symmetric])
apply (rule set_eqI, rename_tac z)
apply (subgoal_tac "(\<Squnion>i. V_take i\<cdot>z) \<in> Rep_ideal x \<longleftrightarrow> (\<Squnion>i. V_take i\<cdot>z) \<in> Rep_ideal y")
apply (simp add: V.reach)
apply (simp add: ideal_lub_iff [OF Rep_ideal'])
done
end

instance ideal :: complete_cer
(*<*)
proof
  fix S :: "nat \<Rightarrow> ideal"
  assume "\<forall>i j. i \<le> j \<longrightarrow> rel i (S i) (S j)"
  hence *: "\<And>i j x. i \<le> j \<Longrightarrow>
    V_take i\<cdot>x \<in> Rep_ideal (S i) \<longleftrightarrow> V_take i\<cdot>x \<in> Rep_ideal (S j)"
    unfolding rel_ideal_def by simp
  have ideal_T: "ideal {x. \<forall>i. V_take i\<cdot>x \<in> Rep_ideal (S i)}"
    apply (rule idealI)
    apply (simp add: ideal_bottom [OF Rep_ideal'])
    apply clarify
    apply (rule ideal_downward [OF Rep_ideal'])
    apply (erule monofun_cfun_arg)
    apply simp
    apply simp
    apply (rule adm_all)
    apply (rule adm_subst, simp)
    apply (rule ideal_adm [OF Rep_ideal'])
    done
  let ?T = "Abs_ideal {x. \<forall>i. V_take i\<cdot>x \<in> Rep_ideal (S i)}"
  have "\<forall>i. rel i ?T (S i)"
    unfolding rel_ideal_def
    apply (subst Abs_ideal_inverse' [OF ideal_T])
    apply (simp, safe)
    apply (drule_tac x=i in spec, simp add: V.take_take)
    apply (rename_tac i z j)
    apply (simp add: V.take_take min_def, safe)
    apply (subst *, assumption)
    apply (rule ideal_downward [OF Rep_ideal'])
    apply (rule monofun_cfun_fun)
    apply (erule chain_mono [OF V.chain_take])
    apply assumption
    apply (subst * [symmetric])
    apply simp
    apply assumption
    done
  thus "\<exists>z. \<forall>i. rel i z (S i)" ..
qed

lemma ideal_image_VNat:
  assumes S: "ideal S"
  shows "ideal ((\<lambda>x. VNat\<cdot>x) ` S)"
apply (rule ideal_image [OF _ _ S])
apply (case_tac x, simp_all add: flat_eq)
apply (rule_tac x="fromNat" in exI)
apply (rule allI)
apply (case_tac "x = \<bottom>")
apply simp
apply simp
done

definition VUnit_ideal :: ideal ("[1]") where
"[1] = Abs_ideal {\<bottom>, VUnit}"

lemma Rep_VUnit_ideal : "Rep_ideal [1] = {\<bottom>, VUnit}"
unfolding VUnit_ideal_def
apply (rule Abs_ideal_inverse')
apply (rule idealI)
apply simp
apply simp
apply (erule disjE)
apply simp
apply (case_tac x, simp_all)
done

definition
  VNat_ideal :: ideal ("[\<nat>]")
where
  "[\<nat>] = Abs_ideal (range (\<lambda>x. VNat\<cdot>x))"

lemma Rep_VNat_ideal: "Rep_ideal [\<nat>] = range (\<lambda>x. VNat\<cdot>x)"
unfolding VNat_ideal_def
apply (rule Abs_ideal_inverse')
apply (rule ideal_image)
apply (case_tac x, simp_all)
apply (rule_tac x="\<Lambda>(VNat\<cdot>x). x" in exI)
apply (rule allI, case_tac "x = \<bottom>", simp, simp)
apply (simp add: idealI)
done

fixrec vApply :: "V \<rightarrow> V \<rightarrow> V State" where
"n \<noteq> \<bottom> \<Longrightarrow> vApply\<cdot>(VNat\<cdot>n)\<cdot>x = sReturn\<cdot>Wrong" |
"vApply\<cdot>VUnit\<cdot>x = sReturn\<cdot>Wrong" |
"vApply\<cdot>(VFun\<cdot>f)\<cdot>x = f\<cdot>x" |
"vApply\<cdot>Wrong\<cdot>x = sReturn\<cdot>Wrong"

lemma [simp]: "vApply\<cdot>\<bottom>\<cdot>x = \<bottom>"
apply fixrec_simp
done

abbreviation vapp :: " V \<Rightarrow> V \<Rightarrow> V State" (infixl "\<bullet>" 900) where
"f\<bullet>x \<equiv> vApply\<cdot>f\<cdot>x"

lemma [simp] : "sfst\<cdot>(sReturn\<cdot>x\<cdot>n) = x"
apply (simp add: sReturn_def)
done

definition VFun_ideal :: "ideal \<Rightarrow> ideal \<Rightarrow> ideal" (infix "[\<rightarrow>]" 55)
where
     "S [\<rightarrow>] T = Abs_ideal {f. \<forall> x \<in>(Rep_ideal S). \<forall> n. (sfst\<cdot>((f\<bullet>x)\<cdot>n)) \<in> Rep_ideal T}"

lemma less_apply: "f \<sqsubseteq> g \<Longrightarrow> f\<bullet>x \<sqsubseteq> g\<bullet>x"
apply (cases f, simp_all)
apply (cases g, simp_all)
apply (cases g, simp_all)
apply (rule monofun_cfun_fun)
apply simp
apply (cases g, simp_all)
apply (cases g, simp_all)
done

lemma Rep_VFun_ideal: 
   "Rep_ideal (S [\<rightarrow>] T) = {f. \<forall> x \<in>(Rep_ideal S). \<forall> n. (sfst\<cdot>((f\<bullet>x)\<cdot>n)) \<in> Rep_ideal T}"
unfolding VFun_ideal_def
apply (rule Abs_ideal_inverse')
apply (rule idealI)
apply clarsimp
apply (rule ideal_bottom [OF Rep_ideal'])
apply clarsimp thm ideal_downward 
apply (subst ideal_downward)
apply (rule Rep_ideal')
apply (subgoal_tac "sfst\<cdot>((x \<bullet> xa)\<cdot>n) \<sqsubseteq> sfst\<cdot>((y \<bullet> xa)\<cdot>n)")
apply simp
apply (rule monofun_cfun_arg)
apply (rule monofun_cfun_fun)
apply (rule less_apply, assumption)
apply simp
apply simp
apply clarsimp
apply (rule adm_ball)
apply (rule adm_all)
apply (rule adm_subst)
back
apply simp
apply (rule ideal_adm)
apply (rule Rep_ideal')
done
(*>*)
fun tyM :: "ty \<Rightarrow> ideal" where
"tyM TyNat = [\<nat>]" |
"tyM TyUnit = [1]" |
"tyM (TyM t) = tyM t" |
"tyM (TyFun t t') = (tyM t) [\<rightarrow>] (tyM t')"

fixrec vPlus :: "V \<rightarrow> V \<rightarrow> V" where
"vPlus\<cdot>(VNat\<cdot>(up\<cdot>n))\<cdot>(VNat\<cdot>(up\<cdot>n')) = VNat\<cdot>(up\<cdot>(n + n'))" |
"vPlus\<cdot>\<bottom>\<cdot>(VNat\<cdot>(up\<cdot>n)) = \<bottom>" |
"vPlus\<cdot>(VNat\<cdot>(up\<cdot>n))\<cdot>\<bottom> = \<bottom>" |
"vPlus\<cdot>\<bottom>\<cdot>\<bottom> = \<bottom>" |
"vPlus\<cdot>(VFun\<cdot>f)\<cdot>(VFun\<cdot>f) = Wrong" |
"vPlus\<cdot>(VFun\<cdot>f)\<cdot>(VNat\<cdot>(up\<cdot>n)) = Wrong" |
"vPlus\<cdot>(VFun\<cdot>f)\<cdot>VUnit = Wrong" |
"vPlus\<cdot>(VFun\<cdot>f)\<cdot>Wrong = Wrong" |
"vPlus\<cdot>(VNat\<cdot>(up\<cdot>n))\<cdot>(VFun\<cdot>f) = Wrong" |
"vPlus\<cdot>Wrong\<cdot>(VFun\<cdot>f) = Wrong" |
"vPlus\<cdot>VUnit\<cdot>(VFun\<cdot>f) = Wrong" |
"vPlus\<cdot>VUnit\<cdot>(VNat\<cdot>(up\<cdot>n)) = Wrong" |
"vPlus\<cdot>VUnit\<cdot>Wrong = Wrong"

fixrec vFix :: "V \<rightarrow> V State" where
"vFix\<cdot>(VFun\<cdot>f) = fix\<cdot>(\<Lambda> y. sBind\<cdot>y\<cdot>f)" |
"vFix\<cdot>\<bottom> = \<bottom>" |
"vFix\<cdot>VUnit = sReturn\<cdot>Wrong" |
"vFix\<cdot>(VNat\<cdot>(up\<cdot>n)) = sReturn\<cdot>Wrong"

abbreviation vLam :: "(V \<Rightarrow> V State) \<Rightarrow> V" (binder "\<Delta> " 10) where
"vLam f \<equiv> VFun\<cdot>(\<Lambda> x. f x)"

definition eApp :: "V State \<rightarrow> V State \<rightarrow> V State" where
"eApp = (\<Lambda> f a. sBind\<cdot>a\<cdot>(\<Lambda> x. sBind\<cdot>f\<cdot>(\<Lambda> y. y\<bullet>x)))" (*>*)

fun lamM :: "lam \<Rightarrow> V cenv \<rightarrow> V State" where
"lamM (LNat n) = (\<Lambda> \<sigma>. sReturn\<cdot>(VNat\<cdot>(up\<cdot>n)))" |
"lamM (LLam n _ e) = (\<Lambda> \<sigma>. sReturn\<cdot>(\<Delta> x. lamM e\<cdot>(sfun_upd\<cdot>\<sigma>\<cdot>n\<cdot>x)))" |
"lamM (LApp e1 e2) = (\<Lambda> \<sigma>. eApp\<cdot>(lamM e1\<cdot>\<sigma>)\<cdot>(lamM e2\<cdot>\<sigma>))" |
"lamM (LVar n) = (\<Lambda> \<sigma>. sReturn\<cdot>(slookup n\<cdot>\<sigma>))"|
"lamM (LFix _ f) = (\<Lambda> \<sigma>. sBind\<cdot>(lamM f\<cdot>\<sigma>)\<cdot>vFix)" |
"lamM LGet = (\<Lambda> \<sigma>. sGet)"|
"lamM (LPut e) = (\<Lambda> \<sigma>. sBind\<cdot>(lamM e\<cdot>\<sigma>)\<cdot>sPut)" |
"lamM (LPlus e1 e2) = (\<Lambda> \<sigma>. sBind\<cdot>(lamM e1\<cdot>\<sigma>)\<cdot>(\<Lambda> v. sBind\<cdot>(lamM e2\<cdot>\<sigma>)\<cdot>(\<Lambda> v'. sReturn\<cdot>(vPlus\<cdot>v\<cdot>v'))))" |
"lamM (LBind e1 e2) = (\<Lambda> \<sigma>. eApp\<cdot>(lamM e2\<cdot>\<sigma>)\<cdot>(lamM e1\<cdot>\<sigma>))" |
"lamM (LReturn e) = (\<Lambda> \<sigma>. lamM e\<cdot>\<sigma>)"

text {* As an example of a simple property we can verify, consider the
        sequencing operator that runs two effectful computations in sequence: a simple specialization of the bind operator. *}

definition LSeq where
"LSeq t l1 l2 \<equiv> LBind l1 (LLam 0 t l2)"

text {* We can show, then, that the sequence of two ``get''s is the same
        as doing just one. *}

lemma "lamM (LSeq t LGet LGet) = lamM LGet" (*<*)
apply (rule cfun_eqI)
apply (rule cfun_eqI)
apply (simp add: eApp_def LSeq_def)
apply (simp add: sBind_def sReturn_def sGet_def)
done

lemma [simp]: "Rep_ideal x \<noteq> {}"
apply (subgoal_tac "\<bottom> \<in> Rep_ideal x")
apply blast
apply (rule ideal_bottom)
apply (rule Rep_ideal')
done

lemma [simp] : "Wrong \<notin> (Rep_ideal (tyM t))"
apply (induct t)
apply (force simp: Rep_VNat_ideal)
apply (simp add: Rep_VFun_ideal)
apply simp
apply (simp add: Rep_VUnit_ideal)
done

lemma [simp] : "\<bottom> \<in> (Rep_ideal (tyM t))"
apply (rule ideal_bottom)
apply (rule Rep_ideal')
done (*>*)
(*<*)
definition env_compat :: "ty_env \<Rightarrow> V cenv \<Rightarrow> bool" where
"env_compat tys \<sigma> \<equiv> \<forall> n. (slookup n\<cdot>\<sigma>) \<in> (Rep_ideal (tyM (tys n)))"(*>*)

(*<*)
lemma "\<lbrakk>lamM l\<cdot>\<sigma>\<cdot>n = (:VNat\<cdot>(up\<cdot>a),up\<cdot>b:)\<rbrakk> \<Longrightarrow> (sBind\<cdot>(lamM l\<cdot>\<sigma>)\<cdot>sPut\<cdot>n) = (:VUnit,up\<cdot>a:)"
apply (simp add: sBind_def)
done

lemma "sfst\<cdot>(:VFun\<cdot>f,up\<cdot>n:) \<notin> Rep_ideal ([\<nat>])"
apply (force simp: Rep_VNat_ideal)
done

lemma [simp]: "vPlus\<cdot>\<bottom>\<cdot>a = \<bottom>"
apply (case_tac a)
apply simp
apply simp_all
apply (case_tac u)
apply simp
apply simp
apply fixrec_simp
apply fixrec_simp
apply fixrec_simp
done

lemma [simp]: "vPlus\<cdot>a\<cdot>\<bottom> = \<bottom>"
apply (case_tac a)
apply simp
apply simp
apply (case_tac u)
apply simp
apply simp
apply fixrec_simp+
done

declare Rep_cfun_inverse [simp]

lemma VFun_drule : "\<lbrakk>sfst\<cdot>(lamM l\<cdot>\<sigma>\<cdot>n) \<in> (Rep_ideal ((tyM t1) [\<rightarrow>] (tyM t2)))\<rbrakk> \<Longrightarrow> ((lamM l\<cdot>\<sigma>\<cdot>n) = \<bottom>) \<or> (\<exists> f n'. (lamM l\<cdot>\<sigma>\<cdot>n) = (: VFun\<cdot>f, up\<cdot>n':))"
apply (case_tac "lamM l\<cdot>\<sigma>\<cdot>n")
apply simp
apply (case_tac x)
apply simp
apply simp
apply (case_tac u)
apply simp
apply simp
apply (force simp: Rep_VFun_ideal)
apply (case_tac y)
apply simp
apply force
apply (force simp: Rep_VFun_ideal)
apply (force simp: Rep_VFun_ideal)
done

lemma VNat_drule : "\<lbrakk>sfst\<cdot>(lamM l\<cdot>\<sigma>\<cdot>n) \<in> (Rep_ideal [\<nat>])\<rbrakk> \<Longrightarrow> ((lamM l\<cdot>\<sigma>\<cdot>n) = \<bottom>) \<or> (\<exists> a n'. ((lamM l\<cdot>\<sigma>\<cdot>n) = (: VNat\<cdot>(up\<cdot>a), up\<cdot>n':)))"
apply (case_tac "lamM l\<cdot>\<sigma>\<cdot>n")
apply simp
apply (case_tac x)
apply simp
apply (case_tac u)
apply simp
apply (case_tac y)
apply simp
apply simp
apply (force simp: Rep_VNat_ideal)+
done


lemma [simp] : "fup\<cdot>\<bottom>\<cdot>x = \<bottom>"
apply (cases x)
by simp+(*>*)
(*<*)
lemma vFixy : "\<lbrakk> lamM l1\<cdot>\<sigma>\<cdot>n = (:x, y:); x \<noteq> \<bottom>; y \<noteq> \<bottom>; sfst\<cdot>(lamM l1\<cdot>\<sigma>\<cdot>n) \<in> Rep_ideal (tyM t1 [\<rightarrow>] tyM t1) \<rbrakk> \<Longrightarrow> sfst\<cdot>(fup\<cdot>(vFix\<cdot>x)\<cdot>y) \<in> Rep_ideal (tyM t1)"
apply simp
apply (case_tac x)
apply simp
apply (force simp: Rep_VFun_ideal)
defer
apply (force simp: Rep_VFun_ideal)
apply (force simp: Rep_VFun_ideal)
apply (simp add: sBind_def)
apply (rule fix_ind)
apply (rule adm_subst)
back
apply simp
apply (rule ideal_adm)
apply (rule Rep_ideal')
apply simp
apply simp
apply (case_tac y)
apply simp
apply simp
apply (case_tac "xa\<cdot>xaa")
apply simp
apply simp
apply (simp add: Rep_VFun_ideal)
apply (drule_tac x="xb" in bspec)
apply simp
apply (case_tac ya)
apply simp
apply simp
done (*>*)

text {* Now, we can prove our "don't go wrong" theorem for this calculus without much more difficulty. The theorem statement we need is slightly more complicated, though, because we need to "extract" the value from the monadic computation and then show that the result is contained within the type of the term. This does complicate the proof somewhat, but it's still essentially just repeated simplification and cases. *}

lemma "\<lbrakk>lam_ty tys l t; env_compat tys \<sigma>\<rbrakk> \<Longrightarrow> sfst\<cdot>(lamM l\<cdot>\<sigma>\<cdot>n) \<in> (Rep_ideal (tyM t))"
(*<*)
apply (induct arbitrary: \<sigma> n rule: lam_ty.induct)
(* var case *)
apply (force simp: env_compat_def)
(* plus case *)
apply (subgoal_tac "sfst\<cdot>(lamM l1\<cdot>\<sigma>\<cdot>n) \<in> Rep_ideal [\<nat>]")
apply (drule VNat_drule)
apply (erule disjE)
apply (simp add: sBind_def Rep_VNat_ideal)
apply (erule exE)
apply (erule exE)
apply (subgoal_tac "sfst\<cdot>(lamM l2\<cdot>\<sigma>\<cdot>n') \<in> Rep_ideal [\<nat>]")
apply (drule VNat_drule)
apply (erule disjE)
apply (simp add: sBind_def Rep_VNat_ideal)
apply (erule exE)
apply (erule exE)
apply (simp add: sBind_def Rep_VNat_ideal)
apply simp
apply simp
(* app case *)
apply (simp add: eApp_def sBind_def)
apply (case_tac "lamM l2\<cdot>\<sigma>\<cdot>n")
apply simp
apply simp
apply (case_tac y)
apply simp
apply simp
apply (case_tac "lamM l1\<cdot>\<sigma>\<cdot>xa")
apply simp
apply simp
apply (simp add: Rep_VFun_ideal)
apply (subgoal_tac "sfst\<cdot>(lamM l2\<cdot>\<sigma>\<cdot>n) \<in> Rep_ideal (tyM t1)")
apply simp
apply (subgoal_tac "\<forall>x\<in>Rep_ideal (tyM t1). \<forall>na. sfst\<cdot>((sfst\<cdot>(lamM l1\<cdot>\<sigma>\<cdot>xa) \<bullet> x)\<cdot>na) \<in> Rep_ideal (tyM t2)")
apply (drule_tac x="x" in bspec)
apply simp
apply simp
apply (case_tac ya)
apply simp
apply simp
apply simp
apply auto
apply (drule_tac x=\<sigma> in meta_spec)
apply (drule_tac x=xa in meta_spec)
apply simp
apply (drule_tac x="\<sigma>" in meta_spec)
back
apply (drule_tac x="n" in meta_spec)
apply simp
(* LNat case *)
apply (force simp: Rep_VNat_ideal)
(* Lam case *)
apply (simp add: Rep_VFun_ideal env_compat_def)
(* Fix case *)
apply (case_tac "lamM l1\<cdot>\<sigma>\<cdot>n")
apply (simp add: sBind_def)
apply (simp add: sBind_def)
apply (erule vFixy)
apply simp
apply simp
apply simp
(* LGet case *)
apply (simp add: Rep_VNat_ideal sGet_def)
(* LPut case *)
apply (subgoal_tac "sfst\<cdot>(lamM l\<cdot>\<sigma>\<cdot>n) \<in> Rep_ideal [\<nat>]")
apply (drule VNat_drule)
apply (erule disjE)
apply (simp add: Rep_VUnit_ideal sBind_def)
apply (force simp: Rep_VUnit_ideal sBind_def)
apply assumption

(* Bind case *)
apply (simp add: eApp_def sBind_def)
apply (case_tac "lamM l1\<cdot>\<sigma>\<cdot>n")
apply simp
apply simp
apply (case_tac y)
apply simp
apply simp
apply (case_tac "lamM l2\<cdot>\<sigma>\<cdot>xa")
apply simp
apply simp
apply (simp add: Rep_VFun_ideal)
apply (subgoal_tac "sfst\<cdot>(lamM l1\<cdot>\<sigma>\<cdot>n) \<in> Rep_ideal (tyM t1)")
apply simp
apply (subgoal_tac "\<forall>x\<in>Rep_ideal (tyM t1). \<forall>na. sfst\<cdot>((sfst\<cdot>(lamM l2\<cdot>\<sigma>\<cdot>xa) \<bullet> x)\<cdot>na) \<in> Rep_ideal (tyM t2)")
apply (drule_tac x="x" in bspec)
apply simp
apply simp
apply (case_tac ya)
apply simp
apply simp
apply simp
apply auto
apply (drule_tac x=\<sigma> in meta_spec)
apply (drule_tac x=xa in meta_spec)
apply simp
apply (drule_tac x="\<sigma>" in meta_spec)
back
apply (drule_tac x="n" in meta_spec)
apply simp
done

end
(*>*)