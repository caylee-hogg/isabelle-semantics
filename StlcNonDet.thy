theory StlcNonDet
imports HOLCF Cenv
"~~/src/HOL/HOLCF/Library/Nat_Discrete"
 begin

datatype ty = TyNat | TyFun ty ty

datatype lam = LVar nat | LApp lam lam | LAbs nat ty lam
             | LNat nat | LPlus lam lam | LChoice lam lam
(* just like our previous example except with the non-deterministic choice
   added into the language *)

domain V = VNat "nat u" | VFun "V \<rightarrow> (V)\<natural>" | Wrong

type_synonym ty_env = "nat \<Rightarrow> ty"

inductive lam_ty :: "ty_env \<Rightarrow> lam \<Rightarrow> ty \<Rightarrow> bool" where
  LVar : "\<lbrakk>tys n = ty\<rbrakk> \<Longrightarrow> lam_ty tys (LVar n) ty" |
  LPlus : "\<lbrakk>lam_ty tys l1 TyNat; lam_ty tys l2 TyNat\<rbrakk> \<Longrightarrow> lam_ty tys (LPlus l1 l2) TyNat" |
  LApp  :"\<lbrakk>lam_ty tys l1 (TyFun t1 t2); lam_ty tys l2 t1\<rbrakk> \<Longrightarrow> lam_ty tys (LApp l1 l2) t2" |
  LNat  : "lam_ty tys (LNat n) TyNat" |
  LLam  : "\<lbrakk>lam_ty (tys (n :=t1)) l1 t2\<rbrakk> \<Longrightarrow> lam_ty tys (LAbs n t1 l1) (TyFun t1 t2)" |
  LChoice : "\<lbrakk>lam_ty tys l t; lam_ty tys l' t\<rbrakk> \<Longrightarrow> lam_ty tys (LChoice l l') t"

fixrec vApply :: "V \<rightarrow> V \<rightarrow> (V)\<natural>" where
"n \<noteq> \<bottom> \<Longrightarrow> vApply\<cdot>(VNat\<cdot>n)\<cdot>x = {Wrong}\<natural>" |
"f \<noteq> \<bottom> \<Longrightarrow> vApply\<cdot>(VFun\<cdot>f)\<cdot>x = f\<cdot>x" |
"vApply\<cdot>Wrong\<cdot>x = {Wrong}\<natural>"

lemma [simp]: "vApply\<cdot>\<bottom>\<cdot>x = \<bottom>" 
apply fixrec_simp
done

fixrec vPlus :: "V \<rightarrow> V \<rightarrow> V"(*<*) where
"vPlus\<cdot>(VNat\<cdot>(up\<cdot>n))\<cdot>(VNat\<cdot>(up\<cdot>n')) = VNat\<cdot>(up\<cdot>(n+n'))" |
"f \<noteq> \<bottom> \<Longrightarrow> vPlus\<cdot>(VNat\<cdot>(up\<cdot>n))\<cdot>(VFun\<cdot>f) = Wrong" |
"f \<noteq> \<bottom> \<and> f' \<noteq> \<bottom> \<Longrightarrow> vPlus\<cdot>(VFun\<cdot>f)\<cdot>(VFun\<cdot>f') = Wrong" |
"f \<noteq> \<bottom> \<Longrightarrow> vPlus\<cdot>(VFun\<cdot>f)\<cdot>(VNat\<cdot>(up\<cdot>n)) = Wrong" |
"f \<noteq> \<bottom> \<Longrightarrow> vPlus\<cdot>Wrong\<cdot>(VFun\<cdot>f) = Wrong" |
"vPlus\<cdot>Wrong\<cdot>(VNat\<cdot>(up\<cdot>n)) = Wrong" |
"vPlus\<cdot>(VNat\<cdot>(up\<cdot>n))\<cdot>Wrong = Wrong" |
"f \<noteq> \<bottom> \<Longrightarrow> vPlus\<cdot>(VFun\<cdot>f)\<cdot>Wrong = Wrong" (*>*)

lemma [simp]: "vPlus\<cdot>(VNat\<cdot>(up\<cdot>n))\<cdot>\<bottom> = \<bottom>"
              "vPlus\<cdot>\<bottom>\<cdot>(VNat\<cdot>(up\<cdot>n)) = \<bottom>"
              "vPlus\<cdot>\<bottom>\<cdot>\<bottom> = \<bottom>"
apply fixrec_simp+
done

abbreviation vapp :: " V \<Rightarrow> V \<Rightarrow> (V)\<natural>" (infixl "\<bullet>" 900) where
"f\<bullet>x \<equiv> vApply\<cdot>f\<cdot>x"

abbreviation vLam :: "(V \<Rightarrow> (V)\<natural>) \<Rightarrow> V" (binder "\<Delta> " 10) where
"vLam f \<equiv> VFun\<cdot>(\<Lambda> x. f x)" 

definition natSet :: "V set" where
"natSet \<equiv> {VNat\<cdot>n | n. True}"

lemma [simp]: "\<bottom> \<in> natSet"
by (simp add: natSet_def)

lemma [simp]: "VNat\<cdot>(up\<cdot>n) \<in> natSet"
by (simp add: natSet_def)

definition pElem :: "('a :: bifinite) \<Rightarrow> ('a)\<natural> \<Rightarrow> bool" where
"pElem x xs = (convex_plus\<cdot>{x}\<natural>\<cdot>xs = xs)"

lemma "{y}\<natural> \<union>\<natural> \<bottom> \<sqsubseteq> \<bottom> \<Longrightarrow> y = \<bottom>" 



lemma "{y}\<natural> \<union>\<natural> \<bottom> = \<bottom> \<Longrightarrow> y = \<bottom>"
apply (subgoal_tac "{y}\<natural> \<union>\<natural> \<bottom> \<sqsubseteq> \<bottom>")
apply simp

lemma "pElem y {x}\<natural> \<Longrightarrow> y = x \<or> y = \<bottom>"
apply (simp add: pElem_def)
apply (subgoal_tac "{y, x}\<natural> \<sqsubseteq> {x}\<natural>")
apply (subgoal_tac "{x}\<natural> \<sqsubseteq> {y, x}\<natural>")
apply (case_tac "x=\<bottom>")
apply simp
apply (simp add: convex_pd_below_simps)

apply 
apply (simp add: convex_pd_below_simps)

apply (case_tac "x=\<bottom>")
apply simp
apply (case_tac "y=\<bottom>")
apply simp
apply simp

definition funSet :: "V set \<Rightarrow> V set \<Rightarrow> V set" where
"funSet A B \<equiv> {VFun\<cdot>f | f. (\<forall> x. x \<in> A \<longrightarrow> (\<forall> y. pElem y (f\<cdot>x) \<longrightarrow> y \<in> B))}"

lemma [simp]: "\<lbrakk> (\<forall> x. x \<in> A \<longrightarrow> (\<forall> y. pElem y (f\<cdot>x) \<longrightarrow> y \<in> B)) \<rbrakk> \<Longrightarrow> VFun\<cdot>f \<in> funSet A B"
apply (simp add: funSet_def)
done

lemma [simp]: "\<bottom> \<in> funSet A B"
apply (simp add: funSet_def pElem_def)

fun tyM :: "ty \<Rightarrow> (V set)" where
"tyM TyNat = natSet" |
"tyM (TyFun t1 t2) = funSet (tyM t1) (tyM t2)"

(* now here's where things get a bit different, because in order to model 
   this calculus we need to use powerdomains instead of simply returning
   elements of V.

   for this we use the convex powerdomain (V)\<natural>
*)
term "{\<bottom>}\<natural>"

fun lamM :: "lam \<Rightarrow> V cenv \<rightarrow> (V)\<natural>" where
"lamM (LNat n) = (\<Lambda> \<sigma>. {VNat\<cdot>(up\<cdot>n)}\<natural>)" |
"lamM (LAbs n _ e) = (\<Lambda> \<sigma>. {(\<Delta> x. lamM e\<cdot>(sfun_upd\<cdot>\<sigma>\<cdot>n\<cdot>x))}\<natural>)" |
"lamM (LChoice l l') = (\<Lambda> \<sigma>. convex_plus\<cdot>(lamM l\<cdot>\<sigma>)\<cdot>(lamM l'\<cdot>\<sigma>))" |
"lamM (LApp l l') = (\<Lambda> \<sigma>. (\<Union>\<natural> x\<in>(lamM l\<cdot>\<sigma>). \<Union>\<natural> y\<in>(lamM l'\<cdot>\<sigma>). x\<bullet>y))" |
"lamM (LPlus l l') = (\<Lambda> \<sigma>. (\<Union>\<natural> x\<in>(lamM l\<cdot>\<sigma>). \<Union>\<natural> y\<in>(lamM l'\<cdot>\<sigma>). {vPlus\<cdot>x\<cdot>y}\<natural>))" |
"lamM (LVar n) = (\<Lambda> \<sigma>. {slookup n\<cdot>\<sigma>}\<natural>)"

definition env_compat :: "ty_env \<Rightarrow> V cenv \<Rightarrow> bool" where
"env_compat tys \<sigma> \<equiv> \<forall> n. (slookup n\<cdot>\<sigma>) \<in> tyM (tys n)"

theorem "\<lbrakk>lam_ty tys l t; env_compat tys \<sigma>\<rbrakk> \<Longrightarrow> \<forall> y. pElem y (lamM l\<cdot>\<sigma>) \<longrightarrow> y \<in> (tyM t)"
apply (induct arbitrary: \<sigma> rule: lam_ty.induct)
apply simp
apply (rule allI)
apply (simp add: env_compat_def)
apply (simp add: pElem_def)