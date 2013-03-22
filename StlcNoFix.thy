theory StlcNoFix 
imports HOLCF Cenv
"~~/src/HOL/HOLCF/Library/Nat_Discrete"
 begin

datatype ty = TyNat | TyFun ty ty

datatype lam = LVar nat | LApp lam lam | LAbs nat ty lam | LNat nat
             | LPlus lam lam

domain V = VNat "nat u" | VFun "V \<rightarrow> V" | Wrong

type_synonym ty_env = "nat \<Rightarrow> ty"

inductive lam_ty :: "ty_env \<Rightarrow> lam \<Rightarrow> ty \<Rightarrow> bool" where
  LVar : "\<lbrakk>tys n = ty\<rbrakk> \<Longrightarrow> lam_ty tys (LVar n) ty" |
  LPlus : "\<lbrakk>lam_ty tys l1 TyNat; lam_ty tys l2 TyNat\<rbrakk> \<Longrightarrow> lam_ty tys (LPlus l1 l2) TyNat" |
  LApp  :"\<lbrakk>lam_ty tys l1 (TyFun t1 t2); lam_ty tys l2 t1\<rbrakk> \<Longrightarrow> lam_ty tys (LApp l1 l2) t2" |
  LNat  : "lam_ty tys (LNat n) TyNat" |
  LLam  : "\<lbrakk>lam_ty (tys (n :=t1)) l1 t2\<rbrakk> \<Longrightarrow> lam_ty tys (LAbs n t1 l1) (TyFun t1 t2)"

fixrec vApply :: "V \<rightarrow> V \<rightarrow> V" where
"n \<noteq> \<bottom> \<Longrightarrow> vApply\<cdot>(VNat\<cdot>n)\<cdot>x = Wrong" |
"f \<noteq> \<bottom> \<Longrightarrow> vApply\<cdot>(VFun\<cdot>f)\<cdot>x = f\<cdot>x" |
"vApply\<cdot>Wrong\<cdot>x = Wrong"

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

abbreviation vapp :: " V \<Rightarrow> V \<Rightarrow> V" (infixl "\<bullet>" 900) where
"f\<bullet>x \<equiv> vApply\<cdot>f\<cdot>x"

abbreviation vLam :: "(V \<Rightarrow> V) \<Rightarrow> V" (binder "\<Delta> " 10) where
"vLam f \<equiv> VFun\<cdot>(\<Lambda> x. f x)" 

definition natSet :: "V set" where
"natSet \<equiv> {VNat\<cdot>n | n. True}"

lemma [simp]: "\<bottom> \<in> natSet"
by (simp add: natSet_def)

lemma [simp]: "VNat\<cdot>(up\<cdot>n) \<in> natSet"
by (simp add: natSet_def)

definition funSet :: "V set \<Rightarrow> V set \<Rightarrow> V set" where
"funSet A B \<equiv> {VFun\<cdot>f | f. (\<forall> x. x \<in> A \<longrightarrow> (f\<cdot>x) \<in> B)}"

lemma [simp]: "\<lbrakk>(\<forall> x. x \<in> A \<longrightarrow> (f\<cdot>x) \<in> B)\<rbrakk> \<Longrightarrow> VFun\<cdot>f \<in> funSet A B"
apply (simp add: funSet_def)
done

fun tyM :: "ty \<Rightarrow> (V set)" where
"tyM TyNat = natSet" |
"tyM (TyFun t1 t2) = funSet (tyM t1) (tyM t2)"

fun lamM :: "lam \<Rightarrow> V cenv \<rightarrow> V" where
"lamM (LNat n) = (\<Lambda> \<sigma>. VNat\<cdot>(up\<cdot>n))" |
"lamM (LAbs n _ e) = (\<Lambda> \<sigma>. (\<Delta> x. lamM e\<cdot>(sfun_upd\<cdot>\<sigma>\<cdot>n\<cdot>x)))" |
"lamM (LApp e1 e2) = (\<Lambda> \<sigma>. (lamM e1\<cdot>\<sigma>)\<bullet>(lamM e2\<cdot>\<sigma>))" |
"lamM (LPlus e1 e2) = (\<Lambda> \<sigma>. vPlus\<cdot>(lamM e1\<cdot>\<sigma>)\<cdot>(lamM e2\<cdot>\<sigma>))" |
"lamM (LVar n) = (\<Lambda> \<sigma>. slookup n\<cdot>\<sigma>)"

definition env_compat :: "ty_env \<Rightarrow> V cenv \<Rightarrow> bool" where
"env_compat tys \<sigma> \<equiv> \<forall> n. (slookup n\<cdot>\<sigma>) \<in> tyM (tys n)"

lemma natSetE : "\<lbrakk>d \<in> natSet ; \<And> n. d = VNat\<cdot>(up\<cdot>n) \<Longrightarrow> P; d = \<bottom> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" 
apply (simp add: natSet_def)
apply (erule exE)
apply (case_tac n)
apply simp
apply simp
done

lemma funSetE : "\<lbrakk>d \<in> funSet A B; \<And> f. \<lbrakk>d = VFun\<cdot>f; \<forall> x \<in> A. f\<cdot>x \<in> B\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
apply (simp add: funSet_def)
apply (erule exE)
apply simp
done

lemma [simp]: "\<bottom> \<in> tyM t"
apply (induct t)
apply simp
apply (simp add: funSet_def)
done

theorem "\<lbrakk>lam_ty tys l t; env_compat tys \<sigma>\<rbrakk> \<Longrightarrow> lamM l\<cdot>\<sigma> \<in> tyM t"
apply (induct arbitrary: \<sigma> rule: lam_ty.induct)
apply (force simp: env_compat_def)
apply simp
apply (subgoal_tac "lamM l1\<cdot>\<sigma> \<in> natSet")
apply (subgoal_tac "lamM l2\<cdot>\<sigma> \<in> natSet")
apply (erule natSetE)
apply (erule natSetE)
apply simp
apply simp
apply (erule natSetE)
apply simp
apply simp
apply simp
apply simp
apply (subgoal_tac "lamM l1\<cdot>\<sigma> \<in> funSet (tyM t1) (tyM t2)")
apply (erule funSetE)
apply (case_tac "f=\<bottom>")
apply simp
apply simp
apply simp
apply simp
apply (simp add: env_compat_def)
done

theorem "\<lbrakk>lam_ty tys l t; env_compat tys \<sigma>\<rbrakk> \<Longrightarrow> lamM l\<cdot>\<sigma> \<in> tyM t"
proof (induct arbitrary: \<sigma> rule: lam_ty.induct)
case goal2
   have "lamM l1\<cdot>\<sigma> \<in> tyM TyNat" using goal2 by simp
   moreover have "lamM l2\<cdot>\<sigma> \<in> tyM TyNat" using goal2 by simp
   ultimately show ?case apply simp
                         apply (erule natSetE)
                         apply (erule natSetE)
                         apply simp+
                         apply (erule natSetE)
                         by simp+
next
case goal3
   have "lamM l1\<cdot>\<sigma> \<in> funSet (tyM t1) (tyM t2)" using goal3 by simp
   thus ?case using goal3 apply -
                          apply (erule funSetE)
                          apply simp
                          apply (case_tac "f=\<bottom>")
                          apply simp
                          apply simp
                          done
qed (auto simp: env_compat_def)
(*>*)

text {* Now, the final piece we need is that Wrong inhabits the meaning of no
        type. This, again, is simply a proof by simplification and follows essentially automatically. *}

lemma "Wrong \<notin> tyM ty"
(*<*)
apply (induct ty)
apply (simp add: natSet_def)
apply (simp add: funSet_def)
done(*>*)