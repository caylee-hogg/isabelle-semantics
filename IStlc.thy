theory IStlc
imports HOLCF Ideal Cenv CER begin

datatype ty = TyNat | TyFun ty ty

datatype lam = LVar nat | LApp lam lam | LLam nat ty lam | LNat nat
             | LPlus lam lam | LFix ty lam

type_synonym ty_env = "nat \<Rightarrow> ty"

inductive lam_ty :: "ty_env \<Rightarrow> lam \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ : _") where
  LVar : "\<lbrakk>tys n = ty\<rbrakk> \<Longrightarrow> tys \<turnstile> (LVar n) : ty" |
  LPlus : "\<lbrakk>(tys \<turnstile> l1 : TyNat); (tys \<turnstile> l2 : TyNat)\<rbrakk> \<Longrightarrow> tys \<turnstile> (LPlus l1 l2) : TyNat" |
  LApp  : "\<lbrakk>tys \<turnstile> l1 : (TyFun t1 t2); tys \<turnstile> l2 : t1\<rbrakk> \<Longrightarrow> tys \<turnstile> (LApp l1 l2) : t2" |
  LNat  : "lam_ty tys (LNat n) TyNat" |
  LLam  : "\<lbrakk>(tys (n :=t1)) \<turnstile> l1 : t2\<rbrakk> \<Longrightarrow> tys \<turnstile> (LLam n t1 l1) : (TyFun t1 t2)" |
  LFix  : "\<lbrakk>tys \<turnstile> l1 : (TyFun t1 t1)\<rbrakk> \<Longrightarrow> tys \<turnstile> (LFix t1 l1) : t1"

domain V = VNat (fromNat :: "nat lift") | VFun (lazy "V \<rightarrow> V") | Wrong

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
apply simp+
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
    apply (rule monofun_cfun_fun) thm V.chain_take
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

fixrec fromFun :: "V \<rightarrow> (V \<rightarrow> V)" where
"fromFun\<cdot>(VFun\<cdot>f) = f" |
"fromFun\<cdot>Wrong = \<bottom>" |
"n \<noteq> \<bottom> \<Longrightarrow> fromFun\<cdot>(VNat\<cdot>n) = \<bottom>" |
"fromFun\<cdot>\<bottom> = \<bottom>"

lemma "fromFun\<cdot>Wrong = \<bottom>"
apply (fixrec_simp)
done

fixrec vFix :: "V \<rightarrow> V" where
"vFix\<cdot>(VFun\<cdot>f) = fix\<cdot>f" |
"vFix\<cdot>Wrong = Wrong" |
"n \<noteq> \<bottom> \<Longrightarrow> vFix\<cdot>(VNat\<cdot>n) = Wrong"

lemma [simp]: "vFix\<cdot>\<bottom> = \<bottom>"
apply fixrec_simp
done

fixrec vApply :: "V \<rightarrow> V \<rightarrow> V" where
"n \<noteq> \<bottom> \<Longrightarrow> vApply\<cdot>(VNat\<cdot>n)\<cdot>x = Wrong" |
"vApply\<cdot>(VFun\<cdot>f)\<cdot>x = f\<cdot>x" |
"vApply\<cdot>Wrong\<cdot>x = Wrong"

lemma [simp]: "vApply\<cdot>\<bottom>\<cdot>x = \<bottom>"
apply fixrec_simp
done

abbreviation vapp :: " V \<Rightarrow> V \<Rightarrow> V" (infixl "\<bullet>" 900) where
"f\<bullet>x \<equiv> vApply\<cdot>f\<cdot>x"

abbreviation vLam :: "(V \<Rightarrow> V) \<Rightarrow> V" (binder "\<Delta> " 10) where
"vLam f \<equiv> VFun\<cdot>(\<Lambda> x. f x)"

definition VFun_ideal :: "ideal \<Rightarrow> ideal \<Rightarrow> ideal" (infix "[\<rightarrow>]" 55)
where
     "S [\<rightarrow>] T = Abs_ideal {f. \<forall> x \<in>(Rep_ideal S). f\<bullet>x \<in> Rep_ideal T}"

lemma less_apply: "f \<sqsubseteq> g \<Longrightarrow> f\<bullet>x \<sqsubseteq> g\<bullet>x"
apply (cases f, simp_all)
apply (cases g, simp_all)
apply (cases g, simp_all)
apply (rule monofun_cfun_fun)
apply simp
apply (cases g, simp_all)
done

lemma app_lub : "chain Y \<Longrightarrow> (\<Squnion> i. Y i) \<bullet> x = (\<Squnion> i. Y i \<bullet> x)"
apply (rule cont2contlubE, simp+)
done

lemma Rep_VFun_ideal:
  "Rep_ideal (S [\<rightarrow>] T) = ({f. \<forall>x\<in>(Rep_ideal S). f\<bullet>x \<in> Rep_ideal T})"
(*<*)
unfolding VFun_ideal_def
apply (rule Abs_ideal_inverse')
apply (rule idealI)
apply clarsimp
apply (rule ideal_bottom)
apply (rule Rep_ideal')
apply clarsimp thm ideal_downward
apply (rule_tac y="y\<bullet>xa" in ideal_downward)
apply (rule Rep_ideal')
apply (erule less_apply)
apply simp
apply clarsimp
apply (rule adm_ball)
apply (rule admI)
apply (subgoal_tac "chain (\<lambda>i. Y i \<bullet> x)")
apply (subst app_lub)
apply simp
apply (subgoal_tac "adm (\<lambda>x. x\<in> Rep_ideal T)")
apply (drule_tac Y="(\<lambda> i. Y i \<bullet> x)" in admD) 
apply simp
apply simp
apply simp
apply (rule ideal_adm)
apply (rule Rep_ideal')
apply (rule chainI)
apply (rule less_apply)
apply (rule chainE)
apply simp
done

fun tyM :: "ty \<Rightarrow> ideal" where
"tyM TyNat = [\<nat>]" |
"tyM (TyFun t1 t2) = (tyM t1) [\<rightarrow>] (tyM t2)"

fixrec vPlus :: "V \<rightarrow> V \<rightarrow> V" where
"n \<noteq> \<bottom> \<and> n' \<noteq> \<bottom> \<Longrightarrow> vPlus\<cdot>(VNat\<cdot>n)\<cdot>(VNat\<cdot>n') = VNat\<cdot>((FLIFT x x'. Def (x + x'))\<cdot>n\<cdot>n')" |
"n \<noteq> \<bottom> \<Longrightarrow> vPlus\<cdot>(VNat\<cdot>n)\<cdot>(VFun\<cdot>f) = Wrong" |
"vPlus\<cdot>(VFun\<cdot>f)\<cdot>(VFun\<cdot>f') = Wrong" |
"n \<noteq> \<bottom> \<Longrightarrow> vPlus\<cdot>(VFun\<cdot>f)\<cdot>(VNat\<cdot>n) = Wrong" |
"vPlus\<cdot>Wrong\<cdot>(VFun\<cdot>f) = Wrong" |
"n \<noteq> \<bottom> \<Longrightarrow> vPlus\<cdot>Wrong\<cdot>(VNat\<cdot>n) = Wrong" |
"n \<noteq> \<bottom> \<Longrightarrow> vPlus\<cdot>(VNat\<cdot>n)\<cdot>Wrong = Wrong" |
"vPlus\<cdot>(VFun\<cdot>f)\<cdot>Wrong = Wrong"

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

fun lamM :: "lam \<Rightarrow> V cenv \<Rightarrow> V" where
"lamM (LNat n) \<sigma> = VNat\<cdot>(Def n)" |
"lamM (LLam n _ e) \<sigma> = (\<Delta> x. lamM e (sfun_upd\<cdot>\<sigma>\<cdot>n\<cdot>x))" |
"lamM (LApp e1 e2) \<sigma> = (lamM e1 \<sigma>)\<bullet>(lamM e2 \<sigma>)" |
"lamM (LPlus e1 e2) \<sigma> = vPlus\<cdot>(lamM e1 \<sigma>)\<cdot>(lamM e2 \<sigma>)" |
"lamM (LVar n) \<sigma> = slookup n\<cdot>\<sigma>"|
"lamM (LFix _ f) \<sigma> = vFix\<cdot>(lamM f \<sigma>)"

(* define compatibility between environments and \<sigma> *)

definition env_compat :: "ty_env \<Rightarrow> V cenv \<Rightarrow> bool" where
"env_compat tys \<sigma> \<equiv> \<forall> n. (slookup n\<cdot>\<sigma>) \<in> (Rep_ideal (tyM (tys n)))"

lemma [simp] : "\<bottom> \<in> (Rep_ideal (tyM t))"
apply (rule ideal_bottom)
apply (rule Rep_ideal')
done

lemma [simp] : "adm (\<lambda> x. x \<in> (Rep_ideal (tyM t)))"
apply (rule ideal_adm)
apply (rule Rep_ideal')
done

lemma fixy: "\<lbrakk>\<forall> v \<in> P. f\<cdot>v \<in> P; adm (\<lambda> x. x \<in> P); \<bottom> \<in> P\<rbrakk> \<Longrightarrow> fix\<cdot>f \<in> P"
apply (rule fix_ind)
apply simp
apply simp
apply simp
done (* this is a fact we need for the fixed point case *)

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
done

(* cont (lamM l) \<Longrightarrow> cont (\<lambda>x. \<Lambda> xa. lamM l (x\<cdot>xa)) *)

lemma cont_helper : "cont f \<Longrightarrow> cont (\<lambda> x. \<Lambda> xa. f (x\<cdot>xa))"
apply (rule cont2cont_LAM)
apply (rule cont_compose)
back
apply simp
apply simp
apply (rule cont_compose)
back
apply simp
apply simp
done

lemma [simp] : "cont (lamM l)"
apply (induct l)
apply simp
apply simp
apply simp
defer
apply simp
apply simp
apply simp
apply (rule cont_compose)
back
back
defer
apply simp
apply (rule cont_compose)
back
apply simp
apply (rule cont_helper)
apply simp
done

lemma [simp] : "cont (\<lambda> x. lamM l (sfun_upd\<cdot>\<sigma>\<cdot>n\<cdot>x))"
apply (rule cont_compose)
back
apply simp
apply simp
done


lemma "\<lbrakk>tys \<turnstile> l : t; env_compat tys \<sigma>\<rbrakk> \<Longrightarrow> lamM l \<sigma> \<in> (Rep_ideal (tyM t))"
apply (induct arbitrary: \<sigma> rule: lam_ty.induct)
apply (force simp: env_compat_def)
apply simp
apply (case_tac "lamM l1 \<sigma>")
apply (case_tac "lamM l2 \<sigma>")
apply force
apply force
apply (force simp: Rep_VNat_ideal)
apply (force simp: Rep_VNat_ideal)
apply (case_tac "lamM l2 \<sigma>")
apply force
apply (case_tac lifta)
apply simp
apply (case_tac lift)
apply simp
apply (simp add: Rep_VNat_ideal)
apply (force simp: Rep_VNat_ideal)
apply (force simp: Rep_VNat_ideal)
apply (force simp: Rep_VNat_ideal)
apply (force simp: Rep_VNat_ideal)
defer
apply (simp add: Rep_VNat_ideal)
defer
apply simp
apply (case_tac "lamM l1 \<sigma>")
apply simp
apply (force simp: Rep_VFun_ideal)
apply simp
apply (rule fixy)
apply (force simp: Rep_VFun_ideal)
apply simp
apply simp
apply (force simp: Rep_VFun_ideal)
apply (case_tac "lamM l1 \<sigma>")
apply simp
apply (force simp: Rep_VFun_ideal)
apply (force simp: Rep_VFun_ideal)
apply (force simp: Rep_VFun_ideal)
apply (auto simp: Rep_VFun_ideal env_compat_def)
done


end