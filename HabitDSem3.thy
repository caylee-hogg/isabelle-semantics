theory HabitDSem3 
imports HabitAST3 HOLCF Cenv Ideal CPER
"~~/src/HOL/HOLCF/Library/Nat_Discrete"
"~~/src/HOL/HOLCF/Library/Bool_Discrete"
"~~/src/HOL/HOLCF/Library/Int_Discrete"
"~~/src/HOL/HOLCF/Library/List_Predomain" 
 begin

domain V = VUnit | VNat "nat u" | VInt "int u"
         | VProd "V \<otimes> V" | VSum "V \<oplus> V" 
         | VFun (fromFun :: "V \<rightarrow> (V list \<rightarrow> (V \<otimes> ((V list) u)))")
         | VBool "bool u" | VBit "(bool list) u" | Wrong

lemma chain_bot : "\<lbrakk>chain Y; (\<Squnion> i. (Y i)) = \<bottom>\<rbrakk> \<Longrightarrow> Y j = \<bottom>"
apply (subgoal_tac "Y j \<sqsubseteq> (\<Squnion> i. Y i)")
apply simp
apply (erule is_ub_thelub)
done

class taken = pcpo + 
  fixes take :: "nat \<Rightarrow> 'a \<rightarrow> 'a"
  assumes take_0 [simp]: "take 0\<cdot>x = \<bottom>"
  assumes take_below [simp]: "take n\<cdot>x \<sqsubseteq> x"
  assumes take_take : "take m\<cdot>(take n\<cdot>x) = take (min m n)\<cdot>x"
  assumes take_reach : "(\<Squnion> i. take i\<cdot>x) = x"
  assumes take_chain : "chain (\<lambda> i. take i\<cdot>x)"
  assumes take_chain2 : "chain take"

lemma take_bot : "take i\<cdot>\<bottom> = \<bottom>"
apply (subgoal_tac "(\<Squnion> i. take i\<cdot>\<bottom>) = \<bottom>")
apply (rule chain_bot)
apply (rule take_chain)
apply assumption
apply (rule take_reach)
done

instantiation V :: taken begin
definition "take_V \<equiv> V_take"
instance
apply (default, unfold take_V_def)
apply simp
apply (rule V.take_below)
apply (rule V.take_take)
apply (rule V.reach)
apply simp
apply (rule V.chain_take)
done
end

instantiation "set" :: ("taken") cer begin

definition "inCer A \<equiv> ideal A"

definition "rel i S T \<equiv> (\<forall> z. take i\<cdot>z \<in> S \<longleftrightarrow> take i\<cdot>z \<in> T)" 

instance
apply (default, unfold rel_set_def inCer_set_def)
apply (rule_tac x="UNIV" in exI)
apply (simp add: ideal_def)
apply simp
apply simp
apply simp
apply (simp add: ideal_bottom)

apply (rule allI)
apply (drule_tac x="take i\<cdot>z" in spec)
apply (subgoal_tac "take (Suc i)\<cdot>(take i\<cdot>z) = take i\<cdot>z")
apply simp 
apply (subgoal_tac "min (Suc i) i = i")
apply (force simp: take_take)
apply simp
apply (rule set_eqI, rename_tac z)
apply (subgoal_tac "(\<Squnion>i. take i\<cdot>z) \<in> x \<longleftrightarrow> (\<Squnion>i. take i\<cdot>z) \<in> y")
apply (simp add: take_reach)
apply (simp add: take_chain ideal_lub_iff)

 (*>*)
done
end

instance "set" :: ("taken") complete_cer proof
  fix S :: "nat \<Rightarrow> (('a :: taken) set)"
  assume 1: "\<forall> i. inCer (S i)"
  hence **: "\<forall> i. ideal (S i)" 
  unfolding inCer_set_def by simp
  assume 2: "\<forall> i j. i \<le> j \<longrightarrow> rel i (S i) (S j)"
  hence *: "\<And>i j x. i \<le> j \<Longrightarrow>
    take i\<cdot>x \<in> (S i) \<longleftrightarrow> take i\<cdot>x \<in> (S j)"
    unfolding rel_set_def by simp
  have ideal_T: "inCer {x. \<forall> i. take i\<cdot>x \<in> (S i)}"
    unfolding inCer_set_def
    apply (rule idealI)
    apply simp
    apply (rule allI)
    apply (subst "take_bot")
    apply (rule ideal_bottom)
    apply (simp add: **)
    apply clarify
    apply (rule ideal_downward)
    apply (simp add: **)
    apply (erule monofun_cfun_arg)
    apply simp
    apply simp
    apply (rule adm_all)
    apply (rule adm_subst, simp)
    apply (rule ideal_adm)
    apply (simp add: **)
    done
    
    let ?T = "{x. \<forall>i. take i\<cdot>x \<in> (S i)}"
    have "\<forall>i. rel i ?T (S i)"
    unfolding rel_set_def
    apply (simp, safe)
    apply (drule_tac x=i in spec) thm taken.take_take
    apply (subgoal_tac "take i\<cdot>(take i\<cdot>z) = take i\<cdot>z")
    apply simp
    apply (simp add: take_take min_def)
    apply (rename_tac i z j)
    apply (simp add: take_take min_def, safe)
    apply (subst *, assumption)
    apply (rule ideal_downward)
    apply (simp add: **) thm monofun_cfun_fun
    apply (rule_tac f="take j" and g="take i" in monofun_cfun_fun)
    apply (rule chain_mono)
    apply (rule take_chain2)
    apply assumption
(*    apply (subst * [symmetric]) *)
    apply assumption
    apply (subst * [symmetric])
    apply simp
    apply assumption
    done
  thus "\<exists>z. inCer z \<and> (\<forall>i. rel i z (S i))" using ideal_T by auto
qed

definition cconst :: "'a \<Rightarrow> ('b \<rightarrow> 'a)" where
"cconst a = (\<Lambda> b. a)"

type_synonym 'a State = "V list \<rightarrow> ('a \<otimes> ((V list) u))"
(*
lemma ideal_image_VNat:
   assumes S: "ideal S"
   shows "ideal ((\<lambda> x. VNat\<cdot>x) ` S)"
apply (rule ideal_image [OF _ _ S])
apply (case_tac x, simp_all add: flat_eq)
apply (rule_tac x="(\<Lambda> (VNat\<cdot>x). x)" in exI)
apply (rule allI)
apply (case_tac "x = \<bottom>")
apply simp
apply simp
done *)

definition return :: "'a \<rightarrow> 'a State" where
"return \<equiv> \<Lambda> x vs. (: x, up\<cdot>vs :)"

fixrec vApply :: "V \<rightarrow> V \<rightarrow> V State" where
"n \<noteq> \<bottom> \<Longrightarrow> vApply\<cdot>(VNat\<cdot>n)\<cdot>x = return\<cdot>Wrong" |
"i \<noteq> \<bottom> \<Longrightarrow> vApply\<cdot>(VInt\<cdot>i)\<cdot>x = return\<cdot>Wrong" |
"p \<noteq> \<bottom> \<Longrightarrow> vApply\<cdot>(VProd\<cdot>p)\<cdot>x = return\<cdot>Wrong" |
"vApply\<cdot>VUnit\<cdot>x = return\<cdot>Wrong" |
"s \<noteq> \<bottom> \<Longrightarrow> vApply\<cdot>(VSum\<cdot>s)\<cdot>x = return\<cdot>Wrong" |
"f \<noteq> \<bottom> \<Longrightarrow> vApply\<cdot>(VFun\<cdot>f)\<cdot>x = f\<cdot>x" |
"bs \<noteq> \<bottom> \<Longrightarrow> vApply\<cdot>(VBit\<cdot>bs)\<cdot>x = return\<cdot>Wrong" |
"b \<noteq> \<bottom> \<Longrightarrow> vApply\<cdot>(VBool\<cdot>b)\<cdot>x = return\<cdot>Wrong" |
"vApply\<cdot>Wrong\<cdot>x = return\<cdot>Wrong"
(* TODO - fix up apply so it has the right properties, i.e. (VFun\<cdot>f)\<bullet>\<bottom> = \<bottom> *)

lemma [simp]: "vApply\<cdot>\<bottom>\<cdot>x = \<bottom>"
apply fixrec_simp
done

abbreviation vapp :: " V \<Rightarrow> V \<Rightarrow> V State" (infixl "\<bullet>" 900) where
"f\<bullet>x \<equiv> vApply\<cdot>f\<cdot>x"

definition VUnit_ideal :: "V set" ("[1]") where
"[1] = {\<bottom>,VUnit}"

definition VNat_set :: "V set" ("[\<nat>]") where
"[\<nat>] = (range (\<lambda> x. VNat\<cdot>(up\<cdot>x)))"

definition VSum_ideal :: "V set \<Rightarrow> V set \<Rightarrow> V set" (infix "[+]" 55) where
"S [+] T = ((\<lambda> x. VSum\<cdot>x) ` ((\<lambda> x. sinl\<cdot>x) ` S \<union> (\<lambda> x. sinr\<cdot>x) ` T))"

definition VFun_ideal :: "V set \<Rightarrow> V set \<Rightarrow> V set" (infix "[\<rightarrow>]" 55) where
"S [\<rightarrow>] T = {f. \<forall> x \<in> S. \<forall> n. (sfst\<cdot>((f\<bullet>x)\<cdot>n)) \<in> T}"

definition VProd_ideal :: "V set \<Rightarrow> V set \<Rightarrow> V set" (infix "[*]" 55) where
"S [*] T = ((\<lambda> x. VProd\<cdot>x) ` {(:x,y:) | x y. x \<in> S \<and> y \<in> T})" 
definition VBool_set :: "V set" ("[2]") where
"[2] = (range (\<lambda> x. VBool\<cdot>(up\<cdot>x)))"
definition VInt_set :: "V set" ("[I]") where
"[I] = (range (\<lambda> x. VInt\<cdot>(up\<cdot>x)))"
definition VBit_set :: "nat \<Rightarrow> V set" ("[B]") where
"[B] n \<equiv> (\<lambda> x. VBit\<cdot>(up\<cdot>x)) ` { l . length l = n}"

lemma less_apply: "f \<sqsubseteq> g \<Longrightarrow> f\<bullet>x \<sqsubseteq> g\<bullet>x"
apply (cases f, simp_all add: return_def)
apply (cases g, simp_all add: return_def)
apply (cases g, simp_all add: return_def)
apply (cases g, simp_all add: return_def)
apply (cases g, simp_all add: return_def)
apply (cases g, simp_all add: return_def)
apply (cases g, simp_all add: return_def)
apply (rule monofun_cfun_fun)
apply simp
apply (cases g, simp_all add: return_def)
apply (cases g, simp_all add: return_def)
apply (cases g, simp_all add: return_def)
done

lemma ideal_image_VSum:
  assumes S: "ideal S"
  shows "ideal ((\<lambda>x. VSum\<cdot>x) ` S)"
apply (rule ideal_image [OF _ _ S])
apply (case_tac x, simp_all)
apply (rule_tac x="\<Lambda>(VSum\<cdot>x). x" in exI)
apply (rule allI, case_tac "x = \<bottom>", simp, simp)
done

lemma sum_ideal : "\<lbrakk>ideal S; ideal T\<rbrakk> \<Longrightarrow> ideal ((\<lambda> x. VSum\<cdot>x) ` ((\<lambda> x. sinl\<cdot>x) ` S \<union> (\<lambda> x. sinr\<cdot>x) ` T))"
apply (rule ideal_image_VSum)
apply (rule ideal_union)
apply (rule ideal_image_sinl)
apply assumption
apply (rule ideal_image_sinr)
apply assumption
done

lemma ideal_image_VProd: 
  assumes S: "ideal S"
  shows "ideal ((\<lambda> x. VProd\<cdot>x) ` S)"
apply (rule ideal_image [OF _ _ S])
apply (case_tac x, simp_all)
apply (rule_tac x="\<Lambda>(VProd\<cdot>x). x" in exI)
apply (rule allI)
apply (case_tac "x=\<bottom>")
apply simp
apply simp
done

lemma prod_ideal : "\<lbrakk>ideal S; ideal T\<rbrakk> \<Longrightarrow> ideal ((\<lambda> x. VProd\<cdot>x) ` {(:x,y:) | x y. x \<in> S \<and> y \<in> T})"
apply (rule ideal_image_VProd)
apply (rule idealI)
apply simp
apply (rule_tac x=\<bottom> in exI)
apply (rule_tac x=\<bottom> in exI)
apply (simp add: ideal_bottom)

apply simp
apply (erule exE)
apply (erule exE)
apply simp
apply (case_tac x)
apply simp
apply ((rule_tac x="\<bottom>" in exI)+, simp add: ideal_bottom)
apply simp
apply (rule_tac x="xb" in exI)
apply (rule_tac x="yb" in exI)
apply clarsimp
apply (rule conjI)
apply (rule ideal_downward)
apply assumption
apply (subgoal_tac "xb \<sqsubseteq> xa")
apply simp
apply (case_tac "xa=\<bottom>")
apply simp
apply (case_tac "ya=\<bottom>")
apply simp
apply (simp add: spair_below)
apply simp
apply (rule ideal_downward)
apply assumption
apply (subgoal_tac "yb \<sqsubseteq> ya")
apply (simp add: spair_below)
apply (simp add: spair_below)
apply simp
apply (rule admI)
apply simp
apply (rule_tac x="sfst\<cdot>(\<Squnion> i. (Y i))" in exI)
apply (rule_tac x="ssnd\<cdot>(\<Squnion> i. (Y i))" in exI)
apply (rule conjI)
apply (simp add: spair_sfst_ssnd)
apply (rule conjI)
apply (subgoal_tac "sfst\<cdot>(\<Squnion> i. Y i) = (\<Squnion> i. sfst\<cdot>(Y i))")
apply simp
apply (rule admD)
apply (rule ideal_adm)
apply assumption
apply simp
apply (drule_tac x=i in spec)
apply (erule exE)+
apply (case_tac "x=\<bottom>")
apply simp
apply (case_tac "y=\<bottom>")
apply simp
apply (rule ideal_bottom)
apply assumption
apply simp
apply (erule contlub_cfun_arg)
apply (rule admD)
apply (rule adm_subst)
back
apply simp
apply (rule ideal_adm)
apply assumption
apply simp
apply (drule_tac x=i in spec)
apply (erule exE)+
apply (case_tac "x=\<bottom>")
apply simp
apply (rule ideal_bottom)
apply assumption
apply simp
done

lemma rel_VProd_ideal : "\<lbrakk>ideal S; ideal T; ideal S'; ideal T'; rel i S S';
                          rel i T T'\<rbrakk> \<Longrightarrow> rel (Suc i ) (S [*] T) (S' [*] T')"
unfolding rel_set_def take_V_def
apply (simp add: VProd_ideal_def)
apply (rule allI)
apply (case_tac z)
apply (simp add: image_def ideal_bottom prod_ideal)
apply (rule iffI)
apply (rule_tac x="\<bottom>" in exI)+
apply (simp add: ideal_bottom)
apply (rule_tac x="\<bottom>" in exI)+
apply (simp add: ideal_bottom)

apply (simp add: image_def)
apply (simp add: image_def)
apply (simp add: image_def)

apply (simp add: image_def)
apply (case_tac "sprod_map\<cdot>(V_take i)\<cdot>(V_take i)\<cdot>sprod = \<bottom>")
apply simp
apply (rule iffI)
apply (rule_tac x="\<bottom>" in exI)+
apply (simp add: ideal_bottom)
apply (rule_tac x="\<bottom>" in exI)+
apply (simp add: ideal_bottom)
apply (case_tac sprod)
apply simp
apply (simp add: image_def)
apply (rule iffI)
apply (erule exE)+
apply (rule_tac x="V_take i\<cdot>x" in exI)
apply (rule_tac x="V_take i\<cdot>y" in exI)
apply simp
apply (rule conjI)
apply (drule_tac x=x in spec)
apply (erule conjE)+
apply (subgoal_tac "xa = V_take i\<cdot>x")
apply simp 
apply (drule_tac x="V_take i\<cdot>x" and y = "V_take i\<cdot>y" in spair_inject)
apply simp
apply simp
apply simp

apply (erule conjE)+
apply (drule_tac x="V_take i\<cdot>x" and y = "V_take i\<cdot>y" in spair_inject)
apply simp
apply simp
apply force
apply (erule exE)+
apply (rule_tac x="V_take i\<cdot>x" in exI)
apply (rule_tac x="V_take i\<cdot>y" in exI)
apply simp
apply (erule conjE)+
apply (drule_tac x="V_take i\<cdot>x" and y = "V_take i\<cdot>y" in spair_inject)
apply simp
apply simp
apply simp

defer
defer
apply (simp add: image_def)
apply (simp add: image_def)
apply (simp add: image_def)

apply (simp add: image_def)
apply (case_tac "ssum_map\<cdot>(V_take i)\<cdot>(V_take i)\<cdot>ssum = \<bottom>")
apply (simp add: image_def)
apply (rule iffI)
apply (rule_tac x="\<bottom>" in exI)+
apply (simp add: ideal_bottom)
apply (rule_tac x="\<bottom>" in exI)+
apply (simp add: ideal_bottom)
apply (simp add: image_def)

apply (simp add: image_def)

apply (rule iffI)
apply (rule conjI)
apply (rule_tac x="\<bottom>" in exI)+ apply (simp add: ideal_bottom)
defer
apply (rule conjI)
apply (rule_tac x="\<bottom>" in exI)+ apply (simp add: ideal_bottom)

apply (case_tac "cfun_map\<cdot>(V_take i)\<cdot>
            (cfun_map\<cdot>(list_map (V_take i))\<cdot>
             (sprod_map\<cdot>(V_take i)\<cdot>(u_map\<cdot>(list_map (V_take i)))))\<cdot>
            cfun = \<bottom>")

apply (simp add: ideal_bottom)
apply (simp add: image_def)

apply (case_tac "cfun_map\<cdot>(V_take i)\<cdot>
            (cfun_map\<cdot>(list_map (V_take i))\<cdot>
             (sprod_map\<cdot>(V_take i)\<cdot>(u_map\<cdot>(list_map (V_take i)))))\<cdot>
            cfun = \<bottom>")
apply (simp add: ideal_bottom)
apply (simp add: image_def)
done

lemma rel_VSum_ideal:
  "\<lbrakk>ideal S; ideal T; ideal S'; ideal T'; rel i S S'; rel i T T'\<rbrakk> \<Longrightarrow> rel (Suc i) (S [+] T) (S' [+] T')" 
unfolding rel_set_def take_V_def
apply (simp add: VSum_ideal_def)
apply (rule allI)
apply (case_tac z)
apply (simp add: image_def ideal_bottom)
apply (simp add: image_def VSum_ideal_def)
apply (simp add: image_def VSum_ideal_def)
apply (simp add: image_def VSum_ideal_def)
apply (simp add: image_def VSum_ideal_def)
apply (case_tac "sprod_map\<cdot>(V_take i)\<cdot>(V_take i)\<cdot>sprod = \<bottom>")
apply (simp add: image_def ideal_bottom)
apply (simp add: image_def VSum_ideal_def)
apply (case_tac ssum rule: ssumE2)
apply (simp add: image_def VSum_ideal_def ideal_bottom)
apply (simp add: image_def ideal_bottom VSum_ideal_def)
defer
apply (simp add: image_def VSum_ideal_def)
apply (simp add: image_def VSum_ideal_def)
apply (simp add: image_def VSum_ideal_def)
apply (case_tac "cfun_map\<cdot>(V_take i)\<cdot>
            (cfun_map\<cdot>(list_map (V_take i))\<cdot>
             (sprod_map\<cdot>(V_take i)\<cdot>(u_map\<cdot>(list_map (V_take i)))))\<cdot>
            cfun = \<bottom>")
apply (simp add: image_def VSum_ideal_def ideal_bottom)
apply (simp add: image_def VSum_ideal_def)
done(*>*)

definition bind :: "('a State) \<rightarrow> ('a \<rightarrow> 'b State) \<rightarrow> 'b State" where
"bind \<equiv> (\<Lambda> s f n. (\<Lambda> (: a , up\<cdot>n' :). (f\<cdot>a)\<cdot>n')\<cdot>(s\<cdot>n))"

abbreviation vLam :: "(V \<Rightarrow> V State) \<Rightarrow> V" (binder "\<Delta> " 10) where
"vLam f \<equiv> VFun\<cdot>(\<Lambda> x. f x)"

definition eApp :: "V State \<rightarrow> V State \<rightarrow> V State" where
"eApp = (\<Lambda> f a. bind\<cdot>a\<cdot>(\<Lambda> x. bind\<cdot>f\<cdot>(\<Lambda> y. y\<bullet>x)))"

(* need dictionary for constants as well as data constructors:
   data constructors can be some kind of large product, I guess?
   Example: lists will have two constructors, one Nil such that
   D[Nil] = VUnit and the other Cons such that
   D[Cons] = VFun\<cdot>(\<Lambda> x y. (: x, y :))

   another problem is having repeated lambda application cuz, like,
   ATM you can't do something like \<Delta> x y. z because of the way the kleisli arrows
   work :-/ I suppose it's not that much of a problem it's just that the right
   way to do the D[Cons] example is to have \<Delta> x. return\<cdot>(\<Delta> y. return\<cdot>(: x, y :))

   that should work, eh?
    *)

type_synonym d_env = "nat \<Rightarrow> V"
type_synonym c_env = "nat \<Rightarrow> V"
term bind

definition readRef' :: "nat \<Rightarrow> V State" where
"readRef' n \<equiv> (\<Lambda> s. (: nth s n, up\<cdot>s :))"

fixrec readRef :: "V \<rightarrow> V State" where
"readRef\<cdot>(VNat\<cdot>(up\<cdot>n)) = readRef' n"

fun updateList :: "nat \<Rightarrow> ('a :: cpo) \<Rightarrow> 'a list \<Rightarrow> ('a list) u" where
"updateList 0 v vs = up\<cdot>(v # (tl vs))" |
"updateList (Suc n) v [] = \<bottom>" |
"updateList (Suc n) v (v' # vs) = fup\<cdot>(\<Lambda> xs. up\<cdot>(v' # xs))\<cdot>(updateList n v vs)"

definition writeRef' :: "nat \<Rightarrow> V \<Rightarrow> V State" where
"writeRef' i v \<equiv> (\<Lambda> s. (: VUnit, updateList i v s :))"

fixrec writeRef :: "V \<rightarrow> V \<rightarrow> V State" where
"writeRef\<cdot>(VNat\<cdot>(up\<cdot>n))\<cdot>v = \<bottom>"

fun denoteExpr :: "d_env \<Rightarrow> c_env \<Rightarrow> expr \<Rightarrow> V cenv \<rightarrow> V State" and
    denotePat :: "d_env \<Rightarrow> c_env \<Rightarrow> pat \<Rightarrow> V cenv \<rightarrow> V \<rightarrow> V cenv" and
    denoteLit :: "lit \<Rightarrow> V" and
    denoteDecls :: "d_env \<Rightarrow> c_env \<Rightarrow> decls \<Rightarrow> V cenv \<rightarrow> V cenv" where
"denoteExpr \<Phi> \<Psi> (ELit l) = cconst (return\<cdot>(denoteLit l))" |
"denoteExpr \<Phi> \<Psi> (EVar v) = (\<Lambda> \<sigma>. return\<cdot>(slookup v\<cdot>\<sigma>))" |
"denoteExpr \<Phi> \<Psi> (EApp l l') = (\<Lambda> \<sigma>. eApp\<cdot>(denoteExpr \<Phi> \<Psi> l\<cdot>\<sigma>)\<cdot>(denoteExpr \<Phi> \<Psi> l\<cdot>\<sigma>))" |
"denoteExpr \<Phi> \<Psi> (ERef n) = cconst (return\<cdot>(VNat\<cdot>(up\<cdot>n)))" |
"denoteExpr \<Phi> \<Psi> (EData d) = cconst (return\<cdot>(\<Phi> d))" |
"denoteExpr \<Phi> \<Psi> (EConst c) = cconst (return\<cdot>(\<Psi> c))" |
"denoteExpr \<Phi> \<Psi> EReturn = cconst (return\<cdot>(\<Delta> x. return\<cdot>x))" |
"denoteExpr \<Phi> \<Psi> (EBind e1 e2) = (\<Lambda> \<sigma>. eApp\<cdot>(denoteExpr \<Phi> \<Psi> e2\<cdot>\<sigma>)\<cdot>(denoteExpr \<Phi> \<Psi> e1\<cdot>\<sigma>))" |
"denoteExpr \<Phi> \<Psi> EReadRef = cconst (return\<cdot>(\<Delta> x. readRef\<cdot>x))" |
"denoteExpr \<Phi> \<Psi> EWriteRef = cconst (return\<cdot>(\<Delta> x. return\<cdot>(\<Delta> y. writeRef\<cdot>x\<cdot>y)))" |
"denoteExpr \<Phi> \<Psi> (ELam p e) = (\<Lambda> \<sigma>. return\<cdot>(\<Delta> x. denoteExpr \<Phi> \<Psi> e\<cdot>(denotePat \<Phi> \<Psi> p\<cdot>\<sigma>\<cdot>x)))" | 
"denotePat \<Phi> \<Psi> p = \<bottom>" |
"denoteLit (LBit bs) = VBit\<cdot>(up\<cdot>bs)" |
"denoteLit (LSigned i) = VInt\<cdot>(up\<cdot>i)" |
"denoteLit (LUnsigned n) = VNat\<cdot>(up\<cdot>n)" |
"denoteLit (LLab l) = VNat\<cdot>(up\<cdot>l)" |
"denoteDecls \<Phi> \<Psi> d = \<bottom>"