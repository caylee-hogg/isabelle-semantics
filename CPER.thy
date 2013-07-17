header {* Converging Equivalence Relations *}

theory CPER
imports Main
begin

class cer =
  fixes rel :: "nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes inCer :: "'a \<Rightarrow> bool"
  assumes rel_ex   : "\<exists> x. inCer x"
  assumes rel_refl : "inCer x \<Longrightarrow> rel i x x"
(*  assumes rel_inCer : "(\<forall> i. rel i x x) \<Longrightarrow> inCer x" *)
  assumes rel_sym : "rel i x y \<Longrightarrow> rel i y x"
  assumes rel_trans : "rel i x y \<Longrightarrow> rel i y z \<Longrightarrow> rel i x z"
  assumes rel_zero : "\<lbrakk>inCer x; inCer y\<rbrakk> \<Longrightarrow> rel 0 x y"
  assumes rel_SucD : "rel (Suc i) x y \<Longrightarrow> rel i x y"
  assumes rel_ext : "\<lbrakk>inCer x; inCer y;\<forall>i. rel i x y\<rbrakk> \<Longrightarrow> x = y"
(*
lemma inCerI1 : "rel i x y \<Longrightarrow> inCer x"
apply (rule rel_inCer)
apply (rule rel_trans)
apply assumption
by (rule rel_sym)

lemma inCerI2 : "i > 0 \<Longrightarrow> rel i x y \<Longrightarrow> inCer y"
apply (rule rel_inCer)
apply (rule rel_trans)
by (rule rel_sym) *)

lemma expand_cer_eq:
  fixes x y :: "'a :: cer"
  assumes "inCer x"
  and     "inCer y"
  shows "x = y \<longleftrightarrow> (\<forall>i. rel i x y)"
  by (auto simp add: rel_refl assms rel_ext)

lemma rel_less:
  assumes 1: "rel j x y" and 2: "i < j" shows "rel i x y"
  using 2 1 apply (induct rule: strict_inc_induct)
  apply (rule rel_SucD, simp)
  apply (rule rel_SucD, simp)
  done

subsection {* Nonexpansive and contractive maps *}

definition
  nonexpansive :: "('a :: cer  \<Rightarrow> 'b :: cer ) \<Rightarrow> bool"
where
  "nonexpansive f \<equiv> (\<forall> x. inCer x \<longrightarrow> inCer (f x)) \<and> (\<forall>i x y. rel i x y \<longrightarrow> rel i (f x) (f y))"

definition
  contractive :: "('a :: cer \<Rightarrow> 'b :: cer) \<Rightarrow> bool"
where
  "contractive f \<equiv> (\<forall> x. inCer x \<longrightarrow> inCer (f x)) \<and> (\<forall>i x y. rel i x y \<longrightarrow> rel (Suc i) (f x) (f y))"

lemma nonexpansiveI:
  "\<lbrakk>\<And> x. inCer x \<Longrightarrow> inCer (f x); (\<And>i x y. rel i x y \<Longrightarrow> rel i (f x) (f y))\<rbrakk> \<Longrightarrow> nonexpansive f"
  unfolding nonexpansive_def by simp

lemma nonexpansiveD1:
  "nonexpansive f \<Longrightarrow> rel i x y \<Longrightarrow> rel i (f x) (f y)"
  unfolding nonexpansive_def by simp

lemma nonexpansiveD2: 
  "\<lbrakk>nonexpansive f; inCer x\<rbrakk> \<Longrightarrow> inCer (f x)"
  unfolding nonexpansive_def by simp

lemma contractiveI:
  "\<lbrakk>\<And> x. inCer x \<Longrightarrow> inCer (f x); (\<And>i x y. rel i x y \<Longrightarrow> rel (Suc i) (f x) (f y))\<rbrakk> \<Longrightarrow> contractive f"
  unfolding contractive_def by simp

lemma contractiveD1:
  "contractive f \<Longrightarrow> rel i x y \<Longrightarrow> rel (Suc i) (f x) (f y)"
  unfolding contractive_def by simp

lemma contractiveD2:
  "\<lbrakk>contractive f; inCer x\<rbrakk> \<Longrightarrow> inCer (f x)"
  unfolding contractive_def by simp

lemma contractive_implies_nonexpansive:
  "contractive f \<Longrightarrow> nonexpansive f"
  apply (rule nonexpansiveI)
  apply (erule (1) contractiveD2)
  apply (rule rel_SucD)
  apply (erule (1) contractiveD1)
  done

lemma nonexpansive_compose:
  assumes f: "nonexpansive f"
  assumes g: "nonexpansive g"
  shows "nonexpansive (\<lambda>x. f (g x))"
  apply (rule nonexpansiveI)
  apply (rule nonexpansiveD2 [OF f])
  apply (erule nonexpansiveD2 [OF g])  
  apply (rule nonexpansiveD1 [OF f])
  apply (erule nonexpansiveD1 [OF g])
  done

lemma nonexpansive_contractive_compose:
  assumes f: "nonexpansive f"
  assumes g: "contractive g"
  shows "contractive (\<lambda>x. f (g x))"
  apply (rule contractiveI)
  apply (rule nonexpansiveD2 [OF f])
  apply (erule contractiveD2 [OF g])
  apply (rule nonexpansiveD1 [OF f])
  apply (erule contractiveD1 [OF g])
  done

lemma contractive_nonexpansive_compose:
  assumes f: "contractive f"
  assumes g: "nonexpansive g"
  shows "contractive (\<lambda>x. f (g x))"
  apply (rule contractiveI)
  apply (rule contractiveD2 [OF f])
  apply (erule nonexpansiveD2 [OF g])
  apply (rule contractiveD1 [OF f])
  apply (erule nonexpansiveD1 [OF g])
  done

lemmas contractive_compose =
  nonexpansive_contractive_compose [OF contractive_implies_nonexpansive]

lemma nonexpansive_ident: "nonexpansive (\<lambda>x. x)"
  by (rule nonexpansiveI) assumption

lemma contractive_const: "inCer c \<Longrightarrow> contractive (\<lambda>x. c)"
  apply (rule contractiveI)
  apply assumption
  apply (rule rel_refl)
  apply assumption
done

lemma nonexpansive_double:
  assumes 1: "\<And>y. nonexpansive (\<lambda>x. f x y)"
  assumes 2: "\<And>x. nonexpansive (\<lambda>y. f x y)"
  shows "nonexpansive (\<lambda>x. f x x)"
apply (rule nonexpansiveI)
apply (erule nonexpansiveD2 [OF 1])
apply (rule rel_trans)
apply (erule nonexpansiveD1 [OF 1])
apply (erule nonexpansiveD1 [OF 2])
done

lemma contractive_double:
  assumes 1: "\<And>y. contractive (\<lambda>x. f x y)"
  assumes 2: "\<And>x. contractive (\<lambda>y. f x y)"
  shows "contractive (\<lambda>x. f x x)"
apply (rule contractiveI)
apply (erule contractiveD2 [OF 1])
apply (rule rel_trans)
apply (erule contractiveD1 [OF 1])
apply (erule contractiveD1 [OF 2])
done

text {* Fixed points of contractive functions are unique. *}

lemma contractive_fixed_unique:
  assumes f: "contractive f"
  assumes x: "f x = x" and y: "f y = y"
  assumes inCerx : "inCer x" and inCery : "inCer y"
  shows "x = y"
apply (rule rel_ext)
apply (rule inCerx)
apply (rule inCery)
apply (rule nat.induct [THEN allI])
apply (rule rel_zero)
apply (rule inCerx)
apply (rule inCery)
apply (drule contractiveD1 [OF f])
apply (simp only: x y)
done

subsection {* Complete CERs *}

class complete_cer = cer +
  assumes complete_cer:
    "\<lbrakk>\<forall>i j. i \<le> j \<longrightarrow> rel i (S i) (S j); \<forall> i. inCer (S i)\<rbrakk> \<Longrightarrow> \<exists>z. inCer z \<and> (\<forall>i. rel i z (S i))"

lemma complete_cer_ex1:
  fixes S :: "nat \<Rightarrow> 'a :: complete_cer"
  assumes "\<forall>i j. i \<le> j \<longrightarrow> rel i (S i) (S j)"
  assumes "\<forall> i. inCer (S i)"
  shows "\<exists>!z. inCer z \<and> (\<forall>i. rel i z (S i))"
proof (rule ex_ex1I)
  from assms show "\<exists>z. inCer z \<and> (\<forall>i. rel i z (S i))"
  apply (rule complete_cer)
  done
next
  fix x y
  assume "(inCer x) \<and> (\<forall>i. rel i x (S i))" and "(inCer y) \<and> (\<forall>i. rel i y (S i))"
  hence "(inCer x) \<and> (inCer y) \<and> (\<forall>i. rel i x y)" by (fast elim: rel_trans [OF _ rel_sym])
  thus "x = y"
  apply -
  apply (rule rel_ext)
  apply simp+
  done
qed

lemma contractive_fixed_exists:
  fixes f :: "'a \<Rightarrow> 'a :: complete_cer"
  assumes f: "contractive f"
  shows "\<exists>x. f x = x \<and> inCer x"
proof -
  obtain x0 where x0_rel : "inCer (x0 :: 'a)" 
     using rel_ex ..
  let ?S = "\<lambda>i. (f^^i) x0"
  have 1: "\<And>i. rel i (?S i) (?S (Suc i))"
    apply (induct_tac i)
    apply (rule rel_zero)
    apply (simp add: x0_rel)
    apply (simp add: contractiveD2 [OF f] x0_rel)
    apply (simp add: contractiveD1 [OF f])
    done
  have 2:"\<And> j. rel j ((f ^^ j) x0) ((f ^^ j) x0)"
    apply (induct_tac j)
    apply (simp add: x0_rel rel_refl)
    apply (simp add: contractiveD1 [OF f])
    done
    
  have 3: "\<forall>i j. i \<le> j \<longrightarrow> rel i (?S i) (?S j)"
    apply clarify
    apply (erule inc_induct)
    apply (rule 2)
    apply (erule rel_trans [COMP swap_prems_rl, OF rel_SucD])
    apply (rule 1)
    done

   have 4 : "\<forall> i. inCer (?S i)"
   apply (rule allI)
   apply (induct_tac i)
   apply (simp add: x0_rel)
   apply simp
   apply (rule contractiveD2 [OF f])
   by assumption

   have "\<exists>z. inCer z \<and> (\<forall>i. rel i z (?S i))" using 3 4
    by (rule complete_cer)
  then obtain z where z1: "inCer z" and z2: "\<And>i. rel i z (?S i)"
    by auto
  have "f z = z"
    apply (rule rel_ext [rule_format])
    apply (rule contractiveD2 [OF f])
    apply (rule z1)
    apply (rule z1)
    apply (rule rel_trans [OF _ rel_sym [OF z2]])
    apply (case_tac i)
    apply (simp)
    apply (rule rel_zero)
    apply (rule contractiveD2 [OF f])
    apply (rule z1)
    apply (rule x0_rel)
    apply (simp add: contractiveD1 [OF f z2])
    done
  thus "\<exists>x. f x = x \<and> inCer x" using z1 by auto
qed

lemma contractive_fixed_ex1:
  fixes f :: "'a \<Rightarrow> 'a :: complete_cer"
  assumes f: "contractive f"
  shows "\<exists>!x. f x = x \<and> inCer x"
proof (rule ex_ex1I)
  from f show "\<exists>x. f x = x \<and> inCer x"
    by (rule contractive_fixed_exists)
next
  fix x y assume "f x = x \<and> inCer x" and "f y = y \<and> inCer y"
  with f show "x = y"
    by (auto intro: contractive_fixed_unique [of f x y])
qed

subsection {* Fixed-point combinator *}

definition
  fixed_point :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a :: complete_cer"
where
  "fixed_point f = (THE x. f x = x \<and> inCer x)"

lemma fixed_point_fixed' : 
  assumes f: "contractive f"
  shows "f (fixed_point f) = fixed_point f \<and> inCer (fixed_point f)"
unfolding fixed_point_def
apply (rule theI')
apply (rule contractive_fixed_ex1 [OF f])
done

lemma fixed_point_fixed:
  assumes f: "contractive f"
  shows "f (fixed_point f) = fixed_point f"
using f by (rule fixed_point_fixed' [THEN conjunct1])

lemma fixed_point_inCer : 
  assumes f: "contractive f"
  shows "inCer (fixed_point f)"
using f
by (rule fixed_point_fixed' [THEN conjunct2])

lemma fixed_point_unique:
  assumes f: "contractive f"
  assumes x_fix: "f x = x"
  assumes x_inCer: "inCer x"
  shows "fixed_point f = x"
unfolding fixed_point_def
apply (rule the_equality)
apply (rule conjI [OF x_fix x_inCer])
apply (erule conjE)
apply (erule contractive_fixed_unique [OF f])
apply (rule x_fix)
apply assumption
apply (rule x_inCer)
done

text {* The fixed point combinator preserves contractiveness. *}

lemma rel_fixed_point_lemma:
  assumes f: "contractive f"
  assumes g: "contractive g"
  assumes fg: "\<And>z. rel (Suc i) (f z) (g z)"
  assumes i: "rel i (fixed_point f) (fixed_point g)"
  shows "rel (Suc i) (fixed_point f) (fixed_point g)"
apply (subst fixed_point_fixed [OF f, symmetric])
apply (subst fixed_point_fixed [OF g, symmetric])
apply (rule rel_trans [OF _ fg])
apply (rule contractiveD1 [OF f i])
done

lemma rel_fixed_point:
  assumes f: "contractive f"
  assumes g: "contractive g"
  assumes fg: "\<And>x. rel i (f x) (g x)"
  shows "rel i (fixed_point f) (fixed_point g)"
using fg
apply (induct i)
apply (rule rel_zero)
apply (rule fixed_point_inCer [OF f])
apply (rule fixed_point_inCer [OF g])
apply (rule rel_fixed_point_lemma [OF f g])
apply (erule meta_spec)
apply (erule meta_mp)
apply (rule rel_SucD)
apply (erule meta_spec)
done

lemma nonexpansive_fixed_point:
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a :: complete_cer"
  assumes 1: "\<And>y. nonexpansive (\<lambda>x. f x y)"
  assumes 2: "\<And>x. contractive (\<lambda>y. f x y)"
  shows "nonexpansive (\<lambda>x. fixed_point (\<lambda>y. f x y))"
apply (rule nonexpansiveI)
apply (rule fixed_point_inCer)
apply (rule 2)
apply (rule rel_fixed_point [OF 2 2])
apply (erule nonexpansiveD1 [OF 1])
done


(* 
CH:  I'm going to weaken this slightly, in order to work in the locale

lemma contractive_fixed_point:
  fixes f :: "'a::cer \<Rightarrow> 'b \<Rightarrow> 'b::complete_cer"
  assumes 1: "\<And>y. contractive (\<lambda>x. f x y)"
  assumes 2: "\<And>x. contractive (\<lambda>y. f x y)"
  shows "contractive (\<lambda>x. fixed_point (\<lambda>y. f x y))"
apply (rule contractiveI)
apply (rule rel_fixed_point [OF 2 2])
apply (erule contractiveD [OF 1])
done
end
*)

lemma contractive_fixed_point:
  assumes 1: "\<And>y. contractive (\<lambda>x. f x y)"
  assumes 2: "\<And>x. contractive (\<lambda>y. f x y)"
  shows "contractive (\<lambda>x. fixed_point (\<lambda>y. f x y))"
apply (rule contractiveI)
apply (rule fixed_point_inCer)
apply (rule 2)
apply (rule rel_fixed_point [OF 2 2])
apply (erule contractiveD1 [OF 1])
done

instantiation "prod" :: (cer, cer) cer
begin

definition
  "rel i x y \<equiv> rel i (fst x) (fst y) \<and> rel i (snd x) (snd y)"

definition 
  "inCer x \<equiv> inCer (fst x) \<and> inCer (snd x)"
instance
apply default
apply (unfold inCer_prod_def)
apply simp
apply (rule conjI)
apply (rule rel_ex)
apply (rule rel_ex)
apply (unfold inCer_prod_def rel_prod_def)
apply (erule conjE)
apply (rule conjI)
apply (erule rel_refl)
apply (erule rel_refl)
apply (erule conjE)
apply (rule conjI)
apply (erule rel_sym)
apply (erule rel_sym)

apply (erule conjE)
apply (erule conjE)
apply (rule conjI)
apply (erule rel_trans, simp)+

apply (erule conjE)
apply (erule conjE)
apply (rule conjI)
apply (erule rel_zero, simp)
apply (erule rel_zero, simp)

apply (erule conjE)
apply (rule conjI)
apply (erule rel_SucD)
apply (erule rel_SucD)

apply (rule prod_eqI)
apply (simp add: rel_ext)
apply (simp add: rel_ext)
done

end

instance "prod" :: (complete_cer, complete_cer) complete_cer
proof
  fix f :: "nat \<Rightarrow> 'a \<times> 'b"
  assume 1: "\<forall> i. inCer (f i)"
  hence  l1: "\<forall> i. inCer (fst (f i))" and l2: "\<forall> i. inCer (snd (f i))"
  unfolding inCer_prod_def by simp_all
  assume 2: "\<forall>i j. i \<le> j \<longrightarrow> rel i (f i) (f j)"
  hence "\<forall>i j. i \<le> j \<longrightarrow> rel i (fst (f i)) (fst (f j))"
    and "\<forall>i j. i \<le> j \<longrightarrow> rel i (snd (f i)) (snd (f j))"
    unfolding rel_prod_def by simp_all
  hence "\<exists>a. inCer a \<and> (\<forall>i. rel i a (fst (f i)))"
    and "\<exists>b. inCer b \<and> (\<forall>i. rel i b (snd (f i)))" using l1 l2
    by (simp_all add: complete_cer)
  then obtain a and b where "inCer (a,b)" and "\<forall>i. rel i (a, b) (f i)"
    unfolding rel_prod_def inCer_prod_def by auto
  thus "\<exists>z. inCer z \<and> (\<forall>i. rel i z (f i))" by auto
qed

lemma rel_Pair:
  assumes "rel i x x'" and "rel i y y'"
  shows "rel i (x, y) (x', y')"
  unfolding rel_prod_def using assms by simp

lemma inCer_Pair: 
  assumes "inCer x" and "inCer y"
  shows "inCer (x,y)"
  unfolding inCer_prod_def using assms by simp

lemma rel_PairE:
  assumes "rel i (x, y) (x', y')"
  obtains "rel i x x'" and "rel i y y'"
  using assms unfolding rel_prod_def by simp

lemma rel_fst: "rel i x y \<Longrightarrow> rel i (fst x) (fst y)"
  unfolding rel_prod_def by simp

lemma rel_snd: "rel i x y \<Longrightarrow> rel i (snd x) (snd y)"
  unfolding rel_prod_def by simp

lemma contractive_Pair:
  assumes f: "contractive (\<lambda>x. f x)"
  assumes g: "contractive (\<lambda>x. g x)"
  shows "contractive (\<lambda>x. (f x, g x))"
apply (rule contractiveI)
apply (rule inCer_Pair)
apply (erule contractiveD2 [OF f])
apply (erule contractiveD2 [OF g])
apply (rule rel_Pair)
apply (erule contractiveD1 [OF f])
apply (erule contractiveD1 [OF g])
done

lemma contractive_split:
  assumes 1: "\<And>y. contractive (\<lambda>x. f x y)"
  assumes 2: "\<And>x. contractive (\<lambda>y. f x y)"
  shows "contractive (\<lambda>(x, y). f x y)"
apply (rule contractiveI)
apply (clarsimp simp add: inCer_prod_def)
apply (erule contractiveD2 [OF 1])
apply (clarsimp simp add: rel_prod_def)
apply (rule rel_trans)
apply (erule contractiveD1 [OF 1])
apply (erule contractiveD1 [OF 2])
done

subsection {* Functions form a CER *}

instantiation "fun" :: (type, cer) cer
begin

definition
  "rel i f g \<longleftrightarrow> (\<forall>x. rel i (f x) (g x))"
definition
  "inCer f \<equiv> (\<forall> x. inCer (f x))"
instance
apply default
apply (subgoal_tac "\<exists> (x :: 'b). inCer x")
apply (erule exE)
apply (rule_tac x="\<lambda> y. x" in exI)
apply (unfold inCer_fun_def)
apply simp
apply (rule rel_ex)
apply (unfold rel_fun_def)
apply (rule allI)
apply (drule_tac x="xa" in spec)
apply (erule rel_refl)

apply (rule allI, drule_tac x="xa" in spec)
apply (erule rel_sym)

apply (rule allI, drule_tac x="xa" in spec, drule_tac x="xa" in spec)
apply (erule rel_trans, simp)

apply (rule allI, drule_tac x="xa" in spec, drule_tac x="xa" in spec)
apply (erule rel_zero, simp)

apply (rule allI, drule_tac x="xa" in spec)
apply (erule rel_SucD)

apply (rule ext)
apply (force simp: rel_ext)
done

end

instance "fun" :: (type, complete_cer) complete_cer
proof
  fix f :: "nat \<Rightarrow> 'a \<Rightarrow> 'b"
  assume "\<forall> i. inCer (f i)"
  hence 1: "\<forall> x i. inCer (f i x)"
   unfolding inCer_fun_def by simp

  assume "\<forall>i j. i \<le> j \<longrightarrow> rel i (f i) (f j)"
  hence "\<forall>x i j. i \<le> j \<longrightarrow> rel i (f i x) (f j x)"
    unfolding rel_fun_def by simp
  hence "\<forall>x. \<exists>!a. inCer a \<and> (\<forall>i. rel i a (f i x))" using 1
    apply -
    apply (rule allI) thm complete_cer_ex1
    apply (drule_tac x="x" in spec)
    back
    apply (drule_tac x="x" in spec)
    apply (rule complete_cer_ex1)
    apply simp
    apply simp
    done
  hence "\<exists>!g. \<forall>x. inCer (g x) \<and> (\<forall> i.  rel i (g x) (f i x))"
    by (simp add: choice_eq)
  hence "\<exists>!g. inCer g \<and> (\<forall>i. rel i g (f i))"
    unfolding inCer_fun_def rel_fun_def by auto
  thus "\<exists>g. inCer g \<and> (\<forall>i. rel i g (f i))"
    by (rule ex1_implies_ex)
qed

lemma nonexpansive_fun_iff:
  "nonexpansive (\<lambda>x y. f x y) \<longleftrightarrow> (\<forall>y. nonexpansive (\<lambda>x. f x y))"
  unfolding nonexpansive_def rel_fun_def inCer_fun_def by auto

lemma contractive_fun_iff:
  "contractive (\<lambda>x y. f x y) \<longleftrightarrow> (\<forall>y. contractive (\<lambda>x. f x y))"
  unfolding contractive_def rel_fun_def inCer_fun_def by auto

lemma nonexpansive_lambda:
  assumes "\<And>y. nonexpansive (\<lambda>x. f x y)"
  shows "nonexpansive (\<lambda>x y. f x y)"
  unfolding nonexpansive_fun_iff using assms by simp

lemma contractive_lambda:
  assumes "\<And>y. contractive (\<lambda>x. f x y)"
  shows "contractive (\<lambda>x y. f x y)"
  unfolding contractive_fun_iff using assms by simp

end
