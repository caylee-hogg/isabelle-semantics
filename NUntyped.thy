(*<*)theory NUntyped 
imports HOLCF
"~~/src/HOL/HOLCF/Library/Nat_Discrete"
"~~/src/HOL/HOLCF/Library/List_Cpo"
begin(*>*)

section {* The Untyped Lambda Calculus: A First Example *}

text {* In this section, we will give a simple denotational semantics for the
        pure untyped lambda calculus and show that our semantics satisfies the
        standard beta-reduction rule.

        Our representation of the term language is entirely standard. There
        are lambda abstractions, applications, and variables. We are, here,
        using de Bruijn indices for simplicity.*}

datatype lam = Lam lam | App lam lam | Var nat
(*<*)
fun shift :: "nat \<Rightarrow> nat \<Rightarrow> lam \<Rightarrow> lam" where
"shift d c (Var n) = (if n < c then Var n else Var (n + d))" |
"shift d c (Lam l) = Lam (shift d (Suc c) l)" |
"shift d c (App l l') = App (shift d c l) (shift d c l')"

fun shiftD :: "nat \<Rightarrow> nat \<Rightarrow> lam \<Rightarrow> lam" where
"shiftD d c (Var n) = (if n < c then Var n else Var (n - d))" |
"shiftD d c (Lam l) = Lam (shiftD d (Suc c) l)" |
"shiftD d c (App l l') = App (shiftD d c l) (shiftD d c l')"

lemma [simp]: "shiftD x n (shift x n l) = l"
apply (induct l arbitrary: x n)
apply simp
apply simp
apply simp
done

fun subst :: "nat \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam" where
"subst j s (Var n) = (if n = j then s else Var n)" |
"subst j s (Lam l) = Lam (subst (Suc j) (shift 1 0 s) l)" |
"subst j s (App l l') = (App (subst j s l) (subst j s l'))"

definition topsubst :: "nat \<Rightarrow> lam \<Rightarrow> lam \<Rightarrow> lam" where
"topsubst n l l' = shiftD 1 0 (subst n (shift 1 0 l') l)"

definition beta :: "lam \<Rightarrow> lam \<Rightarrow> lam" where
"beta l l' = shiftD 1 0 (subst 0 (shift 1 0 l') l)"

declare beta_def [simp](*>*)

text {* We then need, of course, a domain for us to interpret the meaning of
        the untyped lambda calculus terms. In this case, since we are talking about the pure untyped calculus we then need a "set" where all its elements can be interpreted as endomorphisms on the "set". Fortunately, while such a set does not exist, that is easily definable as a domain with our domain command in HOLCF.*}

domain D = DFun "D \<rightarrow> D" 

text {* Here we use the "lazy" keyword in order to signify that there is a difference between the divergent term $\perp$ and the actual value which is a function that diverges on all inputs, $\lambda x. \perp$. *}

text {* Now we can rather simply define our "internal" notion of application of one lambda term to another using fixrec. In this case, we are choosing to represent a call by name evaluation order as we are not insisting that the application of a function to the argument $\perp$ is equal to $\perp$. *}

fixrec dApply :: "D \<rightarrow> D \<rightarrow> D" where
"dApply\<cdot>(DFun\<cdot>f)\<cdot>x = f\<cdot>x" |
"dApply\<cdot>\<bottom>\<cdot>x = \<bottom>"

text {* For convenience, we also introduce the abbreviations for lambda abstraction and application {\em within} the model. The end result is that we can use $\Delta$ as a binder for easy definition of functions. *}

abbreviation dLam :: "(D \<Rightarrow> D) \<Rightarrow> D" (binder "\<Delta> " 10) where
"dLam f \<equiv> DFun\<cdot>(\<Lambda> x. f x)"

abbreviation dapp :: " D \<Rightarrow> D \<Rightarrow> D" (infixl "\<bullet>" 900) where
"f\<bullet>x \<equiv> dApply\<cdot>f\<cdot>x"

lemma [simp]: "(\<forall> x. f\<cdot>x = \<bottom>) \<Longrightarrow> f = \<bottom>"
apply (rule cfun_eqI)
apply simp
done

lemma model_ext : "(\<forall> x. f\<bullet>x = g\<bullet>x) \<Longrightarrow> f = g"
apply (case_tac f)
apply (case_tac g)
apply simp
apply simp
apply (case_tac g)
apply simp
apply simp
apply (rule cfun_eqI)
apply (drule_tac x=x in spec)
apply simp
done
(*<*)

lemma model_eta : "(\<Delta> x. f\<bullet>x) = f"
apply (rule model_ext) 
apply (cases f)
apply simp
apply simp
done

fixrec chead :: "D list \<rightarrow> D" where
"chead\<cdot>[] = \<bottom>" |
"chead\<cdot>(y # ys) = y"

definition ctail :: "D list \<rightarrow> D list" where
"ctail = (\<Lambda> x. case x of [] \<Rightarrow> [] | y # ys \<Rightarrow> ys)"

lemma [simp] : "ctail\<cdot>[] = []"
               "ctail\<cdot>(x # xs) = xs"
apply (simp add: ctail_def)
apply (simp add: ctail_def)
done

definition match_0 :: "nat \<rightarrow> 'a match \<rightarrow> 'a match" where
"match_0 = (\<Lambda> n k. case n of 0 \<Rightarrow> k | (Suc n') \<Rightarrow> Fixrec.fail)"

definition match_Suc :: "nat \<rightarrow> (nat \<rightarrow> 'a match) \<rightarrow> 'a match" where
"match_Suc = (\<Lambda> n k. case n of 0 \<Rightarrow> Fixrec.fail | (Suc n') \<Rightarrow> k\<cdot>n')"

lemma match_0_simps [simp]: 
  "match_0\<cdot>0\<cdot>k = k" 
  "match_0\<cdot>(Suc n)\<cdot>k = Fixrec.fail"
unfolding match_0_def by simp_all

lemma match_Suc_simps [simp]:
  "match_Suc\<cdot>0\<cdot>k = Fixrec.fail"
  "match_Suc\<cdot>(Suc n)\<cdot>k = k\<cdot>n"
unfolding match_Suc_def by simp_all
term "0 :: nat"

ML {* @{const_name Groups.zero_class.zero} *}

setup {* 
  Fixrec.add_matchers
  [ (@{const_name Groups.zero_class.zero}, @{const_name match_0}),
    (@{const_name Suc}, @{const_name match_Suc})] *}

fun cnth :: "nat \<Rightarrow> D list \<rightarrow> D" where
"cnth 0 = chead" |
"cnth (Suc n) = (cnth n oo ctail)"(*>*)

lemma "cont cnth"
by simp

text {* We now come to our denotation function, which we define by ordinary
        structural recursion of the lambda terms. At this point, we are able
        to simply define the meaning of lambda abstractions as lambda abstractions within the model, applications as applications within the model, and
        variables as lookup within the environment. The definition of the cnth function we have elided as it is simply a continuous operation on lists. Here, we are able to use the fact that an instance has been defined for the built in list datatype that makes lists of a cpo a cpo, so we are able to define continuous operations on lists and keep everything nice and computable in our semantics.*}

fun lamDenote :: "lam \<Rightarrow> D list \<rightarrow> D" ("\<parallel>_\<parallel>") where
"\<parallel>Lam l\<parallel> = (\<Lambda> \<sigma>. (\<Delta> x. \<parallel>l\<parallel>\<cdot>(x # \<sigma>)))" |
"\<parallel>Var n\<parallel> = (\<Lambda> \<sigma>. cnth n\<cdot>\<sigma>)" |
"\<parallel>App l1 l2\<parallel> = (\<Lambda> \<sigma>. \<parallel>l1\<parallel>\<cdot>\<sigma>\<bullet>\<parallel>l2\<parallel>\<cdot>\<sigma>)"
term length term append

lemma "\<lbrakk>length xs = n\<rbrakk> \<Longrightarrow> \<parallel>shift (Suc 0) n f\<parallel>\<cdot>(xs @ (y # ys)) = \<parallel>f\<parallel>\<cdot>(xs @ ys)"
apply (induct f arbitrary: xs y ys n)
defer
apply simp
apply (case_tac "nat=n")
defer
apply simp
apply simp

lemma "\<parallel>shift (Suc 0) 0 f\<parallel>\<cdot>(x # \<sigma>) = \<parallel>f\<parallel>\<cdot>\<sigma>"
apply (induct f arbitrary: x \<sigma>)
defer
apply simp
apply simp
apply simp

lemma "\<parallel>Lam (App (shift f (Var 0))\<parallel>\<cdot>\<sigma> = \<parallel>f\<parallel>\<cdot>\<sigma>"
apply simp 
apply (rule model_ext)
apply (rule allI)
apply simp

text {* We are also able to prove, fortunately, that this semantics respects
        beta reduction. *}

lemma "\<parallel>(beta l l')\<parallel>\<cdot>\<sigma> = \<parallel>App (Lam l) l'\<parallel>\<cdot>\<sigma>"
apply (simp)
apply (induct l arbitrary: \<sigma> l')
apply simp
apply (rule cfun_eqI)
apply simp
defer
apply simp
apply (case_tac nat)
apply simp
apply (simp add: ctail_def)


lemma "lamDenote (beta l l')\<cdot>[] = lamDenote (App (Lam l) l')\<cdot>[]"
(*<*)apply simp
apply (induct l)
defer
apply simp
apply (case_tac nat)
apply (simp add: chead_def)
apply (simp add: ctail_def)
apply simp
oops(*>*) 
(*<*)
definition C0 :: lam where
"C0 \<equiv> (Lam (Lam (Var 0)))"

definition C1 :: lam where
"C1 \<equiv> (Lam (Lam (App (Var 1) (Var 0))))"

definition CSucc :: lam where
"CSucc \<equiv> (Lam (Lam (Lam (App (Var 1) (App (App (Var 2) (Var 1)) (Var 0))))))"(*>*)

text {* We can also prove simple examples such as the successor of 0 is 1, using just simplification. *}

lemma "lamDenote (App CSucc C0)\<cdot>[] = lamDenote C1\<cdot>[]"(*<*)
apply (simp add: CSucc_def C1_def C0_def eval_nat_numeral ctail_def chead_def)
done(*>*)
(*<*)
definition CTrue :: lam where
"CTrue \<equiv> (Lam (Lam (Var 1)))"

definition CFalse :: lam where
"CFalse \<equiv> (Lam (Lam (Var 0)))"

definition CAnd :: lam where
"CAnd \<equiv> (Lam (Lam (App (App (Var 1) (Var 0)) (Var 1))))" (*>*)

text {* Or that the and operator behaves as expected. *}

lemma "lamDenote (App (App CAnd CTrue) CTrue) = lamDenote CTrue"(*<*)
apply (simp add: CAnd_def CTrue_def eval_nat_numeral ctail_def chead_def)
done(*>*)

lemma "lamDenote (App (App CAnd CFalse) CTrue) = lamDenote CFalse"(*<*)
apply (simp add: CAnd_def CTrue_def CFalse_def eval_nat_numeral ctail_def chead_def)
done(*>*)
(*<*)
lemma "lamDenote CFalse = lamDenote C0"
apply (simp add: CFalse_def C0_def eval_nat_numeral ctail_def chead_def)
done

end(*>*)