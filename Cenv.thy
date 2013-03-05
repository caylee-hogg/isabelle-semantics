theory Cenv 
imports HOLCF
"~~/src/HOL/HOLCF/Library/Nat_Discrete"
 begin

default_sort "cpo"

type_synonym 'a cenv = "nat \<rightarrow> 'a"

definition slookup :: "nat \<Rightarrow> 'a cenv \<rightarrow> 'a" where
"slookup n \<equiv> (\<Lambda> \<rho>. \<rho>\<cdot>n)"

definition sfun_upd :: "'a cenv \<rightarrow> nat  \<rightarrow> 'a \<rightarrow> 'a cenv" where
"sfun_upd = (\<Lambda> \<eta> n v n'. if n' = n then v else slookup n'\<cdot>\<eta>)"

lemma lookup_update [simp]: "slookup n\<cdot>(sfun_upd\<cdot>\<eta>\<cdot>n\<cdot>v) = v"
apply (simp add: slookup_def sfun_upd_def)
done

lemma lookup_update' [simp]: "\<lbrakk> m \<noteq> n\<rbrakk> \<Longrightarrow> slookup n\<cdot>(sfun_upd\<cdot>\<eta>\<cdot>m\<cdot>v) = slookup n\<cdot>\<eta>"
apply (simp add: slookup_def sfun_upd_def)
done

end