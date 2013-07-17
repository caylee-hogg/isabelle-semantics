theory HabitOpSem3 
imports HabitAST3 begin

datatype val = VLit lit | VLam pat expr | VData dcon "val list" | VReturn "expr option"
             | VBind "val option" "val option"
             | VReadRef "val option" | VWriteRef "val option" "val option"
             | VConst const "val list" (* I think these are all the values? *)
term None
inductive eval :: "expr \<Rightarrow> val \<Rightarrow> bool" where
lit : "eval (ELit lit) (VLit lit)" |
lam : "eval (ELam p e) (VLam p e)" |
return : "eval EReturn (VReturn None)" |
bind : "eval EBind (VBind None None)" |
const : "eval (EConst c) (VConst c [])" |
data : "eval (EData d) (VData d [])" | (* okay now we need to do the actually non-trivial
                                          cases *)
(* need to handle a bunch of only slightly non-trivial things related to application *)
retApp : "\<lbrakk>eval e1 (VReturn None)\<rbrakk> \<Longrightarrow> eval (EApp e1 e2) (VReturn (Some e2))" |
constApp : "\<lbrakk>eval e1 (VConst c vs); eval e2 v2\<rbrakk> \<Longrightarrow> eval (EApp e1 e2) (VConst c (vs @ [v2]))" |
bindApp1 : "\<lbrakk>eval e1 (VBind None None); eval e2 v2\<rbrakk> \<Longrightarrow> eval (EApp e1 e2) (VBind (Some v2) None)" |
bindApp2 : "\<lbrakk>eval e1 (VBind (Some v1) None); eval e2 v2\<rbrakk> \<Longrightarrow> eval (EApp e1 e2) (VBind (Some v1) (Some v2))" 