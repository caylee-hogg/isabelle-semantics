theory HabitAST3
imports Main begin

datatype akind = Star | Area | Nat | Lab 
datatype kind = KFun akind kind | KA akind

type_synonym var = nat
type_synonym lab = nat
type_synonym dcon = nat
type_synonym const = nat
type_synonym scon = nat

(* let's do debruijn indices for lambdas und lets *)

datatype expr = EVar var | ELit lit | ELam pat expr
              | EData dcon | EApp expr expr | ECase expr "(pat \<times> expr) list"
              | EReturn | EBind | EReadRef | EWriteRef
              | EConst const | ELet decls expr | ELetrec decls expr
              | EUpdate expr "(var \<times> expr) list" | EStruct scon "(var \<times> expr) list" (* need to lookup how the structure declarations here work <_< cuz this doesn't seem right *)
and lit = LBit "bool list" | LSigned int | LUnsigned nat | LLab lab
and pat = PWild | PVar | PLit lit | PCon dcon "pat list" | PAt pat
and decls = Decls "expr list" (* uhh where do bit data come in? something's missing....look it up *) (* also need to add in topdecls and all that *)

end