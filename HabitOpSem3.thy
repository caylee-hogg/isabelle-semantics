theory HabitOpSem3 
imports HabitAST3 begin

datatype val = VLit lit | VLam pat expr | VData dcon | VReturn "expr option"
             | VBind "val option" "val option"
             | VReadRef "val option" | VWriteRef "val option" "val option"
             | VConst const "val list" (* I think these are all the values? *)