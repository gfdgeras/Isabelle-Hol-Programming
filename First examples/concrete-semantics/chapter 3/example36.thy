theory example36 imports Main
begin

  
type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"
  
datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp
  
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N a) s = a" |
  "aval (V x) s = s x" |
  "aval (Plus a b) s = aval a s + aval b s"
fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "subst x a (N k) = (N k)" |
  "subst x a (V y) = (if x = y then a else (V y))" |
  "subst x a (Plus p q) = Plus (subst x a p) (subst x a q)"

theorem aval_subst[simp]:  "aval (subst x a e) s = aval e (s(x:=aval a s))"
apply (induction e)
apply (auto)
done 

theorem "aval a s = aval b s \<Longrightarrow> aval (subst x a e) s = aval (subst x b e) s"
apply (auto)
done
    
fun lval :: "lexp \<Rightarrow> state\<Rightarrow> int" where
  "lval (Nl a) s = a" |
  "lval (Vl x) s = s x" |
  "lval (Plusl p q) s = lval p s + lval q s" |
  "lval (LET x a e) s = lval e (s(x:=lval a s))"

fun inline :: "lexp \<Rightarrow> aexp" where
  "inline (Nl a) = (N a)" |
  "inline (Vl x) = (V x)" |
  "inline (Plusl p q) = Plus (inline p) (inline q)" |
  "inline (LET x a e) = subst x (inline a) (inline e)"  

theorem "aval (inline e) s = lval e s"
apply (induction e arbitrary:s)
apply (auto)
done
end
  