theory example31 imports Main
begin

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N a) s = a" |
  "aval (V x) s = s x" |
  "aval (Plus a b) s = aval a s + aval b s"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
  "asimp_const (N a) = N a" |
  "asimp_const (V x) = V x" |
  "asimp_const (Plus p q) = 
      (case (asimp_const p, asimp_const q) of 
      (N a, N b) \<Rightarrow> N (a+b) |
      (x, y) \<Rightarrow> Plus x y)"

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N a) (N b) = N (a+b)" |
  "plus p (N i) = (if i = 0 then p else Plus p (N i))" |
  "plus (N i) p = (if i = 0 then p else Plus (N i) p)" |
  "plus p q = (Plus p q)"

fun asimp :: "aexp \<Rightarrow> aexp" where
  "asimp (N a) = N a" |
  "asimp (V x) = V x" |
  "asimp (Plus p q) = plus (asimp p) (asimp q)"

fun optimal :: "aexp \<Rightarrow> bool" where
  "optimal (N a) = True" |
  "optimal (V x) = True" |
  "optimal (Plus (N a) (N b)) = False" | 
  "optimal (Plus x y) = ((optimal x) \<and> (optimal y))"

theorem asimp_const_optimal: "optimal (asimp_const a)"
apply (induction a)
apply (auto split: aexp.split)
done
    
end
  