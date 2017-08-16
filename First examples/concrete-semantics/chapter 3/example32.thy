theory example32 imports Main
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

fun plus_ex :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus_ex (N a) (N b) = N (a+b)" |
  "plus_ex (Plus p (N a)) (N b) = Plus p (N (a+b))" |
  "plus_ex (N b) (Plus p (N a)) = Plus p (N (a+b))" |
  "plus_ex (Plus p (N a)) q = Plus (Plus p q) (N a)" |
  "plus_ex q (Plus p (N a)) = Plus (Plus p q) (N a)" |
  "plus_ex p (N i) = (if i = 0 then p else Plus p (N i))" |
  "plus_ex (N i) p = (if i = 0 then p else Plus p (N i))" |
  "plus_ex p q = (Plus p q)"

fun full_asimp :: "aexp \<Rightarrow> aexp" where
  "full_asimp (N a) = N a" |
  "full_asimp (V x) = V x" |
  "full_asimp (Plus p q) = plus_ex (full_asimp p) (full_asimp q)"

value "full_asimp (Plus (Plus ((Plus (V ''x'') (N 7))) (V ''x'')) (N 5))" 

lemma aval_plus_ex: "aval (plus_ex p q) s = aval p s + aval q s"
apply (induction rule:plus_ex.induct)
apply (auto)
done

theorem "aval (full_asimp p) s = aval p s"
apply (induction p)
apply (auto simp add:aval_plus_ex)
done
    
end
  