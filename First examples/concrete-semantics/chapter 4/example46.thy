theory example46 imports Main
begin
  
type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow>val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N a) s = a" |
  "aval (V x) s = s x" |
  "aval (Plus a b) s = aval a s + aval b s"

inductive rel_aval :: "aexp \<Rightarrow> state \<Rightarrow>val \<Rightarrow> bool" where
  ar_N: "rel_aval (N a) s a" |
  ar_V: "rel_aval (V x) s (s x)" |
  ar_Plus: "rel_aval p s p_v \<Longrightarrow> rel_aval q s q_v \<Longrightarrow> rel_aval (Plus p q) s (p_v + q_v)" 

theorem rel_aval_aval: "rel_aval a s v \<Longrightarrow> aval a s = v"
apply (induction rule: rel_aval.induct)
apply (auto)
done

theorem aval_rel_aval: "aval a s = v \<Longrightarrow> rel_aval a s v"
apply (induction a arbitrary: v)
apply (auto intro: ar_N ar_V ar_Plus)
done

theorem "rel_aval a s v \<Longrightarrow> aval a s = v"
apply (rule iffI)
apply (auto intro: aval_rel_aval rel_aval_aval)
  done 
end
  