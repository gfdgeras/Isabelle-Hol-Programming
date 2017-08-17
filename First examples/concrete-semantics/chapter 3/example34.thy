theory example34 imports Main
begin

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

datatype aexp = N int | V vname | Plus aexp aexp | Times aexp aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) s = n" |  
  "aval (V x) s = s x" |
  "aval (Plus a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s + aval a\<^sub>2 s" |
  "aval (Times a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s * aval a\<^sub>2 s"

  
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1+i\<^sub>2)" |
  "plus (N i) a = (if i=0 then a else Plus (N i) a)" |
  "plus a (N i) = (if i=0 then a else Plus a (N i))" |
  "plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"
  
fun times :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "times (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1 * i\<^sub>2)" |
  "times (N i) a = (if i=0 then (N 0) else if i=1 then a else  Times (N i) a)" |
  "times a (N i) = (if i=0 then (N 0) else if i=1 then a else  Times a (N i))" |
  "times a\<^sub>1 a\<^sub>2 = Times a\<^sub>1 a\<^sub>2"


fun asimp :: "aexp \<Rightarrow> aexp" where
  "asimp (N n) = N n" |
  "asimp (V x) = V x" |
  "asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)"|
  "asimp (Times a\<^sub>1 a\<^sub>2) = times (asimp a\<^sub>1) (asimp a\<^sub>2)"



lemma aval_plus[simp]: "aval (plus p q) s = aval p s + aval q s"
apply (induction rule:plus.induct)
apply (auto)
done

lemma aval_times[simp]: "aval (times p q) s = aval p s * aval q s"
apply (induction rule:times.induct)
apply (auto)
done

theorem "aval (asimp p) s = aval p s"
apply (induction p)
apply (auto)
done 

end