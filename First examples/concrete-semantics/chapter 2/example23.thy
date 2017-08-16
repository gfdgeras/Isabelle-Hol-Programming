theory example23  imports Main
begin
  
value "2#[4::int,5,6]"
  
fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count [] x = 0 " |
  "count (h#t) x = (if x = h then Suc(count t x) else (count t x))"
  
value "count [1,2,3](1::nat)" 
value "count [2,4] (1::nat)"
value "count [3, 1, 2, 1, 0] (1::nat)"
value "count [a,a,a,a,a]a"
  
lemma prueba: "count xs x  \<le> lenght xs"
 apply(induction xs)
 apply(auto)
 oops