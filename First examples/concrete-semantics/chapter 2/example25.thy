theory example25 imports Main
begin
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n" |
  "add (Suc m) n = Suc(add m n)"

fun sum_upto:: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0" |
  "sum_upto (Suc n) = (sum_upto n ) + (Suc n)"
  
value "sum_upto 3"
  
lemma "sum_upto n = n * (n + 1) div 2"
  apply (induction n)
  apply (auto)
  done
end