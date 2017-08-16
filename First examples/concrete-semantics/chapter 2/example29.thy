theory example29 imports Main
begin
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n" |
  "add (Suc m) n = Suc(add m n)"
  
lemma suma[simp]: "add x (Suc y) = Suc (add x y)"
  apply (induction x)
  apply (auto)
  done 
    
fun itadd :: "nat \<Rightarrow>nat\<Rightarrow> nat " where
  "itadd 0 n = n" |
  "itadd (Suc m) n = itadd m (Suc n)"

value "itadd 1 3"

theorem add_itadd: "itadd m n = add m n"
apply (induction m arbitrary: n)
apply (auto)
done
end
  