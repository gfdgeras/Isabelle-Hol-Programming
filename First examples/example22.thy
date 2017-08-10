theory example22
  imports Main
begin
  
 
  
  fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

lemma add_associative: "add (add m n) p = add m (add n p)"
  apply(induction m)
   apply(induction n)
    apply(induction p)
  apply auto
  done
    
lemma add_commutative: "add 0  n = add n 0"
    apply (induction n) 
    apply auto
    done
    
 fun double:: "nat \<Rightarrow> nat" where
  "double m = add m m"
  
   lemma double_add: "double m = add m m"
  apply (induction m)
   apply auto
    done
  
end
  