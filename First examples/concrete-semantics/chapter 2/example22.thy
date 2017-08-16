theory example22 imports Main
begin
     
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n" |
  "add (Suc m) n = Suc(add m n)"
  
lemma suma[simp]: "add x (Suc y) = Suc (add x y)"
  apply (induction x)
   apply (auto)
  done 
    
lemma add_associative[simp]: "add (add m n) p = add m (add n p)"
  apply(induction m)
  apply auto
  done
    
lemma add_commutative[simp]: "add 0  n = add n 0"
   apply (induction n) 
   apply auto
   done
    
fun double:: "nat \<Rightarrow> nat" where
  "double 0 = 0" |
  "double (Suc m) = Suc(Suc(double m)) "

value "double 3"
value "add 3 3"
value "double 3 = add 3 3"
  
lemma double_add: "add n n = double n"
 (* nitpick*)
apply(induction n)
apply(auto)
done

end
  