theory example24
  imports Main
begin

fun snoc:: "'a list \<Rightarrow> 'a \<Rightarrow>'a list" where
  "snoc Nil x = (Cons x Nil)" |
  "snoc (h#t) x = h#(snoc t x)"

value "snoc [a, b](c)" 

lemma snoc_equal_at: "snoc l a = l @ [a]"
  apply (induction l)
  apply auto
  done
    
fun reverse:: "'a list\<Rightarrow>'a list" where
  "reverse Nil = Nil" |
  "reverse (h#t) = snoc(reverse t) h"
  
  
value "reverse [a,b,c,d]"
  
lemma reverse_snoc: "reverse (snoc xs a) = a # (reverse xs)"
  apply (induction xs)
  apply auto
done

theorem "reverse (reverse xs) = xs"
  apply (induction xs)
  apply (auto simp add: reverse_snoc)
done