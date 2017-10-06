theory prop_13a
imports Main
begin

datatype Nata = Z | S (p: "Nata")

fun plusa :: "Nata => Nata => Nata" where
  "(plusa Z y) = y"|
  "(plusa (S z) y) = (S (plusa z y))"

fun half :: "Nata => Nata" where
  "(half Z) = Z"|
  "(half (S Z)) = Z"|
  "(half (S (S z))) = (S (half z))"

 

lemma [simp]: "plusa a (S b) = S(plusa a b) "
  apply(induction a )
   by  auto
    
theorem "((half (plusa x x)) = x)"
  apply (induction x)
   apply auto
   done
end