theory prop_01a
imports Main
begin

datatype Nata = Z | S (p: "Nata")

fun plusa :: "Nata => Nata => Nata" where
  "(plusa Z y) = y"|
  "(plusa (S z) y) = (S (plusa z y))"

fun double :: "Nata => Nata" where
  "(double Z) = Z"|
  "(double (S y)) = (S (S (double y)))"

lemma [simp]:"plusa x (S y) = S (plusa x y)"
  by (induction x, auto)
  
lemma [simp]:" plusa x (S x) =S (plusa x x)"
  apply(induction x)
  by auto
    
theorem "((double x) = (plusa x x))"
  apply(induction x)
   by  auto



end