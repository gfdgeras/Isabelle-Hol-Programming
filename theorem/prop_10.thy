theory prop_10
imports Main
begin

datatype Nata = Z | S (p: "Nata")

fun minusa :: "Nata => Nata => Nata" where
  "(minusa Z y) = Z"|
  "(minusa (S z) Z) = (S z)"|
  "(minusa (S z) (S x2)) = (minusa z x2)"

theorem "((minusa m m) = Z)"
  apply (induction m)
  by auto
end