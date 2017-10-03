theory prop_04
imports Main
begin

  datatype ('a) list = nil | cons (head: "'a") (tail: "'a list")

datatype Nata = Z | S (p: "Nata")

fun equal :: "Nata => Nata => bool" where
"(equal Z Z) = True"|
"(equal Z (S z)) = False"|
"(equal (S x2) Z) = False"|
"(equal (S x2) (S y2)) = (equal x2 y2)"

fun count :: "Nata => Nata list => Nata" where
"(count x nil) = Z"|
"(count x (cons z ys)) = (if (equal x z) then (S (count x ys)) else (count x ys))"

 
lemma [simp]: "equal n n"
  apply (induction n)
  apply auto
  done

theorem "((S (count n xs)) = (count n (cons n xs)))"
  apply(induction xs)
  apply(auto)
  done

end