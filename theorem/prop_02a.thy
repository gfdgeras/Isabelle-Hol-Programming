theory prop_02a
imports Main
begin

datatype ('a) list = nil | cons (head: "'a") (tail: "'a list")

datatype Nata = Z | S (p: "Nata")

fun lengtha :: "'a list => Nata" where
  "(lengtha nil) = Z"|
  "(lengtha (cons y xs)) = (S (lengtha xs))"

fun appenda :: "'a list => 'a list => 'a list" where
  "(appenda nil y) = y"|
  "(appenda (cons z xs) y) = (cons z (appenda xs y))"


lemma [simp]:" lengtha (appenda y (cons x1 x)) = S (lengtha (appenda y x)) "
  apply(induction y, auto)
  done
    
theorem "((lengtha (appenda x y)) = (lengtha (appenda y x)))"
  apply(induction x,induction y)
  by(auto)
   
end