theory prop_03a
imports Main
begin

datatype ('a) list = nil | cons (head: "'a") (tail: "'a list")

datatype Nata = Z | S (p: "Nata")

fun plusa :: "Nata => Nata => Nata" where
  "(plusa Z y) = y"|
  "(plusa (S z) y) = (S (plusa z y))"

fun lengtha :: "'a list => Nata" where
  "(lengtha nil) = Z"|
  "(lengtha (cons y xs)) = (S (lengtha xs))"

fun appenda :: "'a list => 'a list => 'a list" where
  "(appenda nil y) = y"|
  "(appenda (cons z xs) y) = (cons z (appenda xs y))"


lemma [simp]: "plusa (lengtha y) (S (lengtha x)) = S (plusa (lengtha y) (lengtha x))"
  apply(induction y)
  by auto

theorem "((lengtha (appenda x y)) = (plusa (lengtha y) (lengtha x)))"
  apply(induction x, induction y)
  by  auto
    
end