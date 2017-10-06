theory prop_06a
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

fun reva :: "'a list => 'a list" where
"(reva nil) = (nil :: 'a list)"|
"(reva (cons y xs)) = (appenda (reva xs) (cons y (nil :: 'a list)))"


lemma[simp]: "lengtha (appenda x (cons x1 nil)) =  S (lengtha x) "
  apply(induction x)
   by  auto

theorem "((lengtha (reva (appenda x y))) = (plusa (lengtha x) (lengtha y)))"
  apply(induction x,induction y)
   by auto


end