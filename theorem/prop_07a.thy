theory prop_07a
imports Main
begin

datatype ('a) list = nil | cons (head: "'a") (tail: "'a list")

datatype Nata = Z | S (p: "Nata")

fun qrev :: "'a list => 'a list => 'a list" where
  "(qrev nil y) = y"|
  "(qrev (cons z xs) y) = (qrev xs (cons z y))"

fun plusa :: "Nata => Nata => Nata" where
  "(plusa Z y) = y"|
  "(plusa (S z) y) = (S (plusa z y))"

fun lengtha :: "'a list => Nata" where
  "(lengtha nil) = Z"|
  "(lengtha (cons y xs)) = (S (lengtha xs))"


lemma[simp]: "S (plusa (lengtha x) (lengtha y)) = plusa (lengtha x) (S (lengtha y))"
  apply(induction x)
  apply auto
  done    
        
theorem "((lengtha (qrev x y)) = (plusa (lengtha x) (lengtha y)))"
  apply(induction x arbitrary: y)
  apply auto
 done

end