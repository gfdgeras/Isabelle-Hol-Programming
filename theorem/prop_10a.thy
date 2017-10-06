theory prop_10a
imports Main
begin

datatype ('a) list = nil | cons (head: "'a") (tail: "'a list")

fun appenda :: "'a list => 'a list => 'a list" where
"(appenda nil y) = y"|
"(appenda (cons z xs) y) = (cons z (appenda xs y))"

fun reva :: "'a list => 'a list" where
"(reva nil) = (nil :: 'a list)"|
"(reva (cons y xs)) = (appenda (reva xs) (cons y (nil :: 'a list)))"


lemma [simp]: "reva (appenda x (cons x1 nil)) = (appenda(cons x1 nil) (reva x))  "
  apply(induction x)
  apply auto
  done
    
theorem "((reva (reva x)) = x)"
   apply(induction x)
    apply auto
   done

end