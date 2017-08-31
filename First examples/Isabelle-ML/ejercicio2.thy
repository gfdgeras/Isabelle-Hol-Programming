theory ejercicio2 imports Main
begin


notepad
begin
ML_prf \<open> val a = 1 \<close>

ML_prf \<open> val b = a + 1 \<close>

ML_prf \<open> val c = b + 1 \<close>
end

  
lemma app_Nil2 [simp]: "xs @ [] = xs"
apply(induct_tac xs)
apply(auto)
  done


lemma app_assoc [simp]: "(xs @ ys) @ zs = xs @ (ys @ zs)"
apply(induct_tac xs)
apply(auto)
  done
    
lemma rev_app [simp]: "rev(xs @ ys) = (rev ys) @ (rev xs)"
apply(induct_tac xs)
apply(auto)
  done
    
theorem rev_rev [simp]: "rev(rev xs) = xs"
apply(induct_tac xs)
apply(auto)
  done
end