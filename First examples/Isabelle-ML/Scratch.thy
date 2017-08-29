theory Scratch imports Main
begin



lemma disj_swap: shows "P \<or> Q \<Longrightarrow> Q \<or> P "
apply(erule disjE)
apply(rule disjI2)
apply(assumption)
apply(rule disjI1)
apply(assumption)
done

ML \<open> 
  let 
    val ctxt = @{context}
    val goal = @{prop "P \<or> Q \<Longrightarrow> Q \<or> P "}
  in
    Goal.prove ctxt ["P", "Q"] [] goal
    (fn _ =>  eresolve_tac @{context} @{thms disjE } 1 
      THEN resolve_tac @{context} @{thms disjI2 } 1
      THEN  assume_tac @{context} 1
      THEN resolve_tac @{context} @{thms disjI1 } 1
      THEN assume_tac @{context} 1
     )
  end
\<close> 
  
ML_val  \<open>
  val foo_tac = 
    ( eresolve_tac @{context} @{thms disjE } 1 
      THEN resolve_tac @{context} @{thms disjI2 } 1
      THEN  assume_tac @{context} 1
      THEN resolve_tac @{context} @{thms disjI1 } 1
      THEN assume_tac @{context} 1
     )
\<close>  

lemma shows "P \<or> Q \<Longrightarrow> Q \<or> P "
apply(tactic \<open>foo_tac @{context}\<close>)
oops





ML  \<open> 
signature WELLFORMED_TERMS =
sig
val get: theory -> term list
val add: term -> theory -> theory
end;
\<close>

value "[2,6,8] @ [6,9,8,7::int]"



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