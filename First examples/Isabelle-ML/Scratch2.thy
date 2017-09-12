theory Scratch2 imports Main
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
  
ML  \<open>
  fun foo_tac ctxt = 
    ( 
      eresolve_tac ctxt @{thms disjE } 1 
      THEN resolve_tac ctxt @{thms disjI2 } 1
      THEN  assume_tac ctxt 1
      THEN resolve_tac ctxt @{thms disjI1 } 1
      THEN assume_tac ctxt 1
     )
\<close>  

lemma shows "P \<or> Q \<Longrightarrow> Q \<or> P "
apply(tactic \<open>foo_tac @{context} \<close>)
  done
    
ML \<open>
  fun inductive_applications' thy prop =
  let
    fun inductive_apps thy prop =
      let
        val (t,args) = Term.strip_comb prop
      in
        case t of
           Const _ =>
           (t |> (fst o Term.dest_Const)
              |> (fn name => name ^ ".induct")
              |> (fn name => (args, Global_Theory.get_thm thy name))
              |> (fn (args, rule) => if exists (exists_subterm is_Bound) args
                                     then maps (inductive_apps thy) args
                                     else (args, rule) :: maps (inductive_apps thy) args)
              handle ERROR _ => maps (inductive_apps thy) args
                    | TERM _ => maps (inductive_apps thy) args)
         | Abs (n, T, _) => betapply (t, Free (n, T))
                              |> inductive_apps thy
                              |> (fn res => res @ maps (inductive_apps thy) args)
         | _ =>  maps (inductive_apps thy) args
      end
    val transform = map (fn arg => SOME (NONE, (arg, false)))
  in
    prop |> inductive_apps thy
         (* Applications with smaller arguments are considered first *)
         |> sort (fn args =>
                    args |> apply2 fst
                         |> apply2 (map Term.size_of_term)
                         |> apply2 (fn l => Library.foldl (op +) (0, l))
                         |> int_ord)
         |> map (fn (y, z) => (transform y, z))
  end

fun computation_induction_tac' ctxt thy (goal, i) =
    case inductive_applications' thy goal of
          (args, induction) :: _ => 
            DETERM (Induction.induction_tac ctxt true [args] [] [] (SOME [induction]) [] i)
         | [] => no_tac

  
\<close>  
  
fun suma :: "nat\<Rightarrow>nat\<Rightarrow>nat" where
  "suma 0 y = y"|
  "suma (Suc x) y = Suc (suma x y)"

lemma "suma x 0 = suma 0 x"
  apply(induction x )
  apply(auto)
  done
    
lemma "suma x 0 = suma 0 x"
apply(tactic \<open>computation_induction_tac' @{context} @{theory} \<close>)
lemma "suma x y = suma y x"
  apply (induction x y rule: suma.induct)

    
ML \<open> 
  signature WELLFORMED_TERMS =
  sig
    val get: theory -> term list
    val add: term -> theory -> theory
  end;
\<close>

end