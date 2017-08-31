theory ejercicio2 imports Main
begin


notepad
begin
ML_prf \<open> val a = 1 \<close>

ML_prf \<open> val b = a + 1 \<close>

ML_prf \<open> val c = b + 1 \<close>
end

notepad
begin
  fix A B C :: 'a \<Rightarrow> bool
  have \<And>x. A x \<Longrightarrow> B x \<Longrightarrow> C x
  ML_val \<open>
    val {goal, context = goal_ctxt, ...} = @{Isar.goal};
    val (focus as {params, asms, concl, ...}, goal') =
    Subgoal.focus goal_ctxt 1 (SOME [@{binding x}]) goal;
    val [A, B] = #prems focus;
    val [(_, x)] = #params focus;
  \<close>
   sorry
end


notepad
begin
assume ex: \<exists> x. B x
ML_prf \<open>
  val ctxt0 = @{context};
  val (([(_, x)], [B]), ctxt1) = ctxt0
    |> Obtain.result (fn _ => eresolve_tac ctxt0 @{thms exE} 1)
    [@{thm ex}];
\<close>

ML_prf \<open> singleton (Proof_Context.export ctxt1 ctxt0) @{thm refl}; \<close>

ML_prf \<open> Proof_Context.export ctxt1 ctxt0 [Thm.reflexive x]
            handle ERROR msg => (warning msg; []);\<close>
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