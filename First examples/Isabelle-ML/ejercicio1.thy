theory ejercicio1 imports Main
begin

(*VARIABLES*)

ML_val \<open> 
  (*static compile-time context -- for testing only*)
  val ctxt0 = @{context};
  (*locally fixed parameters -- no type assignment yet*)
  val ([x, y], ctxt1) = ctxt0 |> Variable.add_fixes ["x", "y"];
  (*t1: most general fixed type; t1’: most general arbitrary type*)
  val t1 = Syntax.read_term ctxt1 "x";
  val t1' = singleton (Variable.polymorphic ctxt1) t1;
  (*term u enforces specific type assignment*)
  val u = Syntax.read_term ctxt1 "(x::nat) \<equiv> y";
  (*official declaration of u -- propagates constraints etc.*)
  val ctxt2 = ctxt1 |> Variable.declare_term u;
  val t2 = Syntax.read_term ctxt2 "x"; (*x::nat is enforced*)
\<close> 

ML_val \<open> 
  val ctxt0 = @{context};
  val ([x1, x2, x3], ctxt1) =
    ctxt0 |> Variable.variant_fixes ["x", "x", "x"];
\<close>
  
notepad
begin
ML_prf 
\<open>
  val ctxt0 = @{context};
  val ([x1], ctxt1) = ctxt0 |> Variable.add_fixes ["x"];
  val ([x2], ctxt2) = ctxt1 |> Variable.add_fixes ["x"];
  val ([x3], ctxt3) = ctxt2 |> Variable.add_fixes ["x"];
  val ([y1, y2], ctxt4) =
    ctxt3 |> Variable.variant_fixes ["y", "y"];
\<close> 
end
(*ASSUMPTIONS*)
ML_val \<open>
(*static compile-time context -- for testing only*)
val ctxt0 = @{context};
val ([eq], ctxt1) =
  ctxt0 |> Assumption.add_assumes [@{cprop "x \<equiv> y"}];
val eq' = Thm.symmetric eq;
(*back to original context -- discharges assumption*)
val r = Assumption.export false ctxt1 ctxt0 eq';
\<close>
  
ML_val \<open>
(*static compile-time context -- for testing only*)
val ctxt0 = @{context};
val ([eq], ctxt1) =
  ctxt0 |> Assumption.add_assumes [@{cprop "A\<and>B  \<equiv> B\<and>A"}];
val eq' = Thm.symmetric eq;
val r = Assumption.export false ctxt1 ctxt0 eq';
\<close> 
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
  
end                                      