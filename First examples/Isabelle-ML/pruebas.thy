theory pruebas imports Main
begin
lemma ex: "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume "A \<and> B"
  then obtain B and A ..
  then show "B \<and> A" ..
qed

ML_val \<open>
  val thy = @{theory};
  val ctxt = @{context};
  val prf =
    Proof_Syntax.read_proof thy true false
      "impI \<cdot> _ \<cdot> _ \<bullet> \
      \   (\<^bold>\<lambda>H: _. \
      \     conjE \<cdot> _ \<cdot> _ \<cdot> _ \<bullet> H \<bullet> \
      \       (\<^bold>\<lambda>(H: _) Ha: _. conjI \<cdot> _ \<cdot> _ \<bullet> Ha \<bullet> H))";
  val thm =
    prf
    |> Reconstruct.reconstruct_proof ctxt @{prop "A \<and> B \<longrightarrow> B \<and> A"}
    |> Proof_Checker.thm_of_proof thy
    |> Drule.export_without_context;
\<close>
ML \<open>
  fun factorial 0 = 1
   | factorial n = n * factorial (n - 1)
\<close>
ML_val \<open> factorial 100 \<close>
ML_command \<open>writeln (string_of_int (factorial 100))\<close>

notepad
begin
ML_val \<open> factorial 100 \<close>
ML_command \<open>writeln (string_of_int (factorial 100))\<close>
end

notepad
begin
fix A B :: bool
assume a:A and b:B
have "A \<and> B"
apply (tactic \<open> resolve_tac @{context} @{thms conjI } 1 \<close> )
using a apply (tactic \<open> resolve_tac @{context} facts 1 \<close> )
using b apply (tactic \<open> resolve_tac @{context} facts 1 \<close> )
done

have "A \<and> B"
using a and b
ML_val \<open> @{Isar.goal} \<close>
apply (tactic \<open> Method.insert_tac @{context} facts 1 \<close> )
apply (tactic \<open> (resolve_tac @{context} @{thms conjI } THEN_ALL_NEW
assume_tac @{context}) 1 \<close> )
done
end


end
  