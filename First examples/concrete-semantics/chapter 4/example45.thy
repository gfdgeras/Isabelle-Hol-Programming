theory example45 imports Main
begin
  
datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
  S_0: "S []" |
  S_wrp: "S w \<Longrightarrow> S (a # w @ [b])" |
  S_cc: "S w \<Longrightarrow> S u \<Longrightarrow> S (w @ u)"

inductive T :: "alpha list \<Rightarrow> bool" where
  T_0: "T []" |
  T_intr: "T w \<Longrightarrow> T u \<Longrightarrow> T (w @ [a] @ u @ [b])" 

lemma T_comm: "T u \<Longrightarrow> T w \<Longrightarrow> T (w @ u)"
apply (induction  rule:T.induct)
apply (simp)
apply (metis T_intr append_assoc)
done

theorem T_S: "T w \<Longrightarrow> S w"
apply (induction rule:T.induct)
apply (auto intro: S_0 S_cc S_wrp)
done

theorem S_T: "S w \<Longrightarrow> T w"
apply (induction rule:S.induct)
apply (simp add: T_0)
apply (metis T_0 T_intr append_Cons append_Nil)
apply (auto intro: T_comm)
done

theorem "S w = T w"
apply (auto simp add: S_T T_S)
done
end
  