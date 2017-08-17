theory example51 imports Main 
begin
  
lemma assumes T: "\<forall> x y. T x y \<or> T y x"
 and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
 and TA: "\<forall> x y. T x y \<longrightarrow> A x y" and "A x y"
 shows "T x y"
proof (rule ccontr)
  assume "\<not> T x y"
  from this and T have "T y x" by (blast)
  from this and TA have "A y x" by (blast)
  from this and `A x y` and A have "x = y" by (blast)
  from this and `\<not> T x y` and `T y x` show "False" by (blast)
qed


end
  