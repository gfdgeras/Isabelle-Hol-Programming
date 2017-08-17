theory example42 imports Main
begin
  
inductive palindrome :: "'a list \<Rightarrow> bool" where
  pal0: "palindrome []" |
  pal1: "palindrome [x]" |  
  pal_SS: "palindrome l \<Longrightarrow> palindrome (a # (l @ [a]))"

theorem rev_pal: "palindrome l \<Longrightarrow> rev l = l"
apply (induction rule:palindrome.induct)
apply (auto)
done
end    