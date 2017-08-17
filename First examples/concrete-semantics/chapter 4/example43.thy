theory example43 imports Main
(*Checar ejercicio*)
begin
inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>  bool" for r where
  refl: "star r x x" |
  step: "r x y \<Longrightarrow> star r y z  \<Longrightarrow> star r x z"

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow>  bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow>  bool" for r where
  refl': "star' r x x" |
  step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma star_star': "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
apply (induction rule:star.induct)
apply (auto intro: refl step)
done

lemma star'_star: "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
apply (induction rule:star'.induct)
apply (auto intro: refl' step')
done
      
theorem "star r x y \<Longrightarrow> star' r x y"
apply (induction rule:star.induct)
apply (auto simp add: refl' intro:  star'_star)
done

theorem "star' r x y \<Longrightarrow> star r x y"
apply (induction rule:star'.induct)
apply (auto simp add: refl intro: star_star')
done
end
  