theory example44 imports Main
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

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  it0: "iter r 0 x x" |
  it_SS: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

theorem "star r x y \<Longrightarrow> \<exists> n. iter r n x y"
apply (induction rule:star.induct)
apply (auto intro: it0 it_SS)
done  
  
end
  