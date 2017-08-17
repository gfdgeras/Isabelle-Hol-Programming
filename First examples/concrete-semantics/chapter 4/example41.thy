theory example41 imports Main
begin
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
    "set Tip = {}" |
    "set (Node l x r) =  {x} \<union> set l \<union> set r"

fun ord :: "int tree \<Rightarrow> bool" where
  "ord Tip = True" |
  "ord (Node l x r) = ((\<forall> y \<in> set l. x \<ge> y) \<and> (\<forall> y \<in>  set r. y \<ge> x) \<and> ord l \<and> ord r)"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
  "ins a Tip = Node Tip a Tip" |
  "ins a (Node r x l) = 
      (if a = x then 
        Node r x l 
      else if x > a then 
        Node (ins a r) x l 
      else Node r x (ins a l))"

theorem set_ins[simp]: "set (ins x t) = {x} \<union> set t"
apply (induction t)
apply (auto)
done

theorem "ord t \<Longrightarrow> ord (ins i t)"
apply (induction t)
apply (auto)
done
end
  