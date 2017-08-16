theory example28 imports Main
begin
fun intersperse :: "'a\<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse _ Nil = []" |
  "intersperse x (h1#h2#t) = h1 # x  # (intersperse x (h2 # t))" |
  "intersperse x xs = []"
  
value "intersperse a [b,c,d,e]"
  
theorem map_intersperse: "map f (intersperse a l) = intersperse (f a) (map f l)"
apply (induction l rule:intersperse.induct)
apply (auto)
done
end
  