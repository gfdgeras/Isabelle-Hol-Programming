theory example26 imports Main
begin
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []" |
  "contents (Node l v r) = v # ((contents l) @ (contents r))"
  
  
fun treesum :: "nat tree \<Rightarrow> nat" where
  "treesum Tip = 0" |
  "treesum (Node l v r) = v + (treesum l) + (treesum r)"

lemma "treesum t = listsum(contents t)"
  apply (induction t)
  apply auto
  oops
    
end