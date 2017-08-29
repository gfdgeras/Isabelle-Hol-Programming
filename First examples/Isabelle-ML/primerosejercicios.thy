theory primerosejercicios imports Main
begin
(*primeros ejercicios*)
ML\<open>
  val x = 42;
  val y = true;
  writeln (@{make_string} {x = x, y = y});
  @{print} {x = x, y = y};
  @{print tracing} {x = x, y = y};
\<close>
  
ML \<open>
val s =
  Buffer.empty
  |> Buffer.add "digits: "
  |> fold (Buffer.add o string_of_int) (0 upto 9)
  |> Buffer.content;
@{assert} (s = "digits: 0123456789");
\<close>

ML \<open>
warning(cat_lines 
  ["ESTO ES UNA ADVERTENCIA",
   "BLABLABLABLABALBALBAL",
   "dfsdfsafsa dsfgsadfa",
   "fin !"]);
\<close>
  
ML \<open>
warning (Pretty.string_of (Pretty.para
  "Beware the Jabberwock, my son! \
  \The jaws that bite, the claws that catch! \  
  \Beware the Jubjub Bird, and shun \
  \The frumious Bandersnatch!"))
\<close>

ML \<open>
  fun undefined _ = raise Match
\<close>
ML \<open>
  fun undefined _ = @{undefined}
\<close>    

ML \<open>
  val s = "\<A>";
  @{assert} (length (Symbol.explode s) = 1);
  @{assert} (size s = 4);
\<close>
ML \<open>
  val items = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
  val list1 = fold cons items [];
  @{assert} (list1 = rev items);
  val list2 = fold_rev cons items [];
  @{assert} (list2 = items);
\<close>

end
  