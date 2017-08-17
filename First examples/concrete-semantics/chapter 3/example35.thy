theory example35 imports Main
begin
(*Ejercicio obtenido de repositorio externo*)
type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"
datatype aexp2 = N2 int | V2 vname | PlusPlus2 vname | Plus2 aexp2 aexp2 | 
 Times2 aexp2 aexp2 | Div2 aexp2 aexp2 

fun aval2 :: "aexp2 \<Rightarrow>state \<Rightarrow> (val \<times> state) option" where
  "aval2 (N2 a) s = Some (a, s)" |
  "aval2 (V2 x) s = Some (s x, s)" |
  "aval2 (PlusPlus2 x) s = Some (s x, s(x:= 1 + (s x)))" |
  "aval2 (Plus2 a b) s = 
          (case (aval2 a s, aval2 b s) of 
          (None, Some q)\<Rightarrow> None |
          (Some p, None)\<Rightarrow> None |
          (Some p, Some q) \<Rightarrow> Some ((fst p + fst q), (\<lambda>x.((snd p) x) + ((snd q) x) - (s x))))" |
  "aval2 (Times2 a b) s = 
          (case (aval2 a s, aval2 b s) of 
          (None, Some q) \<Rightarrow> None |
          (Some p, None) \<Rightarrow> None |
          (Some p, Some q) \<Rightarrow> Some ((fst p * fst q), (\<lambda>x.((snd p) x) + ((snd q) x) - (s x))))" |
  "aval2 (Div2 a b) s =
          (case (aval2 a s, aval2 b s) of 
          (None, Some q) \<Rightarrow> None |
          (Some p, None) \<Rightarrow> None |
          (Some p, Some q) \<Rightarrow> 
          (if fst q = 0 then 
              None 
          else Some ((fst p div fst q), (\<lambda>x.((snd p) x) + ((snd q) x) - (s x)))))"
end
  