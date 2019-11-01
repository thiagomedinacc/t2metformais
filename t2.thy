theory t2
imports Main
begin

(*Problema 1*)
primrec soma::"nat \<Rightarrow> nat \<Rightarrow> nat" where
soma1: "soma x 0 = x"|
soma2: "soma x (Suc y) = Suc (soma x y)"

value "soma 0 0" (* OK *)

(* soma(x,y) = x + y *)
theorem t1 "soma x y = x + y"
proof (induct y)
  show " soma x 0 = x + 0"
  proof -
    have "soma x 0 = x" by (simp only:soma1)
    also have "... = x + 0" by (simp)
    finally show "soma x 0 = x + 0" by (simp)
  qed
next
  fix y::nat
  assume HI: "soma x y = x + y"
  show "soma x (Suc y) = x + Suc y"
  proof -
    have "soma x (Suc y) = Suc (soma x y)" by (simp only: soma2)
    also have "... = Suc x + y" by (simp only: HI)
    also have "... = x + Suc y" by (simp)
    finally show "soma x (Suc y) = x + Suc y" by (simp)
  qed
qed (*erro*)



(* soma(x,y) = soma(y,x) *)
theorem t2 " soma x y = soma y x"
proof (induct y)
  show "\<forall>x. soma x 0 = soma 0 x"
  proof-
    have "soma x 0 = x by (soma1)
    also have "... = 0 + x by (simp)
  



(* soma (x,0) = 0 *)

(* soma (0,x) = x *)

(* soma(x,soma(y,z)) = soma(soma (x,y),z) *)





(*Problema 2*)
primrec mult::"nat \<Rightarrow> nat \<Rightarrow> nat" where
"mult x 0 = 0"|
"mult x (Suc y) = soma x (mult x y)"

value " mult 8 3 " (* OK *)


(* mult(x,y) = x * y *)

(* mult(x,y) = mult(y,x) *)

(* mult (x,1) = 1 *)

(* mult (1,x) = x *)

(* mult(x,mult(y,z)) = mult(mult (x,y),z) *)
end