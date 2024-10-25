open Type
open Ast

(* ***EXEMPLES*** *)  
let ex_id : pterm = Abs ("x", Var "x") 
let ex_k : pterm = Abs ("x", Abs ("y", Var "x")) 
let ex_s : pterm = Abs ("x", Abs ("y", Abs ("z", App (App (Var "x", Var "z"), App (Var "y", Var "z")))))
let ex_nat1 : pterm = App (Abs ("x", Add(Var "x", N 1)), N 3)
let ex_nat2 : pterm = Abs ("x", Add( Var "x", Var "x"))
let ex_omega : pterm = App (Abs ("x", App (Var "x", Var "x")), Abs ("y", App (Var "y", Var "y")))
let succ_term = Abs ("n", Abs ("f", Abs ("x", App (Var "f", App (App (Var "n", Var "f"), Var "x"))))) 
let add_term =  Abs ("m", Abs ("n", Abs ("f", Abs ("x", App (App (Var "m", Var "f"), App (App (Var "n", Var "f"), Var "x"))))))