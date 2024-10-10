open Printf
open type



  (* Environnements de typage *) 
  type env = (string * ptype) list
  (* Listes d'équations *) 
  type equa = (ptype * ptype) list

   (* printter *) 
  let rec print_type (t : ptype) : string =
    match t with
    Var x -> x
    |Arr (t1 , t2) -> "(" ^ ( print_type t1) ^" -> "^ ( print_type t2) ^")"
    |Nat -> "Nat"

  exception Unexist
  (* Chercher une variable dans l'env*)
  let rec cherche_type (v : string) (e : env) : ptype =
    match e with
    []-> raise Unexist
    | (v1,t1)::q when v1=v -> t1
    |(_,_)::q -> (cherche_type v q)

  (*Occur check*)
  let check_type_var (v :string) (t:ptype) : bool =
    match t with
    Var v1 when v1=v -> true
    |Arr (t1 , t2) -> (check_type_var v t1) || (check_type_var v t2)
    |_ -> false 

  (* remplace une variable par un type dans type *)
let rec substitue_type (t : ptype) (v : string) (t0 : ptype) : ptype =
  match t with
    Var v1 when v1 = v -> t0
  | Var v2 -> Var v2
  | Arr (t1, t2) -> Arr (substitue_type t1 v t0, substitue_type t2 v t0) 
  | Nat -> Nat 

(* remplace une variable par un type dans une liste d'équations*)
let substitue_type_partout (e : equa) (v : string) (t0 : ptype) : equa =
  List.map (fun (x, y) -> (substitue_type x v t0, substitue_type y v t0)) e