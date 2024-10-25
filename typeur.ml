open Printf
open Type
open Ast

(* Environnements de typage *) 
type env = (string * ptype) list
(* Listes d'équations *) 
type equa = (ptype * ptype) list

type equa_zip = ptype * ptype
  

(* printter *) 
let rec print_type (t : ptype) : string =
  match t with
  | TVar x -> x
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^ " -> " ^ (print_type t2) ^ ")"
  | Nat -> "Nat"

exception Unexist
(* Chercher une variable dans l'env*)
let rec cherche_type (v : string) (e : env) : ptype =
  match e with
  | [] -> raise Unexist
  | (v1, t1)::q when v1 = v -> t1
  | (_, _)::q -> (cherche_type v q)

(* Occur check *)
let rec check_type_var (v : string) (t : ptype) : bool =
  match t with
  | TVar v1 when v1 = v -> true
  | Arr (t1, t2) -> (check_type_var v t1) || (check_type_var v t2)
  | _ -> false 

(* Remplace une variable par un type dans type *)
let rec substitue_type (t : ptype) (v : string) (t0 : ptype) : ptype =
  match t with
  | TVar v1 when v1 = v -> t0
  | TVar v2 -> TVar v2
  | Arr (t1, t2) -> Arr (substitue_type t1 v t0, substitue_type t2 v t0) 
  | Nat -> Nat 

(* remplace unee variable par un type dans un zipper d'équations *)
let substitue_type_zip  (v : string) (t0 : ptype) (e : equa_zip) : equa_zip =
  match e with
    (e1, e2) -> (substitue_type e1 v t0, substitue_type e2 v t0)

(* Remplace une variable par un type dans une liste d'équations *)
let substitue_type_partout (e : equa) (v : string) (t0 : ptype) : equa =
  List.map (substitue_type_zip v t0) e

let compteur_var_t : int ref = ref 0
let nouvelle_var_t () : string = compteur_var_t := !compteur_var_t + 1;
"T" ^ (string_of_int !compteur_var_t)

let rec genere_equa (te : pterm) (ty : ptype) (e : env) : equa =
  match te with
  | Var x -> let t_x = cherche_type x e in [(t_x, ty)]
  | Abs (x, t) -> 
      let nv1 : string = nouvelle_var_t () 
      and nv2 : string = nouvelle_var_t () in
      (ty, Arr (TVar nv1, TVar nv2)) :: (genere_equa t (TVar nv2) ((x, TVar nv1) :: e))
  | App (t1, t2) -> 
      let nv : string = nouvelle_var_t () in
      let eq1 : equa = genere_equa t1 (Arr (TVar nv, ty)) e in
      let eq2 : equa = genere_equa t2 (TVar nv) e in
      eq1 @ eq2 

exception Echec_unif of string 

(* Fonction  pour comparer deux types *)
let rec compare_ptype (t1: ptype) (t2: ptype) : bool =
  match (t1, t2) with
  | (TVar v1, TVar v2) -> v1 = v2
  | (Arr (t1a, t1b), Arr (t2a, t2b)) -> compare_ptype t1a t2a && compare_ptype t1b t2b
  | (Nat, Nat) -> true
  | (PList p1, PList p2) -> compare_ptype p1 p2
  | (TPunit, TPunit) -> true
  | (TRef t1, TRef t2) -> compare_ptype t1 t2
  | (Forall (vars1, t1'), Forall (vars2, t2')) -> 
      vars1 = vars2 && compare_ptype t1' t2'
  | (_, _) -> false

let rec unificateur (eq: equa) (sub : env) =
  match eq with 
  | [] -> ([], sub)
  | (t, t1)::q when (compare_ptype t t1) -> unificateur q sub 
  | ((TVar x), td)::q -> 
      if check_type_var x td then raise (Echec_unif ("occurence de " ^ x ^ " dans " ^ (print_type td)))  
      else (
        let new_eq = substitue_type_partout q x td in
        let new_sub = (x, td) :: (List.map (fun (v, t) -> (v, substitue_type td x t)) sub) in
        unificateur new_eq new_sub)
  | (td, (TVar x))::q ->  
      if check_type_var x td then raise (Echec_unif ("occurence de " ^ x ^ " dans " ^ (print_type td)))  
      else (
        let new_eq = substitue_type_partout q x td in
        let new_sub = (x, td) :: (List.map (fun (v, t) -> (v, substitue_type td x t)) sub) in
        unificateur new_eq new_sub)
  | (Arr (t1, t2), Arr (t3, t4))::q -> unificateur ((t1, t3)::(t2, t4)::q) sub
  | _ -> raise (Echec_unif "Non typable")

exception Time_out

let rec solve_system (eqs : equa) (substitutions_acc : env) : (equa * env) option =
  match eqs with
  | [] -> Some ([], substitutions_acc)  (* Le système est résolu si la liste est vide *)
  | _ -> 
      try
        (* Appel à la fonction d'unification pour une étape *)
        let (next_eqs, new_substitutions) = unificateur eqs substitutions_acc in
        solve_system next_eqs new_substitutions  (* Résoudre récursivement le système *)
      with Failure _ -> None  (* En cas d'échec d'unification, retourner None *)


(* Fonction qui résout un système avec timeout et substitutions *)
(* let solve_with_timeout (eqs : equa) (timeout_duration : float) : (equa * env) option =
  timeout (fun () -> solve_system eqs []) timeout_duration *)

  
let inference (env: env) (term : pterm) : string =
  (* Étape 1: Générer une nouvelle variable de type qui représentera le type à inférer *)
  let tvar = TVar (nouvelle_var_t ()) in
  
  (* Étape 2: Générer les équations basées sur le terme et son type supposé (tvar) *)
  let equations = genere_equa term tvar env in
    
  (* Étape 3: Résoudre les équations en utilisant l'unificateur *)
  match solve_system equations [] with
    | Some (_, substitutions) -> "le terme " ^ (print_term term) ^ " est bien typé"
    | None -> failwith "Unification échouée : le terme n'est pas typable"