open Printf
open Type
open Ast

(* Environnements de typage *) 
type env = (string * ptype) list
(* Listes d'équations *) 
type equa = (ptype * ptype) list

type equa_zip = ptype * ptype

let rec print_equation (equation:equa) : unit =
  match equation with
  | [] -> ()
  | (t1, t2)::q -> printf "%s = %s\n" (print_type t1) (print_type t2); print_equation q

exception Unexist
(* Chercher une variable dans l'env *)
let rec cherche_type (v : string) (e : env) : ptype =
  match e with
  | [] -> raise Unexist
  | (v1, t1)::q when v1 = v -> t1
  | (_, _)::q -> cherche_type v q

(* Occur check *)
let rec check_type_var (v : string) (t : ptype) : bool =
  match t with
  | TVar v1 when v1 = v -> true  
  | Arr (t1, t2) -> (check_type_var v t1) || (check_type_var v t2)  
  | PList t1 -> check_type_var v t1  
  | TRef t1 -> check_type_var v t1  
  | Forall (vars, t1) ->  
      if List.mem v vars then false  (* Si `v` est lié par Forall, il n'est pas libre ici *)
      else check_type_var v t1
  | _ -> false  

(* Remplace une variable par un type dans type *)
let rec substitue_type (t : ptype) (v : string) (t0 : ptype) : ptype =
  match t with
  | TVar v1 when v1 = v -> t0  (* Substitution de v par t0 *)
  | TVar v2 -> TVar v2  (* Conserve les autres variables de type inchangées *)
  | Arr (t1, t2) -> Arr (substitue_type t1 v t0, substitue_type t2 v t0)  (* Substitution récursive dans Arr *)
  | Nat -> Nat  (* Aucun changement pour Nat *)
  | PList t1 -> PList (substitue_type t1 v t0)  (* Substitution dans les types de liste *)
  | TRef t1 -> TRef (substitue_type t1 v t0)  (* Substitution dans les types de référence *)
  | Forall (vars, t1) -> 
      if List.mem v vars then 
        Forall (vars, t1)  (* Si v est lié dans Forall, ne pas substituer *)
      else 
        Forall (vars, substitue_type t1 v t0)  (* Sinon, appliquer la substitution dans t1 *)

(* remplace une variable par un type dans un zipper d'équations *)
let substitue_type_zip  (v : string) (t0 : ptype) (e : equa_zip) : equa_zip =
  match e with
  | (e1, e2) -> (substitue_type e1 v t0, substitue_type e2 v t0)

(* Remplace une variable par un type dans une liste d'équations *)
let substitue_type_partout (e : equa) (v : string) (t0 : ptype) : equa =
  List.map (substitue_type_zip v t0) e

let compteur_var_t : int ref = ref 0
let nouvelle_var_t () : string =
  compteur_var_t := !compteur_var_t + 1;
  "T" ^ (string_of_int !compteur_var_t)

(* liste des vars libres *)
let rec free_type_vars (t : ptype) : string list =
  match t with
  | TVar x -> [x]
  | Arr (t1, t2) -> free_type_vars t1 @ free_type_vars t2
  | Nat -> []
  | PList t -> free_type_vars t
  | TPunit -> []
  | TRef t -> free_type_vars t
  | Forall (vars, t) -> List.filter (fun v -> not (List.mem v vars)) (free_type_vars t)

(* Fonction de généralisation *)
let generalisation (env : env) (t : ptype) : ptype =
  let env_vars = List.map fst env in
  let free_vars_in_t = List.filter (fun v -> not (List.mem v env_vars)) (free_type_vars t) in
  match free_vars_in_t with
  | [] -> t  
  | vars -> Forall (vars, t)  (* Ajout de ∀ pour chaque variable libre *)

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


(*barendregtisation d'un type*)
(*∀ x1, x2, ..., xn. T  si tout xi different de y alors y est liee à T *) 
let renomme_variables_liees (t:ptype) : ptype =
  let rec aux (t:ptype) (vars_libres:string list) : ptype =
  match t with
    TVar v when est_liee v vars_libres -> TVar (nouvelle_var ())
  | TVar v -> TVar v
  | Arr (t1, t2) -> Arr (aux t1 vars_libres, aux t2 vars_libres)
  | Nat -> Nat
  | TPunit -> TPunit
  | TRef t -> TRef (aux t vars_libres)
  | PList t -> PList (aux t vars_libres)
  | Forall (v, t) -> Forall (v, aux t (v@vars_libres))
    and est_liee (v:string) (vars_libres:string list) : bool =
      (*Toute variable non libre est liée*)
      not (List.exists (fun x -> x = v) vars_libres)
  in aux t []

(*ouvre un type*)
let ouvre_type (t:ptype) : ptype = 
  match t with
  | Forall (_, t) -> t
  | _ -> t

let barendregtisation (t:ptype) : ptype = ouvre_type (renomme_variables_liees t)

exception Time_out


(* Fonction qui résout un système avec timeout et substitutions *)
(* let solve_with_timeout (eqs : equa) (timeout_duration : float) : (equa * env) option =
  timeout (fun () -> solve_system eqs []) timeout_duration *)


      let rec genere_equa (te : pterm) (ty : ptype) (e : env) : equa =
        match te with
        | Var x -> 
            let t_x = cherche_type x e in [(t_x, ty)]
        | Abs (x, t) -> 
            let nv1 : string = nouvelle_var_t () 
            and nv2 : string = nouvelle_var_t () in
            (ty, Arr (TVar nv1, TVar nv2)) :: (genere_equa t (TVar nv2) ((x, TVar nv1) :: e))
        | App (t1, t2) -> 
            let nv : string = nouvelle_var_t () in
            let eq1 : equa = genere_equa t1 (Arr (TVar nv, ty)) e in
            let eq2 : equa = genere_equa t2 (TVar nv) e in
            eq1 @ eq2
        | N _ -> [(ty, Nat)]  (* Les nombres sont typés Nat *)
        | Add (t1, t2) -> 
            let t_term1 = genere_equa t1 Nat e in 
            let t_term2 = genere_equa t2 Nat e in 
            (ty, Nat) :: (t_term1 @ t_term2)
        | Sub (t1, t2) -> 
            let t_term1 = genere_equa t1 Nat e in 
            let t_term2 = genere_equa t2 Nat e in 
            (ty, Nat) :: (t_term1 @ t_term2)
        | Mult (t1, t2) -> 
            let t_term1 = genere_equa t1 Nat e in 
            let t_term2 = genere_equa t2 Nat e in 
            (ty, Nat) :: (t_term1 @ t_term2)
        | IfZero (cond, cons, altern) -> 
            let eq1 : equa = genere_equa cond Nat e in
            let eq2 : equa = genere_equa cons ty e in
            let eq3 : equa = genere_equa altern ty e in
            eq1 @ eq2 @ eq3
        | IfEmpty (cond, cons, altern) -> 
            let nv : ptype = PList (TVar (nouvelle_var_t ())) in
            let eq1 : equa = genere_equa cond nv e in
            let eq2 : equa = genere_equa cons ty e in
            let eq3 : equa = genere_equa altern ty e in
            eq1 @ eq2 @ eq3
        | Let (x, t1, t2) -> 
            (* let t1_type_opt = typage t1 e in  *)
            let name = nouvelle_var() in 
            let nVar = TVar name in 
            let nEnv = (x,nVar):: e in 
            let eq = genere_equa t1 nVar nEnv in 

            (match (solve_system eq nEnv) with 
             | Some (_,equation) ->  let inferred_type_opt = List.assoc_opt name equation in 
                match inferred_type_opt with
                  |Some inferred_type -> (let gen_t1_type = generalisation e inferred_type in 
                      let new_env = (x, gen_t1_type) :: nEnv in 
                    genere_equa t2 ty new_env)
                  | None -> failwith "Échec du typage dans Let"
             | None -> failwith "Échec du typage dans Let")
      | Head p -> let nv = nouvelle_var () in
      let equa_e = genere_equa p (PList (TVar nv)) e in
      (ty, TVar nv) :: equa_e
      | Tail p -> let nv = PList (TVar (nouvelle_var ())) in
        let equa_e = genere_equa p nv e in
        (ty, nv) :: equa_e
        | PL l -> 
          (match l with
            Empty -> [ty, PList (TVar (nouvelle_var ()))]
            | Cons (head, tail) -> let nv = TVar (nouvelle_var ()) in 
            let equa_head = genere_equa head nv e in
            let equa_tail = genere_equa (PL tail) (PList nv) e in
            (ty, PList nv) :: equa_head @ equa_tail)
        
        and  unificateur (eq: equa) (sub : env) =
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
        |(Forall(v1,t1),Forall(v2,t2))::q -> unificateur ((barendregtisation (Forall(v1,t1)), barendregtisation (Forall(v2,t2)))::q) sub 
        |(Forall(v1,t1),t2)::q -> unificateur (((barendregtisation (Forall(v1,t1))), t2)::q) sub
        |(t1,Forall(v1,t2))::q -> unificateur ((t1 , barendregtisation (Forall(v1,t2)))::q) sub
        | (PList t1, PList t2)::q -> 
          let eq_with_inner_types = (t1, t2) :: q in
          unificateur eq_with_inner_types sub
        |(t1,(PList t2))::q ->  raise (Echec_unif "type non unifiable")
        |((PList t1),t2)::q->  raise (Echec_unif "type non unifiable")
        |(TPunit,TPunit)::q-> unificateur q sub
        |(t,TPunit)::q-> raise (Echec_unif "type non unifiable")
        |(t,TPunit)::q-> raise (Echec_unif "type non unifiable")
        | _ -> raise (Echec_unif "Non typable")
        and solve_system (eqs : equa) (substitutions_acc : env) : (equa * env) option =
          match eqs with
          | [] -> Some ([], substitutions_acc)  (* Le système est résolu si la liste est vide *)
          | _ -> 
              try
                (* Appel à la fonction d'unification pour une étape *)
                let (next_eqs, new_substitutions) = unificateur eqs substitutions_acc in
                solve_system next_eqs new_substitutions  (* Résoudre récursivement le système *)
              with Failure _ -> None  (* En cas d'échec d'unification, retourner None *)
        
        and inference (env: env) (term : pterm) : (ptype option * equa) =
          let name = (nouvelle_var_t ()) in 
          let tvar = TVar (name) in
          let equations = genere_equa term tvar env in
          match solve_system equations [] with
          | Some (_, substitutions) -> 
              (* Trouver le type inféré pour `tvar` *)
              let inferred_type_opt = List.assoc_opt name substitutions in
              (inferred_type_opt, equations)  (* Retourner aussi les équations générées *)
          | None -> (None, equations)  (* Retourner None et les équations en cas d'échec *)
        
        and  typage (p : pterm) (e : env) : ptype option =
            let solve = inference e p in
              match solve with 
                | (Some t,e) -> Some t
                | (None ,e)-> None 

let test_let_example () =
  let env = [] in
  let term = Let ("id", Abs ("x", Var "x"), App (Var "id", N 5)) in

  (* Appeler la fonction d'inférence qui retourne le type et les équations *)
  let (inferred_type_opt, equations) = inference env term in

  (* Affichage des équations générées *)
  Printf.printf "Generated equations:\n";
  List.iter (fun (t1, t2) -> Printf.printf "%s = %s\n" (print_type t1) (print_type t2)) equations;

  match inferred_type_opt with
  | Some inferred_type ->
      (* Afficher le type inféré *)
      Printf.printf "Type inferred: %s\n" (print_type inferred_type)
  | None ->
      Printf.printf "Failed to infer type.\n"

(* Exécuter le test *)
let () = test_let_example ()
