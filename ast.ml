
type 'a plist = Empty | Cons of 'a * 'a plist

type pterm = 
  Var of string
  | App of pterm * pterm
  | Abs of string * pterm
  | N of int 
  | Add of pterm * pterm
  | Sub of pterm * pterm
  |Mult of pterm * pterm
  |Fix of pterm
  | PL of pterm plist
  | Head of pterm
  | Tail of pterm
  | IfZero of pterm * pterm * pterm
  | IfEmpty of pterm * pterm * pterm
  | Let of string * pterm * pterm

(* Printer de terme *)
let rec print_term (t : pterm) : string =
  match t with
    | Var x -> x
    | N n -> string_of_int n
    | App (t1, t2) -> "(" ^ (print_term t1) ^ " " ^ (print_term t2) ^ ")"
    | Abs (x, t) -> "(λ" ^ x ^ " -> " ^ (print_term t) ^ ")"
    | Add (t1, t2) -> "(" ^ (print_term t1) ^ " + " ^ (print_term t2) ^ ")"
    | Sub (t1, t2) -> "(" ^ (print_term t1) ^ " - " ^ (print_term t2) ^ ")"
    | Mult (t1, t2) -> "(" ^ (print_term t1) ^ " 
    * " ^ (print_term t2) ^ ")"
    | IfZero (t1, t2, t3) -> "(if " ^ (print_term t1) ^ " = 0 then " ^ (print_term t2) ^ " else " ^ (print_term t3) ^ ")"
    | IfEmpty (t1, t2, t3) -> "(if " ^ (print_term t1) ^ " is empty then " ^ (print_term t2) ^ " else " ^ (print_term t3) ^ ")"
    | Let (x, t1, t2) -> "(let " ^ x ^ " = " ^ (print_term t1) ^ " in " ^ (print_term t2) ^ ")"
    |Fix t -> "fix" ^ (print_term t) 
    | PL l -> "[" ^ print_list l ^ "]"
    | Head l -> "(head " ^ (print_term l) ^ ")"
    | Tail l -> "(tail " ^ (print_term l) ^ ")"
    and print_list (l : pterm plist) : string =
      match l with
        Empty -> ""
        | Cons (t, Empty) -> print_term t
        | Cons (t, l) -> (print_term t) ^ "; " ^ (print_list l)
    and print_sequence (l : pterm list) : string =
      match l with
        [] -> ""
        | [t] -> print_term t
        | t::q -> (print_term t) ^ "; " ^ (print_sequence q)
        

(* Compteur de variables et création de nouvelles variables *)
let compteur_var : int ref = ref 0
let nouvelle_var () : string =
  compteur_var := !compteur_var + 1;
  "X" ^ (string_of_int !compteur_var)

type env_name_var = (string * string) list

(* Chercher le nom d'une variable dans l'environnement *)
let find_name (name:string) (name_env: env_name_var) : string =
  let aux (current_name:string) (binding:string*string) : string =
    if current_name = fst binding then snd binding
    else current_name
  in List.fold_left aux name name_env

(* Fonction d'alpha-conversion *)
let rec alpha_conversion (t : pterm) (env : env_name_var) : pterm =
  match t with
  | Var x -> Var (find_name x env)
  | Abs (x, t_body) ->
      let x' = nouvelle_var () in
      let new_env = (x, x') :: env in
      Abs (x', alpha_conversion t_body new_env)
  | App (t1, t2) -> App (alpha_conversion t1 env, alpha_conversion t2 env)
  | Add (t1, t2) -> Add (alpha_conversion t1 env, alpha_conversion t2 env)
  | Sub (t1, t2) -> Sub (alpha_conversion t1 env, alpha_conversion t2 env)
  |Mult (t1,t2) -> Mult (alpha_conversion t1 env , alpha_conversion t2 env)
  | IfZero (t1, t2, t3) -> 
      IfZero (alpha_conversion t1 env, alpha_conversion t2 env, alpha_conversion t3 env)
  | IfEmpty (t1, t2, t3) -> 
      IfEmpty (alpha_conversion t1 env, alpha_conversion t2 env, alpha_conversion t3 env)
  | Let (x, t1, t2) ->
      let x' = nouvelle_var () in
      let new_env = (x, x') :: env in
      Let (x', alpha_conversion t1 env, alpha_conversion t2 new_env)
  |Fix t -> Fix (alpha_conversion t env)
  | N n -> N n


(* Fonction pour récupérer les variables libres dans un terme *)
let rec free_vars (t : pterm) : string list =
  match t with
  | Var x -> [x]  
  | Abs (x, body) -> List.filter (fun v -> v <> x) (free_vars body)  
  | App (t1, t2) -> (free_vars t1) @ (free_vars t2) 
  | N _ -> []  
  | Add (t1, t2) -> (free_vars t1) @ (free_vars t2)  
  | Sub (t1, t2) -> (free_vars t1) @ (free_vars t2)  
  | Mult (t1, t2) -> (free_vars t1) @ (free_vars t2)  (* Multiplication *)
  | Fix (Abs (f, body)) -> List.filter (fun v -> v <> f) (free_vars body)  (* Récursion : on exclut f des variables libres *)
  | PL l -> free_vars_list l (* Listes : combiner les variables libres de chaque élément *)
  | Head t -> free_vars t  
  | Tail t -> free_vars t  
  | IfZero (cond, t_then, t_else) -> (free_vars cond) @ (free_vars t_then) @ (free_vars t_else)  
  | IfEmpty (cond, t_then, t_else) -> (free_vars cond) @ (free_vars t_then) @ (free_vars t_else)  
  | Let (x, t1, t2) -> (free_vars t1) @ (List.filter (fun v -> v <> x) (free_vars t2))
  and  free_vars_list(l: pterm plist) : string list =
      match l with 
      |Empty -> []
      |Cons (t,ts)-> (free_vars t) @ (free_vars_list ts) 


(* Substitution de variable par un terme, évitant la capture de variables *)
let rec substitution (x : string) (n : pterm) (t : pterm) : pterm =
  match t with
  | Var v when v = x -> n  (* Si la variable correspond, on la remplace par le terme *)
  | Var v -> Var v  (* Sinon, on laisse la variable inchangée *)

  | Abs (y, body) when y = x -> Abs (y, body)  (* Pas de substitution dans les variables liées *)
  
  | Abs (y, body) ->
      if List.mem y (free_vars n) then
        (* On renomme `y` pour éviter la capture de variable si elle est libre dans `n` *)
        let y' = nouvelle_var () in
        let body' = substitution y (Var y') body in
        Abs (y', substitution x n body')
      else
        Abs (y, substitution x n body)

  | App (t1, t2) -> App (substitution x n t1, substitution x n t2)

  | N num -> N num  (* Les nombres restent inchangés *)

  | Add (t1, t2) -> Add (substitution x n t1, substitution x n t2)
  | Sub (t1, t2) -> Sub (substitution x n t1, substitution x n t2)
  | Mult (t1, t2) -> Mult (substitution x n t1, substitution x n t2)
  |PL l -> PL (substitution_list x n l)
  |Head t -> Head (substitution x n t)
  |Tail t-> Tail (substitution x n t)
  |Fix (t)-> Fix (substitution x n t)

  | IfZero (cond, t_then, t_else) ->
      IfZero (substitution x n cond, substitution x n t_then, substitution x n t_else)

  | IfEmpty (cond, t_then, t_else) ->
      IfEmpty (substitution x n cond, substitution x n t_then, substitution x n t_else)

  | Let (y, t1, t2) ->
      if y = x then
        Let (y, substitution x n t1, t2)
      else if List.mem y (free_vars n) then
        let y' = nouvelle_var () in
        let t2' = substitution y (Var y') t2 in
        Let (y', substitution x n t1, substitution x n t2')
      else
        Let (y, substitution x n t1, substitution x n t2)
  and substitution_list (v:string) (p:pterm) (l:pterm plist) : (pterm plist) =
    (match l with
      | Empty -> Empty
      | Cons (t, ts) -> Cons (substitution v p t, substitution_list v p ts))

(* Détection des valeurs *)
let rec isValue(p:pterm) : bool =
  match p with
  | Var _ -> true
  | Abs(_,_) -> true
  | N _ -> true
  | App (Var(x), t') -> isValue t'
  | _ -> false 

(* Réduction beta *)
let rec beta_reduced (p:pterm) : pterm = 
  match p with
  | App (m, n) -> let m' = beta_reduced m in let n' = beta_reduced n in 
      (match m' with
        | Abs (vn, at) when isValue n' -> beta_reduced (substitution vn n' at)
        | _ -> beta_reduced (App (m', n'))
      )
  | _ -> p

(* Fonction de réduction Call-by-Value qui implémente la stratégie LtR-CbV *)
let rec ltr_cbv_step (t : pterm) : pterm option =
  match t with
  (* Beta reduction *)
  | App (Abs (x, body), v) when isValue v ->
      Some (substitution x v body)
  | App (m, n) ->
      (* Si la partie gauche peut être réduite, on réduit cette partie *)
      (match ltr_cbv_step m with
      | Some m' -> Some (App (m', n))
      | None ->
          (* Sinon, si m est une valeur, on tente de réduire la partie droite *)
          (match ltr_cbv_step n with
          | Some n' -> Some (App (m, n'))
          | None -> None))
  | Add (N n1, N n2) -> Some (N (n1 + n2))  (* Évaluation de l'addition *)
  | Add (t1, t2) when isValue t1 ->
      (match ltr_cbv_step t2 with
      | Some t2' -> Some (Add (t1, t2'))
      | None -> None)
  | Add (t1, t2) ->
      (match ltr_cbv_step t1 with
      | Some t1' -> Some (Add (t1', t2))
      | None -> None)
  | Sub (N n1, N n2) -> Some (N (n1 - n2))  (* Évaluation de la soustraction *)
  | Sub (t1, t2) when isValue t1 ->
      (match ltr_cbv_step t2 with
      | Some t2' -> Some (Sub (t1, t2'))
      | None -> None)
  | Sub (t1, t2) ->
      (match ltr_cbv_step t1 with
      | Some t1' -> Some (Sub (t1', t2))
      | None -> None)
  |Mult (N n1,N n2) -> Some (N (n1*n2))
  |Mult (t1,t2) when isValue t1 -> 
    (match ltr_cbv_step t2 with
    | Some t2' -> Some (Mult (t1, t2'))
    | None -> None) 
  |Mult (t1,t2) -> 
    (match ltr_cbv_step t1 with
      | Some t1' -> Some (Mult (t1', t2))
      | None -> None)
  |PL l -> let l' = ltr_cbv_step_list l in Some (PL l')
  |Fix (Abs(x,t))-> Some (substitution x (Fix(Abs(x,t))) t)
  | IfZero (N 0, t2, _) -> Some t2
  | IfZero (N _, _, t3) -> Some t3
  | IfZero (t1, t2, t3) ->
      (match ltr_cbv_step t1 with
      | Some t1' -> Some (IfZero (t1', t2, t3))
      | None -> None)
  | IfEmpty ((PL Empty),t2,_) -> Some t2
  |IfEmpty(PL _, _ ,t3) -> Some t 
  | IfEmpty (t1,t2,t3) ->
    (match ltr_cbv_step t1 with 
      |Some(PL Empty) -> ltr_cbv_step t2
      |Some(PL _) -> ltr_cbv_step t3
      |_ -> None )
  |Head (l) -> let l' = ltr_cbv_step l in 
    (match l' with 
      | Some(PL Empty) -> None
      | Some (PL (Cons (t1,t2)))-> Some (t1)
      | _ -> None)
  | Tail (l) -> let l' = ltr_cbv_step l in 
    (match l' with 
      |Some(PL Empty) -> None 
      |Some(PL (Cons (t1,t2))) -> Some(PL t2)
      |_ -> None)
  | Let (x, t1, t2) when isValue t1 -> 
    let t2'= substitution x t1 t2 in 
    ltr_cbv_step t2'
  | Let (x, t1, t2) ->
      (match ltr_cbv_step t1 with
      | Some t1' -> Some (Let (x, t1', t2))
      | None -> None)
  | _ -> None  (* Pas de réduction possible *)
  and ltr_cbv_step_list (l:pterm plist) =
    (match l with
    | Empty -> Empty
    | Cons (t, ts) -> let t'= ltr_cbv_step t  in 
      let ts' = ltr_cbv_step_list ts in 
        match t' with 
          |Some t'' -> Cons (t'',ts')
          |None -> Cons (t,ts)
    )


(* Forme normale d'un pterm *)
let rec ltr_cbv_norm (t : pterm) : pterm =
  match ltr_cbv_step t with
    | Some reduced_term -> ltr_cbv_norm reduced_term
    | None -> t  

(* Comparaison alpha-équivalente entre deux termes *)
let alphaequal t1 t2 =
  let rec alpha_eq env t1 t2 =
    match t1, t2 with
    | Var x1, Var x2 ->
        (try List.assoc x1 env = x2
         with Not_found -> x1 = x2)
    | Abs (x1, t1'), Abs (x2, t2') ->
        let new_env = (x1, x2) :: env in
        alpha_eq new_env t1' t2'
    | App (t1a, t1b), App (t2a, t2b) ->
        alpha_eq env t1a t2a && alpha_eq env t1b t2b
    | _ -> false
  in
  alpha_eq [] t1 t2

exception Time_out

(* Forme normale d'un pterm avec limite de réduction *)
let rec ltr_cbv_norm_ameliorer (t : pterm) (compteur : int) : pterm =
  if compteur <= 0 then
    raise Time_out  (* Lève une exception si le compteur atteint zéro *)
  else
    match ltr_cbv_step t with
    | Some reduced_term -> 
        if alphaequal reduced_term t then
          ltr_cbv_norm_ameliorer reduced_term (compteur - 1)
        else
          reduced_term
    | None -> t
