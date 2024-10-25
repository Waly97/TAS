type pterm = 
  Var of string
  | App of pterm * pterm
  | Abs of string * pterm
  |N of int 
  |Add of pterm * pterm
  |Sub of pterm * pterm
  |IfZero of pterm * pterm * pterm
  |IfEmpty of pterm * pterm * pterm
  |Let of string * pterm * pterm
  


  (*printer de term*)
  let rec print_term (t : pterm) : string =
  match t with
    Var x -> x
    |N n -> string_of_int n 
    | App (t1 , t2) -> "(" ^ ( print_term t1) ^" "^ ( print_term t2) ^ ")"
    | Abs (x, t) -> "(ℷ"^ x ^" -> " ^ ( print_term t) ^")"
    |Add (t1,t2) ->  "(" ^ ( print_term t1) ^ " + " ^ ( print_term t2) ^ ")"
    |Sub (t1,t2) ->  "(" ^ ( print_term t1) ^ " - " ^ ( print_term t2) ^ ")"
    |IfZero (t1,t2,t3) -> "(if " ^ (print_term t) ^ " = 0 then " ^ (print_term t2) ^ " else " ^ (print_term t3)

  (*compteur de variable et creation de nouvelle variable*)
  let compteur_var : int ref = ref 0
  let nouvelle_var () : string = compteur_var := ! compteur_var + 1;
  "X" ^ ( string_of_int ! compteur_var )

  type env_name_var= (string * string) list
  
  (*chercher le nom d'une varable dans l'environnment*)
  let find_name (name:string) (name_env: env_name_var) : string =
    let aux (current_name:string) (binding:string*string) : string =
      if current_name = fst binding then snd binding
      else current_name
    in List.fold_left aux name name_env
  
  (*alpha conversion*)
  (* let rec alphaconv (t : pterm) : pterm =
    let rec aux (pt:pteem) (name_env:env_name_var) =
      match pt with 
        Abs (name,p1) -> let new_var = nouvelle_var in 
        Abs (nv, aux p1 ((name,nv)::name_env))
        |App (p2,p3) -> App(aux p1 name_env , aux p3 name_env) 
        |Var x -> Var (find_name x name_env)
        |Add (t1,t2) -> Add (alphaconv t1, alphaconv t2) *)

  (*substitution de variable par un patern de patern *)
  let rec substitution (x : string) (n: pterm) (t : pterm) : pterm =
    match t with
    Var v1 when v1 = x -> n
    | Var v2 -> Var v2
    | Abs (y1, p1) when y1 = x -> Abs (y1, p1)  (* Pas de substitution dans les variables liées *)
    | Abs (y, p) -> Abs (y, substitution x n p)
    | App (p1, p2) -> App (substitution x n p1, substitution x n p2) 


  let rec isValue(p:pterm) : bool =
    match p with
    Var _ -> true
    | Abs(_,_) -> true
    | N _ -> true
    | App ( Var(x) , t' ) ->  isValue (t') 
    | _ -> false 
  
  (*beta reducion*)
  let rec beta_reduced (p:pterm) : pterm = 
    match p with
    | App (m, n) -> let m' = beta_reduced m in let n' = beta_reduced n in 
      (match m' with
        | Abs (vn, at) when isValue n' -> beta_reduced (substitution vn n' at)
        | _ -> beta_reduced (App (m', n'))
      )
    | _ -> p

  


  (*fonction de r´eduction Call-by-Value qui impl´emente la strat´egie LtR-CbV*)
  let rec ltr_cbv_step (t : pterm) : pterm option =
    match t with
    (* Beta reduction *)
    | App (Abs (x, body), v) when isValue v ->
      Some (substitution x v body)
    | App (m, n) ->
        (match ltr_cbv_step m with
        (* M -> M' => M N -> M' N *)
        | Some m' -> Some (App (m', n))
        | None when (isValue m) = false ->None
        | _  ->
            (* Si la partie gauche est déjà une valeur, on essaie de réduire la partie droite *)
            (
            match ltr_cbv_step n with
            | Some n' -> Some (App (m, n'))
            | None -> None)
          )
    | _ -> None 
    
  
  (*forme normale d'un pterm*)
  let rec ltr_cbv_norm (t : pterm) : pterm =
    match ltr_cbv_step t with
      | Some reduced_term -> ltr_cbv_norm reduced_term 
      | None -> t  

  (* let rec sont_identiques (t1 : pterm) (t2 : pterm) : bool =
    match (t1, t2) with
      | (Var v1, Var v2) -> v1 = v2  (* Compare les variables *)
      | (Abs (x1, body1), Abs (x2, body2)) ->
            x1 = x2 && sont_identiques body1 body2  (* Compare les abstractions *)
      | (App (t11, t12), App (t21, t22)) ->
            sont_identiques t11 t21 && sont_identiques t12 t22  (* Compare les applications *)
      | _ -> false  Les termes sont différents *)

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
          |  _-> false
        in
        alpha_eq [] t1 t2

  
  exception Time_out

  (*forme normale d'un pterm*)
  let rec ltr_cbv_norm_ameliorer (t : pterm) (compteur : int) : pterm =
    if compteur <= 0 then
      raise Time_out  (* Lève une exception si le compteur atteint zéro *)
    else
      match ltr_cbv_step t with
      | Some reduced_term -> 
          if alphaequal reduced_term t then
            (* Si le terme réduit est identique à l'original, on continue la normalisation *)
            ltr_cbv_norm_ameliorer reduced_term (compteur - 1)
          else
            (* Si le terme a changé, on retourne la forme réduite *)
            reduced_term
      | None -> t  (* Si aucune réduction n'est possible, retourne le terme courant *)
  

    


               

  