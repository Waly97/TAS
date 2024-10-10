
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


  (*beta reducion*)
  let rec beta_reduced (p:pterm): pterm =
    match p with
      Var v -> Var v 
      |Abs (x, body) -> Abs (x, beta_reduced body)
      |App (Abs(x,body),arg) -> 
        let r_arg = beta_reduced arg in
        let r_body = substitution x r_arg body in
        beta_reduced r_body
      |App (p1,p2) -> 
        let r1 =  beta_reduced p1 in 
        let r2 = beta_reduced p2 in 
        App(r1,r2)


  (* let rec peut_se_reduire (t : pterm) : bool =
    match t with
    | Var _ -> false                       (* Une variable ne peut pas être réduite *)
    | Abs (_, body) -> peut_se_reduire body (* Vérifie si le corps d'une abstraction peut être réduit *)
    | App (Abs (_, _), _) -> true          (* Une application avec une abstraction en tête peut être réduite *)
    | App (t1, t2) ->                      (* Vérifie si une des parties de l'application peut être réduite *)
    peut_se_reduire t1 || peut_se_reduire t2 *)

  (*fonction de r´eduction Call-by-Value qui impl´emente la strat´egie LtR-CbV*)
  let rec ltr_cbv_step (t : pterm) : pterm option =
    match t with 
    Var x -> None
    | Abs (x,t1) -> Some (Abs (x,t1))
    | App (t1,t2) -> 
        match ltr_cbv_step t1 with
          Some  reduce_t1 -> Some (App (reduce_t1,t2))
          |None -> 
            match ltr_cbv_step t2 with
              Some reduce_t2 -> Some (App (t1, reduce_t2))
              | None -> match (t1,t2) with 
                  (Abs (_,_),_)-> Some (beta_reduced t)
                  |_ -> None
  
  (*forme normale d'un pterm*)
  let rec ltr_cbv_norm (t : pterm) : pterm =
    match ltr_cbv_step t with
      | Some reduced_term -> ltr_cbv_norm reduced_term 
      | None -> t  

  let rec sont_identiques (t1 : pterm) (t2 : pterm) : bool =
    match (t1, t2) with
      | (Var v1, Var v2) -> v1 = v2  (* Compare les variables *)
      | (Abs (x1, body1), Abs (x2, body2)) ->
            x1 = x2 && sont_identiques body1 body2  (* Compare les abstractions *)
      | (App (t11, t12), App (t21, t22)) ->
            sont_identiques t11 t21 && sont_identiques t12 t22  (* Compare les applications *)
      | _ -> false  (* Les termes sont différents *)

  let compteur : int ref = ref 5
  let decremente () : unit = compteur := !compteur - 1;
  exception Time_out

  (*forme normale d'un pterm*)
  let rec ltr_cbv_norm_ameliorer (t : pterm) : pterm =
    if !compteur = 0 then raise Time_out; 
    match ltr_cbv_step t with
    | Some reduced_term -> 
      (* Décrémente le compteur après chaque réduction *)
        decremente ();  
        if sont_identiques reduced_term t then 
          (* Continue la normalisation si le terme a changé *)
          ltr_cbv_norm_ameliorer reduced_term  
        else 
          (* Retourne le terme réduit s'il a changé *)
          reduced_term  
    | None -> t 


               



  
        
  let () =
  (* Création du terme : (\x -> \y -> x) 3 *)
  let term = App (Abs ("x", Abs ("y", Var "x")), Var "3") in
        
  (* Affichage du terme avant la réduction *)
  print_endline "Terme avant la réduction :";
  print_endline(print_term term);
        
  (* Réduction bêta *)
  let evaluated_term = beta_reduced term in
        
  (* Affichage du terme après la réduction *)
  print_endline "Terme après la réduction :";
  print_endline(print_term evaluated_term);

print_endline "je marche";


