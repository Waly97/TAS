

type pterm = 
  Var of string
  | App of pterm * pterm
  | Abs of string * pterm
  |N of int 
  |Add of pterm * pterm
  |Sub of pterm * pterm
  |IfZero of pterm * pterm * pterm
  |IfEmpty of pterm * pterm * pterm
  |let of string * pterm * pterm
  


  (*printer de term*)
  let rec print_term (t : pterm) : string =
  match t with
    Var x -> x
    | App (t1 , t2) -> "(" ^ ( print_term t1) ^" "^ ( print_term t2) ^ ")"
    | Abs (x, t) -> "(fun "^ x ^" -> " ^ ( print_term t) ^")"
    |N n -> n 
    |Add (t1,t2) ->  "(" ^ ( print_term t1) ^ " + " ^ ( print_term t2) ^ ")"
    |Sub (t1,t2) ->  "(" ^ ( print_term t1) ^ " - " ^ ( print_term t2) ^ ")"
    |IfZero (t1,t2,t3) -> "(if " ^ (print_term t) ^ " = 0 then " ^ (print_term t2) ^ " else " ^ (print_term t3)

  (*compteur de variable et creation de nouvelle variable*)
  let compteur_var : int ref = ref 0
  let nouvelle_var () : string = compteur_var := ! compteur_var + 1;
  "X"ˆ( string_of_int ! compteur_var )

  type env_name_var= (string * string) list
  
  (*chercher le nom d'une varable dans l'environnment*)
  let find_name (name:string) (name_env: env_name_var) : string =
    let aux (current_name:string) (binding:string*string) : string =
      if current_name = fst binding then snd binding
      else current_name
    in List.fold_left aux name name_env
  
  (*alpha conversion*)
  let rec alphaconv (t : pterm) : pterm =
    let rec aux (pt:pteem) (name_env:env_name_var) =
      match pt with 
      Abs (name,p1) -> let new_var = nouvelle_var in 
        Abs (nv, aux p1 ((name,nv)::name_env))
      |App (p2,p3) -> App(aux p1 name_env , aux p3 name_env) 
      |Var x -> Var (find_name x name_env)
      |Add (t1,t2) -> Add (alpha_conversion t1, alpha conversion t2)



  (*substitution de variable par un patern de patern *)
  let rec substitution (x : string) (n: pterm) (t : pterm) : pterm =
    match t with
    Var v when v=x -> n
    Var v -> Var v 
    |Abs (y,p) when y=x -> Abs (y,p)
    |Abs (y,p) when y != x -> Asb (y , substitution x n p)
    |App (p1,p2) -> App(substitution x n p1 , substitution x n p2) 


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

  
  let rec ltr_cbv_norm (t : pterm) : pterm =
    match t with
      Var x-> Var x 
      |Abs


