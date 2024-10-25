(* test_unificateur.ml *)

open OUnit2
open Printf
open Ast
open Typeur
open Type

(* Fonction pour comparer deux types *)
let test_type_eq t1 t2 =
  assert_equal t1 t2 ~printer:print_type

(* Cas de tests pour l'unification *)

(* Unification simple : même variable et même type *)
let unification_simple_test =
  let eqs = [(TVar "T1", TVar "T1"); (Arr (TVar "T1", TVar "T2"), Arr (TVar "T1", TVar "T2"))] in
  eqs

(* Unification avec substitution *)
let unification_substitution_test =
  let eqs = [(TVar "T1", Arr (TVar "T2", TVar "T3")); (Arr (TVar "T2", TVar "T3"), TVar "T4")] in
  eqs

(* Test unification échouée corrigé *)
let unification_succes_test=
  let eqs = [
    (TVar "T1", TVar "T2"); 
    (Arr (TVar "T1", TVar "T2"), Arr (TVar "T3", TVar "T4"))
  ] in
  eqs

(* Test d'unification avec échec (sans utiliser Nat) *)
let unification_echec_test =
  let eqs = [
    (Nat , Arr (TVar "T1", TVar "T2"));  (* T1 est une variable, mais doit unifier avec une fonction *)
    (Arr (TVar "T3", Nat), TVar "T1")   (* Conflit car T1 doit être un type fonctionnel mais ici, il est utilisé avec des types concrets *)
  ] in
  eqs

let abs_test =
  let env = [] in
  let term = Abs ("x", Var "x") in
  let expected_type = print_term term in
  (env, term, expected_type)

let app_test =
  let env = [("f", Arr (TVar "T1", TVar "T2")); ("x", TVar "T1")] in
  let term = App (Var "f", Var "x") in
  let expected_type = print_term term in
  (env, term, expected_type)

let nested_abs_test =
  let env = [] in
  let term = Abs ("x", Abs ("y", App (Var "x", Var "y"))) in
  let expected_type = print_term term in
  (env, term, expected_type)
  

(* Tests d'unification *)
let tests = "Unification Tests" >::: [

  (* Test d'unification simple *)
  "unification simple" >:: (fun _ ->
    let eqs = unification_simple_test in
    match solve_system eqs [] with
    | Some _ -> ()
    | None -> assert_failure "Expected successful unification"
  );

  (* Test d'unification avec substitution *)
  "unification avec substitution" >:: (fun _ ->
    let eqs = unification_substitution_test in
    match solve_system eqs [] with
    | Some (_, substitutions) ->
      (* Vérification des substitutions *)
      let expected_substitutions = [("T4", Arr (TVar "T2", TVar "T3")); ("T1", Arr (TVar "T2", TVar "T3"))] in
      List.iter (fun (v, t) ->
        let expected = List.assoc v expected_substitutions in
        test_type_eq t expected
      ) substitutions
    | None -> assert_failure "Expected successful unification"
  );

  (* Test d'unification réussie *)
  "unification réussie" >:: (fun _ ->
    let eqs = unification_succes_test in
    match solve_system eqs [] with
    | Some _ -> ()  (* Succès attendu, car l'unification doit réussir *)
    | None -> assert_failure "Expected successful unification"
  );

  "Abstraction" >:: (fun _ ->
    let env, term, expected = abs_test in
    let result = inference env term in
    assert_equal ("le terme " ^ expected ^ " est bien typé") result
  );

  "Application" >:: (fun _ ->
    let env, term, expected = app_test in
    let result = inference env term in
    assert_equal ("le terme " ^ expected ^ " est bien typé") result
  );

  "Nested Abstraction" >:: (fun _ ->
    let env, term, expected = nested_abs_test in
    let result = inference env term in
    assert_equal ("le terme " ^ expected ^ " est bien typé") result
  );
]

(* Fonction principale pour lancer les tests *)
let () =
  run_test_tt_main tests
