open Type
open Ast
open Exemple_ast

(* Fonctions de test pour afficher les résultats *)
let print_question (p:pterm) (desc:string) : unit =
  print_endline (desc ^ (print_term p))

let print_beta_reduction (p:pterm) : unit =
  print_endline (print_term (beta_reduced p))

let print_ltr_cbv_norm (p:pterm) : unit =
  print_endline (print_term (ltr_cbv_norm_ameliorer  p 10))

let print_subs_question (p:pterm) (var:string) (q:pterm) : unit =
  print_endline ("? " ^ var ^ " par " ^ (print_term q) ^ " dans " ^ (print_term p))

let announce_test_case (desc:string) (p:pterm) : unit =
  print_endline ("- testcase: " ^ desc ^ "\n  term: " ^ (print_term p) ^ "\n")

let skk = App(App(ex_s,ex_k),ex_k)
let sii = App(App(ex_s,ex_id),ex_id)
let addition = App(App(add_term,ex_nat1),ex_nat1)

(* Fonction pour exécuter les tests *)
let run_tests () =
  print_endline "> Running tests";
  print_endline "========= Normalisation ========";
  announce_test_case "Normalisation de ID" ex_id;
  print_ltr_cbv_norm ex_id;

  announce_test_case "Normalisation de K" ex_k;
  print_ltr_cbv_norm ex_k;

  announce_test_case "Normalisation de S" ex_s;
  print_ltr_cbv_norm ex_s;

  announce_test_case "Normalisation de skk" skk;
  print_ltr_cbv_norm skk;



  (* announce_test_case "Normalisation de omega" ex_omega;
  print_ltr_cbv_norm ex_omega; *)



  (* announce_test_case "Normalisation de addition" skk;
  print_ltr_cbv_norm addition;

  announce_test_case "Normalisation de omega" ex_omega;
  print_ltr_cbv_norm ex_omega; *)

  announce_test_case "Normalisation de SII" sii ;
  print_ltr_cbv_norm sii;

  print_endline "iiiiiii"
  

(* Point d'entrée principal du programme *)
let () =
  print_endline "=== Démarrage des tests ===";
  run_tests ();
  print_endline "=== Tests terminés ==="
