(* typecheck.ml *)
open Infer

let run (prog:Ast.program) : bool =
  match check_program prog with
  | Ok _ -> true
  | Error msg ->
    Printf.printf "[Type error] %s\n" msg; false
