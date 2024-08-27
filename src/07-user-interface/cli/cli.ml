open Utils
module Ast = Language.Ast
module Backend = CliInterpreter
module Loader = Loader.Loader (Backend)
module Comp = Compiler

type config = { filenames : string list; use_stdlib : bool ; compile : bool}

let parse_args_to_config () =
  let filenames = ref [] and use_stdlib = ref true  and compile = ref false in
  let usage = "Run Millet as '" ^ Sys.argv.(0) ^ Sys.argv.(1) ^" [filename.mlt] ...'"
  and anonymous filename = filenames := filename :: !filenames
  and options =
    Arg.align
      [
        ( "--no-stdlib",
          Arg.Clear use_stdlib,
          " Do not load the standard library" );
        ( "--compile",
          Arg.Set compile,
          " Compile the given programs"
        )
      ]
  in
  Arg.parse options anonymous usage;
  { filenames = List.rev !filenames; use_stdlib = !use_stdlib ; compile = !compile}

let rec run (state : Backend.run_state) =
  Backend.view_run_state state;
  match Backend.steps state with
  | [] -> ()
  | steps ->
      let i = Random.int (List.length steps) in
      let step = List.nth steps i in
      let state' = step.next_state () in
      run state'

let main () =
  let config = parse_args_to_config () in
  try
    Random.self_init ();
    let conf_pair = (config.use_stdlib, config.compile) in
    match conf_pair with 
    | (true,false) ->
      (let state = Loader.load_source Loader.initial_state Loader.stdlib_source
      in
      let state' = List.fold_left Loader.load_file state config.filenames in
      let run_state = Backend.run state'.backend in
      run run_state)
    | (true, true) ->
      (let state = Loader.load_source Loader.initial_state Loader.stdlib_source
      in
      let state' = List.fold_left Loader.load_file state config.filenames in
      Compiler.compile_prog state'.cmds)
      |> ignore
    | (false, true) -> 
      (let state' = List.fold_left Loader.load_file Loader.initial_state config.filenames in
      Compiler.compile_prog state'.cmds)
      |> ignore
    | (false, false) -> 
      (let state' = List.fold_left Loader.load_file Loader.initial_state config.filenames in
      let run_state = Backend.run state'.backend in
      run run_state)
  with Error.Error error ->
    Error.print error;
    exit 1

let _ = main ()
