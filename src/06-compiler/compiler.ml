module Const = Language.Const
module Typed = Typechecker.TypedAst
module Ast = Language.Ast
module Ty = Typechecker
module Lower = Lower
module Env = Env
module Types = Wasm.Types
module Arrange = Wasm.Arrange
module Sexpr = Wasm.Sexpr
module Wasm = Wasm.Ast 
open Emit
open Source

type pat_class = IrrelevantPat | TotalPat | PartialPat

let max_func_arity = 12

let ref_cast idx = Wasm.RefCast (Types.NoNull, Types.VarHT (Types.StatX idx))

  (* coerce *)

let rec compile_coerce ctxt src dst t =
  if src <> dst then
  let emit ctxt = List.iter (Emit.emit_instr ctxt) in
  let non_null n1 n2 =
    if n1 = Lower.Null && n2 = Lower.Nonull then emit ctxt [RefAsNonNull] in
  match src, dst with
  | Lower.BlockRep _, DropRep when Ty.eq t (Ast.TyTuple []) ->
    ()
  | _, DropRep ->
    emit ctxt [
      Drop;
    ]
  | _, BlockRep _ when Ty.eq t (Ast.TyTuple []) ->
    emit ctxt [
      Drop;
    ]
  | BlockRep _, _ when Ty.eq t (Ast.TyTuple []) ->
    emit ctxt [
      IntConst (I32T, 0);
      RefI31;
    ]
  | (BlockRep n1 | BoxedRep n1 | BoxedAbsRep n1), BoxedAbsRep n2
  | (BlockRep n1 | BoxedRep n1), (BlockRep n2 | BoxedRep n2) ->
    non_null n1 n2
  | BoxedAbsRep n1, (BlockRep n2 | BoxedRep n2) ->
    (match t with
    | (Ast.TyConst Const.BooleanTy | Ast.TyConst Const.IntegerTy) ->
      emit ctxt [
        RefCast (Null, I31HT);
      ]
    | Ast.TyConst Const.FloatTy ->
      let boxedfloat = Lower.lower_var_type ctxt (Ast.TyConst Const.FloatTy) in
      emit ctxt [
        ref_cast boxedfloat;
      ]
    | Ast.TyTuple [] ->
      non_null n1 n2
    | t ->
      (* No types handled here can use super RTTs *)
      let x = Lower.lower_var_type ctxt t in
      non_null n1 n2;
      emit ctxt [
        ref_cast x;
      ]
    )
  | (BlockRep _ | BoxedRep _ | BoxedAbsRep _), (UnboxedRep n2 | UnboxedLaxRep n2) ->
    compile_coerce ctxt src (BoxedRep n2) t;
    (match t with
    | Ast.TyConst Const.BooleanTy ->
      emit ctxt [
        I31Get ZX;
      ]
    | Ast.TyConst Const.IntegerTy ->
      emit ctxt [
        I31Get SX;
      ]
    | Ast.TyConst Const.FloatTy ->
      let boxedfloat = Lower.lower_var_type ctxt (Ast.TyConst Const.FloatTy) in
      emit ctxt [
        Wasm.StructGet (boxedfloat, 0, None);
      ]
    | _ -> ()
    )
  | (UnboxedRep n1 | UnboxedLaxRep n1), (BlockRep n2 | BoxedRep n2 | BoxedAbsRep n2) ->
    (match t with
    | Ast.TyConst Const.BooleanTy | Ast.TyConst Const.IntegerTy ->
      emit ctxt [
        RefI31;
      ]
    | Ast.TyConst Const.FloatTy ->
      let boxedfloat = Lower.lower_var_type ctxt (Ast.TyConst Const.FloatTy) in
      emit ctxt [
        StructNew (boxedfloat, Explicit);
      ]
    | _ -> non_null n1 n2
    )
  | UnboxedLaxRep n1, UnboxedRep n2 ->
    (match t with
    | Ast.TyConst Const.IntegerTy ->
      emit ctxt [
        IntConst (I32T, 1);
        Shl I32T;
        IntConst (I32T, 1);
        Shr I32T;
      ]
    | Ast.TyConst Const.BooleanTy | Ast.TyConst Const.FloatTy -> ()
    | _ -> non_null n1 n2
    )
  | (UnboxedRep n1 | UnboxedLaxRep n1), (UnboxedRep n2 | UnboxedLaxRep n2) ->
    (match t with
    | Ast.TyConst Const.BooleanTy | Ast.TyConst Const.IntegerTy | Ast.TyConst Const.FloatTy -> ()
    | _  -> non_null n1 n2
    )
  | DropRep, _ -> assert false



(* helpers *)
let compile_load_arg ctxt i arg argv_opt =
  let emit ctxt = List.iter (emit_instr ctxt) in
  match argv_opt with
  | None ->
    assert (i < max_func_arity); 
    emit ctxt [
      LocalGet (arg-1 + i);
    ]
  | Some argv ->
    emit ctxt [
      LocalGet (arg-1);
      IntConst (I32T, i);
      RefI31;
      ArrayGet (argv, None);
      RefAsNonNull;
    ]

let rec find_var f ctxt x envs =
  match envs with
  | [] ->
    assert false
  | (_, env)::envs' ->
    match f x !env with
    | Some {it = locs; _} -> locs
    | None -> find_var f ctxt x envs'

let find_val_var = find_var Env.find_opt_val 

let filter_loc (ctxt : Lower.ctxt) find_var vals =
  Ast.VariableMap.filter (fun x _ ->
    match find_var ctxt x ctxt.ext.envs with
    | (Lower.PreLoc _ | Lower.GlobalLoc _), _ -> false
    | (Lower.LocalLoc _ | Lower.ClosureLoc _), _ -> true
  ) vals

let filter_vars (ctxt : Lower.ctxt) vars =
  filter_loc ctxt find_val_var vars

let curry_fun_idx = Lower.clos_env_idx
let curry_arg_idx = Lower.clos_env_idx + 1 (* first argument or argv *)

let compile_push_args ctxt n shift compile_eI =
  let emit ctxt = List.iter (emit_instr ctxt) in
  match Lower.lower_param_types ctxt n with
  | _, None ->
    for i = 0 to n - 1 do
      compile_eI i
    done
  | _, Some argv ->
    let tmp = emit_local ctxt {ltype = (RefT (NoNull, VarHT (StatX argv)))} in
    emit ctxt [
      IntConst (I32T, 0);
      RefI31;
      IntConst (I32T, n);
      ArrayNew (argv, Explicit);
      LocalTee (tmp + shift);
      RefAsNonNull;
    ];
    for i = 0 to n - 1 do
      emit ctxt [
        LocalGet (tmp + shift);
        IntConst (I32T, i);
      ];
      compile_eI i;
      emit ctxt [
        ArraySet (argv);
      ]
    done

(* Constants *)
let lower_text_type ctxt : int =
  emit_type ctxt (SubT (NoFinal, [], (DefArrayT (ArrayT (FieldT (Var, PackStorageT Pack8))))))

let compile_text_new ctxt : int =
  let i32_load8_u align offset =
    Wasm.Load {ty = I32T; align; offset; pack = Some (Pack8, ZX)} in
  let block bt es = Wasm.Block (bt, es) in
  let loop bt es = Wasm.Loop (bt, es) in
  Emit.lookup_intrinsic ctxt "text_new" (fun _ ->
    let text = lower_text_type ctxt in
    let textref = (Types.RefT (NoNull, VarHT (StatX text))) in
    let textnullref = Wasm.{ltype = (Types.RefT (Null, VarHT (StatX text)))} in 
    emit_func ctxt [NumT I32T; NumT I32T] [textref] (fun ctxt _ ->
      let src = emit_param ctxt in
      let len = emit_param ctxt in
      let dst = emit_local ctxt textnullref in
      List.iter (emit_instr ctxt) [
        LocalGet (len);
        ArrayNew (text, Implicit);
        LocalSet (dst);
        block (Types.ValBlockType None) (List.map (fun e -> e) Wasm.[
          loop (Types.ValBlockType None) (List.map (fun e -> e) [
            LocalGet (len);
            Eqz I32T;
            BrIf (1);
            LocalGet (dst);
            LocalGet (len);
            IntConst (I32T, 1);
            Sub I32T;
            LocalTee (len);
            LocalGet (len);
            LocalGet (src);
            Add I32T;
            i32_load8_u 0 0;
            ArraySet (text);
            Br (0);
          ])
        ]);
        LocalGet (dst);
        RefAsNonNull;
      ]
    )
  )

let compile_lit ctxt l =
  let emit ctxt = List.iter (emit_instr ctxt) in
  match l with
  | Const.Boolean b ->
    emit ctxt [
      IntConst (I32T, (if b then 1 else 0));
    ]
  | Integer i ->
    emit ctxt Wasm.[
      IntConst (I32T, i);
    ]
  | Float z ->
    emit ctxt Wasm.[
      FloatConst (F64T, z);
    ]
  | String s ->
    let addr = emit_active_data ctxt s in
    emit ctxt [
      IntConst (I32T, addr);
    ];
    emit ctxt [
      IntConst (I32T, (String.length s));
      Call (compile_text_new ctxt);
    ]

let compile_load_args ctxt i j shift arg0 src_argv_opt =
  assert (j <= max_func_arity || src_argv_opt <> None);
  if j - i > max_func_arity && i = 0 then
    (* Reuse argv *)
    emit_instr ctxt (LocalGet (arg0 + shift))
  else
    compile_push_args ctxt (j - i) shift (fun k ->
      compile_load_arg ctxt (i + k) (arg0 + shift) src_argv_opt
    )


let rec compile_func_apply arity typeidx ctxt=
  assert (arity > 0);
  Emit.lookup_intrinsic ctxt ("func_apply" ^ string_of_int arity) (fun def_fwd ->
    let emit ctxt = List.iter (emit_instr ctxt) in
    let anyclos = Lower.lower_anyclos_type ctxt in
    let argts, argv_opt = Lower.lower_param_types ctxt arity in
    emit_func ctxt ((RefT (NoNull, VarHT (StatX anyclos))) :: argts) [RefT Lower.absref] (fun ctxt fn ->
      def_fwd fn;
      let clos = emit_param ctxt in
      let args = List.map (fun _ -> emit_param ctxt ) argts in
      let arg0 = List.hd args in
      let block bt es = Wasm.Block (bt, es) in
      emit_block ctxt block (ValBlockType None) (fun ctxt ->
        emit_block ctxt block (ValBlockType None)(fun ctxt ->
          let rec over_apply ctxt = function
            | 0 ->
              (* Dispatch on closure arity *)
              let labs = List.init (arity + 1) (fun i -> (max 0 (i - 1)) ) in
              emit ctxt [
                LocalGet (clos);
                StructGet (anyclos, Lower.clos_arity_idx, None);
                BrTable (labs, arity);
              ]
            | n ->
              emit_block ctxt block (ValBlockType None) (fun ctxt ->
                over_apply ctxt (n - 1);
              );
              (* Dispatching here when closure arity n < apply arity *)

              let _, closN = Lower.lower_func_type ctxt n in
              let ref_closN_0 = emit_local ctxt {ltype = (RefT (NoNull, VarHT (StatX closN)))} in
              (* Downcast closure type *)
              emit ctxt [
                LocalGet (clos);
                ref_cast (closN);
                LocalSet ref_closN_0
              ];
              (* Bind result to local *)
              emit_block ctxt block (ValBlockType None) (fun ctxt ->
                (* Call target function with arguments it can handle *)
                emit ctxt [
                  LocalGet ref_closN_0;
                ];
                compile_load_args ctxt 0 n 1 arg0 argv_opt;
                emit ctxt [
                  LocalGet ref_closN_0;
                  StructGet (closN, Lower.clos_code_idx, None);
                  CallRef typeidx;
                  (* Downcast resulting closure *)
                  ref_cast anyclos;
                ];
                (* Apply result to remaining arguments *)
                compile_load_args ctxt n arity 1 arg0 argv_opt;
                emit ctxt [
                  Call (compile_func_apply (arity - n) typeidx ctxt) ;
                  Return;  (* TODO: should be tail call *)
                ];
              )
          in over_apply ctxt (arity - 1)
        );
        (* Dispatching here when closure arity n = apply arity *)
        let _, closN = Lower.lower_func_type ctxt arity in
        let ref_closN_1 = emit_local ctxt {ltype = (RefT (NoNull, VarHT (StatX closN)))} in
        (* Downcast closure type *)
        emit ctxt [
          LocalGet (clos);
          ref_cast closN;
          LocalSet ref_closN_1;
        ];
        (* Bind result to local *)
        emit_block ctxt block (ValBlockType None) (fun ctxt ->
          (* Call target function *)
          emit ctxt [
            LocalGet ref_closN_1; 
          ];
          compile_load_args ctxt 0 arity 1 arg0 argv_opt;
          emit ctxt [
            LocalGet ref_closN_1;
            StructGet (closN, Lower.clos_code_idx, None);
            CallRef typeidx;
            Return;  (* TODO: should be tail call *)
          ]
        )
      );
      (* Dispatching here when closure arity > apply arity *)
      (* Create curried closure *)
      let flds = List.map Lower.field ((RefT (NoNull, VarHT (StatX anyclos))) :: argts) in
      let _, _, curriedN = Lower.lower_clos_type ctxt 1 flds in
      emit ctxt [
        IntConst (I32T, 1);
        RefFunc (compile_func_curry arity ctxt typeidx);
        LocalGet (clos);
      ];
      compile_load_args ctxt 0 arity 0 arg0 argv_opt;
      emit ctxt [
        StructNew (curriedN, Explicit);
      ]
    )
  )
    


and compile_func_curry arity ctxt typeidx=
  let block bt es = Wasm.Block (bt, es) in
  let loop bt es = Wasm.Loop (bt, es) in
  let arity_string =
    if arity <= max_func_arity then string_of_int arity else "vec" in
  Emit.lookup_intrinsic ctxt ("func_curry" ^ arity_string) (fun def_fwd ->
    let emit ctxt = List.iter (emit_instr ctxt ) in
    let anyclos = Lower.lower_anyclos_type ctxt in
    let argts, argv_opt = Lower.lower_param_types ctxt arity in
    let flds = List.map Lower.field ((RefT (NoNull, VarHT (StatX anyclos))) :: argts) in
    let _, clos1, curriedN = Lower.lower_clos_type ctxt 1 flds in
    (* curryN = fun xN => apply_N+1 x0 ... xN-1 xN *)
    emit_func ctxt [RefT (NoNull, VarHT (StatX clos1)); RefT Lower.absref] [RefT Lower.absref] (fun ctxt fn ->
      def_fwd fn;
      let clos = emit_param ctxt in
      let arg0 = emit_param ctxt in
      let ref_curriedN = emit_local ctxt {ltype = (RefT (NoNull, VarHT (StatX curriedN)))} in
      emit_func_ref ctxt fn;
      (* Downcast generic to specific closure type *)
      emit ctxt [
        LocalGet (clos);
        ref_cast curriedN;
        LocalSet ref_curriedN;
      ];
      (* Bind result to local *)
      emit_block ctxt block (ValBlockType (Some (RefT Lower.absref))) (fun ctxt ->
        (* Load arguments *)
        if arity <= max_func_arity then begin
          (* Load target function *)
          emit ctxt [
            LocalGet ref_curriedN;
            StructGet (curriedN, curry_fun_idx, None);
          ];
          (* Target expects direct args, load them individually *)
          compile_push_args ctxt (arity + 1) 1 (fun i ->
            if i < arity then
              (* First arity args are loaded from closure environment *)
              emit ctxt [
                LocalGet ref_curriedN;
                StructGet (curriedN, curry_arg_idx + i, None);
              ]
            else
              (* Last arg is the applied one *)
              emit ctxt [
                LocalGet (arg0 + 1);
              ]
          );
          (* Call target *)
          emit ctxt [
            Call (compile_func_apply (arity + 1) typeidx ctxt);
            Return;  (* TODO: should be tail call *)
          ]
        end else begin
          (* Target expects arg vector, copy to extended vector *)
          (* This code is agnostic to static arity, hence works for any *)
          
          let argv = Option.get argv_opt in
          let src = emit_local ctxt {ltype = (RefT (NoNull, VarHT (StatX argv)))} in
          let dst = emit_local ctxt {ltype = (RefT (NoNull, VarHT (StatX argv)))} in
          let len = emit_local ctxt {ltype = (NumT I32T)} in
          let i = emit_local ctxt {ltype = (NumT I32T)} in
          emit ctxt [
            (* Array init value *)
            IntConst (I32T, 0);
            RefI31;
            (* Load source *)
            LocalGet ref_curriedN;  (* curriedN *)
            StructGet (curriedN, curry_arg_idx, None);
            LocalTee (src + 1);
            (* Load length *)
            ArrayLen;
            LocalTee (i + 1);
            (* Allocate destination *)
            IntConst (I32T, 1);
            Add I32T;
            LocalTee (len + 1);
            ArrayNew (argv, Explicit);
            LocalTee (dst + 1);
            (* Initialise applied argument *)
            LocalGet (i + 1);
            LocalGet (arg0 + 1);
            ArraySet (argv);
          ];
          (* Copy closure arguments, from upper to lower *)
          emit_block ctxt block (ValBlockType None)(fun ctxt ->
            emit_block ctxt loop (ValBlockType None)(fun ctxt ->
              emit ctxt [
                (* Check termination condition *)
                LocalGet (i + 1);
                Eqz I32T;
                BrIf 1;
                (* Load destination *)
                LocalGet (dst + 1);
                (* Compute next index *)
                LocalGet (i + 1);
                IntConst (I32T, 1);
                Sub I32T;
                LocalTee (i + 1);
                (* Read arg value from source *)
                LocalGet (src + 1);
                LocalGet (i + 1);
                ArrayGet (argv, None);
                (* Store arg value to destination *)
                ArraySet (argv );
                (* Iterate *)
                Br 0;
              ]
            )
          );
          emit_block ctxt block (ValBlockType None) (fun ctxt ->
            let _, closNP = Lower.lower_func_type ctxt (arity + 1) in
            let ref_closNP = emit_local ctxt {ltype = (RefT (NoNull, VarHT (StatX closNP)))} in
            emit ctxt [
              (* Load source arity *)
              LocalGet (len + 1);
              (* Load destination arity *)
              LocalGet ref_curriedN;
              StructGet (curriedN, curry_fun_idx, None);
              StructGet (anyclos, Lower.clos_arity_idx, None);
              (* Compare *)
              Ne I32T;
              BrIf 0;
              (* All arguments collected, perform call *)
              LocalGet ref_curriedN;
              StructGet (curriedN, curry_fun_idx, None);
              ref_cast (closNP);
            ];
            (* Bind closure at specific type *)

            emit_block ctxt block (ValBlockType (Some (RefT Lower.absref))) (fun ctxt ->
              emit ctxt [
                LocalGet ref_closNP;
                LocalGet (dst + 2);
                RefAsNonNull;
                LocalGet ref_closNP;
                StructGet (closNP, Lower.clos_code_idx, None);
                CallRef typeidx;
                Return;  (* TODO: should be tail call *)
              ]
            )
          );
          (* Still missing arguments, create new closure *)
          emit ctxt [
            IntConst (I32T, 1);
            RefFunc (compile_func_curry arity ctxt typeidx);
            LocalGet 0;
            StructGet (curriedN, curry_fun_idx, None);
            LocalGet (dst + 1);
            RefAsNonNull;
            (*rtt_canon (curriedN );*)
            StructNew (curriedN, Explicit);
          ]
        end
      )
    )
  )

(* strings *)

let lower_text_type ctxt : int =
  emit_type ctxt (SubT (NoFinal, [], DefArrayT (ArrayT (FieldT (Var, PackStorageT Pack8)))))


let compile_text_eq ctxt : int =
  let block bt es = Wasm.Block (bt, es) in
  let loop bt es = Wasm.Loop (bt, es) in
  let if_ bt es1 es2 = Wasm.If (bt, es1, es2) in
  Emit.lookup_intrinsic ctxt "text_eq" (fun _ ->
    let text = lower_text_type ctxt in
    let textref = (Types.RefT (NoNull, VarHT (StatX text))) in
    emit_func ctxt [textref; textref] [NumT I32T] (fun ctxt _ ->
      let arg1 = emit_param ctxt in
      let arg2 = emit_param ctxt in
      let len = emit_local ctxt {ltype = NumT I32T} in
      List.iter (emit_instr ctxt ) [
        block (ValBlockType None) (List.map (fun e -> e) Wasm.[
          LocalGet (arg1);
          LocalGet (arg2);
          RefEq;
          if_ (ValBlockType None) (List.map (fun e -> e) [
            IntConst (I32T, 1);
            Return 
          ]) [];
          LocalGet (arg1);
          ArrayLen;
          LocalGet (arg2);
          ArrayLen;
          LocalTee (len);
          Ne I32T;
          BrIf (0);
          block (ValBlockType None) (List.map (fun e -> e) [
            loop (ValBlockType None) (List.map (fun e -> e) [
              LocalGet (len);
              Eqz I32T;
              BrIf 1;
              LocalGet (arg1);
              LocalGet (len);
              IntConst (I32T, 1);
              Sub I32T;
              LocalTee (len);
              ArrayGet (text, Some ZX);
              LocalGet (arg2);
              LocalGet (len);
              ArrayGet (text, Some ZX);
              Ne I32T;
              BrIf 2;
              Br 0;
            ])
          ]);
          IntConst (I32T, 1);
          Return;
        ]);
        IntConst (I32T, 0);
      ]
    )
  )

(* variables *)

let compile_var find_var (ctxt : Lower.ctxt) x =
  let loc, funcloc_opt = find_var ctxt x ctxt.ext.envs in
  (match loc with
  | Lower.PreLoc _ -> failwith "Preloc val_var"
    (*let _, l = List.nth Prelude.vals (idx) in
    compile_lit ctxt l*) 
  | Lower.LocalLoc idx ->
    emit_instr ctxt (Wasm.LocalGet (idx));
  | Lower.GlobalLoc idx ->
    emit_instr ctxt (Wasm.GlobalGet idx);
  | Lower.ClosureLoc (null, idx, localidx, typeidx) ->
    emit_instr ctxt (LocalGet (localidx ));
    emit_instr ctxt (StructGet (typeidx, idx, None));
    if null = Null then emit_instr ctxt RefAsNonNull
  );
  loc, funcloc_opt


let compile_val_var ctxt x t dst =
  let loc, funcloc_opt = compile_var find_val_var ctxt x in
  let rep = Lower.loc_rep loc in
  match funcloc_opt with
  | None -> compile_coerce ctxt rep dst t 
  | Some ({typeidx; _} : Lower.func_loc) ->
    ignore typeidx;
    if Lower.null_rep rep = Null && Lower.null_rep dst <> Null then
      emit_instr ctxt Wasm.RefAsNonNull 

  let compile_val_var_bind_pre ctxt x t funcloc_opt =
  let scope, env = Lower.current_scope ctxt in
  let rep = Lower.scope_rep scope in
  let vt =
    match funcloc_opt with
    | None -> Lower.lower_value_type ctxt rep t
    | Some ({typeidx; _} : Lower.func_loc) ->
      if Lower.null_rep rep = Null then (RefT (Null, VarHT (StatX typeidx))) else (RefT (NoNull, VarHT (StatX typeidx)))
  in
  let loc =
    match scope with
    | PreScope -> assert false
    | LocalScope -> Lower.LocalLoc (emit_local ctxt ({ltype = vt}))
    | GlobalScope -> Lower.GlobalLoc (emit_global ctxt Var vt None)
  in
  env := Env.extend_val !env x (make_phrase (loc, funcloc_opt))

let compile_val_var_bind_post ctxt x t src =
  let _, env = Lower.current_scope ctxt in
  let loc, _ = (Env.find_val x !env).it in
  compile_coerce ctxt src (Lower.loc_rep loc) t;
  (match loc  with
  | PreLoc _ | ClosureLoc _ -> assert false
  | LocalLoc idx -> emit_instr ctxt (LocalSet (idx)) 
  | GlobalLoc idx -> emit_instr ctxt (GlobalSet (idx))
  )

let compile_val_var_bind ctxt x t src funcloc_opt =
  compile_val_var_bind_pre ctxt x t funcloc_opt;
  compile_val_var_bind_post ctxt x t src

(* closures *)

let local_ref_ty idx = 
  let x = (Types.RefT (NoNull, VarHT (StatX idx))) in 
  Wasm.{ltype = x}

let compile_load_env ctxt clos (closNenv : int) vars envflds=
  if vars <> Ast.VariableMap.empty then begin
    let emit ctxt = List.iter (emit_instr ctxt) in
    let envlocal = emit_local ctxt (local_ref_ty closNenv) in
    let rttidx = closNenv in
    emit ctxt [
      LocalGet clos;
      ref_cast rttidx;
      LocalSet (envlocal);
    ];
    let _, env = Lower.current_scope ctxt in
    let _ =
      Ast.VariableMap.fold (fun x _ i ->
        let idx = Lower.clos_env_idx + i in
        let _, func_loc_opt = find_val_var ctxt x ctxt.ext.envs in
        let null =
          if func_loc_opt = None then Lower.Nonull else
          match List.nth envflds i with
          | (Types.FieldT (_ ,ValStorageT (RefT (Null, _)))) -> Null
          | _ -> Nonull
        in
        env := Env.extend_val !env x
          (make_phrase (Lower.ClosureLoc (null, idx, envlocal, closNenv), func_loc_opt)); 
        i + 1
      ) vars 0 
    in ()
  end

let compile_alloc_clos ctxt fn arity vars rec_xs closNenv=
  let emit ctxt = List.iter (emit_instr ctxt) in
  let rttidx = closNenv in
  emit_func_ref ctxt fn;
  emit ctxt [
    IntConst (I32T, arity);
    RefFunc fn;
  ];
  Ast.VariableMap.iter (fun x t ->
    let rep = if Ast.VariableMap.mem x rec_xs then Lower.local_rep () else Lower.clos_rep () in
    compile_val_var ctxt x t rep
  ) vars;
  emit ctxt [
    GlobalGet (rttidx);
  ];
  emit ctxt [
    StructNew (closNenv, Explicit);
  ]

  (* patterns *)

let rec classify_pat p = 
    match p.it with
    | Typed.PVar _ -> TotalPat 
    | Typed.PAnnotated (p1, _) -> classify_pat p1
    | Typed.PAs (p1, _) -> classify_pat p1
    | Typed.PTuple ps -> List.fold_left max IrrelevantPat (List.map classify_pat ps)
    | Typed.PVariant (_, None) -> PartialPat
    | Typed.PVariant (_, Some p1) -> classify_pat p1
    | Typed.PConst _ -> PartialPat 
    | Typed.PNonbinding -> IrrelevantPat 

let rec compile_pattern ctxt (fail : int) (pat : Typed.pattern) funcloc_opt= 
  let emit ctxt = List.iter (emit_instr ctxt) in
  match pat.it with
  | Typed.PNonbinding | Typed.PTuple [] -> 
    compile_coerce ctxt (Lower.pat_rep ()) DropRep (Ast.TyParam (Ast.TyParam.fresh ""))
  | Typed.PVar var -> 
    compile_val_var_bind ctxt var (et pat) (Lower.pat_rep ()) funcloc_opt 
  | Typed.PAnnotated (p, _) -> compile_pattern ctxt fail p funcloc_opt
  | Typed.PAs (p, var) -> 
    compile_pattern ctxt fail p funcloc_opt;
    compile_val_var_bind ctxt var (et p) (Lower.pat_rep ()) funcloc_opt
  | Typed.PTuple ps -> 
    let typeidx = Lower.lower_var_type ctxt (et pat) in
    let tmp = emit_local ctxt {ltype = RefT (Types.Null, VarHT (StatX typeidx))} in
    compile_coerce ctxt (Lower.pat_rep ()) Lower.rigid_rep (et pat); 
    emit ctxt [
      LocalSet (tmp);
    ];
    List.iteri (fun i pI ->
      if classify_pat pI > IrrelevantPat then begin
        emit ctxt [
          LocalGet tmp;
        ];
        emit ctxt [
          StructGet (typeidx, i, None);
        ];
        compile_coerce ctxt Lower.field_rep (Lower.pat_rep ()) (et pI);
        compile_pattern ctxt fail pI funcloc_opt;
      end
    ) ps
  | Typed.PVariant (lbl, pat) -> 
    (match (Lower.find_lbl lbl ctxt) with 
    | {tag = i; typeidx = t} -> 
      let tmp = emit_local ctxt {ltype = RefT (Types.Null, VarHT (StatX t))} in
      emit ctxt [
        LocalGet tmp;
        StructGet (t, 0, None);
        IntConst (I32T, i);
        BrIf fail
      ];
      match pat with 
      | None -> ()
      | Some x -> 
        (
          emit ctxt [
            LocalGet tmp;
            StructGet (t, 1, None);
          ];
          compile_coerce ctxt Lower.field_rep (Lower.pat_rep ()) (et x);
          compile_pattern ctxt fail x funcloc_opt;
        )
    )
  | Typed.PConst const -> 
    compile_coerce ctxt (Lower.pat_rep ()) Lower.rigid_rep (et pat);
    compile_lit ctxt const; 
    (match et pat with 
    | Ast.TyConst (IntegerTy) | Ast.TyConst (BooleanTy) -> 
      emit ctxt [Wasm.Ne I32T]
    | Ast.TyConst (FloatTy) -> 
      emit ctxt [Wasm.Ne F64T] 
    | Ast.TyConst (StringTy) -> 
      emit ctxt [Call (compile_text_eq ctxt); Eqz I32T]
    | _ -> assert false
    );
    emit ctxt [
      BrIf fail
    ]

    (* expressions *)
and compile_expression (ctxt : 'a ctxt) (exp : Typed.expression) dst : Lower.func_loc option= 
  let emit ctxt = List.iter (emit_instr ctxt) in 
  let t = et exp in
  match it exp with
  | Typed.Var var -> 
    compile_val_var ctxt var t dst;
    let _, func_loc_opt = find_val_var ctxt var ctxt.ext.envs in
    func_loc_opt
  | Const c -> 
    compile_lit ctxt c; None
  | Annotated (exp1, _) -> compile_expression ctxt exp1 dst
  | Tuple [] -> compile_coerce ctxt Lower.unit_rep dst (Ast.TyTuple []); None
  | Tuple es -> 
    let typ = Lower.lower_var_type ctxt t in 
    List.iter (fun e -> ignore (compile_expression ctxt e Lower.field_rep)) es;
    emit ctxt [
      StructNew (typ, Explicit)
    ];
    compile_coerce ctxt Lower.rigid_rep dst t;
    None
  | Variant (lbl, e) -> 
    let data = (Lower.find_lbl lbl ctxt) in
    emit ctxt [
      IntConst (I32T, data.tag);
    ];
    (match e with 
    | None -> ()
    | Some x -> 
      ignore (compile_expression ctxt x (Lower.field_rep));
    );
    emit ctxt [
      StructNew (data.typeidx, Explicit);
    ];
    compile_coerce ctxt Lower.rigid_rep dst (et exp);
    None
  | Lambda _ -> 
    Some (compile_func ctxt exp)
  | RecLambda (var, abs) -> Some (compile_func_rec ctxt (Typed.make_expression (Typed.Lambda abs) (et abs)) var t) 

    (* functions *)

and compile_func ctxt e : Lower.func_loc =
  let func_loc, def, _fixup = compile_func_staged ctxt Ast.VariableMap.empty e in
  def ctxt;
  func_loc

and compile_func_rec ctxt (e : Typed.expression) rec_var f_ty: Lower.func_loc = 
  match f_ty with 
  | Ast.TyArrow (ty_from, _) ->
  let recs = Ast.VariableMap.add rec_var ty_from Ast.VariableMap.empty in
  let func_loc, def, _fixup = compile_func_staged ctxt recs e in
  def ctxt;
  func_loc
  | _ -> failwith "this function only accepts reclambdas"

and compile_func_staged ctxt (rec_xs : Ast.ty Ast.VariableMap.t) (f : Typed.expression) : Lower.func_loc * _ * _ =
  let remove_keys_of_second_map map1 map2 =
    Ast.VariableMap.filter (fun key _ -> not (Ast.VariableMap.mem key map2)) map1 in
  let emit ctxt = List.iter (emit_instr ctxt) in
  let temporary = Typed.free_exp f in
  let t = remove_keys_of_second_map temporary rec_xs in 
  let vars = filter_vars ctxt t in
  let t = et f in
  let rec flat ps (e : Typed.expression) recs =
    match it e with
    | Typed.Lambda {it = (p, {it = Return x; _}); _} -> flat (p::ps) x recs
    | RecLambda (var, {it = (p, {it = Return x; _}); _}) ->
      (match et e with 
      | Ast.TyArrow (from_ty, _) ->
      flat (p :: ps) x (Ast.VariableMap.add var from_ty recs)
      | _ -> failwith "it has to be TyArrow")
    | _ ->
      let fn, def_func = emit_func_deferred ctxt in
      let envflds, fixups = Lower.lower_clos_env ctxt vars rec_xs in
      let ps = List.rev ps in
      let arity = List.length ps in
      let _code, closN, closNenv = Lower.lower_clos_type ctxt arity envflds in
      let def ctxt =
        let argts, argv_opt = Lower.lower_param_types ctxt arity in
        def_func ctxt ((RefT (NoNull, VarHT (StatX closN))) :: argts) [RefT Lower.absref] (fun ctxt _ ->
          let ctxt = Lower.enter_scope ctxt LocalScope in
          let clos = emit_param ctxt in
          let args = List.map (fun _ -> emit_param ctxt) argts in
          let arg0 = List.hd args in
          compile_load_env ctxt clos closNenv vars envflds;

          let partial = List.exists (fun p -> classify_pat p = PartialPat) ps in
          if not partial then
            List.iteri (fun i pI ->
              match classify_pat pI with
              | IrrelevantPat ->
                ignore (compile_expression ctxt e Lower.arg_rep)
              | TotalPat ->
                compile_load_arg ctxt i arg0 argv_opt;
                compile_coerce ctxt Lower.arg_rep (Lower.pat_rep ()) (et pI);
                compile_pattern ctxt (-1) pI None;
                ignore (compile_expression ctxt e Lower.arg_rep)
              | PartialPat -> assert false
            ) ps
          else
            let block bt es = Wasm.Block (bt, es) in
            emit_block ctxt block (ValBlockType None) (fun ctxt ->
              emit_block ctxt block (ValBlockType None) (fun ctxt ->
                List.iteri (fun i pI ->
                  match classify_pat pI with
                  | IrrelevantPat -> 
                    ignore (compile_expression ctxt e Lower.arg_rep)
                  | TotalPat ->
                    compile_load_arg ctxt i arg0 argv_opt;
                    compile_coerce ctxt Lower.arg_rep (Lower.pat_rep ()) (et pI);
                    compile_pattern ctxt (-1) pI None;
                    ignore (compile_expression ctxt e Lower.arg_rep);
                  | PartialPat ->
                    compile_load_arg ctxt i arg0 argv_opt;
                    compile_coerce ctxt Lower.arg_rep (Lower.pat_rep ()) (et pI);
                    compile_pattern ctxt 0 pI None;
                    ignore (compile_expression ctxt e Lower.arg_rep);
                ) ps;
                emit ctxt [Br (1)];
              );
              emit ctxt [Unreachable]
            );
        );
        compile_alloc_clos
          ctxt fn (List.length ps) vars rec_xs closNenv
      in
      let fixup ctxt self =
        if fixups <> [] then begin
          let tmp = emit_local ctxt ({ltype = RefT (Null, VarHT (StatX closNenv))}) in
          let rttidx = (Types.NoNull, Types.VarHT (StatX closNenv)) in
          compile_val_var ctxt self t Lower.ref_rep;
          emit ctxt [
            (*ref_as_data;*) 
            RefCast (rttidx);
            LocalSet (tmp);
          ];
          List.iter (fun (x, t, i) ->
            emit ctxt [Wasm.LocalGet (tmp)];
            compile_val_var ctxt x t (Lower.clos_rep ());
            emit ctxt [
              StructGet ((closNenv), (Lower.clos_env_idx + i), None);
            ];
          ) fixups
        end
      in
      Lower.{funcidx = fn; typeidx = closN; arity = List.length ps}, def, fixup
  in flat [] f rec_xs



let rec compile_computation ctxt comp dst = 
  let emit ctxt = List.iter (emit_instr ctxt) in
  let block bt es = Wasm.Block (bt, es) in
  match it comp with
  | Typed.Return exp -> compile_expression ctxt exp Lower.rigid_rep 
  | Do (compute, {it = (pat, cont); _}) -> 
    (match classify_pat pat with
    | IrrelevantPat ->
      ignore (compile_computation ctxt compute Lower.DropRep;)
    | TotalPat ->
      let funcloc_opt = compile_computation ctxt compute (Lower.pat_rep ()) in
      compile_pattern ctxt (-1) pat funcloc_opt;
    | PartialPat ->
      emit_block ctxt block (ValBlockType None)(fun ctxt ->
        emit_block ctxt block (ValBlockType None) (fun ctxt ->
          let funcloc_opt = compile_computation ctxt compute (Lower.pat_rep ()) in
          compile_pattern ctxt 0 pat funcloc_opt;
          emit ctxt [Br (1)];
        );
        emit ctxt [Unreachable]
      ) 
    );
    compile_computation ctxt cont (Lower.rigid_rep)
  | Match (exp, []) -> 
    ignore (compile_expression ctxt exp (Lower.pat_rep ()));
    emit ctxt [Unreachable;];
    None
  | Match (exp, abs_ls) -> 
    let t1 = et exp in
    let ty = et comp in
    let tmp = emit_local ctxt ({ltype = Lower.lower_value_type ctxt (Lower.tmp_rep ()) t1}) in
    let block bt es = Wasm.Block (bt, es) in
    ignore (compile_expression ctxt exp (Lower.tmp_rep ()));
    emit ctxt [
      LocalSet (tmp);
    ];
    let bt = Lower.lower_block_type ctxt dst ty in
    emit_block ctxt block bt (fun ctxt ->
      let ends_with_partial =
        List.fold_left (fun _ {it = (pI, cI); _} ->
          match classify_pat pI with
          | IrrelevantPat ->
            ignore (compile_computation ctxt cI dst);
            emit ctxt [Br 0];
            false
          | TotalPat ->
            let ctxt = Lower.enter_scope ctxt LocalScope in
            let typ = et pI in
            emit ctxt [LocalGet (tmp)];
            compile_coerce ctxt (Lower.tmp_rep ()) (Lower.pat_rep ()) typ;
            compile_pattern ctxt (-1) pI None;
            ignore (compile_computation ctxt cI dst);
            emit ctxt [Br 0];
            false
          | PartialPat ->
            let ctxt = Lower.enter_scope ctxt LocalScope in
            emit_block ctxt block (ValBlockType None)(fun ctxt ->
              emit ctxt [LocalGet tmp];
              compile_coerce ctxt (Lower.tmp_rep ()) (Lower.pat_rep ()) t1;
              compile_pattern ctxt 0 pI None;
              ignore (compile_computation ctxt cI dst);
              emit ctxt [Br 1];
            );
            true
        ) true abs_ls 
      in
      if ends_with_partial then emit ctxt [Unreachable]
    );
    None
  | Apply (exp1, exp2) -> 
    let ty = et comp in 
    match exp1.it with 
    | (RecLambda _ | Lambda _) -> 
      (match compile_expression ctxt exp1 Lower.rigid_rep with
      | Some {funcidx = f; arity = n; _} when n = 1 ->
        compile_push_args ctxt 1 0 (fun i ->
          ignore (compile_expression ctxt exp2 (Lower.arg_rep), i)
        );
        emit ctxt [
          Call (f);
        ]
      | Some {typeidx = t; arity = n; _} ->
        compile_push_args ctxt 1 0 (fun i ->
          ignore (compile_expression ctxt exp2 (Lower.arg_rep), i)
        );
        emit ctxt [
          Call (compile_func_apply n t ctxt);
        ]
      | _ -> failwith "not possible"
      );

      compile_coerce ctxt Lower.arg_rep dst ty;
      None
    | (Var x) -> 
      let _, env = Lower.current_scope ctxt in
      (match (Env.find_func x !env).it with
      | {funcidx = f; arity = n; _} when n = 1 ->
        compile_push_args ctxt 1 0 (fun i ->
          ignore (compile_expression ctxt exp2 (Lower.arg_rep), i)
        );
        emit ctxt [
          Call f;
        ]
      | {typeidx = t; arity = n; _} ->
        compile_push_args ctxt 1 0 (fun i ->
          ignore (compile_expression ctxt exp2 (Lower.arg_rep), i)
        );
        emit ctxt [
          Call (compile_func_apply n t ctxt);
        ]
      );
      compile_coerce ctxt Lower.arg_rep dst ty;
      None

    | _ -> failwith "not possible"

let compile_ty_defs ctxt ty_defs = 
  let _, env = Lower.current_scope ctxt in
  let compile_ty_def ty_def = 
    match ty_def with 
    | _, name, ty -> 
      match ty with 
      | Ast.TyInline t -> 
        let tyidx = Lower.lower_inline_type ctxt t in 
          env := Env.extend_typ !env name (make_phrase Lower.([(None, {tag = -1; typeidx = tyidx})]))
      | Ast.TySum t_ls -> 
        let x = (List.mapi (fun i (lbl, ty_opt) -> 
          let tyidx = (Lower.lower_sum_type ctxt ty_opt) in 
          Lower.extend_lbl ctxt lbl Lower.{tag = i; typeidx = tyidx};
          Lower.((Some lbl, {tag = i; typeidx = tyidx})))
        ) t_ls in
         env := Env.extend_typ !env name (make_phrase x)
  in
  List.iter compile_ty_def ty_defs

let compile_command ctxt comp dst = 
  match comp with 
  | Typed.TyDef ty_defs -> 
    compile_ty_defs ctxt ty_defs
  | TopLet (name, exp) -> 
    let ctxt' = Lower.enter_scope ctxt Lower.LocalScope in
    (match it exp with
    | Lambda _ -> 
      print_endline "lam";
      let _, env = Lower.current_scope ctxt' in
      let funcloc_opt = compile_func ctxt' exp in
      env := Env.extend_func !env name (make_phrase (funcloc_opt))
    | RecLambda (var, _) -> 
      print_endline "rec_lam";
      let _, env = Lower.current_scope ctxt' in
      let funcloc_opt = compile_func_rec ctxt' exp var (et exp)in
      env := Env.extend_func !env name (make_phrase (funcloc_opt))
    | _ -> 
      compile_val_var_bind ctxt name (et exp) dst None
    )
  | TopDo cmp -> 
    let _, env = Lower.current_scope ctxt in
    let pat = Typed.make_pattern Typed.PNonbinding (Ast.TyTuple []) in
    let abs = Typed.make_abstraction (pat, cmp) (Ast.TyArrow (Ast.TyTuple [], et cmp)) in
    let lam = Typed.make_expression (Typed.Lambda abs) (et abs) in
    let func_loc = compile_func ctxt lam in 
    let name = "run_" ^ (string_of_int !env.runs) in
    emit_func_export ctxt ("func " ^ name) func_loc.funcidx;
    env := Env.update_runs !env 

let rec compile_commands ctxt ds dst =
  match ds with
  | [] ->
    compile_coerce ctxt Lower.unit_rep dst (Ast.TyTuple [])
  | [d] ->
    compile_command ctxt d dst
  | d::ds' ->
    compile_command ctxt d DropRep;
    compile_commands ctxt ds' dst

let compile_prog cmds : unit =
  let ctxt = Lower.enter_scope (Lower.make_ctxt ()) GlobalScope in
  (* Compile declarations directly *)
  compile_commands ctxt cmds (Lower.global_rep ());
  (* Directly emit exports for modules and values *)
  let _, env = Lower.current_scope ctxt in
  Env.iter_vals (fun x' locs ->
    let name = Ast.string_of_expression (Ast.Var x') in
    let (loc, funcloc_opt) = locs.it in
    emit_global_export ctxt name (Lower.as_global_loc loc);
    Option.iter (fun Lower.{funcidx; _} ->
      emit_func_export ctxt ("func " ^ name) funcidx) funcloc_opt
  ) !env;
  (* Generate the WebAssembly module *)
  Emit.gen_module ctxt
  |> Arrange.module_
  |> Sexpr.to_string 64
  |> print_endline
