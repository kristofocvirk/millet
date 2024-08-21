module Ast = Language.Ast
module Const = Language.Const
module Ty = Typechecker
module Lower = Lower
module Env = Env
open Wasm
open Emit
open Source

type pat_class = IrrelevantPat | TotalPat | PartialPat

let max_func_arity = 12

let ref_cast idx = Wasm.RefCast (Wasm.NoNull, Wasm.VarHT (Wasm.StatX idx))

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

let rec find_var f ctxt x envs =
  match envs with
  | [] ->
    assert false
  | (_, env)::envs' ->
    match f x !env with
    | Some {it = locs; _} -> locs
    | None -> find_var f ctxt x envs'

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

let compile_load_args ctxt i j shift arg0 src_argv_opt =
  assert (j <= max_func_arity || src_argv_opt <> None);
  if j - i > max_func_arity && i = 0 then
    (* Reuse argv *)
    emit_instr ctxt (LocalGet (arg0 + shift))
  else
    compile_push_args ctxt (j - i) shift (fun k ->
      compile_load_arg ctxt (i + k) (arg0 + shift) src_argv_opt
    )


let rec compile_func_apply arity ctxt typeidx=
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
      let block bt es = Block (bt, es) in
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
                  Call (compile_func_apply (arity - n) ctxt typeidx) ;
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
  let block bt es = Block (bt, es) in
  let loop bt es = Loop (bt, es) in
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
            Call (compile_func_apply (arity + 1) ctxt typeidx);
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
  env := Env.extend_val !env x ((@@) (loc, funcloc_opt))

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
  let x = (RefT (NoNull, VarHT (StatX idx))) in 
  {ltype = x}

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
          | (FieldT (_ ,ValStorageT (RefT (Null, _)))) -> Null
          | _ -> Nonull
        in
        env := Env.extend_val !env x
          ((@@) (Lower.ClosureLoc (null, idx, envlocal, closNenv), func_loc_opt)); 
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

let rec classify_pat = function
    | Ast.PVar _ -> TotalPat 
    | Ast.PAnnotated (p1, _) -> classify_pat p1
    | Ast.PAs (p1, _) -> classify_pat p1
    | Ast.PTuple ps -> List.fold_left max IrrelevantPat (List.map classify_pat ps)
    | Ast.PVariant (_, None) -> PartialPat
    | Ast.PVariant (_, Some p1) -> classify_pat p1
    | Ast.PConst _ -> PartialPat 
    | Ast.PNonbinding -> IrrelevantPat 

let rec compile_pattern ctxt (state : Ty.state)  (fail : int) pat funcloc_opt= 
  let emit ctxt = List.iter (emit_instr ctxt) in
  match pat with
  | Ast.PNonbinding | Ast.PTuple [] -> 
    compile_coerce ctxt (Lower.pat_rep ()) DropRep (Ast.TyParam (Ast.TyParam.fresh ""))
  | Ast.PVar var -> 
    let t, _, _ = Ty.infer_pattern state pat in
    compile_val_var_bind ctxt var t (Lower.pat_rep ()) funcloc_opt 
  | Ast.PAnnotated (pat, _) -> compile_pattern ctxt state fail pat funcloc_opt
  | Ast.PAs (pat, var) -> ignore (pat,var); failwith "not implemented"
  | Ast.PTuple ps -> 
    let typ, _, _ = Ty.infer_pattern state pat in 
    let typeidx = Lower.lower_var_type ctxt typ in
    let tmp = emit_local ctxt {ltype = RefT (Wasm.Null, VarHT (StatX typeidx))} in
    compile_coerce ctxt (Lower.pat_rep ()) Lower.rigid_rep typ; 
    emit ctxt [
      LocalSet (tmp);
    ];
    List.iteri (fun i pI ->
      let pat_ty, _, _ = Ty.infer_pattern state pI in
      if classify_pat pI > IrrelevantPat then begin
        emit ctxt [
          LocalGet tmp;
        ];
        emit ctxt [
          StructGet (typeidx, i, None);
        ];
        compile_coerce ctxt Lower.field_rep (Lower.pat_rep ()) pat_ty;
        compile_pattern ctxt state fail pI funcloc_opt;
      end
    ) ps
  | Ast.PVariant (lbl, pat) -> ignore (lbl, pat); failwith "not implemented"
  | Ast.PConst const as c -> 
    let typ, _, _ = Ty.infer_pattern state c in 
    compile_coerce ctxt (Lower.pat_rep ()) Lower.rigid_rep typ;
    ignore (compile_expression ctxt state (Ast.Const const) Lower.rigid_rep); 
    (match typ with 
    | Ast.TyConst (IntegerTy) | Ast.TyConst (BooleanTy) -> 
      emit ctxt [Wasm.Ne I32T]
    | Ast.TyConst (FloatTy) -> 
      emit ctxt [Wasm.Ne F64T] 
    | Ast.TyConst (StringTy) -> failwith "not implemented"
    | _ -> assert false
    )

    (* expressions *)
and compile_expression (ctxt : 'a ctxt) (state : Ty.state) exp dst : Lower.func_loc option= 
  let emit ctxt = List.iter (emit_instr ctxt) in 
  match exp with
  | Ast.Var var -> 
    let ty, _ = Ty.infer_expression state exp in  
    compile_val_var ctxt var ty dst;
    let _, func_loc_opt = find_val_var ctxt var ctxt.ext.envs in
    func_loc_opt
  | Ast.Const (Const.Integer i) -> emit ctxt [IntConst (I32T, i)]; None 
  | Ast.Const (Const.String s) -> ignore s; failwith "not implemented"
  | Ast.Const (Const.Boolean b) -> 
    (match b with 
    | true ->  emit ctxt [IntConst (I32T, 1)] 
    | false -> emit ctxt [IntConst (I32T, 0)]); None
  | Ast.Const (Const.Float f) -> emit ctxt [FloatConst (F64T, f)]; None 
  | Ast.Annotated (exp1, _) -> compile_expression ctxt state exp1 dst
  | Ast.Tuple [] -> compile_coerce ctxt Lower.unit_rep dst (Ast.TyTuple []); None
  | Ast.Tuple es -> 
    let ty, _ = Ty.infer_expression state exp in  
    let typ = Lower.lower_var_type ctxt ty in 
    List.iter (fun e -> ignore (compile_expression ctxt state e Lower.field_rep)) es;
    emit ctxt [
      StructNew (typ, Explicit)
    ];
    compile_coerce ctxt Lower.rigid_rep dst ty;
    None
  | Ast.Variant _ -> failwith "not implemented"
  | Ast.Lambda _ -> Some (compile_func ctxt state exp)
  | Ast.RecLambda (var, abs) -> Some (compile_func_rec ctxt state (Ast.Lambda abs) var)

    (* functions *)

and compile_func ctxt state e : Lower.func_loc =
  let func_loc, def, _fixup = compile_func_staged ctxt state Ast.VariableMap.empty e in
  def ctxt;
  func_loc

and compile_func_rec ctxt (state : Ty.state) e rec_var : Lower.func_loc = 
  let _, ty = Ast.VariableMap.find rec_var state.variables in 
  let recs = Ast.VariableMap.add rec_var ty Ast.VariableMap.empty in
  let func_loc, def, _fixup = compile_func_staged ctxt state recs e in
  def ctxt;
  func_loc

and compile_func_staged ctxt state (rec_xs : Ast.ty Ast.VariableMap.t) f : Lower.func_loc * _ * _ =
  let emit ctxt = List.iter (emit_instr ctxt) in
  let vars = filter_vars ctxt (Ty.free_exp state f) in
  let ty, _ = Ty.infer_expression state f in
  let rec flat ps (e : Ast.expression) recs =
    match e with
    | Ast.Lambda (p, Ast.Return x) -> flat (p::ps) x recs
    | Ast.RecLambda (var, (p, Ast.Return x)) ->
      let _, ty = Ast.VariableMap.find var state.variables in
      flat (p :: ps) x (Ast.VariableMap.add var ty recs)
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
              let ty, _, _ = Ty.infer_pattern state pI in
              match classify_pat pI with
              | IrrelevantPat -> ()
              | TotalPat ->
                compile_load_arg ctxt i arg0 argv_opt;
                compile_coerce ctxt Lower.arg_rep (Lower.pat_rep ()) (ty);
                compile_pattern ctxt state (-1) pI None
              | PartialPat -> assert false
            ) ps
          else
            let block bt es = Block (bt, es) in
            emit_block ctxt block (ValBlockType None)(fun ctxt ->
              emit_block ctxt block (ValBlockType None) (fun ctxt ->
                List.iteri (fun i pI ->
                  let ty, _, _ = Ty.infer_pattern state pI in
                  match classify_pat pI with
                  | IrrelevantPat -> ()
                  | TotalPat ->
                    compile_load_arg ctxt i arg0 argv_opt;
                    compile_coerce ctxt Lower.arg_rep (Lower.pat_rep ()) (ty);
                    compile_pattern ctxt state (-1) pI None
                  | PartialPat ->
                    compile_load_arg ctxt i arg0 argv_opt;
                    compile_coerce ctxt Lower.arg_rep (Lower.pat_rep ()) (ty);
                    compile_pattern ctxt state 0 pI None;
                ) ps;
                emit ctxt [Br (1)];
              );
              emit ctxt [Unreachable]
            );
          ignore (compile_expression ctxt state e Lower.arg_rep)
        );
        compile_alloc_clos
          ctxt fn (List.length ps) vars rec_xs closNenv
      in
      let fixup ctxt self =
        if fixups <> [] then begin
          let tmp = emit_local ctxt ({ltype = RefT (Null, VarHT (StatX closNenv))}) in
          let rttidx = (NoNull, VarHT (StatX closNenv)) in
          compile_val_var ctxt self ty Lower.ref_rep;
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

let rec compile_computation ctxt state comp dst = 
  let emit ctxt = List.iter (emit_instr ctxt) in
  let block bt es = Block (bt, es) in
  match comp with
  | Ast.Return exp -> compile_expression ctxt state exp Lower.rigid_rep 
  | Ast.Do (compute, (pat, cont)) -> 
    (match classify_pat pat with
    | IrrelevantPat ->
      ignore (compile_computation ctxt state compute Lower.DropRep;)
    | TotalPat ->
      let funcloc_opt = compile_computation ctxt state compute (Lower.pat_rep ()) in
      compile_pattern ctxt state (-1) pat funcloc_opt;
    | PartialPat ->
      emit_block ctxt block (ValBlockType None)(fun ctxt ->
        emit_block ctxt block (ValBlockType None) (fun ctxt ->
          let funcloc_opt = compile_computation ctxt state compute (Lower.pat_rep ()) in
          compile_pattern ctxt state 0 pat funcloc_opt;
          emit ctxt [Br (1)];
        );
        emit ctxt [Unreachable]
      ) 
    );
    compile_computation ctxt state cont (Lower.rigid_rep)
  | Ast.Match (exp, []) -> 
    ignore (compile_expression ctxt state exp (Lower.pat_rep ()));
    emit ctxt [Unreachable;];
    None
  | Ast.Match (exp, abs_ls) -> 
    let t1, _ = Ty.infer_expression state exp in
    let ty, _ = Ty.infer_computation state comp in
    let tmp = emit_local ctxt ({ltype = Lower.lower_value_type ctxt (Lower.tmp_rep ()) t1}) in
    let block bt es = Block (bt, es) in
    ignore (compile_expression ctxt state exp (Lower.tmp_rep ()));
    emit ctxt [
      LocalSet (tmp);
    ];
    let bt = Lower.lower_block_type ctxt dst ty in
    emit_block ctxt block bt (fun ctxt ->
      let ends_with_partial =
        List.fold_left (fun _ (pI, cI) ->
          match classify_pat pI with
          | IrrelevantPat ->
            ignore (compile_computation ctxt state cI dst);
            emit ctxt [Br 0];
            false
          | TotalPat ->
            let ctxt = Lower.enter_scope ctxt LocalScope in
            let typ, _, _ = Ty.infer_pattern state pI in
            emit ctxt [LocalGet (tmp)];
            compile_coerce ctxt (Lower.tmp_rep ()) (Lower.pat_rep ()) typ;
            compile_pattern ctxt state (-1) pI None;
            ignore (compile_computation ctxt state cI dst);
            emit ctxt [Br 0];
            false
          | PartialPat ->
            let ctxt = Lower.enter_scope ctxt LocalScope in
            emit_block ctxt block (ValBlockType None)(fun ctxt ->
              emit ctxt [LocalGet tmp];
              compile_coerce ctxt (Lower.tmp_rep ()) (Lower.pat_rep ()) t1;
              compile_pattern ctxt state 0 pI None;
              ignore (compile_computation ctxt state cI dst);
              emit ctxt [Br 1];
            );
            true
        ) true abs_ls 
      in
      if ends_with_partial then emit ctxt [Unreachable]
    );
    None
  | Ast.Apply (exp1, exp2) -> 
    match exp1 with 
    | (RecLambda _ | Lambda _) -> ignore (exp1, exp2); failwith "not implemented"
    | (Var _) -> ignore (exp1,exp2); failwith "not implemented"
    | _ -> failwith "not possible"

let compile_ty_defs ctxt ty_defs = 
  let _, env = Lower.current_scope ctxt in
  let compile_ty_def ty_def = 
    match ty_def with 
    | _, name, ty -> 
      match ty with 
      | Ast.TyInline t -> 
        let tyidx = Lower.lower_inline_type ctxt t in 
         env := Env.extend_typ !env name ((@@) Lower.([(None, {tag = -1; typeidx = tyidx})]))
      | Ast.TySum t_ls -> 
        let x = (List.mapi (fun i (lbl, ty_opt) -> 
          let tyidx = (Lower.lower_sum_type ctxt ty_opt) in 
          Lower.((Some lbl, {tag = i; typeidx = tyidx})))
        ) t_ls in
         env := Env.extend_typ !env name ((@@) x)
  in
  List.iter compile_ty_def ty_defs

let compile_command ctxt state comp = 
  match comp with 
  | Ast.TyDef ty_defs -> compile_ty_defs ctxt ty_defs
  | Ast.TopLet (name, exp) -> 
    (match exp with
    | Ast.Lambda _ -> 
      let _, env = Lower.current_scope ctxt in
      let funcloc_opt = compile_func ctxt state exp in
      env := Env.extend_func !env name ((@@) (funcloc_opt))
    | Ast.RecLambda (var, _) -> 
      let _, env = Lower.current_scope ctxt in
      let funcloc_opt = compile_func_rec ctxt state exp var in
      env := Env.extend_func !env name ((@@) (funcloc_opt))
    | _ -> 
      let var_ty, _ = Ty.infer_expression state exp in
      compile_val_var_bind ctxt name var_ty (Lower.global_rep ()) None
    )
  | Ast.TopDo cmp -> ignore cmp; failwith "not implemented" 