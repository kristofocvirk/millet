module Ast = Language.Ast
module Const = Language.Const
module Ty = Typechecker
module Lower = Lower
module Env = Env
open Wasm
open Emit
open Source

type pat_class = IrrelevantPat | TotalPat | PartialPat

let rec compile_coerce ctxt src dst t =
  if src <> dst then
  let ref_cast idx = Wasm.RefCast (Wasm.NoNull, Wasm.VarHT (Wasm.StatX idx)) in
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

let find_val_var = find_var Env.find_opt_val 


let filter_loc (ctxt : Lower.ctxt) find_var vals =
  Ast.VariableMap.filter (fun x _ ->
    match find_var ctxt x ctxt.ext.envs with
    | (Lower.PreLoc _ | Lower.GlobalLoc _), _ -> false
    | (Lower.LocalLoc _ | Lower.ClosureLoc _), _ -> true
  ) vals

let filter_vars (ctxt : Lower.ctxt) vars =
  filter_loc ctxt find_val_var vars

let compile_var find_var (ctxt : Lower.ctxt)x =
  let loc, funcloc_opt = find_var ctxt x ctxt.ext.envs in
  (match loc with
  | Lower.PreLoc idx -> ignore idx; failwith "Preloc val_var"
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

let rec classify_pat = function
    | Ast.PVar _ -> TotalPat 
    | Ast.PAnnotated (p1, _) -> classify_pat p1
    | Ast.PAs (p1, _) -> classify_pat p1
    | Ast.PTuple ps -> List.fold_left max IrrelevantPat (List.map classify_pat ps)
    | Ast.PVariant (_, None) -> PartialPat
    | Ast.PVariant (_, Some p1) -> classify_pat p1
    | Ast.PConst _ -> PartialPat 
    | Ast.PNonbinding -> IrrelevantPat 

let rec compile_pattern ctxt (state : Ty.state)  fail pat = 
  let emit ctxt = List.iter (emit_instr ctxt) in
  match pat with
  | Ast.PNonbinding | Ast.PTuple [] -> 
    compile_coerce ctxt (Lower.pat_rep ()) DropRep (Ast.TyParam (Ast.TyParam.fresh ""))
  | Ast.PVar var -> ignore var; failwith "not implemeted PVar"
  | Ast.PAnnotated (pat, _) -> compile_pattern ctxt state fail pat
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
        compile_pattern ctxt state fail pI;
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
    | Ast.TyConst (FloatTy) -> emit ctxt [Wasm.Ne F64T] 
    | Ast.TyConst (StringTy) -> failwith "not implemented"
    | _ -> assert false
    )

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
  | Ast.RecLambda _ -> failwith "not implemented"

and compile_func ctxt state e : Lower.func_loc =
  let func_loc, def, _fixup = compile_func_staged ctxt state Env.Set.empty e in
  def ctxt;
  func_loc

and compile_func_staged ctxt rec_xs f : Lower.func_loc * _ * _ =
  let emit ctxt = List.iter (emit_instr ctxt f.at) in
  let vars = filter_vars ctxt (free_exp f) in
  let rec flat ps e =
    match e.it with
    | FunE (p, e') -> flat (p::ps) e'
    | _ ->
      let fn, def_func = emit_func_deferred ctxt f.at in
      let envflds, fixups = lower_clos_env ctxt f.at vars rec_xs in
      let ps = List.rev ps in
      let arity = List.length ps in
      let _code, closN, closNenv = lower_clos_type ctxt f.at arity envflds in
      let def ctxt =
        let argts, argv_opt = lower_param_types ctxt f.at arity in
        def_func ctxt W.(ref_ closN :: argts) [absref] (fun ctxt _ ->
          let ctxt = enter_scope ctxt LocalScope in
          let clos = emit_param ctxt f.at in
          let args = List.map (fun _ -> emit_param ctxt f.at) argts in
          let arg0 = List.hd args in
          compile_load_env ctxt clos closN closNenv vars envflds f.at;

          let partial = List.exists (fun p -> classify_pat p = PartialPat) ps in
          if not partial then
            List.iteri (fun i pI ->
              match classify_pat pI with
              | IrrelevantPat -> ()
              | TotalPat ->
                Intrinsic.compile_load_arg ctxt pI.at i arg0 argv_opt;
                compile_coerce ctxt arg_rep (pat_rep ()) (Source.et pI) f.at;
                compile_pat ctxt (-1l) None pI
              | PartialPat -> assert false
            ) ps
          else
            emit_block ctxt f.at W.block W.void (fun ctxt ->
              emit_block ctxt f.at W.block W.void (fun ctxt ->
                List.iteri (fun i pI ->
                  match classify_pat pI with
                  | IrrelevantPat -> ()
                  | TotalPat ->
                    Intrinsic.compile_load_arg ctxt pI.at i arg0 argv_opt;
                    compile_coerce ctxt arg_rep (pat_rep ()) (Source.et pI) f.at;
                    compile_pat ctxt (-1l) None pI
                  | PartialPat ->
                    Intrinsic.compile_load_arg ctxt pI.at i arg0 argv_opt;
                    compile_coerce ctxt arg_rep (pat_rep ()) (Source.et pI) f.at;
                    compile_pat ctxt 0l None pI;
                ) ps;
                emit ctxt W.[br (1l @@ f.at)];
              );
              emit ctxt W.[unreachable]
            );
          compile_exp ctxt e arg_rep
        );
        compile_alloc_clos
          ctxt fn (List.length ps) vars rec_xs closN closNenv f.at
      in
      let fixup ctxt self =
        if fixups <> [] then begin
          let tmp = emit_local ctxt f.at W.(ref_null_ closNenv) in
          let rttidx = lower_rtt_global ctxt f.at closNenv in
          compile_val_var ctxt Source.(self @@ f.at) (Source.et f) ref_rep;
          emit ctxt W.[
            ref_as_data;
            global_get (rttidx @@ f.at);
            ref_cast;
            local_set (tmp @@ f.at);
          ];
          List.iter (fun (x, t, i) ->
            emit ctxt W.[local_get (tmp @@ f.at)];
            compile_val_var ctxt Source.(x @@ f.at) t (clos_rep ());
            emit ctxt W.[
              struct_set (closNenv @@ f.at) (clos_env_idx +% int32 i @@ f.at)
            ];
          ) fixups
        end
      in
      {funcidx = fn; typeidx = closN; arity = List.length ps}, def, fixup
  in flat [] f

let compile_computation ctxt state = function
  | Ast.Return exp -> compile_expression ctxt state exp Lower.rigid_rep 
  | Ast.Do (comp, abs) -> ignore (comp, abs); failwith "not implemented" 
  | Ast.Match (exp, abs_ls) -> let comp_exp = compile_expression ctxt state exp in ignore (comp_exp, abs_ls); failwith "not implemented" 
  | Ast.Apply (exp1, exp2) -> 
    match exp1 with 
    | (RecLambda _ | Lambda _) -> ignore (exp1, exp2); failwith "not implemented"
    | (Var _) -> ignore (exp1,exp2); failwith "not implemented"
    | _ -> failwith "not possible"


let compile_ty_def = function
 | Ast.TySum _ -> failwith "not implemented"
 | Ast.TyInline _ -> failwith "not implemented"

let compile_command ctxt state = function
  | Ast.TyDef _ -> failwith "not implemented" 
  | Ast.TopLet (name, exp) -> 
    ignore name;
    (match exp with
    | Ast.Const _ -> compile_expression ctxt state exp Lower.rigid_rep
    | Ast.Annotated _ -> compile_expression ctxt state exp Lower.rigid_rep
    | Ast.Tuple _ | Ast.Var _ | Ast.Variant _  -> failwith "not implemented"
    | Ast.Lambda _ | Ast.RecLambda _ -> failwith "not implemented"
    )
  | Ast.TopDo _ -> failwith "not implemented" 