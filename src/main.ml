module Ctx = Map.Make (String)
module Subst = Map.Make (Int)

type ty =
  | TyUnifVar of int
  | TyVar of string
  | TyLam of ty * ty
  [@@deriving show, ord]

type ty_schema =
  | TSTy of ty
  | TSForAll of string * ty_schema
  [@@deriving show, ord]

type expr =
  | ExprVar of string
  | ExprLetIn of string * expr * expr
  | ExprAbs of string * expr
  | ExprApp of expr * expr
  [@@deriving show]

type ty_ctx = ty_schema Ctx.t

type subst = ty Subst.t

type tycheck_state = {
  next_unif_var_num : int ref;
  ty_ctx : ty_ctx; [@opaque]
} [@@deriving show]

type ty_error =
  | TyErrUnboundVar of string
  | TyErrUnimplemented
  | TyErrUnknown
  [@@deriving show]

type 'a tycheck_result = ('a, ty_error) result

type 'a tychecker = tycheck_state -> 'a tycheck_result

let (>>=) (m : 'a tychecker) (f : 'a -> 'b tychecker) : 'b tychecker =
  fun state ->
    match m state with
    | Ok res -> f res state
    | Error err -> Error err

let (>>) m f = m >>= fun _ -> f

let (let*) = (>>=)

let return (x : 'a) : 'a tychecker = fun _ -> Ok x

let get_state : tycheck_state tychecker =
  fun state -> Ok state

let get_ctx : ty_ctx tychecker =
  fun state -> Ok state.ty_ctx

let transform_state f m : 'a tychecker=
  fun state -> m (f state)

let transform_ty_ctx (f : ty_ctx -> ty_ctx) m =
  transform_state (fun state -> { state with ty_ctx = f state.ty_ctx }) m

let with_extended_ty_ctx name ty (m : 'a tychecker) : 'a tychecker =
  transform_ty_ctx (Ctx.add name ty) m

let new_unif_var : int tychecker = fun state ->
  (* TODO: this will run out of variables after 26 letters lol *)
  state.next_unif_var_num := 1 + !(state.next_unif_var_num);
  return (!(state.next_unif_var_num)) state
  (* return (String.make 1 @@ Char.chr @@ !(state.next_unif_var_num)) state *)

let fail err = fun _ -> Error err

let rec substitute (s : subst) (ty : ty) : ty =
  (* perform subst of all unification variables *)
  match ty with
  | TyUnifVar i -> substitute s (Subst.find i s) (* has potential to loop infinitely? *)
  | TyVar x -> TyVar x
  | TyLam (t1, t2) -> TyLam (substitute s t1, substitute s t2)

let rec substitute_ty_schema (s: subst) (ty_schema : ty_schema) : ty_schema =
  match ty_schema with
  | TSTy t -> TSTy (substitute s t)
  | TSForAll (x, t) -> TSForAll (x, substitute_ty_schema s t)

let rec substitute_env (s : subst) (ty_ctx : ty_ctx) : ty_ctx =
  Ctx.map (substitute_ty_schema s) ty_ctx

let overwrite_subst (s1 : subst) (s2 : subst) : subst =
  let merge _ x y = match x, y with
  | Some x, _ -> Some x
  | None, y -> y
  in Subst.merge merge s1 s2

(* TODO: implement unify. http://cs.iit.edu/~cs440/lectures/lec15-unify.pdf *)
(* TODO: *)
(* TODO: *)
(* TODO: *)
(* TODO: *)
(* TODO: NEXT THING TO DO! *)
let rec unify (t1 : ty) (t2 : ty) : subst tychecker =
  match t1, t2 with
  | _ -> _
(* TODO: *)
(* TODO: *)
(* TODO: *)
(* TODO: *)
(* TODO: *)

let rec inst (t : ty_schema) : ty tychecker =
  let rec inst_ty (x : string) (i : int) (t : ty) =
    match t with
    | TyVar y -> if x = y then TyUnifVar i else TyVar y
    | TyUnifVar i -> TyUnifVar i
    | TyLam (t1, t2) -> TyLam (inst_ty x i t1, inst_ty x i t2)
  in match t with
  | TSTy t_inner -> return t_inner
  | TSForAll (x, t) ->
    let* unif_idx = new_unif_var in
    let* t' = inst t in
    return @@ inst_ty x unif_idx t'

let rec tycheck (e : expr) : (ty * subst) tychecker =
  let* ty_ctx = get_ctx in
  match e with
  | ExprVar x ->
    let x_ty_schema = Ctx.find x ty_ctx in
    let* x_ty = inst x_ty_schema in
    return (x_ty, Subst.empty)
  | ExprAbs (x, body) ->
    let* unif_idx = new_unif_var in
    let x_ty = TyUnifVar unif_idx in
    let* (body_ty, body_subst) = with_extended_ty_ctx x (TSTy x_ty) (tycheck body) in
    let x_ty_substituted = substitute body_subst x_ty in
    let expr_ty = TyLam (x_ty_substituted, body_ty) in
    return (expr_ty, body_subst)
  | ExprApp (lam, arg) ->
    let* (lam_ty, lam_subst) = tycheck lam in
    let* (arg_ty, arg_subst) = transform_ty_ctx (substitute_env lam_subst) (tycheck arg) in
    let* unif_idx = new_unif_var in
    let* unif_subst = unify (substitute arg_subst lam_ty) (TyLam (arg_ty, TyUnifVar unif_idx)) in
    let ret_ty = Subst.find unif_idx unif_subst in
    let expr_subst = overwrite_subst unif_subst (overwrite_subst arg_subst lam_subst) in
    return (ret_ty, expr_subst)
  (* | ExprLetIn (binder, bound, body) -> _ *)
  | _ -> fail TyErrUnimplemented
  (* match e with
  | ExprVar x -> (match Ctx.find_opt x ty_ctx with
    | None -> fail @@ TyErrUnboundVar x
    | Some t -> return (t, []))

  | ExprLetIn (binder, bound, body) ->
    let* (ty_bound, constrs_bound) = tycheck bound in
    with_extended_ty_ctx binder ty_bound begin
      let* (ty_body, constrs_body) = tycheck body in
      return (ty_body, List.append constrs_bound constrs_body)
    end

  | ExprAbs (x, body) ->
    let* ty_x = new_tyvar in
    with_extended_ty_ctx x (TyVar ty_x) begin
      tycheck body
    end

  | ExprApp (lam, arg) ->
    let* (ty_lam, constrs_lam) = tycheck lam in
    let* (ty_arg, constrs_arg) = tycheck arg in
    let* ty_in = new_tyvar in
    let* ty_out = new_tyvar in
    let constrs =
      [ CEqual (ty_lam, TyLam (TyVar ty_in, TyVar ty_out))
      ; CEqual (ty_arg, TyVar ty_in)
      ] in
    return (TyVar ty_out, constrs @ constrs_lam @ constrs_arg) *)

let init_tycheck_state =
  (* { next_unif_var_num = ref (97 - 1) *)
  { next_unif_var_num = ref 1
  ; ty_ctx = Ctx.empty
  }

let () = print_endline ""
let () = print_endline "Hello, World!"

let var x = ExprVar x
let let_in x e1 e2 = ExprLetIn (x, e1, e2)
let abs x e = ExprAbs (x, e)
let app e1 e2 = ExprApp (e1, e2)

(* let program = abs "f" (abs "x" (app (abs "y" (app (var "f") (var "y"))) (var "x"))) *)
(* program = \f. (\x. (\y. f y) x) *)
let program = abs "f" (abs "x" (app (var "f") (var "x")))
(* program = \f. (\x. f x) *)

let run_tycheck e = (
    let* (ty, cs) = tycheck e in
    let* state = get_state in
    return (ty, cs, state)
  ) init_tycheck_state

let _ = match run_tycheck program with
  | Ok (ty, subst, state) ->
    print_endline @@ show_ty ty;
    (* print_endline @@ show_subst subst; *)
    (* print_endline @@ [%derive.show: constr list] constrs;
    print_endline @@ ([%show: (string * ty) list] (Ctx.bindings state.ty_ctx)) *)
    (* let ctx_unified = unify state.ty_ctx constrs in *)
    (* print_endline @@ [%show: (string * ty) list] (Ctx.bindings ctx_unified) *)
  | Error err ->
    print_endline @@ show_ty_error err
