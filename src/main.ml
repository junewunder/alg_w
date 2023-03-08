module Ctx = Map.Make (String)
module Subst = Map.Make (Int)

type ty =
  | TyUnifVar of int [@printer fun fmt -> fun i -> fprintf fmt "?[%i]" i]
  | TyVar of string [@printer fun fmt -> fun x -> fprintf fmt "%s" x]
  | TyLam of ty * ty [@printer fun fmt -> fun (t1, t2) -> fprintf fmt "(%a -> %a)" pp_ty t1 pp_ty t2]
  (* TODO: add constructor for type parameters i.e. int list *)
  [@@deriving show, ord]

type ty_schema =
  | TSTy of ty [@printer fun fmt -> fun x -> fprintf fmt "%a" pp_ty x]
  | TSForAll of string * ty_schema [@printer fun fmt -> fun (x, ty_s) -> fprintf fmt "∀ %s. %a" x pp_ty_schema ty_s]
  [@@deriving show, ord]

type expr =
  | ExprVar of string [@printer fun fmt -> fun x -> fprintf fmt "%s" x]
  | ExprLetIn of string * expr * expr [@printer fun fmt -> fun (x, e1, e2) -> fprintf fmt "let %s = %a in %a" x pp_expr e1 pp_expr e2]
  | ExprAbs of string * expr [@printer fun fmt -> fun (x, e) -> fprintf fmt "\\%s. %a" x pp_expr e]
  | ExprApp of expr * expr [@printer fun fmt -> fun (e1, e2) -> fprintf fmt "(%a %a)" pp_expr e1 pp_expr e2]
  [@@deriving show]

type ty_ctx = ty_schema Ctx.t

type subst = ty Subst.t

(* let pp_ty_ctx (fmt : Format.formatter) (ctx : ty_ctx) =
  Format.fprintf fmt "%a" [%show: (string * ty_schema) list] (Ctx.bindings ctx) *)
let show_ty_ctx (ctx : ty_ctx) = [%show: (string * ty_schema) list] (Ctx.bindings ctx)
let show_subst (s : subst) = [%show: (int * ty) list] (Subst.bindings s)

(* let pp ty_ *)
type tycheck_state = {
  next_unif_var_num : int ref;
  ty_ctx : ty_ctx [@opaque];
  (* ty_ctx : ty_ctx [@printer pp_ty_ctx]; *)
} [@@deriving show]

type ty_error =
  | TyErrUnboundVar of string
  | TyErrCannotUnify of ty * ty
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

let with_transformed_state f m : 'a tychecker=
  fun state -> m (f state)

let with_transformed_ty_ctx (f : ty_ctx -> ty_ctx) m =
  with_transformed_state (fun state -> { state with ty_ctx = f state.ty_ctx }) m

let with_extended_ty_ctx name ty (m : 'a tychecker) : 'a tychecker =
  with_transformed_ty_ctx (Ctx.add name ty) m

let new_unif_var : int tychecker = fun state ->
  state.next_unif_var_num := 1 + !(state.next_unif_var_num);
  return (!(state.next_unif_var_num)) state

(* TODO: this will run out of variables after 26 letters lol *)
(* return (String.make 1 @@ Char.chr @@ !(state.next_unif_var_num)) state *)

let fail err = fun _ -> Error err

let rec substitute (s : subst) (ty : ty) : ty =
  (* perform subst of all unification variables *)
  match ty with
  (* | TyUnifVar i -> substitute s (Subst.find i s) *)
  (* has potential to loop infinitely? *)
  | TyUnifVar i -> (
      try substitute s (Subst.find i s)
      with Not_found -> TyUnifVar i
    )
  | TyVar x -> TyVar x
  | TyLam (t1, t2) -> TyLam (substitute s t1, substitute s t2)

let rec substitute_ty_schema (s: subst) (ty_schema : ty_schema) : ty_schema =
  match ty_schema with
  | TSTy t -> TSTy (substitute s t)
  | TSForAll (x, t) -> TSForAll (x, substitute_ty_schema s t)

let substitute_env (s : subst) (ty_ctx : ty_ctx) : ty_ctx =
  Ctx.map (substitute_ty_schema s) ty_ctx

let with_subsituted_ty_ctx subst (m : 'a tychecker) : 'a tychecker =
  with_transformed_ty_ctx (substitute_env subst) m

(* QUESTION: which of these is the correct behavior? *)
let substitute_subst (s1 : subst) (s2 : subst) : subst =
  Subst.map (substitute s1) s2
let overwrite_subst (s1 : subst) (s2 : subst) : subst =
  let merge _ x y = match x, y with
    | Some x, _ -> Some x
    | None, Some y -> Some (substitute s1 y)
    | None, None -> None
  in Subst.merge merge s1 s2

let rec contains_unif_var (i : int) (t : ty) : bool =
  match t with
  | TyVar _ -> false
  | TyUnifVar j -> i = j
  | TyLam (t1, t2) -> (contains_unif_var i t1) || (contains_unif_var i t2)

let generalize (t : ty) : ty_schema =
  let rec extract_unif_vars (t : ty) : int list =
    match t with
    | TyVar _ -> []
    | TyUnifVar i -> [i]
    | TyLam (t1, t2) -> List.append (extract_unif_vars t1) (extract_unif_vars t2)
  in
  let build_ty_schema (t : ty) (var_names : string list) : ty_schema =
    List.fold_right (fun i t -> TSForAll (i, t)) var_names (TSTy t)
  in
  let var_name_of_int i = String.make 1 @@ Char.chr (97 + i) in
  let unif_vars = List.sort_uniq Int.compare (extract_unif_vars t) in
  let unif_vars_from_zero = List.init (List.length unif_vars) (fun x -> x) in
  let var_names = List.map var_name_of_int unif_vars_from_zero in
  let vars = List.map (fun x -> TyVar x) var_names in
  let new_unif_var_names = (Subst.of_seq @@ List.to_seq (List.combine unif_vars vars)) in
  let generalized_ty = substitute new_unif_var_names t in
  build_ty_schema generalized_ty var_names

let rec unify (t1 : ty) (t2 : ty) : subst tychecker =
  print_endline "unifying" ;
  print_endline @@ show_ty t1 ;
  print_endline @@ show_ty t2 ;
  let fail_cannot_unify = fail (TyErrCannotUnify (t1, t2)) in
  match t1, t2 with
  | TyVar x1, TyVar x2 ->
    if x1 = x2
      then return Subst.empty
      else fail_cannot_unify
  | TyUnifVar i1, TyUnifVar i2 when i1 = i2 -> return Subst.empty
  | TyUnifVar i, t
  | t, TyUnifVar i ->
    if contains_unif_var i t
      then fail_cannot_unify
      else return @@ Subst.singleton i t
  | (TyLam (t1_arg, t1_body)), (TyLam (t2_arg, t2_body)) ->
    let* arg_subst = unify t1_arg t2_arg in
    unify (substitute arg_subst t1_body) (substitute arg_subst t2_body)
  (* missing two cases from Stefan's unification algorithm involving list and pair *)
  | _ -> fail_cannot_unify

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
  print_endline @@ show_ty_ctx ty_ctx;
  match e with
  | ExprVar x ->
    print_endline @@ x;
    let x_ty_schema = Ctx.find x ty_ctx in
    print_endline @@ show_ty_schema x_ty_schema;
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
    let* (arg_ty, arg_subst) = with_subsituted_ty_ctx lam_subst (tycheck arg) in
    let* unif_idx = new_unif_var in
    print_endline @@ [%show: int] unif_idx;
    print_endline @@ show_ty_ctx ty_ctx;
    let* unif_subst = unify (substitute arg_subst lam_ty) (TyLam (arg_ty, TyUnifVar unif_idx)) in
    print_endline @@ show_subst unif_subst;
    let ret_ty = substitute unif_subst (TyUnifVar unif_idx) in
    let expr_subst = substitute_subst unif_subst (substitute_subst arg_subst lam_subst) in
    return (ret_ty, expr_subst)

  | ExprLetIn (binder, bound, body) ->
    let* (bound_ty, bound_subst) = tycheck bound in
    let* (body_ty, body_subst) = with_subsituted_ty_ctx bound_subst begin
      let bound_ty_schema = TSTy (substitute bound_subst bound_ty) in
      print_endline @@ show_ty_schema bound_ty_schema;
      with_extended_ty_ctx binder bound_ty_schema (tycheck body)
    end in
    return (body_ty, substitute_subst body_subst bound_subst)

  | _ -> fail TyErrUnimplemented

let init_tycheck_state =
  { next_unif_var_num = ref 1
  ; ty_ctx = Ctx.empty
  }

let () = print_endline ""
let () = print_endline "Hello, World!"

let var x = ExprVar x
let let_in x e1 e2 = ExprLetIn (x, e1, e2)
let abs x e = ExprAbs (x, e)
let app e1 e2 = ExprApp (e1, e2)

let run_tycheck e = (
    let* (ty, _subst) = tycheck e in
    let* state = get_state in
    return (generalize ty, state)
  ) init_tycheck_state

let tycheck_program program =
  print_endline "";
  print_string "tychecking: ";
  print_endline @@ show_expr program;
  match run_tycheck program with
  | Ok (ty_s, _state) ->
    print_string @@ show_expr program;
    print_string " : ";
    print_endline @@ show_ty_schema ty_s;
  | Error err ->
    print_endline @@ show_ty_error err

(* \f. (\x. f x) *)
let _ = tycheck_program @@ abs "f" (abs "x" (app (var "f") (var "x")))

(* \f. (\x. (\y. f y) x) *)
let _ = tycheck_program @@ abs "f" (abs "x" (abs "y" (app (app (var "f") (var "y")) (var "x"))))

(* \f. (\x. (\y. f y) x) *)
let _ = tycheck_program @@ abs "f" (abs "x" (abs "y" (app (var "f") (var "y"))))

(* \f. (\x. (\y. f y) x) *)
let _ = tycheck_program @@ abs "f" (abs "x" (app (abs "y" (app (var "f") (var "y"))) (var "x")))

(* \f. f f should fail *)
let _ = tycheck_program @@ abs "f" (app (var "f") (var "f"))

(* \x. x *)
let _ = tycheck_program @@ abs "x" (var "x")

(* \x. let y = x in y *)
let _ = tycheck_program @@ abs "x" (let_in "y" (var "x") (var "y"))

