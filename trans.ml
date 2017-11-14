open Config
open Pp
open Ztermops
open Ztypeops
open Names
open Context.Rel.Declaration
open Term

type stmt =
| DeclConst of string * string
| DeclFunction of string * string *string
| DeclSort of string * string
| Def of string * string * string
| Assert of string
| Data of string * string
| Null

let (===) s1 s2 = String.compare s1 s2 == 0

let get_sort env constr = let uj = execute env constr in string_of_ppcmds (pr_constr uj.Environ.uj_type)

let get_type env c = match kind_of_term c with
  | Rel _ -> "Rel"  | Var _ -> "Var"  | Meta _ -> "Meta"
  | Evar _ -> "Evar"  | Sort _ -> "Sort"  | Cast _ -> "Cast"
  | Prod _ -> "Prod"  | Lambda _ -> "Lambda"  | LetIn _ -> "LetIn"
  | App _ -> "App"  | Const _ -> "Const"  | Ind _ -> "Ind"
  | Construct _ -> "Construct"  | Case _ -> "Case"  | Fix _ -> "Fix"
  | CoFix _ -> "CoFix"  | Proj _ -> "Proj"

let get_id id = string_of_ppcmds (Nameops.pr_id id)

let get_ref env constr =
  match kind_of_term constr with
  | Const (c, u) ->
    let (co, _) = (Environ.constant_value env (c,u)) in co
  | _ -> constr

let re = ref ""

let trans_table constr =
  let s = string_of_ppcmds (pr_constr constr) in
  match kind_of_term constr with
  | Ind _ ->
    (try(Hashtbl.find name_map s)
    with Not_found -> "Int")
  | Const _ ->
    (try(Hashtbl.find name_map s)
    with Not_found -> "")
  | Construct _ ->
    (try(Hashtbl.find name_map s)
    with Not_found -> s)
  | _ -> "#Undef#"

let rec nat_to_num constr =
  match kind_of_term constr with
  | App (cst, constrs) -> 1 + (nat_to_num constrs.(0))
  | _ -> 0


let z_to_num constr =
match kind_of_term constr with
| App (cst, constrs) ->
  let s = string_of_ppcmds (pr_constr cst) in
  let rec pos_to_num constr =
    match kind_of_term constr with
    | App (cst, constrs) ->
      let s = string_of_ppcmds (pr_constr cst) in
        if s === "Constr(Coq.Numbers.BinNums.positive,0,2)" then
          2 * (pos_to_num constrs.(0))
        else 1 + 2 * (pos_to_num constrs.(0))
    | _ -> 1
  in
  let pos = pos_to_num constrs.(0) in
  if s === "Constr(Coq.Numbers.BinNums.Z,0,2)" then pos
  else (0 - pos)
| _ -> 0

let rec trans_prop env constr =
  match kind_of_term constr with
  | Prod (Anonymous,t,c) ->
    "(=>" ^ trans_prop env t ^ " " ^ trans_prop env c ^ ")"
  | Prod (Name(id),t,c) ->
    "(forall ((" ^ get_id id ^ " " ^ trans_prop env t ^ ")) (" ^ trans_prop env c ^ "))"
  | App (c,l) ->
   let s = string_of_ppcmds (pr_constr c) in
    if s === "Constr(Coq.Numbers.BinNums.Z,0,2)" || s === "Constr(Coq.Numbers.BinNums.Z,0,3)" then
      string_of_int (z_to_num constr)
    else if s === "Constr(Coq.Init.Datatypes.nat,0,2)" then
      string_of_int (nat_to_num constr)
    else if s === "Ind(Coq.Init.Logic.eq,0)" then
      let cl = List.tl (Array.to_list l) in
      let sl = List.map (fun c' -> trans_prop env c') cl in
      "(" ^ trans_prop env c ^ (List.fold_left (fun s t -> s ^ t ^ " ") " " sl) ^ ")"
    (* else if s === "Cst(compcert.lib.Integers.Int64.unsigned)" then
      trans_prop env (List.hd (Array.to_list l))
    else if s === "Cst(compcert.lib.Integers.Int.unsigned)" then
      trans_prop env (List.hd (Array.to_list l)) *)
    else if s === "Cst(compcert.lib.Integers.Int.testbit)" then
      let () =
        re := "(define-fun testbit ((x (_ BitVec 32)) (i Int)) Bool (not (= #x00000000 (bvand x (bvshl #x00000001 ((_ int2bv 32) i))))))\n" in
      let cl = Array.to_list l in
      let sl = List.map (fun c' -> trans_prop env c') cl in
      "(testbit" ^ (List.fold_left (fun s t -> s ^ t ^ " ") " " sl) ^ ")"
    else
      let cl = Array.to_list l in
      let sl = List.map (fun c' -> trans_prop env c') cl in
        "(" ^ trans_prop env c ^ (List.fold_left (fun s t -> s ^ t ^ " ") " " sl) ^ ")"
  | Ind ((sp, i), u) -> trans_table constr
  | Const (c, u) ->
    let s = string_of_ppcmds (pr_constr constr) in
    (try(Hashtbl.find name_map s)
    with Not_found -> trans_prop env (get_ref env constr))
  | Var id -> get_id id
  | Construct (((sp,i),j),u) ->
    let s = string_of_ppcmds (pr_constr constr) in
    if s === "Constr(Coq.Init.Datatypes.nat,0,1" || s === "Constr(Coq.Numbers.BinNums.Z,0,1)"
    then "0"
    else trans_table constr
  | Rel n ->
    (try(
      match (Environ.lookup_rel n env) with
      | LocalDef (Name(id), oc, c) -> get_id id
      | _ -> "$Err")
    with Not_found -> "$Err")
  | _ -> "##" ^ string_of_ppcmds(pr_constr constr) ^ "##"

let trans_fun env constr =
  let rec f env constr =
    match kind_of_term constr with
    | Prod (Anonymous,t,c) -> (f env t) @ (f env c)
    | Ind ((sp, i), u) -> [trans_table constr]
    | Const (c, u) ->
      let s = string_of_ppcmds (pr_con c) in
      (try([Hashtbl.find name_map s])
      with Not_found -> f env (get_ref env constr))
    | _ -> []
  in
  let ss = f env constr in
  let outtp = (List.hd ss) in
  let tl = List.rev (List.tl ss) in
  let intp = (List.fold_left (fun s t -> s ^ t ^ " ") "" tl) in
  (outtp, "(" ^ intp ^ ")")

let rec trans_constr env id constr =
  let sr = get_sort env constr in
  let tp = get_type env constr in
  if sr === "Prop" then
    let p = trans_prop env constr in
    (Assert p)
  else if sr === "Set" then
    if tp === "Ind" then
      DeclConst (id, "(" ^ (trans_table constr) ^ ")")
    else if tp === "Const" then
      let s = trans_table constr in
      if "" === s then
        trans_constr env id (get_ref env constr)
      else DeclConst (id, "(" ^ s ^ ")")
    else if tp === "Prod" || tp === "App" then
      let (o,i) = trans_fun env constr in
      DeclFunction (id, i, o)
    else Null
  else Null


open Context.Named.Declaration

let rec trans_context env = function
| h::cs ->
  let get_id' id = string_of_ppcmds (Nameops.pr_id id) in
  (match h with
  | (LocalDef (cid, oc, c)) -> let id = get_id' cid in
    (trans_context env cs) @ [trans_constr env id c]
  | (LocalAssum (cid, c)) -> let id = get_id' cid in
    (trans_context env cs) @ [trans_constr env id c])
| _ -> []

let rec trans_goal env goal = trans_constr env "" goal

let rec emit_z3 = function
|(DeclConst (nm, tp))::ss -> "(" ^ "declare-const " ^ nm ^ " " ^ tp ^ ")\n" ^ (emit_z3 ss)
|(DeclFunction (nm, intp, outtp))::ss -> "(" ^ "declare-fun " ^ nm ^ " " ^ intp ^ " " ^ outtp ^ ")\n" ^ (emit_z3 ss)
|(Assert p)::ss -> "(" ^ "assert " ^ p ^ ")\n" ^ (emit_z3 ss)
|_ -> ""
