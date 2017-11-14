open Ztermops
open Ztypeops
open Nameops
open Trans
open Pp
open Format
open Proofview.Goal
open Context.Named.Declaration
open Feedback
open Names.Id

let rec print_context env = function
| h::cs -> let get_id' id = string_of_ppcmds (Nameops.pr_id id) in
  (match h with
  | (LocalDef (cid, oc, c)) -> let id = get_id' cid in
    str id ++ spc() ++ pr_constr oc ++ spc() ++ pr_constr c ++ fnl() ++ print_context env cs
  | (LocalAssum (cid, c)) -> let id = get_id' cid in
    (*++ str(get_type env c) ++ fnl() ++ str(get_sort env c) ++ fnl() ++  *)
    str id ++ spc() ++ str "NONE" ++ spc() ++ pr_constr c ++ fnl() ++ print_context env cs)
| [] -> spc()

let print_goal env goal = pr_constr goal ++ fnl() ++ str(get_sort env goal) ++ fnl()

 let print_coq () =
  Proofview.Goal.nf_enter { enter = fun gl ->
    let goal = Proofview.Goal.concl gl in
    let hyps = Proofview.Goal.hyps gl in
    let env  = Proofview.Goal.env gl in
    msg_info (print_context env hyps); 
    msg_info (print_constr_env env goal  ++ fnl()); 
    Tacticals.New.tclIDTAC}

let print_z3 () =
  Proofview.Goal.nf_enter { enter = fun gl ->
    let goal = Proofview.Goal.concl gl in
    let hyps = Proofview.Goal.hyps gl in
    let env  = Proofview.Goal.env gl in
    let sts = trans_context env hyps in
    match (trans_goal env goal) with
    | Assert st ->
      msg_info (str(emit_z3 sts)); 
      msg_info (str("(assert (not " ^ st ^ "))") ++ fnl());  
      Tacticals.New.tclIDTAC
    | _ -> Tacticals.New.tclIDTAC}

let solve () =
  Proofview.Goal.nf_enter { enter = fun gl ->
    let goal = Proofview.Goal.concl gl in
    let hyps = Proofview.Goal.hyps gl in
    let env  = Proofview.Goal.env gl in
    let sts = trans_context env hyps in
    let (Assert st) = trans_goal env goal in
    let (in_channel,out_channel) = Unix.open_process "z3 -in -smt2" in
    let _ =
      begin
      	let fmt = Format.formatter_of_out_channel out_channel in
      	Format.fprintf fmt "(set-option :produce-unsat-cores true)\n" ;
      	Format.fprintf fmt "(set-option :produce-models true)\n" ;
        Format.fprintf fmt "%s" !re;
        Format.fprintf fmt "%s" (emit_z3 sts) ;
        Format.fprintf fmt "(assert (not %s))" st;
        Format.fprintf fmt "(check-sat)\n" ;
        Format.fprintf fmt "(get-model)\n" ;
      	Format.pp_print_flush fmt () ;
      	flush out_channel ;
      	close_out out_channel
      end
    in
    let buffer_size = 2048 in
    let buffer = Buffer.create buffer_size in
    let string = Bytes.create buffer_size in
    let chars_read = ref 1 in
    while !chars_read <> 0 do
      chars_read := input in_channel string 0 buffer_size;
      Buffer.add_substring buffer string 0 !chars_read
    done;
    ignore (Unix.close_process (in_channel, out_channel));
    let result = Buffer.contents buffer in
    if String.sub result 0 5 === "unsat" then
      Tacticals.New.tclIDTAC
    else
      Tacticals.New.tclFAIL 1 (str("$" ^ result ^ "$" ^ "\nCan't solve!\n"))
  }
