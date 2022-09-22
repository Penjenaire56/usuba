open Utils

type ident = Ident.t

type _expr =
  | Const of int * Usuba_AST.typ option
  | ExpVar of Usuba_AST.var
  | Tuple of expr list
  | Not of expr
  | Log of Usuba_AST.log_op * expr * expr
  | Arith of Usuba_AST.arith_op * expr * expr
  | Shift of Usuba_AST.shift_op * expr * Usuba_AST.arith_expr
[@@deriving eq, show { with_path = false }]

(*| Shuffle of var * int list
  | Bitmask of expr * arith_expr
  | Pack of expr * expr * typ option
  | Fun of ident * expr list
  | Fun_v of ident * arith_expr * expr list *)
and expr = _expr Hash_union.hash_consed
[@@deriving eq, show { with_path = false }]

type p = expr list

module Hash_expr = struct
  type t = _expr

  let equal e1 e2 = equal__expr e1 e2
  let hash e = Hashtbl.hash e
end

module Hexpr = Hash_union.HashTable (Hash_expr)

let table = Hexpr.create 253

module Uexpr = struct
  module HCons = struct
    type t = Hash_expr.t Hash_union.hash_consed

    let compare h1 h2 = Int.compare h1.Hash_union.tag h2.Hash_union.tag
  end

  module HSet = Set.Make (HCons)

  type t = { union : Hash_union.PUnion.t; exprs : HSet.t }

  let create n = { union = Hash_union.PUnion.create n; exprs = HSet.empty }
  let find e u = Hash_union.PUnion.find e.union u.Hash_union.tag

  let union h x y =
    {
      exprs = HSet.add x (HSet.add y h.exprs);
      union = Hash_union.PUnion.union h.union x.Hash_union.tag y.Hash_union.tag;
    }
end

type deq_i = Eqn of Usuba_AST.var list * expr * bool
(*| Loop of {
      id : ident;
      start : arith_expr;
      stop : arith_expr;
      body : deq list;
      opts : stmt_opt list;
    } *)

and deq = { content : deq_i; orig : (ident * deq_i) list }

type def_i = Single of Usuba_AST.p * deq list

type def = {
  id : ident;
  p_in : Usuba_AST.p;
  p_out : Usuba_AST.p;
  opt : Usuba_AST.def_opt list;
  node : def_i;
}

let equiv_class (deqs : deq list) union =
  let equi e =
    Uexpr.HSet.filter
      (fun x ->
        Hash_union.PUnion.equiv union.Uexpr.union x.Hash_union.tag
          e.Hash_union.tag)
      union.Uexpr.exprs
  in

  let find_var exp excluded acc =
    let eq = equi exp in
    Uexpr.HSet.filter
      (fun x ->
        match (x.node, excluded) with
        | ExpVar _, None -> true
        | ExpVar v1, Some v2 -> v1 <> v2
        | _ -> false)
      eq
  in

  let find_best e var_eq acc =
    match
      Uexpr.HSet.filter (fun v -> Uexpr.HSet.mem v acc) var_eq
      |> Uexpr.HSet.elements
    with
    | [] ->
        let v = Uexpr.HSet.choose var_eq in
        (v, Uexpr.HSet.add v acc)
    | [ v ] -> (v, acc)
    | _ -> assert false
  in

  let replace_best e acc excluded =
    let eq = find_var e excluded acc in
    if Uexpr.HSet.is_empty eq then (e, acc) else find_best e eq acc
  in

  let rec replace_by_var union (exp : Hash_expr.t Hash_union.hash_consed) acc
      excluded =
    match exp.node with
    | ExpVar _ -> (exp, acc)
    | Const _ -> (exp, acc)
    | Not e ->
        let e, acc = replace_by_var union e acc excluded in
        let e, acc = replace_best e acc excluded in
        (Hexpr.hashcons table (Not e), acc)
    | Arith (op, e1, e2) ->
        let e1, acc = replace_by_var union e1 acc excluded in
        let e1, acc = replace_best e1 acc excluded in
        let e2, acc = replace_by_var union e2 acc excluded in
        let e2, acc = replace_best e2 acc excluded in
        let e = Hexpr.hashcons table (Arith (op, e1, e2)) in
        replace_best e acc excluded
    | _ -> failwith ""
    (*
      | Log of Usuba_AST.log_op * expr * expr
      | Arith of Usuba_AST.arith_op * expr * expr
      | Shift of Usuba_AST.shift_op * expr * Usuba_AST.arith_expr *)
  in

  let used x acc =
    not
      (Uexpr.HSet.for_all
         (fun e -> match e.node with ExpVar e -> e <> x | _ -> true)
         acc)
  in

  let rec aux_apply acc = function
    | [] -> []
    | ({ content = Eqn ([ x ], _, _); _ } as deq) :: subL when used x acc ->
        deq :: aux_apply acc subL
    | ({ content = Eqn ([ x ], e, b); _ } as deq) :: subL ->
        let e, acc = replace_by_var union e acc (Some x) in
        { deq with content = Eqn ([ x ], e, b) } :: aux_apply acc subL
    | ({ content = Eqn (vl, e, b); _ } as deq) :: subL ->
        let e, acc = replace_by_var union e acc None in
        { deq with content = Eqn (vl, e, b) } :: aux_apply acc subL
  in

  aux_apply Uexpr.HSet.empty deqs

(*
    let rec aux = function
    | Tuple [e] -> Uexpr.HSet.map (fun x -> Tuple [x]) (aux e.Hash_union.node
    )
    | Tuple [e1;e2] -> Uexpr.HSet.map (fun y -> (Uexpr.HSet.map (fun x -> Tuple [y;x]) (aux e2.Hash_union.node))) (aux e1.Hash_union.node)
    | _ -> assert false
  *)

let rec ast_to_es e =
  let res =
    match e with
    | Usuba_AST.Const (i, t) -> Hexpr.hashcons table (Const (i, t))
    | Usuba_AST.ExpVar v -> Hexpr.hashcons table (ExpVar v)
    | Usuba_AST.Tuple el -> Hexpr.hashcons table (Tuple (List.map ast_to_es el))
    | Usuba_AST.Not e -> Hexpr.hashcons table (Not (ast_to_es e))
    | Usuba_AST.Log (op, e1, e2) ->
        Hexpr.hashcons table (Log (op, ast_to_es e1, ast_to_es e2))
    | Usuba_AST.Arith (op, e1, e2) ->
        Hexpr.hashcons table (Arith (op, ast_to_es e1, ast_to_es e2))
    | Usuba_AST.Shift (op, e1, e2) ->
        Hexpr.hashcons table (Shift (op, ast_to_es e1, e2))
    (*| Shuffle (var, il) ->
      | Bitmask (e, ae) ->
      | Pack (e1, e2, o) ->
      | Fun (id, el) ->
      | Fun_v (id, ae, el) -> *)
    | _ -> failwith "ast_to_es"
  in
  Format.eprintf "%a: %d@." Usuba_print.(pp_expr ()) e res.tag;
  res

let rec _es_to_ast = function
  | Const (i, t) -> Usuba_AST.Const (i, t)
  | ExpVar v -> Usuba_AST.ExpVar v
  | Tuple el -> Usuba_AST.Tuple (List.map es_to_ast el)
  | Not e -> Usuba_AST.Not (es_to_ast e)
  | Log (op, e1, e2) -> Usuba_AST.Log (op, es_to_ast e1, es_to_ast e2)
  | Arith (op, e1, e2) -> Usuba_AST.Arith (op, es_to_ast e1, es_to_ast e2)
  | Shift (op, e1, e2) -> Usuba_AST.Shift (op, es_to_ast e1, e2)

and es_to_ast h = _es_to_ast h.node

let eqAst_to_eqEs = function
  | Usuba_AST.Eqn (v, e, b) ->
      List.iter (fun x -> ignore (Hexpr.hashcons table (ExpVar x))) v;
      Eqn (v, ast_to_es e, b)
  | _ -> failwith "eqAst_to_eqEs"

let eqEs_to_eqAst = function Eqn (v, e, b) -> Usuba_AST.Eqn (v, es_to_ast e, b)

let deq_ast_to_es (v : Usuba_AST.deq) =
  {
    content = eqAst_to_eqEs v.content;
    orig = List.map (fun (i, d) -> (i, eqAst_to_eqEs d)) v.orig;
  }

let deq_es_to_ast (v : deq) : Usuba_AST.deq =
  {
    content = eqEs_to_eqAst v.content;
    orig = List.map (fun (i, d) -> (i, eqEs_to_eqAst d)) v.orig;
  }

let fold_deqs (env_var : Usuba_AST.typ Ident.Hashtbl.t)
    (deqs : Usuba_AST.deq list) : deq list =
  List.map deq_ast_to_es deqs

let def_ast_to_es = function
  | Usuba_AST.Single (p, dl) -> Single (p, List.map deq_ast_to_es dl)
  | _ -> failwith "def_ast_to_es"

let def_es_to_ast = function
  | Single (p, dl) -> Usuba_AST.Single (p, List.map deq_es_to_ast dl)

let fold_def (def : Usuba_AST.def) : Usuba_AST.def =
  {
    def with
    Usuba_AST.node =
      (let (Single (p, deqs)) = def_ast_to_es def.node in
       let nb = Array.length table.Hexpr.table in

       let union = Uexpr.create nb in
       let union =
         List.fold_right
           (fun e u ->
             match e.content with
             | Eqn ([ x ], exp, _) ->
                 Uexpr.union u (Hexpr.hashcons table (ExpVar x)) exp
             | _ -> u (* Tuple de variables *))
           deqs union
       in

       (*let cse u ({ content = Eqn (vl, e, b); _ } as deq) =
           { deq with content = Eqn (vl, e, b) }

           let r =
             Uexpr.HSet.filter
               (fun x ->
                 if
                   not
                     (Hash_union.PUnion.equiv u.Uexpr.union x.Hash_union.tag
                        e.Hash_union.tag)
                 then false
                 else match x.Hash_union.node with ExpVar _ -> true | _ -> false)
               u.Uexpr.exprs
           in
           match Uexpr.HSet.min_elt_opt r with
           | None -> deq
           | Some s -> (
               match s.Hash_union.node with
               | ExpVar n when not (List.mem n vl) ->
                   { deq with content = Eqn (vl, s, b) }
               | _ -> deq)

         in
       *)
       let n = Single (p, equiv_class deqs union) in
       def_es_to_ast n);
  }

let run _ prog _ : Usuba_AST.prog =
  { Usuba_AST.nodes = List.map fold_def prog.Usuba_AST.nodes }

let as_pass = (run, "ES", 0)

let ftest deq =
  {
    Usuba_AST.id = Ident.create_unbound "toto";
    Usuba_AST.p_out = [];
    Usuba_AST.p_in = [];
    Usuba_AST.opt = [];
    Usuba_AST.node = Usuba_AST.Single ([], deq);
  }

let%test_module "CSE" =
  (module struct
    open Parser_api
    open Syntax

    let a = v "a"
    let b = v "b"
    let x = v "x"
    let y = v "y"
    let z = v "z"
    let d = v "d"
    let e = v "e"

    let%test "simple1" =
      let deq = mk_deq_i [ [ x ] = a + b; [ y ] = a + b; [ z ] = a - b ] in
      let def = ftest deq in
      let def = fold_def def in
      Format.printf "%a@." Usuba_print.(pp_def ()) def;

      let deq' = mk_deq_i [ [ x ] = y; [ y ] = a + b; [ z ] = a - b ] in

      let def' = ftest deq' in
      Usuba_AST.equal_def def def'

    let%test "simple2" =
      let deq = mk_deq_i [ [ y ] = a + b; [ x ] = a + b; [ z ] = a - b ] in
      let def = ftest deq in
      let def = fold_def def in
      Format.printf "%a@." Usuba_print.(pp_def ()) def;

      let deq' = mk_deq_i [ [ y ] = x; [ x ] = a + b; [ z ] = a - b ] in

      let def' = ftest deq' in
      Usuba_AST.equal_def def def'

    let%test "simple3" =
      let deq =
        mk_deq_i [ [ x ] = a + b; [ y ] = d - (a + b) + e; [ z ] = a - b ]
      in
      let def = ftest deq in
      let def = fold_def def in
      Format.printf "%a@." Usuba_print.(pp_def ()) def;

      let deq' = mk_deq_i [ [ x ] = a + b; [ y ] = d - x + e; [ z ] = a - b ] in

      let def' = ftest deq' in
      Usuba_AST.equal_def def def'

    let%test "simple4" =
      let deq = mk_deq_i [ [ x ] = a + b; [ y ] = a + b + e; [ z ] = x + e ] in
      let def = ftest deq in
      let def = fold_def def in
      Format.printf "%a@." Usuba_print.(pp_def ()) def;

      let deq' = mk_deq_i [ [ x ] = a + b; [ y ] = z; [ z ] = x + e ] in

      let def' = ftest deq' in
      Usuba_AST.equal_def def def'

    let%test "simple5" =
      let deq =
        mk_deq_i [ [ x ] = a + b; [ y ] = a + b + (a + b); [ z ] = x + x ]
      in
      let def = ftest deq in
      let def = fold_def def in
      Format.printf "%a@." Usuba_print.(pp_def ()) def;

      let deq' = mk_deq_i [ [ x ] = a + b; [ y ] = z; [ z ] = x + x ] in

      let def' = ftest deq' in
      Usuba_AST.equal_def def def'
  end)