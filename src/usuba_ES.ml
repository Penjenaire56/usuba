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
  let equi_var e =
    Uexpr.HSet.filter
      (fun x ->
        if
          not
            (Hash_union.PUnion.equiv union.Uexpr.union x.Hash_union.tag
               e.Hash_union.tag)
        then false
        else match x.node with ExpVar _ -> true | _ -> false)
      union.Uexpr.exprs
  in

  let find_var exp excluded =
    let eq = equi_var exp in
    match Uexpr.HSet.min_elt_opt eq with
    | None -> exp
    | Some s -> (
        match s.node with ExpVar n when List.mem n excluded -> exp | _ -> s)
  in

  let rec replace_by_var union (exp : Hash_expr.t Hash_union.hash_consed)
      excluded =
    match exp.node with
    | Const _ -> exp
    | ExpVar _ -> find_var exp excluded
    | Not e ->
        let e = replace_by_var union e excluded in
        let e = Hexpr.hashcons table (Not e) in
        find_var e excluded
    | Arith (op, e1, e2) ->
        let e1 = replace_by_var union e1 excluded in
        let e2 = replace_by_var union e2 excluded in
        let e = Hexpr.hashcons table (Arith (op, e1, e2)) in
        find_var e excluded
    | _ -> failwith "replace_by_var"
    (*
      | Log of Usuba_AST.log_op * expr * expr
      | Arith of Usuba_AST.arith_op * expr * expr
      | Shift of Usuba_AST.shift_op * expr * Usuba_AST.arith_expr *)
  in

  List.map
    (fun ({ content = Eqn (vl, e, b); _ } as deq) ->
      let e = replace_by_var union e vl in
      { deq with content = Eqn (vl, e, b) })
    deqs

(*
    let rec aux = function
    | Tuple [e] -> Uexpr.HSet.map (fun x -> Tuple [x]) (aux e.Hash_union.node
    )
    | Tuple [e1;e2] -> Uexpr.HSet.map (fun y -> (Uexpr.HSet.map (fun x -> Tuple [y;x]) (aux e2.Hash_union.node))) (aux e1.Hash_union.node)
    | _ -> assert false
  *)

let rec ast_to_es e union =
  match e with
  | Usuba_AST.Const (i, t) -> (Hexpr.hashcons table (Const (i, t)), union)
  | Usuba_AST.ExpVar v -> (Hexpr.hashcons table (ExpVar v), union)
  | Usuba_AST.Tuple el ->
      let el, union =
        List.fold_left
          (fun (el, union) e ->
            let e, union = ast_to_es e union in
            (e :: el, union))
          ([], union) el
      in
      (Hexpr.hashcons table (Tuple el), union)
  | Usuba_AST.Not e ->
      let e, union = ast_to_es e union in
      (Hexpr.hashcons table (Not e), union)
  | Usuba_AST.Log (op, e1, e2) ->
      let e1, union = ast_to_es e1 union in
      let e2, union = ast_to_es e2 union in
      (Hexpr.hashcons table (Log (op, e1, e2)), union)
  | Usuba_AST.Arith (op, e1, e2) ->
      let e1, union = ast_to_es e1 union in
      let e2, union = ast_to_es e2 union in

      let n1 = Hexpr.hashcons table (Arith (op, e1, e2)) in
      let n2 = Hexpr.hashcons table (Arith (op, e2, e1)) in
      (n1, Uexpr.union union n1 n2)
  | Usuba_AST.Shift (op, e1, e2) ->
      let e1, union = ast_to_es e1 union in
      (Hexpr.hashcons table (Shift (op, e1, e2)), union)
  (*| Shuffle (var, il) ->
    | Bitmask (e, ae) ->
    | Pack (e1, e2, o) ->
    | Fun (id, el) ->
    | Fun_v (id, ae, el) -> *)
  | _ -> failwith "ast_to_es"

let rec _es_to_ast = function
  | Const (i, t) -> Usuba_AST.Const (i, t)
  | ExpVar v -> Usuba_AST.ExpVar v
  | Tuple el -> Usuba_AST.Tuple (List.map es_to_ast el)
  | Not e -> Usuba_AST.Not (es_to_ast e)
  | Log (op, e1, e2) -> Usuba_AST.Log (op, es_to_ast e1, es_to_ast e2)
  | Arith (op, e1, e2) -> Usuba_AST.Arith (op, es_to_ast e1, es_to_ast e2)
  | Shift (op, e1, e2) -> Usuba_AST.Shift (op, es_to_ast e1, e2)

and es_to_ast h = _es_to_ast h.node

let eqAst_to_eqEs union = function
  | Usuba_AST.Eqn (v, e, b) ->
      List.iter (fun x -> ignore (Hexpr.hashcons table (ExpVar x))) v;
      let e, u = ast_to_es e union in
      (Eqn (v, e, b), u)
  | _ -> failwith "eqAst_to_eqEs"

let eqEs_to_eqAst = function Eqn (v, e, b) -> Usuba_AST.Eqn (v, es_to_ast e, b)

let deq_ast_to_es (v : Usuba_AST.deq) u =
  let d, u = eqAst_to_eqEs u v.content in
  ({ content = d; orig = [] }, u)

let deq_es_to_ast (v : deq) : Usuba_AST.deq =
  {
    content = eqEs_to_eqAst v.content;
    orig = List.map (fun (i, d) -> (i, eqEs_to_eqAst d)) v.orig;
  }

let fold_deqs (deqs : Usuba_AST.deq list) u =
  List.fold_left
    (fun (u, acc) d ->
      let d', u = deq_ast_to_es d u in
      (u, d' :: acc))
    (u, []) deqs

let def_ast_to_es u = function
  | Usuba_AST.Single (p, dl) ->
      let u, dl' = fold_deqs dl u in
      (u, Single (p, dl'))
  | _ -> failwith "def_ast_to_es"

let def_es_to_ast = function
  | Single (p, dl) -> Usuba_AST.Single (p, List.map deq_es_to_ast dl)

let fold_def (def : Usuba_AST.def) : Usuba_AST.def =
  {
    def with
    Usuba_AST.node =
      (let nb = 42000 in
       let union = Uexpr.create nb in

       (* let union, e1, e2 =
            let open Syntax in
            let a = v "a" in
            let b = v "b" in
            let a, union = ast_to_es a union in
            let b, union = ast_to_es b union in

            let e1 = Arith (Usuba_AST.Add, a, b) in
            let e2 = Arith (Usuba_AST.Add, b, a) in
            (union, e1, e2)
          in

          let e1 = Hexpr.hashcons table e1 in
          let e2 = Hexpr.hashcons table e2 in

          let union = Uexpr.union union e1 e2 in

          assert (
            Hash_union.PUnion.equiv union.Uexpr.union e1.Hash_union.tag
              e2.Hash_union.tag);
       *)
       let union, Single (p, deqs) = def_ast_to_es union def.node in
       let deqs = List.rev deqs in
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

      let deq1 = mk_deq_i [ [ x ] = a + b; [ y ] = x; [ z ] = a - b ] in
      let def1 = ftest deq1 in

      let deq2 = mk_deq_i [ [ x ] = y; [ y ] = a + b; [ z ] = a - b ] in
      let def2 = ftest deq2 in

      Usuba_AST.equal_def def def1 || Usuba_AST.equal_def def def2

    let%test "simple2" =
      let deq = mk_deq_i [ [ y ] = a + b; [ x ] = a + b; [ z ] = a - b ] in
      let def = ftest deq in
      let def = fold_def def in
      Format.printf "%a@." Usuba_print.(pp_def ()) def;

      let deq1 = mk_deq_i [ [ y ] = x; [ x ] = a + b; [ z ] = a - b ] in
      let def1 = ftest deq1 in

      let deq2 = mk_deq_i [ [ x ] = a + b; [ y ] = x; [ z ] = a - b ] in
      let def2 = ftest deq2 in

      Usuba_AST.equal_def def def1 || Usuba_AST.equal_def def def2

    let%test "simple3" =
      let deq =
        mk_deq_i [ [ x ] = a + b; [ y ] = d - (a + b) + e; [ z ] = a - b ]
      in
      let def = ftest deq in
      let def = fold_def def in
      Format.printf "%a@." Usuba_print.(pp_def ()) def;

      let deq1 = mk_deq_i [ [ x ] = a + b; [ y ] = d - x + e; [ z ] = a - b ] in
      let def1 = ftest deq1 in

      Usuba_AST.equal_def def def1

    let%test "simple4" =
      let deq = mk_deq_i [ [ x ] = a + b; [ y ] = a + b + e; [ z ] = x + e ] in
      let def = ftest deq in
      let def = fold_def def in
      Format.printf "%a@." Usuba_print.(pp_def ()) def;

      let deq1 = mk_deq_i [ [ x ] = a + b; [ y ] = z; [ z ] = x + e ] in
      let def1 = ftest deq1 in

      Usuba_AST.equal_def def def1

    (* Problème avec l'associativité des opérations *)
    let%test "simple5" =
      let deq =
        mk_deq_i [ [ x ] = a + b; [ y ] = a + b + a + b; [ z ] = x + x ]
      in
      let def = ftest deq in
      let def = fold_def def in
      Format.printf "%a@." Usuba_print.(pp_def ()) def;

      let deq' = mk_deq_i [ [ x ] = a + b; [ y ] = z; [ z ] = x + x ] in

      let def' = ftest deq' in
      Usuba_AST.equal_def def def'

    let%test "simple6" =
      let deq =
        mk_deq_i [ [ x ] = a + b; [ y ] = a + b + (a + b); [ z ] = x + x ]
      in
      let def = ftest deq in
      let def = fold_def def in
      Format.printf "%a@." Usuba_print.(pp_def ()) def;

      let deq' = mk_deq_i [ [ x ] = a + b; [ y ] = z; [ z ] = x + x ] in

      let def' = ftest deq' in
      Usuba_AST.equal_def def def'

    (* Problème avec la communtativité des opérations *)
    let%test "simple7" =
      let deq = mk_deq_i [ [ x ] = a + b; [ y ] = b + a; [ z ] = a - b ] in
      let def = ftest deq in
      let def = fold_def def in
      Format.printf "%a@." Usuba_print.(pp_def ()) def;

      let deq1 = mk_deq_i [ [ x ] = y; [ y ] = b + a; [ z ] = a - b ] in
      let def1 = ftest deq1 in

      let deq2 = mk_deq_i [ [ x ] = a + b; [ y ] = x; [ z ] = a - b ] in
      let def2 = ftest deq2 in

      Usuba_AST.equal_def def def1 || Usuba_AST.equal_def def def2

    let%test "simple8" =
      let deq = mk_deq_i [ [ x ] = a + b; [ y ] = a + b; [ z ] = x ] in
      let def = ftest deq in
      let def = fold_def def in
      Format.printf "%a@." Usuba_print.(pp_def ()) def;

      let deq1 = mk_deq_i [ [ x ] = y; [ y ] = a + b; [ z ] = y ] in
      let def1 = ftest deq1 in

      let deq2 = mk_deq_i [ [ x ] = a + b; [ y ] = x; [ z ] = x ] in
      let def2 = ftest deq2 in

      Usuba_AST.equal_def def def1 || Usuba_AST.equal_def def def2
  end)