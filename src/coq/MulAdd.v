(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import ZArith List String Omega.
Require Import Program.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.LLVMAst.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Set Implicit Arguments.
Set Contextual Implicit.

Require Import Vellvm.Memory.

Check (OP_IBinop).

Definition two : exp := EXP_Integer 2.

Definition is_exp_equal_ints (e e': exp): bool :=
  match e with
  | EXP_Integer x =>
    match e' with
    | EXP_Integer y => x =? y
    | _ => false
    end
  |  _ => false
  end.

Definition nuw_enabled : bool := true.
Definition nsw_enabled : bool := true.

Fixpoint rewrite_exp  (e:exp) : exp :=
  match e with
  | OP_IBinop add (TYPE_I 32) v1 v2 =>
    if is_exp_equal_ints v1 v2
    then OP_IBinop (Mul nuw_enabled nsw_enabled) (TYPE_I 32) v1 two
    else e
  | _ => e
  end.

Definition rewrite_instr(i: instr): instr :=
  match i with
  | INSTR_Op e => INSTR_Op (rewrite_exp e)
  | _ => i
  end.

(* Definition code := list (instr_id * instr). *)
Definition rewrite_code(c: code): code :=
  List.map (fun x => (fst x, rewrite_instr (snd x))) c.

(*
Record block : Set :=
  mk_block
    {
      blk_id    : block_id;
      blk_phis  : list (local_id * phi);
      blk_code  : code;
      blk_term  : instr_id * terminator;
    }.
*)
Definition rewrite_block(b: block): block :=
  mk_block (blk_id b)
           (blk_phis b)
           (rewrite_code (blk_code b))
           (blk_term b).


(*
Record definition (FnBody:Set) :=
  mk_definition
  {
    df_prototype   : declaration;
    df_args        : list local_id;
    df_instrs      : FnBody;
  }.
*)
Definition rewrite_definition(d: definition (list block)) :=
  mk_definition (list block)
    (df_prototype d)
    (df_args d)
    (map rewrite_block (df_instrs d)).

(*
Record modul (FnBody:Set) : Set :=
  mk_modul
  {
    m_name: option string;
    m_target: option string;
    m_datalayout: option string;
    m_type_defs: list (ident * typ);
    m_globals: list global;
    m_declarations: list declaration;
    m_definitions: list (definition FnBody);
  }.
*)
Definition rewrite_modul(m: modul (list block)): modul (list block) :=
  {| m_name := m_name m;
     m_target := m_target m;
     m_datalayout := m_datalayout m;
     m_type_defs := m_type_defs m;
     m_globals := m_globals m;
     m_declarations := m_declarations m;
     m_definitions := map rewrite_definition (m_definitions m);
  |}.

Definition rewrite_toplevel_entity (tle : toplevel_entity (list block)) : toplevel_entity (list block) :=
  match tle with
  | TLE_Definition d => TLE_Definition (rewrite_definition d)
  | _ => tle
  end.

Definition transform (prog: list (toplevel_entity (list block))) : list (toplevel_entity (list block)) :=
  List.map rewrite_toplevel_entity prog.
