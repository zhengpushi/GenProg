(*
  Copyright 2024 Zhengpu Shi
  This file is part of GenProg. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Utilities
  author    : Zhengpu Shi
  date      : 2023.09.15

  1. 表达式 - x * y 的含义
     在数学上是 - (x * y), 因为乘除的有限级更高，
     但在Coq中是 (- x) * y，因为默认优先级不同：
       Reserved Infix    "+"    (at level 50, left associativity).    (* add *)
       Reserved Infix    "-"    (at level 50, left associativity).    (* sub *)
       Reserved Infix    "*"    (at level 40, left associativity).    (* mul *)
       Reserved Infix    "/"    (at level 40, left associativity).    (* div *)
       Reserved Notation "- x"  (at level 35, right associativity).   (* neg *)
  2. 

 *)

From FinMatrix Require Export Matrix.

(* 这会导入 d1 这样的名称 *)
(* Import Reals. *)
Export Rbase Rtrigo.

Arguments vec : clear implicits.

(* Close Scope mat_scope. *)
(* Close Scope vec_scope. *)
(* Require Export Bool.Bool. *)
(* Require Export Nat. *)
(* Require Export Reals. *)
(* Require Export List. Export ListNotations. *)
Require Export Ascii String.
Open Scope string.
Open Scope nat.


(** ** Coq选项 *)

(** 设置打印的深度限制 *)
Set Printing Depth 2000.


(** ** 保留的记号 *)


(** ** Extension for pair *)
Section pair.

  Definition pair3 A B C := (A * B * C)%type.
  Definition p31 {A B C} (x:pair3 A B C) : A := fst (fst x).
  Definition p32 {A B C} (x:pair3 A B C) : B := snd (fst x).
  Definition p33 {A B C} (x:pair3 A B C) : C := snd x.

End pair.


(** ** Extension for option *)
Section option.
  
  Definition ofst {A B} (o:option (A*B)) : option A :=
    match o with Some x => Some (fst x) | _ => None end.
  
  Definition osnd {A B} (o:option (A*B)) : option B :=
    match o with Some x => Some (snd x) | _ => None end.
  
  Definition oget {A} (o:option A) (def:A) : A :=
    match o with Some x => x | _ => def end.
  
End option.


(** ** Real numbers *)
Section R.

  (** 实数与字符串的简单封装 *)
  Record Rstring :=
    mkRstring {
        Rval : R;
        Rstr : string
      }.

  (* todo: 还可以扩展至有理数 Q *)
  Definition nat2Rstring (n:nat) : Rstring := mkRstring (INR n) (nat2str n).
  Coercion nat2Rstring : nat >-> Rstring.

  (** 标量一元运算 *)
  Inductive Rop1 :=
  | Rop1_neg | Rop1_sin | Rop1_cos
  | Rop1_asin | Rop1_atan
  .

  Definition Rop1_eval (op:Rop1) : R->R :=
    match op with
    | Rop1_neg => Ropp
    | Rop1_sin => sin | Rop1_cos => cos
    | Rop1_asin => asin | Rop1_atan => atan
    end.

  Definition Rop1_str (op:Rop1) (s:string) : string :=
    match op with
    | Rop1_neg => "-(" ++ s ++ ")"
    | Rop1_sin => "sin(" ++ s ++ ")"
    | Rop1_cos => "cos(" ++ s ++ ")"
    | Rop1_asin => "asin(" ++ s ++ ")"
    | Rop1_atan => "atan(" ++ s ++ ")"
    end.

  (** 标量二元运算 *)
  Inductive Rop2 :=
  | Rop2_add | Rop2_sub | Rop2_mul | Rop2_div
  | Rop2_atan2
  .

  Parameter Ratan2 : R -> R -> R.
  Definition Rop2_eval (op:Rop2) : R->R->R :=
    match op with
    | Rop2_add => Rplus | Rop2_sub => (fun x y => Rplus x (Ropp y))
    | Rop2_mul => Rmult | Rop2_div => (fun x y => Rmult x (Rinv y))
    | Rop2_atan2 => Ratan2
    end.

  Definition Rop2_str (op:Rop2) (s1 s2:string) : string :=
    match op with
    | Rop2_add => "(" ++ s1 ++ " + " ++ s2 ++ ")"
    | Rop2_sub => "(" ++ s1 ++ " - " ++ s2 ++ ")"
    | Rop2_mul => s1 ++ " * " ++ s2
    | Rop2_div => s1 ++ " / " ++ s2
    | Rop2_atan2 => "atan2(" ++ s1 ++ ", " ++ s2 ++ ")"
    end.

End R.


(** ** LF and CR strings *)
Section LF_CR.

  (* 换行(Line Feed)，即 \n (new line) *)
  Definition CharLF : ascii := ascii_of_nat 10.

  (* 回车(CarryReturn)，即 \r *)
  Definition CharCR : ascii := ascii_of_nat 13.
  
  (* 在Unix/Linux使用LF，在Widows使用\r\n, Mac使用\n *)
  Definition strNewlineUnix : string := String CharLF "".
  Definition strNewlineWin : string := String CharCR (String CharLF "").
  Definition strNewlineMac : string := String CharCR "".
  Definition strNewline : string := strNewlineUnix.
  
End LF_CR.


(** ** bool missing *)
Section bool_missing.

  (* A transparent definition for Bool.eqb_prop *)
  Lemma bool_eqb_prop : forall a b : bool, Bool.eqb a b = true -> a = b.
  Proof.
    destruct a,b; simpl; auto.
  Defined.

  (* A transparent definition for andb_prop *)
  Lemma andb_prop : forall b1 b2 : bool, b1 && b2 = true -> b1 = true /\ b2 = true.
  Proof.
    destruct b1,b2; simpl; split; intros; auto.
  Defined.

End bool_missing.


(** ** nat missing *)
Section nat_missing.

  (* A transparent definition for Nat.eqb_eq *)
  Lemma nat_eqb_eq : forall (n m : nat), Nat.eqb n m = true -> n = m.
  Proof.
    induction n; destruct m; simpl; auto; intros; easy.
  Defined.

  (** Coq.Arith.Lt.lt_S_n is deprecated since Coq 8.16.
    1. although coqc suggest us to use Nat.succ_lt_mono,
       but that is a  a bidirectional version, not exactly same as lt_S_n.
    2. from Coq 8.16, there is a same lemma Arith_prebase.lt_S_n,
       but it not exist in Coq 8.13,8.14.
   *)
  Definition lt_S_n: forall n m : nat, S n < S m -> n < m.
  Proof.
    intros. apply Nat.succ_lt_mono. auto.
  Qed.
  
End nat_missing.


(** ** string missing *)
Section string_missing.

  (* A transparent definition for Ascii.eqb_eq *)
  Lemma ascii_eqb_eq : forall c1 c2 : ascii, Ascii.eqb c1 c2 = true -> c1 = c2.
  Proof.
    destruct c1,c2. simpl.
    repeat match goal with
           | |- context[Bool.eqb ?b1 ?b2] =>
               let E := fresh "E" in
               destruct (Bool.eqb b1 b2) eqn:E; try easy;
               apply bool_eqb_prop in E
           end; subst; auto.
  Defined.

  (* A transparent definition for String.eqb_eq *)
  Lemma string_eqb_eq : forall s1 s2 : string, String.eqb s1 s2 = true -> s1 = s2.
  Proof.
    induction s1; destruct s2; simpl; auto; intros; try easy.
    destruct (a =? a0)%char eqn:E1.
    - apply ascii_eqb_eq in E1. apply IHs1 in H. subst. auto.
    - easy.
  Defined.
  
End string_missing.


(** ** list missing *)
Section list_missing.

  (* A transparent definition for List.remove *)
  Fixpoint removeb {A:Type} (f:A -> bool) (l:list A) (x:A) : list A :=
    match l with
    | [] => []
    | h :: tl => if f h then removeb f tl x else h :: removeb f tl x
    end.

  (* fold_left1，这是对 fold_left 的改进版，当列表非空时，不使用初始项。
     例如：
     fold_left  [a;b;c] f 0 = f (f (f 0 a) b) c
     fold_left1 [a;b;c] f 0 = f (f a b) c *)
  Definition fold_left1 {A} (f:A->A->A) (l:list A) (a:A) : A :=
    match l with
    | [] => a
    | x :: l' => fold_left f l' x
    end.

  (** 找到列表中的新的编号。空表返回0，否则返回 “最大编号+1”。
      参数 toID ：筛选满足条件的项，并给出其 id；不满足条件的会忽略。*)
  Definition list_new_id {A} (toID:A->(bool*nat)) (l:list A) : nat :=
    let fix F (l0:list A) (newID:nat) :=
      match l0 with
      | [] => newID
      | x :: l1 =>
          let '(valid, id) := toID x in
          if valid
          then F l1 (max newID (S id))
          else F l1 newID
      end in
    F l 0.

  Section test.
    Variable A:Type. Variable (a:A) (b:A) (c:A) (a0:A). Variable f:A->A->A.
    (* Compute fold_left1 f [] a0. *)
    (* Compute fold_left1 f [a] a0. *)
    (* Compute fold_left1 f [a;b] a0. *)
    (* Compute fold_left1 f [a;b;c] a0. *)

    (* Compute list_new_id (fun i=>i) []. *)
    (* Compute list_new_id (fun i=>i) [0;1]. *)
  End test.
  
End list_missing.


(** ** Sequence *)
Section seq.
  
  (* 折叠一个序列 *)
  Fixpoint fold_seq {A B} (seq:nat->A) (n:nat) (f:A->B->B) (b:B) : B :=
    match n with
    | O => b
    (* 普通递归： [a1;a2;a3] b => a3 + (a2 + (a1 + b)) *)
    (* | S n' => f (seq n') (fold_f seq n' f b) *)
    (* 尾递归： [a1;a2;a3] b => a1 + (a2 + (a3 + b)) *)
    | S n' => fold_seq seq n' f (f (seq n') b)
    end.

  Section test.
    (* [a1;a2;a3] b => a *)
    Variable a1 a2 a3 a4 b:nat.
    Let s (n:nat) : nat :=  match n with 0=>a1|1=>a2|2=>a3|_=>a4 end.
    (* Eval cbn in fold_seq s 3 Nat.add b. *)
  End test.

End seq.


(** ** 基于列表的映射，可用于环境管理等场合 *)
Section lmap.

  Context {V:Type}.             (* 值的类型 *)
  Context {v_eqb:V->V->bool}.
  Context {v_eqb_eq: forall v1 v2, v_eqb v1 v2 = true -> v1 = v2}.
  Context {v_eqb_refl: forall v, v_eqb v v = true}.

  Let K := nat.                   (* 键，也称编号，序号，id *)
  Let KV := (K * V)%type.       (* 键值对 *)
  
  Let key_eqb (k1 k2:K) : bool := Nat.eqb k1 k2.
  
  Definition lmap := list KV.
  Definition empty_lmap : lmap := [].

  (* 新的键  *)
  Definition lmap_new_key (c:lmap) : K := list_new_id (fun i => (true, fst i)) c. 

  (* 两个映射相等。列表中逐项相等 *)
  Fixpoint lmap_eqb (l1 l2 : lmap) : bool :=
    match l1, l2 with
    | [], [] => true
    | (k1,v1) :: l1', (k2,v2) :: l2' =>
        Nat.eqb k1 k2 && v_eqb v1 v2 && lmap_eqb l1' l2'
    | _, _ => false
    end.

  Definition lmap_eqb_eq : forall l1 l2 : lmap, lmap_eqb l1 l2 = true -> l1 = l2.
    induction l1; destruct l2; simpl in *; intros; try easy.
    - destruct a. easy.
    - destruct a,k. repeat (apply andb_prop in H; destruct H).
      apply nat_eqb_eq in H. apply v_eqb_eq in H1. apply IHl1 in H0. subst. auto.
  Defined.

  Definition lmap_eqb_refl : forall l : lmap, lmap_eqb l l = true.
    induction l; auto. simpl. destruct a.
    rewrite Nat.eqb_refl, v_eqb_refl, IHl. auto.
  Defined.

  (* 根据键取出值 *)
  Definition lmap_geto (k:K) (c:lmap) : option V :=
    match find (fun kv => key_eqb (fst kv) k) c with
    | Some kv => Some (snd kv) |  _ => None
    end.
  
  (* 根据键取出值，若不存在使用默认值 *)
  Definition lmap_get (k:K) (c:lmap) (val_def:V) : V :=
    match lmap_geto k c with Some x => x | _ => val_def end.

  (* 根据值取出键值 *)
  (* Definition lmap_getV (v:V) (c:lmap) : option KV := *)
  (*   find (fun kv => v_eqb (snd kv) v) c. *)

  (* 是否存在某个键 *)
  Definition lmap_exist (k:K) (c:lmap) : bool :=
    match lmap_geto k c with Some _ => true | _ => false end.
  (* (* 是否存在某个值 *) *)
  (* Definition lmap_existV (v:V) (c:lmap) : bool := *)
  (*   match lmap_findV v c with Some _ => true | _ => false end. *)

  (* 根据值匹配函数找到第一个键值对 *)
  Fixpoint lmap_find_first (c:lmap) (filter:V->bool) : option (K * V * lmap) :=
    match c with
    | [] => None
    | x :: c' =>
        if filter (snd x)
        then Some (fst x, snd x, c')
        else
          match lmap_find_first c' filter with
          | Some (k,v,l) => Some (k,v,x::l)
          | None => None
          end
    end.

  (* 更新一个键值 *)
  Fixpoint lmap_update (c:lmap) (k:K) (v:V) (chk_type:V->bool) : lmap :=
    match c with
    | [] => []
    | x :: c' => if key_eqb (fst x) k
                then (if chk_type (snd x)
                      then (fst x, v) :: c'
                      else c)
                else x :: (lmap_update c' k v chk_type)
    end.

  (* 根据键删除键值对 *)
  Fixpoint lmap_del (k:K) (c:lmap) : lmap :=
    match c with
    | [] => []
    | x :: c' => if key_eqb (fst x) k then lmap_del k c' else x :: (lmap_del k c')
    end.

  (* 根据值匹配函数删除第一个键值对 *)
  Fixpoint lmap_del_first (c:lmap) (filter:V->bool) : lmap :=
    match c with
    | [] => []
    | x :: c' => if filter (snd x) then c' else x :: (lmap_del_first c' filter)
    end.

  (* 加入值，返回键和新映射 *)
  Definition lmap_add (v:V) (c:lmap) : (K * lmap) :=
    let k := lmap_new_key c in
    let kv := (k, v) in
    (k, kv::c).

  (* 加入值，仅返回新环境 *)
  Definition lmap_add2 (v:V) (c:lmap) : lmap := snd (lmap_add v c).
    
  (* 使用列表来初始化映射 *)
  Definition lmap_init (c:list V) : lmap :=
    fold_left (fun l v => lmap_add2 v l) c empty_lmap.

End lmap.

Section test.

  Let l1 : lmap := lmap_init ["x";"y";"z"].
  (* Compute l1. *)
  (* Compute lmap_add2 "w" l1. *)
  (* Compute lmap_del 2 l1. *)
End test.
