(*
  Copyright 2024 Zhengpu Shi
  This file is part of GenProg. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Translate functional program to C program 
  author    : Zhengpu Shi
  date      : 2023.09.15

 *)

(* Require Import Extraction. *)
Require Import Utils.

Declare Scope CG_scope.
Delimit Scope CG_scope with CG.
Open Scope CG_scope.

Open Scope string_scope.


(* ######################################################################### *)
(** * 核心功能 *)

(* 集合长度为0时的一个索引，尽管它不存在，但为了通过类型检查，只能用这个虚拟值来代替 *)
Parameter dummy_fin0 : fin 0.

(** 自然数转fin，支持构造任意的 fin n (即使 n = 0)  *)
Definition n2f {n : nat} (i : nat) : fin n.
  destruct n.
  apply dummy_fin0. apply #i.
Defined.


(* ======================================================================= *)
(** ** 数组的维数 *)

(** 数组的维数 *)
Inductive dim :=
| dstr (n:nat) (str:string)       (* 变量。此处的 str 是用于代码生成时的输出 *)
| dcnst (n:nat).                  (* 常量 *)

Coercion dcnst : nat >-> dim.

Definition dim2nat (d:dim) : nat :=
  match d with dstr n _ => n | dcnst n => n end.
Definition dim2str (d:dim) : string :=
  match d with dstr n str => str | dcnst n => nat2str n end.

Definition dim_eqb (d1 d2:dim) : bool :=
  match d1, d2 with
  | dstr n1 s1, dstr n2 s2 => Nat.eqb n1 n2 && String.eqb s1 s2
  | dcnst n1, dcnst n2 => Nat.eqb n1 n2
  | _, _ => false
  end.

Definition dim_eqb_eq : forall d1 d2, dim_eqb d1 d2 = true -> d1 = d2.
  destruct d1, d2; simpl; try easy; intros.
  - apply andb_prop in H; destruct H.
    apply nat_eqb_eq in H; apply string_eqb_eq in H0; subst; auto.
  - apply nat_eqb_eq in H; subst; auto.
Defined.

Lemma dim_eqb_refl : forall d, dim_eqb d d = true.
Proof.
  induction d; simpl; rewrite ?Nat.eqb_refl,?String.eqb_refl; auto.
Qed.

(* 由于 item2value_item_real 的证明含有 dim_eqb 而走不下去，所以想到用 dec 这个概念，
   但发现没有什么作用 *)
Definition dim_dec : forall (d1 d2:dim), {d1 = d2} + {d1 <> d2}.
  destruct d1,d2; try (right; intros; easy).
  - destruct (string_dec str str0), (Nat.eq_dec n n0); subst; auto;
      try (right; intro H; inversion H; easy).
  - destruct (Nat.eq_dec n n0); auto;
      try (right; intro; inversion H; easy).
Defined.

Section test.
  Let d1 : dim := 3.
  Compute dim2nat d1.     (* = 3 *)
  Compute dim2str d1.     (* = "3" *)
  
  Variable n : nat.               (* 与Coq内置类型关联起来 *)
  Let d2 : dim := dstr n "xy".
  Compute dim2nat d2.       (* = n *)
  Compute dim2str d2.       (* = "xy" *)
End test.


(* ======================================================================= *)
(** ** 数据种类。利用依赖类型实现左值和右值的类型匹配  *)

Inductive data :=
| dnum                            (* 标量型的数值 *)
| dary (n : dim) (d : data)       (* 数组 *)
| dpair (d1 d2 : data)            (* 对偶 *)
| didx (n : dim).                 (* 索引 *)

Notation dmat r c d := (dary r (dary c d)).

Fixpoint data_eqb (d1 d2 : data) : bool :=
  match d1, d2 with
  | dnum, dnum => true
  | dary n1 d1, dary n2 d2 => dim_eqb n1 n2 && data_eqb d1 d2
  | dpair d11 d12, dpair d21 d22 => data_eqb d11 d21 && data_eqb d12 d22
  | didx n1, didx n2 => dim_eqb n1 n2
  | _, _ => false
  end.

Definition data_eqb_eq : forall d1 d2, data_eqb d1 d2 = true -> d1 = d2.
  intros d1. induction d1; intros d2; destruct d2; simpl; try easy; intros.
  - apply andb_prop in H. destruct H.
    apply dim_eqb_eq in H. apply IHd1 in H0. subst; auto.
  - apply andb_prop in H. destruct H.
    apply IHd1_1 in H. apply IHd1_2 in H0. subst; auto.
  - apply dim_eqb_eq in H. subst; auto.
Defined.

Lemma data_eqb_refl : forall d, data_eqb d d = true.
Proof.
  induction d; simpl; auto; rewrite ?dim_eqb_refl; auto.
  rewrite IHd1, IHd2. auto.
Qed.

(* 对于 xx_eqb n n 的表达式，如果 n 是变量，则化简该表达式的结果并不是 true。 *)
Section problem.
  
  (* 以下结果并不是最简，想办法解决，否则影响证明 *)
  Variable n : nat.
  Let dim_n : dim := dstr n "n".
  Let d : data := dary dim_n dnum.

  Eval cbn in data_eqb d d.
  Eval cbv in data_eqb d d.

  (* 原因在于，自然数变量 n 与自身的相等计算，无法自动归约到 true。*)
  Compute Nat.eqb n n.

  (* 同理，在其他类型上也有这类问题。 *)
  Variable b : bool.
  Compute Bool.eqb b b.

(* 此处虽然看似简单，但由于 data 会为其他类型构成依赖类型，导致类型是变化的，
   使得带依赖类型的证明难以进行（我不了解这一技术）。比如 eeval exp 的例子。 *)
End problem.

(* 是否为相同类别？
   仅判最别外层相似，比如 dary 3 dnum 和 dary 2 (dary 4 dnum) 被认为是相同的 *)
Definition data_same_type (d1 d2 : data) : bool :=
  match d1, d2 with
  | dnum, dnum => true
  | dary n1 d1, dary n2 d2 => true
  | didx n1, didx n2 => true
  | dpair _ _, dpair _ _ => true
  | _, _ => false
  end.

Definition data2prefix (d:data) : string :=
  match d with
  | dnum => "x"
  | dmat _ _ _ => "m"
  | dary _ _ => "v"
  | dpair _ _ => "s"
  | didx _ => "i"
  end.


(* data转字符串，d是ast，num是变量起始编号 *)
Definition data2str (d:data) (num:nat) : string :=
  data2prefix d ++ nat2str num.

(* 数据类别转声明字符串，d是ast，no是变量起始编号
   例如：
   (1) 浮点数       float x0
   (2) 数组下标     int i0
   (3) 数组         float v0[3][4]
   (4) 结构体       struct s0 { float x1; float x2 }
 *)
Definition data2strDecl (d:data) (no:nat) : string :=
  (* 对于数组型的数据类别，生成 [3][4] 等下标 *)
  let fix geSubscript (d0:data) (prefix:string) : string :=
    match d0 with
    | dary n d1 => geSubscript d1 (prefix ++ "[" ++ dim2str n ++ "]")
    | dnum => prefix
    | _ => "err1"
    end in
  let name : string := data2str d no in
  match d with
  | dnum => "float " ++ name
  | didx _ => "int " ++ name
  | dary n _ => "float " ++ name ++ geSubscript d ""
  | dpair d1 d2 =>
      match d1, d2 with
      | dnum, dnum => "struct " ++ name ++ " { float x1; float x2 }"
      | _, _ => "err_data_pair"
      end
  end.

Section test.
  Compute data2str dnum 0. (* x0 *)
  Compute data2str (dary 3 dnum) 1. (* v1 *)
  Compute data2str (dary 3 (dary 4 dnum)) 1. (* v1 *)
  Compute data2str (didx 3) 1. (* i1 *)
  Compute data2str (dpair dnum dnum) 0. (* s0 *)
  
  Compute data2strDecl dnum 0. (* float x0 *)
  Compute data2strDecl (dary 3 dnum) 0. (* float v0[3] *)
  Compute data2strDecl (dary 3 (dary 4 dnum)) 1. (* float m1[3][4] *)
  Compute data2strDecl (didx 3) 1. (* int i1 *)
  Compute data2strDecl (dpair dnum dnum) 0. (* struct s0 { float x1; float x2 } *)

  Variable n : nat.
  Compute data2strDecl (dary (dstr n "n") dnum) 0. (* float v0[n] *)
End test.


(* ======================================================================= *)
(** ** data的语义是值类型 *)

(* Variable d : *)
Fixpoint value (d:data) : Type :=
  match d with
  | dnum => R
  | dary n d => vec (value d) (dim2nat n)
  | dpair d1 d2 => (value d1 * value d2)%type
  | didx n => fin (dim2nat n)
  end.

(* 某个值类型的默认值 *)
Fixpoint value_def (d:data) : value d :=
  match d with
  | dnum => R0
  | dary n d1 => fun i => value_def d1
  | dpair d1 d2 => (value_def d1, value_def d2)
  | didx n => n2f (dim2nat n)
  end.

(* value的相等关系。使用了新的 vec 类型后，不需要这种等价关系来表示相等 *)
(* Fixpoint value_eq {d:data} : value d -> value d -> Prop := *)
(*   match d with *)
(*   | dnum => eq *)
(*   | dary n d1 => veq (Teq:=(@value_eq d1)) *)
(*   | dpair d1 d2 => *)
(*       fun (x y:value (dpair d1 d2)) => *)
(*         @value_eq d1 (fst x) (fst y) /\ @value_eq d2 (snd x) (snd y) *)
(*   | didx n => eq *)
(*   end. *)

Section test.
  Variable n : nat.
  Compute value (dary 3 dnum).
  Eval cbn in value (dary (dstr n "n") dnum).   (* = vec R n *)
  Compute value (dary (dstr n "n") dnum).       (* = 'I_n -> R *)
End test.


(* ======================================================================= *)
(** ** 环境：id -> value *)

(** 环境中的一个项 *)
Inductive item :=
| item_real {d:data} (v:value d)  (* 真实的值，由外部传入 *)
| item_virt (d:data).             (* 虚拟的值，内部临时使用 *)

(* Scheme Equality for item. *)
(* Error: Unable to decide equality of functional arguments. *)

(* 取出item对应的data *)
Definition item2data (i:item) : data :=
  match i with
  | @item_real d v => d
  | item_virt d => d
  end.

(* 取出item对应的value *)
Definition item2value (i:item) (d:data) : value d.
  destruct i.
  - destruct (data_eqb d d0) eqn:E1.
    + apply data_eqb_eq in E1; subst; auto.
    + apply (value_def d).
  - apply (value_def d).
Defined.

(* 环境：编号 => (序号,项) *)
Definition env := @lmap (nat * item).
Definition empty_env : env := empty_lmap.

(* <编号, 序号，值, 环境> 四元组。ive表示 id,no,value,env。
     其中，
     编号：作为查找该item的索引，全局唯一，由 lmap 自动管理。
     序号：根据data类别自动生成，用于打印变量名。
     值：在 eval 时使用
     环境：当前的环境 *)
Definition inve d := (nat * nat * value d * env)%type.

(* 找出 env 中的最大新序号 *)
Definition env_new_no (m:env) (d:data) : nat :=
  list_new_id
    (fun x : nat*(nat*item) =>
       let '(id,(no,i)) := x in
       if data_same_type (item2data i) d
       then (true,no)
       else (false,0)) m.

(* 是否存在某个编号 *)
Definition env_exist (m:env) (id:nat) : bool := lmap_exist id m.
(* 取出某个编号对应的序号 *)
Definition env_get_no_o (m:env) (id:nat) : option nat := ofst (lmap_geto id m).
Definition env_get_no (m:env) (id:nat) : nat := oget (env_get_no_o m id) 99.
(* 取出某个编号对应的项 *)
Definition env_get (m:env) (id:nat) : option item := osnd (lmap_geto id m).
(* 取出某个编号对应的值 *)
Definition env_getv (m:env) (id:nat) d : value d :=
  match (env_get m id) with
  | Some i => item2value i d
  | _ => value_def d
  end.
(* 加入一个项，返回其编号和新环境 *)
Definition env_add (m:env) (no:nat) (i:item) : nat * env
  := lmap_add (no, i) m.
(* 加入一个值，返回其编号和新环境 *)
Definition env_addv (m:env) {d} (v:value d) : inve d :=
  let no := env_new_no m d in
  let '(id,m0) := lmap_add (no, item_real v) m in
  (id, no, v, m0).

(* 新建并加入一个值，返回inve *)
Definition env_new (m:env) (d:data) : inve d :=
  let no := env_new_no m d in
  let i := item_virt d in
  let '(id, m') := lmap_add (no,i) m in
  (id, no, item2value i d, m').
(* 从 inve 中取出各个分量 *)
Definition inve2id    {d} (x:inve d) : nat  := fst (fst (fst x)).
Definition inve2no    {d} (x:inve d) : nat  := snd (fst (fst x)).
Definition inve2value {d} (x:inve d) : value d := snd (fst x).
Definition inve2env   {d} (x:inve d) : env  := snd x.

Notation "'ID' x"  := (inve2id    x) (at level 0, format "'ID' x") : CG_scope.
Notation "'NO' x"  := (inve2no    x) (at level 0, format "'NO' x") : CG_scope.
Notation "'VAL' x" := (inve2value x) (at level 0, format "'VAL' x") : CG_scope.
Notation "'ENV' x" := (inve2env   x) (at level 0, format "'ENV' x") : CG_scope.

Notation "$ x"     := (inve2id    x) (at level 0, format "$ x") : CG_scope.
Notation "& x"     := (inve2env   x) (at level 0, format "& x") : CG_scope.

(* 找到环境m中类别为d的最新的一个项 *)
Definition env_find_first (m:env) (d:data) : option (nat * nat) :=
  match lmap_find_first m (fun x => data_eqb (item2data (snd x)) d) with
  | Some kvl => Some (fst (fst kvl), fst (snd (fst kvl)))
  | _ => None
  end.

(* 根据id更新环境中的一个项 *)
Definition env_update (m:env) (id:nat) {d} (v:value d) : env :=
  if env_exist m id
  then
    let no := env_get_no m id in
    let chk_type (i:nat*item) : bool :=
      Nat.eqb no (fst i) && data_eqb (item2data (snd i)) d in
    lmap_update m id (no, item_real v) chk_type
  else m.

(* 删除环境m中类别为d的最新的一个项 *)
Definition env_del (m:env) (d:data) : env :=
  lmap_del_first m (fun x => data_eqb (item2data (snd x)) d).

(* 变量集合转字符串，用于调试 *)
Definition env2str (m:env) : string :=
  concat "; " (map
                 (fun i => data2str (item2data (snd (snd i))) (fst (snd i)))
                 m).

Section test.
  Let e0 : env := empty_env.
  Let e1 : inve dnum := env_new e0 dnum.  Compute e1.
  Let e2 : inve (dary 2 dnum) := env_new &e1 (dary 2 dnum).  Compute e2.
  Let e3 : inve (didx 3) := env_new &e2 (didx 3).  Compute e3.

  Compute &e3.
  (* 
     = [(2, (0, item_virt (didx 3))); (1, (0, item_virt (dary 2 dnum)));
        (0, (0, item_virt dnum))]
   *)
  
  (* Let e4 : inve := env_del e4 (var_id dnum 0). Compute e5. *)
  Let e4 := env_new &e3 (didx 2).
  Compute &e4.
  (* 
     = [(3, (1, item_virt (didx 2))); (2, (0, item_virt (didx 3)));
        (1, (0, item_virt (dary 2 dnum))); (0, (0, item_virt dnum))]
   *)
  
  Let e5 := env_new &e4 (didx 4).
  Compute &e5.
  (* 
     = [(4, (2, item_virt (didx 4))); (3, (1, item_virt (didx 2))); 
        (2, (0, item_virt (didx 3))); (1, (0, item_virt (dary 2 dnum))); 
        (0, (0, item_virt dnum))]
   *)

  Compute env_find_first &e5 (didx 3).
  Compute e5.
  Compute env2str &e5.     (* = "i2; i1; i0; v0; x0" *)
  Compute env2str (env_del &e5 dnum).     (* = "i2; i1; i0; v0" *)
  Compute env2str (env_del &e5 (didx 2)).     (* = "i2; i0; v0; x0" *)
  Compute env2str (env_del &e5 (didx 3)).     (* = "i2; i1; v0; x0" *)
  Compute env2str (env_del &e5 (didx 4)).     (* = "i1; i0; v0; x0" *)
  Compute env2str (env_del &e5 (didx 5)).     (* = "i2; i1; i0; v0; x0" *)
  
End test.


(** ** 表达式（右值） *)
(* 备注：
   1. 由于Coq要求 Strickly Positivity Occurrence，简言之，在Inductive定义中，
      构造子的参数中如果有函数时要求函数的箭头左侧不能是该类型名本身，否则可能会无穷递归。
      此处是临时关闭了该选项，所以不会自动生成归纳原理，需要自己来证明。
 *)
#[bypass_check(positivity=yes)]
  Inductive exp : data -> Type :=
(* 变量 *)
| e_var {d} (id:nat) : exp d
(* 实数常量 *)
| e_cnst (val:Rstring) : exp dnum
(* 一元操作  *)
| e_op1 (op:Rop1) (e:exp dnum) : exp dnum
(* 二元操作  *)
| e_op2 (op:Rop2) (e1 e2:exp dnum) : exp dnum
(* 对向量e执行f映射  *)
| e_map {d1 d2:data} {n:dim} (f:exp d1 -> exp d2) (e:exp (dary n d1))
  : exp (dary n d2)
(* 使用初始值e和二元运算f对向量ev执行折叠 *)
| e_reduce {d1 d2:data} {n:dim} (f:exp d1->exp d2->exp d2)
    (ev:exp (dary n d1)) (e:exp d2) : exp d2
(* 向量e的迭代器 *)
| e_idx {d} {n} (e:exp (dary n d)) (i:exp (didx n)) : exp d
(* 构造向量 *)
| e_mkv {d} {n} (f:fin(dim2nat n)->exp d) : exp (dary n d)
(* 构造矩阵 *)
| e_mkm {d} {r c} (f:fin(dim2nat r)->fin(dim2nat c)->exp d) : exp (dmat r c d)
(* 向量e的第i个元素 *)
| e_nth {d} {n} (e:exp (dary n d)) (i:fin (dim2nat n)) : exp d
(* 向量e1和e2合并为一个向量 *)
| e_zip {d1 d2} {n} (e1:exp (dary n d1)) (e2:exp (dary n d2))
  : exp (dary n (dpair d1 d2))
(* 两个右值e1和e2作为对偶 *)
| e_pair {d1 d2} (e1:exp d1) (e2:exp d2) : exp (dpair d1 d2)
(* 取出对偶的第一个分量 *)
| e_fst {d1 d2} (e:exp (dpair d1 d2)) : exp d1
(* 取出对偶的第二个分量 *)
| e_snd {d1 d2} (e:exp (dpair d1 d2)) : exp d2
(* 矩阵转置 *)
| e_trans {d} {r c} (e:exp (dmat r c d)) : exp (dmat c r d)
.
Coercion e_var : nat >-> exp.

(* 参考 VST/compcert/cfontend/Clight.v, line434 的做法。不确定此处的用途 *)
Scheme exp_ind := Minimality for exp Sort Prop.

(* Coercion e_cnst : Rstring >-> exp. *)
Definition e_cnst0 : exp dnum := e_cnst 0.
Definition e_cnst1 : exp dnum := e_cnst 1.
Definition e_cnst2 : exp dnum := e_cnst 2.

(* 方便的记号 *)
Notation e_neg := (e_op1 Rop1_neg).
Notation e_add := (e_op2 Rop2_add).
Notation e_mul := (e_op2 Rop2_mul).
Infix "+" := (e_op2 Rop2_add) : CG_scope.
Infix "-" := (e_op2 Rop2_sub) : CG_scope.
Infix "*" := (e_op2 Rop2_mul) : CG_scope.
Infix "/" := (e_op2 Rop2_div) : CG_scope.
Notation "- x" := (e_op1 Rop1_neg x) : CG_scope.
Notation "'Sin' x" := (e_op1 Rop1_sin x) (at level 10) : CG_scope.
Notation "'Cos' x" := (e_op1 Rop1_cos x) (at level 10) : CG_scope.
Notation "'Atan' x" := (e_op1 Rop1_atan x) (at level 10) : CG_scope.
Notation "'Asin' x" := (e_op1 Rop1_asin x) (at level 10) : CG_scope.
Notation "'Atan2' ( x , y )" :=
  (e_op2 Rop2_atan2 x y)
    (at level 10, x,y at next level, format "'Atan2' ( x , y )") : CG_scope.

(* Let f1 : fin (dim2nat 1). *)
(*   Set Printing All. *)
(*   cbn. apply fin0. *)
(* Defined. *)
(* Check e_nth _ f1. *)

Notation "v .1" := (e_nth v (n2f 0)) : CG_scope.
Notation "v .2" := (e_nth v (n2f 1)) : CG_scope.
Notation "v .3" := (e_nth v (n2f 2)) : CG_scope.
Notation "v .4" := (e_nth v (n2f 3)) : CG_scope.

(** exp的语义 *)
Fixpoint eeval {d:data} (e:exp d) (eta:env) {struct e} : value d.
  destruct e.
  - (* e_var *)
    destruct (env_get eta id).
    + apply (item2value i d).
    + apply (value_def d).
  - (* e_cnst *) apply val.
  - (* e_op1 *) apply (Rop1_eval op (eeval _ e eta)).
  - (* e_op2 *) apply (Rop2_eval op (eeval _ e1 eta) (eeval _ e2 eta)).
  - (* e_map *)
    apply (vmake (fun i => eeval _ (f (e_nth e i)) eta)).
  - (* e_reduce *)
    pose (eeval _ e1 eta) as v.  (* e1是待缩减的数组 *)
    pose (eeval _ e2 eta) as x0. (* e2是初始值 *)
    (* 新增d2类型的变量，编号为id，环境更新为 eta1 *)
    pose (env_new eta d2) as inve0.
    pose $inve0 as id.
    pose &inve0 as eta1.
    (* 给该变量赋初始值，环境更新为 eta2 *)
    pose (env_update eta1 id x0) as eta2.
    (* 用自然数i来循环n次，执行 var[id] = f v[i] var[id]，最终环境更新为 eta3 *)
    pose (fold_seq (fun n:nat=>n) (dim2nat n)
            (fun (i:nat) (m:env) =>
               env_update m id (eeval _ (f (e_nth e1 (n2f i)) (e_var id)) m))
            eta2) as eta3.
    (* 取出该环境下的 var[id] 的值 *)
    apply (env_getv eta3 id d2).
  - (* e_idx *)
    pose (eeval _ e1 eta) as v.
    pose (eeval _ e2 eta) as i.
    apply (v i).
  - (* e_mkv *)
    apply (vmake (fun i => eeval _ (f i) eta)).
  - (* e_mkm *)
    apply (mmake (fun i j => eeval _ (f (n2f i) (n2f j)) eta)).
  - (* e_nth *) pose (eeval _ e eta) as v. apply (v i).
  - (* e_zip *)
    pose (eeval _ e1 eta) as v1. pose (eeval _ e2 eta) as v2.
    apply (vmake (fun i => (v1 i, v2 i))).
  - (* e_pair *) apply (eeval _ e1 eta, eeval _ e2 eta).
  - (* e_fst *) apply (fst (eeval _ e eta)).
  - (* e_snd *) apply (snd (eeval _ e eta)).
  - (* e_trans *) apply (mtrans (eeval _ e eta)).
Defined.

Section test.

  Variable (r1 r2:R) (n:nat).
  Let e1:exp dnum := e_cnst (mkRstring r1 "r1").
  Let e2:exp dnum := e_cnst (mkRstring r2 "r2").
  Compute eeval e1 [].
  Compute (eeval (e_neg e1) []).
  Compute (eeval (e_add e1 e2) []).

  Let e3:exp (dary n dnum) := e_mkv (fun i => e_cnst (mkRstring (INR i) "?")).
  Let e4:exp (dary n dnum) := e_mkv (fun i => e_cnst (mkRstring (INR (S i)) "?")).
  Let e5:exp (dary 3 dnum) := e_mkv (fun i => e_cnst (mkRstring (INR (S i)) "?")).
  Eval cbn in eeval (e_zip e3 e4) [].

  Eval cbn in (eeval (e_map e_neg e3) []).
  Eval cbn in (eeval (e_reduce e_add e3 e1) []).
  Eval cbv in (eeval (e_reduce e_add e5 e1) []). (* (1+(2+(3+r1))) *)
End test.

(* 验证单个exp的语义等价 *)
Definition exp_semeq1 {d} (e:exp d) (eta:env) (expected:value d) : Prop :=
  (eeval e eta) = expected.

(* 验证两个exp的语义等价 *)
Definition exp_semeq2 {d} (e1 e2:exp d) (eta:env) : Prop :=
  (eeval e1 eta) = (eeval e2 eta).


(** ** 接收器、左值  *)
Section acc.
  (** 接收器，即左值，或者说是一个可以被改变的对象。*)
  Inductive acc : data -> Type :=
  | a_var {d} (id:nat) : acc d
  | a_idx {d} {n} (a:acc (dary n d)) (e:exp (didx n)) : acc d
  | a_nth {d} {n} (a:acc (dary n d)) (i:nat) : acc d
  (* 对偶的左（右）分量 *)
  | a_fst {d1 d2} (a:acc (dpair d1 d2)) : acc d1
  | a_snd {d1 d2} (a:acc (dpair d1 d2)) : acc d2
  (* 由对偶组成的数组的每个左（右）分量构成数组 *)
  | a_vfst {d1 d2:data} {n:dim} (a:acc (dary n (dpair d1 d2))) : acc (dary n d1)
  | a_vsnd {d1 d2:data} {n:dim} (a:acc (dary n (dpair d1 d2))) : acc (dary n d2)
  .
  Coercion a_var : nat >-> acc.
End acc.

(** ** 访问路径，这是 acc 的语义 *)
Section paths.

  (* 路径 *)
  Inductive path :=
  | p_err
  | p_var (s:string)              (* 由字符串构成的变量，暂时的方案 *)
  | p_idx (n:nat)                   (* 数组索引迭代器 *)
  | p_id (n:nat)                    (* 索引常量 *)
  | p_fst                         (* 对偶左分量 *)
  | p_snd                         (* 对偶右分量 *)
  .

  (* 路径转字符串 *)
  Definition path2str (p:path) : string :=
    let s_inner : string :=
      match p with
      | p_err => "pErr"
      | p_var s => s
      | p_idx n => "i" ++ nat2str n
      | p_id n => nat2str n
      | p_fst => "x1"
      | p_snd => "x2"
      end in
    "[" ++ s_inner ++ "]".

  (* 完整路径 *)
  Definition paths := list path.

  (* 向完整路径增加一个元素 *)
  Definition paths_add (ps:paths) (p:path) : paths := p :: ps.

  (* 完整路径转字符串。倒序输出 *)
  Definition paths2str (ps:paths) : string :=
    concat "" (map path2str ps).
  
  Compute paths2str [p_var "a"; p_var "b"].
  Compute paths2str [p_idx 3; p_var "x0"].

  Fixpoint acc_eval {d:data} (a:acc d) (eta:env) (ps:paths) : paths.
    destruct a.
    - (* a_var *)
      destruct (env_get_no_o eta id) as [no|].
      + apply (paths_add ps (p_var (data2str d no))).
      + apply (paths_add ps p_err).
    - (* a_idx *)
      pose (acc_eval _ a eta ps) as ps1.
      pose (eeval e eta) as i.
      apply (paths_add ps1 (p_idx i)).
    - (* a_nth *)
      pose (acc_eval _ a eta ps) as ps1.
      apply (paths_add ps1 (p_id i)).
    - (* a_fst *)
      pose (acc_eval _ a eta ps) as ps1.
      apply (paths_add ps1 p_fst).
    - (* a_snd *)
      pose (acc_eval _ a eta ps) as ps1.
      apply (paths_add ps1 p_snd).
    - (* a_vfst *)
      pose (acc_eval _ a eta ps) as ps1.
      pose (env_new eta (didx n)) as i.
      pose (paths_add ps1 (p_id $i)) as ps2.
      apply (paths_add ps2 p_fst).
    - (* a_vsnd *)
      pose (acc_eval _ a eta ps) as ps1.
      pose (env_new eta (didx n)) as i.
      pose (paths_add ps1 (p_id $i)) as ps2.
      apply (paths_add ps2 p_snd).
  Defined.

  Section test.

    Variable n : dim.
    Let eta : env := Eval cbv in 
          let x := env_new empty_env dnum in
          let x := env_new &x (dary n dnum) in
          let x := env_new &x (dpair dnum dnum) in
          let x := env_new &x (didx n) in
          let x := env_new &x (dary n (dpair dnum dnum)) in
          &x.
    
    Let a1 : acc dnum := a_var 0.
    Let a2 : acc (dary n dnum) := a_var 1.
    Let a3 : acc (dpair dnum dnum) := a_var 2.
    Let a4 : acc (dary n (dpair dnum dnum)) := a_var 3.
    Let ei : exp (didx n) := e_var 3.
    Eval cbn in acc_eval a1 eta [].
    Eval cbn in acc_eval a2 eta [].
    Eval cbn in acc_eval a3 eta [].
    Eval cbn in acc_eval (a_idx a2 ei) eta [].
    Eval cbn in acc_eval (a_nth a2 2) eta [].
    Eval cbn in acc_eval (a_fst a3) eta [].
    Eval cbn in acc_eval (a_snd a3) eta [].
    Eval cbn in acc_eval (a_vfst a4) eta [].
    Eval cbn in acc_eval (a_vsnd a4) eta [].
  End test.
End paths.


(** ** 命令 *)
Section comm.
  Inductive comm :=
  | c_debug (n:nat)

  | c_skip
  | c_seq (c1 c2:comm)
  | c_new {d} (f:acc d->exp d->comm)
  | c_asgn (a:acc dnum) (e:exp dnum)

  (* 串行for；并行for *)
  | c_for {n:dim} (f:exp (didx n)->comm)
  | c_parfor {d} {n} (a:acc (dary n d)) (f:exp (didx n)->acc d->comm)

  (* map的中间过程 *)
  | c_mapI {d1 d2} {n} (f:acc d2->exp d1->comm) (e:exp (dary n d1)) (a:acc (dary n d2))
  (* | c_mapI {d} {n:dim} (f:acc d->(nat*fin (dim2nat n))->comm) (a:acc (dary n d)) *)
  | c_reduceI {d1 d2} {n} (f:exp d1->exp d2->acc d2->comm)
      (ev:exp (dary n d1)) (e0:exp d2) (c:exp d2->comm)
  (* | c_reduceI {d1 d2} {n} (f:nat->(nat*fin (dim2nat n))->acc d2->comm) *)
  (*     (ev:exp (dary n d1)) (e0:exp d2) (c:exp d2->comm) *)
  (* trans的中间过程 *)
  | c_transI {d} {n m} (a:acc (dmat m n d)) (e:exp (dmat n m d))
  .

  Fixpoint ceval (c:comm) (eta:env) : env.
    destruct c.
    - (* c_debug *)
      apply eta.
    - (* c_skip *)
      apply eta.
    - (* c_seq *)
      apply (ceval c2 (ceval c1 eta)).
    - (* c_new *)
      pose (env_new eta d) as x.
      apply (ceval (f (a_var $x) (e_var $x)) &x).
    - (* c_asgn *)
      apply (env_update eta 0 (eeval e eta)).
    - (* c_for *)
      (* 不太理解 exp (didx n)。
         其实for的语义很明确，就是执行 n 次命令，环境不断被更新 n 次 *)
      (* Compute (value (didx n)). *)
      (* Check (fun i => ceval (f i) eta). *)
      (* Check e_idx. *)
      apply eta.
    - (* c_parfor *)
      apply eta.
    - (* c_mapI *)
      (* 思考：map操作会改变环境吗？*)
      apply eta.
    (* apply (fold_seq *)
    (*          (fun n:nat=>n) (dim2nat n) *)
    (*          (fun i m => ceval (f (a_nth a i) (e_nth e (n2f i))) m) *)
    (*          eta). *)
    - (* c_reduceI *)
      pose (eeval e0 eta) as x0. (* e0是初始值 *)
      (* 新增 d2 类型的变量 x，作为左值是x_acc，编号是 x_id，环境更新为 eta1 *)
      pose (env_new eta d2) as inve0.
      pose $inve0 as x_id.
      pose (@a_var d2 x_id) as x_acc.
      pose (@e_var d2 x_id) as x.
      pose &inve0 as eta1.
      (* 给变量x赋初始值，环境更新为 eta2 *)
      pose (env_update eta1 x_id x0) as eta2.
      (* 用自然数i来循环n次，执行 x = f v[i] x，最终环境更新为 eta3 *)
      pose (fold_seq (fun n:nat=>n) (dim2nat n)
              (fun (i:nat) (m:env) => ceval (f (e_nth ev (n2f i)) x x_acc) m)
              eta2) as eta3.
      (* 继续执行 *)
      apply (ceval (c x) eta3).
    - (* c_transI *)
      apply (env_update eta 0 ((mtrans (eeval e eta)):value (dmat m n d))).
  Defined.

  Section test.


  End test.
End comm.


(** ** From Functional to Imperative *)

(** *** Stage I: Higher-order Functional to Higher-order Imperative *)

(** 赋值 a := e *)
Fixpoint assign {d:data} : acc d -> exp d -> comm :=
  match d with
  | dnum => fun a e => c_asgn a e
  | dary n d1 => fun a e =>
                   c_mapI (fun a x => assign a x) e a
  (* c_mapI (fun a i => assign a (e_idx e i)) a *)
  | dpair d1 d2 => fun a e => c_seq
                                (assign (a_fst a) (e_fst e))
                                (assign (a_snd a) (e_snd e))
  | didx n => fun a e => c_debug 10
  end.

(* 将 mkv 原语转换为命令 *)
Fixpoint mkv2comm {d} {n} (a:acc (dary n d)) (f:fin (dim2nat n) -> exp d)
  (Ctrans : forall d:data, exp d -> (exp d->comm) -> comm)
  (n0:nat) : comm :=
  match n0 with
  | O => c_skip
  | S O => Ctrans _ (f (n2f 0)) (fun x => assign (a_nth a O) x)
  | S n0' =>
      Ctrans _ (f (n2f n0'))
        (fun x =>
           c_seq
             (mkv2comm a f Ctrans n0')
             (assign (a_nth a n0') x))
  end.

(* 将 mkm 原语转换为命令。这其实是 mkv2comm 的简单调用，以后考虑去掉 *)
Definition mkm2comm {d} {r c} (a:acc (dmat r c d))
  (f:fin (dim2nat r)->fin (dim2nat c)-> exp d)
  (Ctrans : forall d:data, exp d -> (exp d->comm) -> comm)
  (r0 c0:nat) : comm :=
  let lst_comm : list comm :=
    map (fun i:nat =>
           mkv2comm (a_nth a i) (f (n2f i)) Ctrans c0) (seq 0 r0) in
  fold_left1 c_seq lst_comm c_skip.

(* Unset Guard Checking. *)

Section build_Atrans.
  Variable Ctrans : forall d (e:exp d) (C:exp d->comm), comm.
  Fixpoint AtransM d (a:acc d) (e:exp d) {struct e} : comm.
    destruct e.
    - (* e_var *)
      apply (assign a (e_var id)).
    - (* e_cnst *)
      apply (c_asgn a (e_cnst val)).
    - (* e_op1 *)
      apply (Ctrans _ e (fun x:exp dnum => c_asgn a (e_op1 op x))).
    - (* e_op2 *)
      apply (Ctrans _ e1 (fun x => Ctrans _ e2 (fun y => c_asgn a (e_op2 op x y)))).
    - (* e_mapI *)
      apply (Ctrans _ e
               (fun x:exp (dary n d1) =>
                  (c_mapI (fun a1 e1 => AtransM _ a1 (f e1)) x a))).
    - (* e_reduceI *)
      apply (Ctrans _ e1
               (fun x =>
                  Ctrans _ e2
                    (fun y => 
                       (c_reduceI
                          (fun id_x i (o:acc d2) =>
                             (* (assign o (f id_x i))) x y) *)
                             Ctrans _ (f id_x i) (fun z => assign o z)) x y)
                         (* Ctrans _ (f id_x i) (fun z => AtransM _ o z)) x y) *)
                         (fun r:exp d2=> assign a r)))).
    (* (fun r:exp d2=> AtransM _ a r)))). *)
    - (* e_idx *)
      apply (c_debug 30).
    - (* e_mkv *)
      apply (mkv2comm a f Ctrans (dim2nat n)).
    - (* e_mkm *)
      apply (mkm2comm a f Ctrans (dim2nat r) (dim2nat c)).
    - (* e_nth *)
      apply (assign a (e_nth e i)).
    - (* e_zip *)
      apply (c_seq (AtransM _ (a_vfst a) e1) (AtransM _ (a_vsnd a) e2)).
    (* Check c_mapI. *)
    (* Check (fun i => assign (a_idx a i) (e_pair (e_idx e1 i) (e_idx e2 i))). *)
    - (* e_pair *)
      apply (c_seq (AtransM _ (a_fst a) e1) (AtransM _ (a_snd a) e2)).
    - (* e_fst *)
      apply (Ctrans _ e (fun x => assign a (e_fst x))).
    (* apply (Ctrans _ e (fun x => AtransM _ a (e_fst x))). *)
    - (* e_snd *)
      apply (Ctrans _ e (fun x => assign a (e_snd x))).
    - (* e_trans *)
      apply (Ctrans _ e (fun x => c_transI a x)).
  Defined.
End build_Atrans.

(* Unset Guard Checking. *)

(* Ctrans的作用：将树形的函数式结构转换为线性的命令式的结构。 *)
Section build_Ctrans.
  Variable Atrans : forall (d:data) (a:acc d) (e:exp d), comm.
  Fixpoint CtransM (d:data) (e:exp d) {struct e} : (exp d->comm) -> comm.
    destruct e; intros C.
    - (* e_var *)
      (* apply (c_new *)
      (*          (fun ae:acc d * exp d => *)
      (*             (assign (fst ae) (snd ae)))). *)
      apply (C (e_var id)).
    - (* e_cnst *)
      apply (C (e_cnst val)).
    - (* e_op1 *)
      apply (CtransM _ e (fun x => C (e_op1 op x))).
    - (* e_op2 *)
      apply (CtransM _ e1 (fun x => CtransM _ e2 (fun y => C (e_op2 op x y)))).
    - (* e_map *)
      apply
        (c_new 
           (fun (a1:acc (dary n d2)) (e1:exp (dary n d2)) =>
              c_seq (Atrans _ a1 (e_map f e)) (C e1))).
    - (* e_reduceI *)
      (* apply (c_reduceI (fun id_x id_i fi (o:acc d2) => *)
      (*                    CtransM _ (f id_x id_i fi) *)
      (*                           (fun z => assign o z)) e1 e2 C). *)
      apply
        (CtransM _ e1
           (fun x =>
              CtransM _ e2
                (fun y =>
                   (c_reduceI
                      (fun id_x i (o:acc d2) =>
                         (* assign o (f id_x i))) x y C))). *)
                         CtransM _ (f id_x i) (fun z => assign o z)) x y C)))).
    (* CtransM _ (f id_x i) (fun z => Atrans _ o z)) x y C)))). *)
    - (* e_idx *)
      apply (CtransM _ e1 (fun x => C (e_idx x e2))).
    - (* e_mkv *)
      apply (C (e_mkv f)).
    - (* e_mkm *)
      apply (C (e_mkm f)).
    - (* e_nth *)
      apply (C (e_nth e i)).
    - (* e_zip *)
      apply (CtransM _ e1 (fun x => CtransM _ e2 (fun y => C (e_zip x y)))).
    - (* e_pair *)
      apply (CtransM _ e1 (fun x => CtransM _ e2 (fun y => C (e_pair x y)))).
    - (* e_fst *)
      apply (CtransM _ e (fun x => C (e_fst x))).
    - (* e_snd *)
      apply (CtransM _ e (fun x => C (e_snd x))).
    - (* e_trans *)
      apply (C (e_trans e)).
  Defined.

End build_Ctrans.


Unset Guard Checking.
Fixpoint
  Ctrans (d:data) (e:exp d) {struct e} : (exp d->comm) -> comm :=
  @CtransM
    Atrans
    d e
with
Atrans (d:data) (a:acc d) (e:exp d) {struct e} : comm :=
  @AtransM Ctrans d a e.

(* Set Guard Checking. *)
Arguments Ctrans {d}.
Arguments Atrans {d}.

(* 调试 cnst *)
Section test.
  (* x0 := 0 *)
  Let a0 : acc dnum := @a_var _ 0.
  Let e0 : exp dnum := e_cnst0.
  Compute Atrans a0 e0.
End test.

(* 调试 map *)
Section test.
  (* x1 := map e1 (+1) *)
  Let a2 : acc (dary 3 dnum) := a_var 0.
  Let e1 : exp (dary 3 dnum) := e_var 1.
  Let e2 : exp (dary 3 dnum) := e_map (fun x => e_cnst1 + x) e1.
  Let e3 : exp (dary 3 dnum) := e_map (fun x => e_cnst1 + x) e2.
  Let e4 : exp (dary 3 dnum) := e_map (fun x => e_cnst1 + x) e3.
  Eval cbn in Atrans a2 e2.
  Eval cbn in Atrans a2 e3.
  Eval cbn in Atrans a2 e4.
End test.

(* 调试 reduce *)
Section test.
  Variable n : dim.
  Variable ev : exp (dary n dnum).
  Variable e0 : exp dnum.
  Variable a : acc dnum.
  Let e1 := e_reduce (e_op2 Rop2_add) ev e0.
  Let e2 := e_reduce (e_op2 Rop2_add) ev e1.
  Compute e1.
  Compute e2.
  Eval cbn in Atrans a e1.
  Eval cbn in Atrans a e2.
End test.



(* 调试 map+reduce *)
Section test.
  (* x1 := map e1 (+1) *)
  Let a2 : acc (dary 3 dnum) := a_var 0.
  Let e1 : exp (dary 3 dnum) := e_var 1.
  Let e2 : exp (dary 3 dnum) := e_map (fun x => (e_reduce (e_op2 Rop2_add) e1 e_cnst1) + x) e1.
  Let e3 : exp (dary 3 dnum) := e_map (fun x => (e_reduce (e_op2 Rop2_add) e2 e_cnst1) + x) e2.
  Let e4 : exp (dary 3 dnum) := e_map (fun x => (e_reduce (e_op2 Rop2_add) e3 e_cnst1) + x) e3.
  Eval cbn in Atrans a2 e2.
  Eval cbn in Atrans a2 e3.
  Eval cbn in Atrans a2 e4.
End test.

(** *** Stage II: Higher-order Imperative to For-loops *)

(* Unset Guard Checking. *)
(** Transalate Higher-order Imperative to For-loops  *)
Fixpoint HItrans (c : comm) : comm :=
  match c with
  | c_debug n => c
  | c_skip => c
  | c_seq c1 c2 => c_seq (HItrans c1) (HItrans c2)
  | c_new f => c_new (fun a e => HItrans (f a e))
  | c_asgn a e => c
  | c_for f => c_for (fun i => HItrans (f i))
  | c_parfor a f => c_parfor a (fun a e => HItrans (f a e))
  | c_mapI f e a => c_parfor a (fun i a => HItrans (f a (e_idx e i)))
  | @c_transI d n m a e =>
      (* 两种循环方式 *)
      (* 方式1：out[i][j] = in[j][i] *)
      (* c_for (fun i =>
               c_for (fun j =>
                        assign
                          (a_idx (a_idx a i) j)
                          (e_idx (e_idx e j) i)))
       *)
      (* 方式2：out[j][i] = in[i][j] *)
      c_for (fun j =>
               c_for (fun i =>
                        assign
                          (a_idx (a_idx a i) j)
                          (e_idx (e_idx e j) i)))
  | c_reduceI f ev e0 C => 
      c_new (fun a1 e1 =>
               c_seq
                 (assign a1 e0)
                 (c_seq
                    (c_for (fun i => f (e_idx ev i) e1 a1))
                    (C e1)))
  end.

(** *** Stage III: For-loops to Parallel Pseudo-C  *)


(** exp转字符串 *)
Fixpoint CGexp {d:data} (e:exp d) (eta:env) (ps:paths) {struct e} : string
  :=
  match e with
  | e_var id =>
      let s :=
        if env_exist eta id
        then let no := env_get_no eta id in data2str d no
        else "err_CGexp_var" in
      s ++ paths2str ps
  | e_cnst rs => Rstr rs
  | e_op1 op e1 => Rop1_str op (CGexp e1 eta [])
  | e_op2 op e1 e2 => Rop2_str op (CGexp e1 eta []) (CGexp e2 eta [])
  | e_map f ev => "err_CGexp_map_must_none"
  | e_reduce f e0 ev => "err_CGexp_reduce_must_none"
  | e_nth ev fi =>
      CGexp ev eta (paths_add ps (p_var (nat2str fi)))
  | e_mkv f => "err_CGexp_mkv_must_none"
  | e_mkm f => "err_CGexp_mkm_must_none"
  | e_idx ev ei =>
      let si := CGexp ei eta [] in
      let ps := paths_add ps (p_var si) in
      CGexp ev eta ps
  (* | @e_idx d n ev i => *)
  (*     let no := env_get_no eta (fst i) in *)
  (*     let ps := paths_add ps (p_idx no) in *)
  (*     (* "@@" ++ nat2str (fst i) ++ "@@" ++ strNewline ++ *) *)
  (*     CGexp ev eta ps *)
  | e_zip ev1 ev2 =>
      match ps with
      | i :: j :: ps =>
          match j with
          | p_fst => CGexp ev1 eta (paths_add ps i)
          | p_snd => CGexp ev2 eta (paths_add ps i)
          | _ => "err_CGexp_path1"
          end
      | _ => "err_CGexp_zip_path2"
      end
  | e_pair e1 e2 =>
      match ps with
      | i :: j :: ps' =>
          match j with
          | p_fst => CGexp e1 eta ps
          | p_snd => CGexp e2 eta ps
          | _ => "err_CGexp_pair_path1"
          end
      | _ => "err_CGexp_pair_path2"
      end
  | e_fst e0 => CGexp e0 eta (paths_add ps p_fst)
  | e_snd e0 => CGexp e0 eta (paths_add ps p_snd)
  | e_trans em =>
      (* "err_CGexp_trans_path" *)
      (* "@" ++ paths2str ps ++ "@" *)
      match ps with
      | i :: j :: ps => CGexp em eta (j :: i :: ps)
      | _ => "err_CGexp_trans_path"
      end
  end.

(** acc转字符串 *)
Fixpoint CGacc {d:data} (a:acc d) (eta:env) (ps:paths) {struct a}
  : string :=
  match a with
  | a_var id =>
      let s := if env_exist eta id
               then data2str d (env_get_no eta id)
               else "err_CGacc_var" in
      s ++ paths2str ps
  | a_idx a0 i =>
      let ps := paths_add ps (p_var (CGexp i eta [])) in
      CGacc a0 eta ps
  (* | @a_idx d n a i => *)
  (*     let no := env_get_no eta (fst i) in *)
  (*     let ps := paths_add ps (p_idx no) in *)
  (*     CGacc a eta ps *)
  | a_nth a0 i =>
      let ps := (paths_add ps (p_var (nat2str i))) in
      CGacc a0 eta ps
  | a_fst a0 => CGacc a0 eta (paths_add ps p_fst)
  | a_snd a0 => CGacc a0 eta (paths_add ps p_snd)
  | a_vfst a =>
      match ps with
      | i :: ps =>
          match i with
          | p_idx i0 =>
              let ps := paths_add (paths_add ps p_fst) i in
              CGacc a eta ps
          | _ => "err_CGacc_vfst_path1"
          end
      | _ => "err_CGacc_vfst_path2"
      end
  | a_vsnd a =>
      match ps with
      | i :: ps =>
          match i with
          | p_idx i0 =>
              let ps := paths_add (paths_add ps p_snd) i in
              CGacc a eta ps
          | _ => "err_CGacc_vsnd_path1"
          end
      | _ => "err_CGacc_vsnd_path2"
      end
  end.


(** comm转字符串 *)
Fixpoint CGcomm (c:comm) (eta:env) {struct c} : string :=
  match c with
  | c_debug n => "debug(" ++ nat2str n ++ ")"
  | c_skip => "/* skip */"
  | c_seq c1 c2 => (CGcomm c1 eta) ++ strNewline ++ (CGcomm c2 eta)
  | @c_new d f =>
      let x := env_new eta d in
      let s1 := data2strDecl d NO(x) in
      let s2 := CGcomm (f (a_var ID(x)) (e_var ID(x))) &x in
      "{" ++ strNewline ++ s1 ++ ";" ++ strNewline ++ s2 ++ strNewline ++ "}"
  | c_asgn a e =>
      (* CGacc a eta ps ++ " = " ++ CGexp e eta ps ++ ";" *)
      CGacc a eta [] ++ " = " ++ CGexp e eta [] ++ ";"
  | @c_for n f =>
      let  i := env_new eta (didx n) in
      let si := data2str (didx n) NO(i) in
      let sn := dim2str n in
      (* let ps := paths_add ps (p_idx NO(i)) in *)
      let s1 := CGcomm (f (e_var $i)) &i in
      (* "&" ++ env2str &i ++ "|" ++ nat2str $i ++ "&" ++ *)
      "for (int " ++ si ++ " = 0; " ++ si ++ " < " ++ sn ++ "; " ++
        si ++ " += 1) {" ++ strNewline ++ s1 ++ strNewline ++ "}"
  | @c_parfor _ n a f =>
      let  i := env_new eta (didx n) in
      let si := data2str (didx n) NO(i) in
      let sn := dim2str n in
      let s1 := CGcomm (f (e_var $i) (a_idx a $i)) &i in
      (* "#pragma omp parallel for" ++ strNewline ++ *)
        "for (int " ++ si ++ " = 0; " ++ si ++ " < " ++ sn ++ "; " ++
        si ++ " += 1) {" ++ strNewline ++ s1 ++ strNewline ++ "}"
  | c_mapI f e a => "err_CGcomm_mapI"
  | c_reduceI f1 e0 ev f2 => "err_CGcomm_reduceI"
  | c_transI a e => "err_CGcomm_transI"
  end.

(** 几个简洁的函数名 *)
Definition CG0 {d} (a:acc d) (e:exp d) : comm := Atrans a e.
Definition CG1 {d} (a:acc d) (e:exp d) : comm := HItrans (CG0 a e).
Definition CG  {d} (a:acc d) (e:exp d) (eta:env) : string := CGcomm (CG1 a e) eta.


(** * Properties of above operations *)

(** item2value (v) = v  *)
Theorem item2value_item_real : forall d (v:value d), item2value (@item_real d v) d = v.
Proof.
  intros. unfold item2value.
  Fail destruct (data_eqb d d).
  Fail rewrite data_eqb_refl.
  (* 不熟悉依赖类型的证明机制，暂无法完成 *)
Admitted.


(** * 用户程序 *)

Section array_copy.

  Variable n : nat.
  Let dn : dim := dstr n "n".
  Variable v1 v2 : vec R n.
  Let _v1 := env_addv empty_env (v1:value (dary dn dnum)).
  Let _v2 := env_addv &_v1 (v2:value (dary dn dnum)).

  Let a : acc (dary dn dnum) := $_v2.
  Let e : exp (dary dn dnum) := $_v1.
  Let eta : env := &_v2.
  Compute CG0 a e.
  (*  = c_mapI (fun (x : exp dnum) (x0 : acc dnum) => c_asgn (x0, x)) 0 1 *)
  Compute CG1 a e.
  (* = c_for (fun x : fin (dim2nat (dstr n "n")) => c_asgn (aidx 1 x, e_idx 0 x)) *)
  Compute CG a e eta.
  (* 
     for (int i0 = 0; i0 < n; i0 += 1) {
         v1[i0] = v0[i0];
     }
   *)

  (* 证明 e 的语义是 v1 *)
  Goal (eeval e eta) = v1.
  Proof.
    (* simpl.                    (* 展开太多了  *) *)
    clear.
    unfold dn,dim2nat in *. cbv in _v1,_v2,e,eta.
    unfold e, eta. unfold eeval.
    unfold env_get, lmap_geto, find, fst, osnd.
    destruct (1=?0)%nat eqn:E1; try easy.
    destruct (0=?0)%nat eqn:E2; try easy.
    unfold snd. rewrite item2value_item_real. reflexivity.
  Qed.
End array_copy.


Section Vmake.
  Definition Vmake {d} {n} (f:nat->exp d) : exp (dary n d) := e_mkv f.
  
End Vmake.

Section Vnth.
  Definition Vnth {d} {n} (v:exp (dary n d)) (fi:fin (dim2nat n)) : exp d :=
    e_nth v fi.
  
  Definition Vnth_CG (d:data) (n:nat) (fi:fin n) :=
    let dn : dim := dstr n "n" in
    let v := env_new empty_env (dary dn d) in
    let x := env_new &v d in
    CG (d:=d) $x (Vnth (n:=n) $v fi) &x.

  Section test.
    Variable n : nat.
    Compute Vnth_CG dnum n (n2f 4).
    (* x0 = v0[4]; *)
    
    Variable m : nat.
    Compute Vnth_CG (dary (dstr m "m") dnum) n (n2f 4).
    (* for (int i0 = 0; i0 < m; i0 += 1) {
           v1[i0] = m0[4][i0];
       } *)
    
    Variable s : nat.
    Compute Vnth_CG (dary (dstr s "s") (dary (dstr m "m") dnum)) n (n2f 4).
  (* for (int i0 = 0; i0 < s; i0 += 1) {
         for (int i1 = 0; i1 < m; i1 += 1) {
             m1[i0][i1] = m0[4][i0][i1];
         }
     } *)
  End test.
End Vnth.

Section Mnth.
  Definition Mnth {d} {r c:dim} (v:exp (dmat r c d)) (i:fin (dim2nat r))
    (j:fin (dim2nat c)) : exp d := Vnth (Vnth v i) j.

  Definition Mnth_CG (d:data) (r c:nat) (fi:fin r) (fj:fin c) :=
    let dr : dim := dstr r "r" in
    let dc : dim := dstr c "c" in
    let m := env_new empty_env (dmat dr dc d) in
    let x := env_new &m d in
    CG (d:=d) $x (Mnth (r:=dr)(c:=dc) (e_var ID(m)) fi fj) &x.
  
  Section test.
    Variable r c : nat.
    Compute Mnth_CG dnum r c (n2f 3) (n2f 4).
    (* x0 = m0[3][4]; *)
  End test.
End Mnth.

Section Mmake.
  Definition Mmake{d} {r c} (f:nat->nat->exp d) : exp (dmat r c d) :=
    e_mkv (fun i => Vmake (f i)).
End Mmake.

Section Mtrans.
  Definition Mtrans {d} {r c} (m:exp (dmat r c d)) : exp (dmat c r d) := e_trans m.

  Definition Mtrans_CG (d:data) (r c:nat) :=
    let dr : dim := dstr r "r" in
    let dc : dim := dstr c "c" in
    let m1 := env_new empty_env (dmat dr dc d) in
    let m2 := env_new &m1 (dmat dc dr d) in
    (* CG0 $m2 (Mtrans (d:=d) (r:=dr) (c:=dc) $m1). *)
    CG $m2 (Mtrans (d:=d) (r:=dr) (c:=dc) $m1) &m2.

  Section test.
    Variable r c : nat.
    Compute Mtrans_CG dnum r c.
  (* 
	for (int i0 = 0; i0 < r; i0 += 1) {
	  for (int i1 = 0; i1 < c; i1 += 1) {
		m1[i0][i1] = m0[i1][i0];
	  }
	}
   *)
  End test.
End Mtrans.

Section Vcmul.
  Definition Vcmul {n} (k:exp dnum) (e:exp (dary n dnum)) : exp (dary n dnum) :=
    e_map (fun x => k * x) e.

  Definition Vcmul_CG (n:nat) :=
    let dn : dim := dstr n "n" in
    let k := env_new empty_env dnum in
    let v1 := env_new &k (dary dn dnum) in
    let v2 := env_new &v1 (dary dn dnum) in
    CG $v2 (Vcmul (n:=dn) $k $v1) &v2.
  
  Section test.
    Compute Vcmul_CG 3.
  (* for (int i0 = 0; i0 < n; i0 += 1) {
           v1[i0] = x0 * v0[i0];
       } *)
  End test.
End Vcmul.

Section Vadd.
  Definition Vadd {n} (v0 v1 : exp (dary n dnum)) : exp (dary n dnum) :=
    e_map (fun x => (e_fst x) + (e_snd x)) (e_zip v0 v1).

  (* Vadd is commutative: ϕ(v0+v1) = ϕ(v1+v0)
     给定AST形式的两个表达式v0,v1，验证 v0+v1 和 v1+v0 的语义相等 *)
  Lemma Vadd_comm : forall n (v0 v1 : exp (dary n dnum)),
      exp_semeq2 (Vadd v0 v1) (Vadd v1 v0) [].
  Proof. intros. apply veq_iff_vnth; intros. cbn. ring. Qed.
  
  (* Vadd's semantics: ϕ(v0+v1) = ϕ(v0) + ϕ(v1)
     给定AST形式的两个表达式v0,v1，验证 v0+v1 的语义等于“v0的语义与v1的语义之和” *)
  Lemma Vadd_sem : forall n (v0 v1 : exp (dary n dnum)) (eta:env),
      exp_semeq1 (Vadd v0 v1) eta
        (vadd (Aadd:=Rplus) (eeval v0 eta) (eeval v1 eta)).
  Proof. intros. apply veq_iff_vnth; intros; cbn. rewrite vnth_vadd. ring. Qed.

  (* 不使用 exp_semeq1 函数，更直接的语义验证 *)
  Notation vadd := (vadd (Aadd:=Rplus)).
  Lemma Vadd_sem' : forall n (v0 v1 : exp (dary n dnum)) (eta : env),
      eeval(Vadd v0 v1) eta = vadd (eeval v0 eta) (eeval v1 eta).
  Proof. intros. apply veq_iff_vnth; intros; cbn. rewrite vnth_vadd. ring. Qed.

  (* 上面的证明很简单，检查为什么会这样？ *)
  Section check_Vadd_sem'.
    Variable n : nat.
    Variable v0 v1 : exp (dary n dnum).
    Variable eta : env.
    (* 可以看到，因为eeval函数是可计算的，它几乎被展开成了右面的形式。 *)
    Eval cbn in eeval (Vadd v0 v1) eta.
    (* = vmake (fun i : 'I_n => (eeval v0 eta i + eeval v1 eta i)%R) *)
    
  End check_Vadd_sem'.

  (* Vadd的原始定义 *)
  Definition Vadd_CG : string :=
    let dn : dim := dstr 0 "n" in
    let v0 := env_new empty_env (dary dn dnum) in
    let v1 := env_new &v0 (dary dn dnum) in
    let v2 := env_new &v1 (dary dn dnum) in
    let e := Vadd (n:=dn) $v0 $v1 in
    CG $v2 e &v2.
  Compute Vadd_CG.

  (* 修改dn为常数的版本 *)
  Definition Vadd_CG' : string :=
    let dn : dim := dcnst 5 in
    let v0 := env_new empty_env (dary dn dnum) in
    let v1 := env_new &v0 (dary dn dnum) in
    let v2 := env_new &v1 (dary dn dnum) in
    let e := Vadd (n:=dn) $v0 $v1 in
    CG $v2 e &v2.
  Compute Vadd_CG'.

  (* v2 = (v0 + v1) + v1 的版本 *)
  Definition Vadd_CG'' : string :=
    let dn : dim := dstr 0 "n" in
    let v0 := env_new empty_env (dary dn dnum) in
    let v1 := env_new &v0 (dary dn dnum) in
    let v2 := env_new &v1 (dary dn dnum) in
    let e := Vadd (n:=dn) (Vadd (n:=dn) $v0 $v1) $v1 in
    CG $v2 e &v2.
  Compute Vadd_CG''.
End Vadd.

Section Vsub.
  Definition Vsub {n} (v0 v1 : exp (dary n dnum)) : exp (dary n dnum) :=
    e_map (fun x => (e_fst x) - (e_snd x)) (e_zip v0 v1).

  Definition Vsub_CG : string :=
    let dn : dim := dstr 0 "n" in
    let i0 := env_new empty_env (didx dn) in
    let v0 := env_new &i0 (dary dn dnum) in
    let v1 := env_new &v0 (dary dn dnum) in
    let v2 := env_new &v1 (dary dn dnum) in
    let e := Vsub (n:=dn) $v0 $v1 in
    CG $v2 e &v2.
  Compute Vsub_CG.
End Vsub.

Section Vsum.
  Definition Vsum {n} (e:exp (dary n dnum)) : exp dnum :=
    let e1 := e_reduce (e_op2 Rop2_mul) e e_cnst1 in
    let e1 := e_reduce (e_op2 Rop2_div) e e1 in
    let e1 := e_reduce (e_op2 Rop2_sub) e e1 in
    let e1 := e_reduce (e_op2 Rop2_add) e e1 in
    e1.

  Definition Vsum_CG (n:nat) :=
    let dn : dim := dstr n "n" in
    let eta := empty_env in
    let i0 := env_new eta (didx dn) in
    let i1 := env_new &i0 (didx dn) in
    let i2 := env_new &i1 (didx dn) in
    let v0 := env_new &i2 (dary dn dnum) in
    let x0 := env_new &v0 dnum in
    (* Vsum (n:=dn) $v0. *)
    (* (CG1 $x0 (Vsum (n:=dn) $v0), &x0). *)
    CG $x0 (Vsum (n:=dn) $v0) &x0.

  Section test.
    Variable n : nat.
    Eval cbv in Vsum_CG n.
  (* 
    {
       float x1;
       x1 = 0;
       for (int i0 = 0; i0 < n; i0 += 1) {
           x1 = v0[i0] + x1;
       }
       x0 = x1;
    } *)
  End test.
End Vsum.

Section Vdot.
  Definition Vdot {n} (v0 v1 : exp (dary n dnum)) : exp dnum :=
    e_reduce (e_op2 Rop2_add)
      (e_map (fun x => (e_fst x) * (e_snd x)) (e_zip v0 v1))
      e_cnst0.

  Definition Vdot_CG : string :=
    let dn : dim := dstr 0 "n" in
    let v0 := env_new empty_env (dary dn dnum) in
    let v1 := env_new &v0 (dary dn dnum) in
    let x0 := env_new &v1 dnum in
    CG $x0 (Vdot (n:=dn) $v0 $v1) &x0.
  
  Eval cbv in Vdot_CG.
  (* 
  {
	float v2[n];
	for (int i2 = 0; i2 < n; i2 += 1) {
	  v2[i2] = v0[i2] * v1[i2];
	}
	{
	  float x1;
	  x1 = 0;
	  for (int i2 = 0; i2 < n; i2 += 1) {
		x1 = (v2[i2] + x1);
	  }
	  x0 = x1;
	}
  }
   *)
  
  Definition Vdot_CG' : string :=
    let dn : dim := dstr 0 "n" in
    let eta := empty_env in
    (* let v1 := env_new eta (dary dn dnum) in *)
    let i0 := env_new eta (didx dn) in
    let i1 := env_new &i0 (didx dn) in
    let v1 := env_new &i1 (dary dn dnum) in
    let v2 := env_new &v1 (dary dn dnum) in
    let x0 := env_new &v2 dnum in
    (* (CG1 $x0 (Vdot (n:=dn) $v1 $v2), &x0). *)
    (* (CG $x0 (Vdot (n:=dn) $v1 $v2) &x0, &x0). *)
    (* (CG $x0 (Vdot (n:=dn) $v1 $v2) &x0, &x0, CG1 $x0 (Vdot (n:=dn) $v1 $v2)). *)
    (CG $x0 (Vdot (n:=dn) $v1 $v2) &x0).

  (* Definition Vdot2_CG (n:nat) := *)
  (*   let dr : dim := dstr r "r" in *)
  (*   let dc : dim := dstr c "c" in *)
  (*   let m1 := env_new empty_env (dmat dr dc dnum) in *)
  (*   let v2 := env_new &v1 (dary dn dnum) in *)
  (*   let x0 := env_new &v2 dnum in *)
  (*   CG $x0 (Vdot (n:=dn) $v1 $v2) &x0. *)

  (* Section test. *)
  (*   Variable n : nat. *)
  (*   Eval cbn in Vdot_CG n. *)

End Vdot.

Section Mcmul.
  (* 方式1：使用 Vcmul *)
  Definition Mcmul {r c:dim} (k:exp dnum) (m:exp (dmat r c dnum))
    : exp (dmat r c dnum) := e_map (fun x => Vcmul k x) m.
  (* 方式2：不使用 Vcmul，而是使用更底层的 e_map *)
  Definition Mcmul' {r c:dim} (k:exp dnum) (m:exp (dmat r c dnum))
    : exp (dmat r c dnum) := e_map (fun x => e_map (fun y => k * y) x) m.

  Definition Mcmul_CG (r c:nat) :=
    let dr : dim := dstr r "r" in
    let dc : dim := dstr c "c" in
    let k := env_new empty_env dnum in
    let m1 := env_new &k (dmat dr dc dnum) in
    let m2 := env_new &m1 (dmat dr dc dnum) in
    CG $m2 (Mcmul (r:=dr) (c:=dc) $k $m1) &m2.

  Section test.
    Compute Mcmul_CG.
  (* 
	for (int i0 = 0; i0 < r; i0 += 1) {
	  for (int i1 = 0; i1 < c; i1 += 1) {
		m1[i0][i1] = (x0 * m0[i0][i1]);
	  }
	}
   *)
  End test.
End Mcmul.

Section Madd.
  Definition Madd {r c} (m0 m1 : exp (dmat r c dnum)) : exp (dmat r c dnum) :=
    e_map (fun x => Vadd (e_fst x) (e_snd x)) (e_zip m0 m1).

  Definition Madd_CG (r c : nat) : string :=
    let dim_r : dim := dstr r "r" in
    let dim_c : dim := dstr c "c" in
    let m0 := env_new empty_env (dmat r c dnum) in
    let m1 := env_new &m0 (dmat r c dnum) in
    let m2 := env_new &m1 (dmat r c dnum) in
    CG $m2 (Madd (r:=dim_r) (c:=dim_c) $m0 $m1) &m2.
  
  Compute Madd_CG.
  (* 
  for (int i0 = 0; i0 < r; i0 += 1) {
    for (int i1 = 0; i1 < c; i1 += 1) {
      m2[i0][i1] = (m0[i0][i1] + m1[i0][i1]);
    }
  }  
   *)

  (* 这里说明 map 可以嵌套。但是有很大的优化空间，这也许是GenProg最有价值之处 *)
  Definition Madd_CG' (r c:nat) :=
    let dim_r : dim := dstr r "r" in
    let dim_c : dim := dstr c "c" in
    let m1 := env_new empty_env (dmat r c dnum) in
    let m2 := env_new &m1 (dmat r c dnum) in
    let m3 := env_new &m2 (dmat r c dnum) in
    let Madd := Madd (r:=dim_r)(c:=dim_c) in
    let Mcmul := Mcmul (r:=dim_r)(c:=dim_c) in
    CG $m3
      (Madd
         (Mcmul
            e_cnst1
            (Madd
               (Madd $m1 $m2)
               (Madd $m2 $m1)))
         (Mcmul
            e_cnst1
            (Madd
               (Madd $m1 $m2)
               (Madd $m2 $m1)))
      )
      &m3
  .
  Compute Madd_CG'.
  
End Madd.

(* 这里是不带转置的版本 *)
Section Mmul'.
  (* 实现原理：
   m1[r][s] * m2[s][c]
   1. 转置m2, m2'[c][s] = m2\T。使用 mtrans
   2. m1的一行与 m2' 的每一行做点积。使用 map (vdot ..)
   3. m1的每一行与 m2' 的每一行做点积。使用 map (map (vdot ...) ...)
   *)
  Definition Mmul' {r s c} (m1:exp (dmat r s dnum)) (m2:exp (dmat c s dnum))
    : exp (dmat r c dnum) :=
    e_map (fun row1 => (e_map (fun col2 =>
                                 Vdot row1 col2
                          (* (e_reduce (e_op2 Rop2_add) col2 e_cnst0) *)
                          (* e_cnst1 *)
                          ) m2)) m1.

  Definition Mmul'_CG (r s c t:nat) :=
    let dr : dim := dstr r "r" in
    let ds : dim := dstr s "s" in
    let dc : dim := dstr c "c" in
    let dt : dim := dstr t "t" in
    let m1 := env_new empty_env (dmat dr ds dnum) in
    let m2 := env_new &m1 (dmat dc ds dnum) in
    let m3 := env_new &m2 (dmat dt ds dnum) in
    let m4 := env_new &m3 (dmat dr dt dnum) in
    (* CG $m3 (Mmul' (r:=dr)(s:=ds)(c:=dc) $m1 $m2) &m3. *)
    (* CG1 $m4 (Mmul' (r:=dr)(s:=dc)(c:=dt) (Mmul' (r:=dr)(s:=ds)(c:=dc) $m1 $m2) $m3). *)
    CG $m4 (Mmul' (r:=dr)(s:=dc)(c:=dt) (Mmul' (r:=dr)(s:=ds)(c:=dc) $m1 $m2) $m3) &m4.

  Section test.
    Variable r c s t : nat.
    Eval cbv in Mmul'_CG r s c t.
  End test.
  
  Definition Mmul''_CG (n:nat) :=
    let dn : dim := dstr n "n" in
    let Mmul' := Mmul' (r:=dn)(s:=dn)(c:=dn) in
    let d := dmat dn dn dnum in
    let i0 := env_new empty_env (didx dn) in
    let i1 := env_new &i0 (didx dn) in
    let m1 := env_new &i1 d in
    let m2 := env_new &m1 d in
    let m3 := env_new &m2 d in
    let m4 := env_new &m3 d in
    let m5 := env_new &m4 d in
    (* CG1 $m5 (Mmul' $m1 $m2). *)
    CG $m5 (Mmul' $m1 $m2) &m5.
  (* CG0 $m5 (Mmul' (Mmul' $m1 $m2) $m3). *)
  (* CG $m5 (Mmul' (Mmul' $m1 $m2) $m3) &m5. *)
  (* CG $m5 (Mmul' $m3 (Mmul' $m1 $m2)) &m5. *)
  (* CG $m5 (Mmul' (Mmul' (Mmul' $m1 $m2) $m3) $m4) &m5. *)
  (* CG $m5 (Mmul' (Mmul' $m1 $m2) (Mmul' $m3 $m4)) &m5. *)

  Section test.
    Variable n : nat.
    Eval cbv in Mmul''_CG n.
  End test.

End Mmul'.

Section Mmul.
  (* 实现原理：
   m1[r][s] * m2[s][c]
   1. 转置m2, m2'[c][s] = m2\T。使用 mtrans
   2. m1的一行与 m2' 的每一行做点积。使用 map (vdot ..)
   3. m1的每一行与 m2' 的每一行做点积。使用 map (map (vdot ...) ...)
   *)
  Definition Mmul {r s c} (m0:exp (dmat r s dnum)) (m1:exp (dmat s c dnum))
    : exp (dmat r c dnum) :=
    e_map (fun row1 => (e_map (fun col2 => Vdot row1 col2) (Mtrans m1))) m0.

  Definition Mmul_CG (r s c:nat) :=
    let dr : dim := dstr r "r" in
    let ds : dim := dstr s "s" in
    let dc : dim := dstr c "c" in
    let m0 := env_new empty_env (dmat dr ds dnum) in
    let m1 := env_new &m0 (dmat ds dc dnum) in
    let m2 := env_new &m1 (dmat dr dc dnum) in
    CG $m2 (Mmul (r:=dr)(s:=ds)(c:=dc) $m0 $m1) &m2.

  Eval cbv in Mmul_CG _ _ _.
  (* 
  for (int i0 = 0; i0 < r; i0 += 1) {
	for (int i1 = 0; i1 < c; i1 += 1) {
	  {
		float v3[s];
		for (int i2 = 0; i2 < s; i2 += 1) {
		  v3[i2] = m0[i0][i2] * m1[i2][i1];
		}
		{
		  float x0;
		  x0 = 0;
		  for (int i2 = 0; i2 < s; i2 += 1) {
			x0 = (v3[i2] + x0);
		  }
		  m2[i0][i1] = x0;
		}
	  }
	}
  }
   *)

  Section test.
    Let m00 : exp (dmat 2 3 dnum) :=
          Mmake (fun i j => (e_cnst i) + (e_cnst j)). (* [[0,1,2];[1,2,3]] *)
    Let m01 : exp (dmat 3 2 dnum) :=
          Mmake (fun i j => (e_cnst i) * (e_cnst j)). (* [[0,0];[0,1];[0,2]] *)
    Let m1 : exp (dmat 2 2 dnum) :=
          Mmul m00 m01. (* [[0,5];[0,8]] *)
    
    Let m1_value : mat R 2 2 :=
          f2m
            (fun i j => match i, j with
                        | 0,0=>0 | 0,1=>5 | 1,0=>0 | 1,1=>8 | _,_ => 0 end)%R.
    
    Let m1_spec : exp_semeq1 m1 [] m1_value.
    Proof.
      apply meq_iff_mnth; intros; cbn. unfold m1_value. rewrite mnth_f2m.
      destruct i,j; simpl in *.
      destruct i.
      - repeat (destruct i0; try (cbv; ring); try lia).
      - destruct i; try lia.
        repeat (destruct i0; try (cbv; ring); try lia).
    Qed.
  End test.

End Mmul.


(** mkv的例子，可按索引来构造数组。*)
Section ex_mkv.
  (* 由v1来构造v2，逻辑可以任意定义 *)
  Definition demo_mkv (v1:exp (dary 3 dnum)) : exp (dary 3 dnum) :=
    e_mkv (fun i:fin (dim2nat 3) =>
             match fin2nat i with
             | 0 => Sin (v1.3)
             | 1 => v1.2
             | 2 => v1.3 + v1.1
             | _ => e_cnst (mkRstring 0 "0")
             end).
  
  Definition demo_mkv_CG : string :=
    let v1 := env_new empty_env (dary 3 dnum) in
    let v2 := env_new &v1 (dary 3 dnum) in
    CG $v2 (demo_mkv $v1) &v2.

  Compute demo_mkv_CG.
(* 
v1[0] = sin(v0[2]);
v1[1] = v0[1];
v1[2] = (v0[2] + v0[0]);
 *)
End ex_mkv.

(** 在 Orientaion Representation 中的算法 *)
Section ex_OrienRepr.

  (* 四元数乘法 *)
  Definition qmul (q1 q2:exp (dary 4 dnum)) : exp (dary 4 dnum) :=
    e_mkv
      (fun i =>
         match fin2nat i with
         | 0 => q1.1*q2.1 - q1.2*q2.2 - q1.3*q2.3 - q1.4*q2.4
         | 1 => q1.1*q2.2 + q1.2*q2.1 + q1.3*q2.4 - q1.4*q2.3
         | 2 => q1.1*q2.3 - q1.2*q2.4 + q1.3*q2.1 + q1.4*q2.2
         | 3 => q1.1*q2.4 + q1.2*q2.3 - q1.3*q2.2 + q1.4*q2.1
         | _ => e_cnst (mkRstring 0 "0")
         end).

  Definition qmul_CG : string :=
    let q1 := env_new empty_env dnum in
    let q2 := env_new &q1 dnum in
    let q3 := env_new &q2 dnum in
    CG $q3 (qmul $q1 $q2) &q3.

  Compute qmul_CG.
  (* 
v2[0] = ((((v0[0] * v1[0]) - (v0[1] * v1[1])) - (v0[2] * v1[2])) - (v0[3] * v1[3]));
v2[1] = ((((v0[0] * v1[1]) + (v0[1] * v1[0])) + (v0[2] * v1[3])) - (v0[3] * v1[2]));
v2[2] = ((((v0[0] * v1[2]) - (v0[1] * v1[3])) + (v0[2] * v1[0])) + (v0[3] * v1[1]));
v2[3] = ((((v0[0] * v1[3]) + (v0[1] * v1[2])) - (v0[2] * v1[1])) + (v0[3] * v1[0]));
   *)

  (* 基本旋转矩阵 *)
  Definition Rx_mat (x:exp dnum) : exp (dmat 3 3 dnum) :=
    e_mkm
      (fun i j =>
         match fin2nat i, fin2nat j with
         | 0, 0 => e_cnst1
         | 1, 1 => Cos x
         | 2, 2 => Cos x
         | 1, 2 => - Sin x
         | 2, 1 => Sin x
         | _,_ => e_cnst0 end).
  Definition Ry_mat (x:exp dnum) : exp (dmat 3 3 dnum) :=
    e_mkm
      (fun i j =>
         match fin2nat i, fin2nat j with
         | 0, 0 => Cos x
         | 2, 2 => Cos x
         | 0, 2 => Sin x
         | 2, 0 => - Sin x
         | 1, 1 => e_cnst1
         | _,_ => e_cnst0 end).
  Definition Rz_mat (x:exp dnum) : exp (dmat 3 3 dnum) :=
    e_mkm
      (fun i j =>
         match fin2nat i, fin2nat j with
         | 0, 0 => Cos x
         | 1, 1 => Cos x
         | 1, 0 => Sin x
         | 0, 1 => - Sin x
         | 2, 2 => e_cnst1
         | _,_ => e_cnst0 end).

  Definition Rx_mat_CG : string :=
    let x := env_new empty_env dnum in
    let m := env_new &x (dmat 3 3 dnum) in
    CG $m (Rx_mat $x) &m.
  Compute Rx_mat_CG.

  (* 由欧拉角计算旋转矩阵（在S123方式下）*)
  Definition S123mat (x1 x2 x3:exp dnum) : exp (dmat 3 3 dnum) :=
    e_mkm
      (fun i j =>
         match fin2nat i, fin2nat j with
         | 0, 0 => Cos x2 * Cos x3
         | 0, 1 => Sin x1 * Sin x2 * Cos x3 - Cos x1  *  Sin x3
         | 0, 2 => Cos x1 * Sin x2 * Cos x3 + Sin x1 * Sin x3
         | 1, 0 => Cos x2 * Sin x3
         | 1, 1 => Sin x1 * Sin x2 * Sin x3 + Cos x1 * Cos x3
         | 1, 2 => Cos x1 * Sin x2 * Sin x3 + Cos x3 * Sin x1
         | 2, 0 => - Sin x2
         | 2, 1 => Sin x1 * Cos x2
         | 2, 2 => Cos x1 * Cos x2
         | _, _ => e_cnst0
         end).

  Definition S123mat_CG : string :=
    let x1 := env_new empty_env dnum in
    let x2 := env_new &x1 dnum in
    let x3 := env_new &x2 dnum in
    let m := env_new &x3 (dmat 3 3 dnum) in
    CG $m (S123mat $x1 $x2 $x3) &m.

  Compute S123mat_CG.
  (* 
     m0[0][0] = cos(x1) * cos(x2);
     m0[0][1] = (sin(x0) * sin(x1) * cos(x2) - cos(x0) * sin(x2));
     m0[0][2] = (cos(x0) * sin(x1) * cos(x2) + sin(x0) * sin(x2));
     m0[1][0] = cos(x1) * sin(x2);
     m0[1][1] = (sin(x0) * sin(x1) * sin(x2) + cos(x0) * cos(x2));
     m0[1][2] = (cos(x0) * sin(x1) * sin(x2) + cos(x2) * sin(x0));
     m0[2][0] = -(sin(x1));
     m0[2][1] = sin(x0) * cos(x1);
     m0[2][2] = cos(x0) * cos(x1);
   *)

  (* 验证 S123mat 的语义？ *)
  (* Lemma S123mat_spec : forall x y z, eeval (S123mat x y z) = .. *)

  (* 我们知道 S123 x y z = Rz z * Ry y * Rx x，也就是说 S123mat 是可以通过符号化
     算出来的。这个等式可以在Coq中进行验证，但是在GenProg的环境下，也许并不能得到很好的
     代码。我们来做一个实验。*)
  Definition B123mat_equiv (x1 x2 x3:exp dnum) : exp (dmat 3 3 dnum) :=
    Mmul (Mmul  (Rz_mat x3) (Ry_mat x2)) (Rx_mat x1).
  Definition B123mat_equiv_CG : string :=
    let x1 := env_new empty_env dnum in
    let x2 := env_new &x1 dnum in
    let x3 := env_new &x2 dnum in
    let m := env_new &x3 (dmat 3 3 dnum) in
    CG $m (B123mat_equiv $x1 $x2 $x3) &m.

  Compute B123mat_equiv_CG.
  (* 从结果来看，矩阵乘法中的 mkv算子尚未彻底展开，这是mkv和mkm原语尚未处理妥当。
     不过，从运行效率来看，我们也许要使用一个化简的结果来编程。*)

  (* 由旋转矩阵计算欧拉角（在S123方式下，小机动范围内的算法）*)
  Definition S123_euler_algSmall (m:exp (dmat 3 3 dnum)) : exp (dary 3 dnum) :=
    e_mkv
      (fun i =>
         match fin2nat i with
         | 0 => Atan (- m.2.3 / m.3.3)
         | 1 => Asin (m.1.3)
         | 2 => Atan (- (m.1.2 / m.1.1))
         | _ => e_cnst0
         end).
  Definition S123_euler_algSmall_CG : string :=
    let m := env_new empty_env (dmat 3 3 dnum) in
    let v := env_new &m (dary 3 dnum) in
    CG $v (S123_euler_algSmall $m) &v.
  Compute S123_euler_algSmall_CG.
  (* 
v1[0] = atan(-(m0[1][2]) / m0[2][2]);
v1[1] = asin(m0[0][2]);
v1[2] = atan(-(m0[0][1] / m0[0][0]));
   *)

  (* 由旋转矩阵计算欧拉角（在S123方式下，大机动范围内的算法）*)
  Definition S123_euler_algBig (m:exp (dmat 3 3 dnum)) : exp (dary 3 dnum) :=
    e_mkv
      (fun i =>
         match fin2nat i with
         | 0 => Atan2 (-m.2.3, m.3.3)
         | 1 => Asin (m.1.3)
         | 2 => Atan2 (-m.1.2, m.1.1)
         | _ => e_cnst0
         end).
  Definition S123_euler_algBig_CG : string :=
    let m := env_new empty_env (dmat 3 3 dnum) in
    let v := env_new &m (dary 3 dnum) in
    CG $v (S123_euler_algBig $m) &v.
  Compute S123_euler_algBig_CG.
  (* 
v1[0] = atan2(-(m0[1][2]), m0[2][2]);
v1[1] = asin(m0[0][2]);
v1[2] = atan2(-(m0[0][1]), m0[0][0]);
   *)

  (* 罗德里杰斯公式(Rodrigues' formula)，表示对给定向量 a 绕
     轴角(Axis-Angle)参数(n,theta)旋转后的结果 *)
  Definition rotaa (a:exp (dary 3 dnum)) (theta:exp dnum) (n:exp (dary 3 dnum))
    : exp (dary 3 dnum) :=
    (* 这是对数学公式的直接翻译，并不是最简洁的程序，需要优化 *)
    let v1 := Vcmul (Vdot a n) n in
    let v2 := Vcmul (Cos theta) (Vsub a v1) in
    let v3 := Vcmul (Sin theta) n in
    Vadd (Vadd v1 v2) v3.
  Definition rotaa_CG : string :=
    let a := env_new empty_env (dary 3 dnum) in
    let theta := env_new &a dnum in
    let n := env_new &theta (dary 3 dnum) in
    let a' := env_new &n (dary 3 dnum) in
    CG $a' (rotaa $a $theta $n) &a'.
  Compute rotaa_CG.
(* 从结果来看，生成了需要的代码，但正确性一时难以判断。主要的问题有几处：
     1. 不需要并行的指令。
     2. 这个算法的C代码是低效的。
        应该有更简形式，可以在Coq中证明，并手写exp形式，再代码生成。
        或许这是相比Matlab及Simulink的某个优势？
        (1) Simulink 中存在大量的函数库，也许已经是手写优化过了的。
        (2) 但是这里的方案可以验证优化是正确的。
        (3) 如何自动的优化为一个更简单的形式？这个问题或许值得研究。
 *)
  
End ex_OrienRepr.


(** 分块矩阵，即 split 和 join 的一种应用 *)
Section ex_block.

End ex_block.



(** ** C Function *)

Section cfun.
  (* 
   备注：
   1. C函数的一些特点
      (1) 函数可以没有返回值，也可以返回数值，但不能返回数组。
      (2) 数组的输出放在参数列表。
      (3) 可以同时返回多个数组（我们可以每次返回一个，用多个函数调用来模拟）
   2. 这里的设计
      (1) 返回值分两种类型：数值、数组
      (2) 如果是数值，则用 return 语句；如果是数组，则不做特殊处理
   *)

  (* 返回值类型 *)
  Inductive cfunRet :=
  | cfr_num
  | cfr_none.
  
  (* 一个参数 *)
  Inductive param :=
  | param_mk d (v:value d).

  (* C函数 *)
  Record cfun {d:data} :=
    cfun_mk {
        cfun_name : string;
        cfun_ret : cfunRet; 
        cfun_args : list param;
        cfun_body : exp d
      }.

  (* 由返回值生成字符串 *)
  Definition str_ret (cfr:cfunRet) : string :=
    match cfr with
    | cfr_num => "float"
    | cfr_none => "void"
    end.

  (* 由参数构造环境 *)
  Definition params2env (l:list param) : env :=
    fold_left
      (fun env p =>
         let '(param_mk d v) := p in
         ENV(env_addv env v)) l empty_env.

  (* 由参数生成字符串 *)
  Definition str_params (eta:env) : string :=
    concat "; " (map
                   (fun i => data2strDecl (item2data (snd (snd i))) (fst (snd i)))
                   (rev eta)).

  (* 对cfun的Atrans *)
  Definition cfun_Atrans {d:data} (cf:@cfun d) : comm :=
    let eta : env := params2env (cfun_args (cf)) in
    match cfun_ret cf with
    | cfr_num =>
        (* todo: 需要实现 声明、赋值、返回。 *)
        let _ret := env_new eta dnum in
        let comm0 := Atrans $_ret (cfun_body cf) in
        comm0
    | cfr_none =>
        let _ret := env_new eta d in
        Atrans $_ret (cfun_body cf)
    end.

  (* 对cfun的HItrans *)
  Definition cfun_HItrans {d:data} (cf:@cfun d) : comm :=
    HItrans (cfun_Atrans cf).

  (* 对cfun的代码生成 *)
  Definition cfun_CG {d:data} (cf:@cfun d) : string
    :=
    let s_funName := cfun_name cf in
    let eta : env := params2env (cfun_args (cf)) in
    let s_params := str_params eta in
    let s_retTy := str_ret (cfun_ret cf) in
    let _ret := env_new eta dnum in
    let s_body_core := CG $_ret (cfun_body cf) &_ret in
    let s_body :=
      match cfun_ret cf with
      | cfr_num =>
          let s_var_ret := CGacc (d:=dnum) $_ret &_ret [] in
          "float " ++ s_var_ret ++ ";" ++ strNewline
            ++ s_body_core ++ strNewline
            ++ "return " ++ s_var_ret ++ ";"
      | cfr_none => s_body_core
      end in
    s_retTy ++ " " ++ s_funName ++ "(" ++ s_params ++  ") {" ++ strNewline ++
      s_body ++ strNewline ++
      "}" ++ strNewline.

  (* cfun的语义 *)
  Definition cfun_eval {d} (cf:@cfun d) : value d :=
    let eta : env := params2env (cfun_args (cf)) in
    eeval (cfun_body cf) eta.
  
End cfun.

Section test.
  (* 
     示例：算术表达式
     float arith1 (float x0, float x1, float x2) {
         retrun x0 + x1 + sin(x2)
     } *)
  Variable x y z : R.
  Let cfun1 : cfun :=
        cfun_mk
          dnum
          "arith1"
          cfr_num
          [param_mk dnum x;
           param_mk dnum y;
           param_mk dnum z]
          ((e_var 0) + (e_var 1) + Sin (e_var 2)).

  Compute cfun_CG cfun1.
  (* 
     float arith1(float x0; float x1; float x2) {
        float x3;
        x3 = x0 + x1 + sin(x2);
        return x3;
     }
 *)

  Let cfun1_spec : cfun_eval cfun1 = (x + y + sin(z))%R.
  Proof. cbn. reflexivity. Qed.
  
End test.

Section test.
  (* 
     示例：数组的数乘运算
     void cmult(float x0, const float v0[], int n, float v1[]) {
       for (int i0 = 0; i0 < n; i0++) {
           v1[i] = x0 * v0[i];
        }
     }    
   *)
  Variable x0 : R.
  Variable n0 : nat.
  Let n : dim := dstr n0 "n".
  Variable v0 v1 : vec R n0.
  Let data_arr : data := dary n dnum.
  Let cfun1 : cfun :=
        cfun_mk
          data_arr
          "cmult"
          cfr_none
          [param_mk dnum x0;
           param_mk data_arr v0;
           param_mk data_arr v1 ]
          (Vcmul (e_var 0) (e_var 1)).

  Compute cfun_Atrans cfun1.
  Compute cfun_HItrans cfun1.
  Compute cfun_CG cfun1.
  (* 
     void cmult(float x0; float v0[n]; float v1[n]) {
       for (int i0 = 0; i0 < n; i0 += 1) {
         v1[i0] = x0 * v0[i0];
       }
     }
   *)

  Let cfun1_spec : cfun_eval cfun1 = vscal (Amul:=Rmult) x0 v0.
  Proof.
    cbn. apply veq_iff_vnth; intros. unfold vmake. rewrite vnth_vscal. f_equal.
    (* 无法化简  (n0 =? n0) && true && true  *)
    Fail rewrite Nat.eqb_refl.
    (* 因依赖类型的复杂性，我暂时不知如何证明 *)
  Abort.
  
End test.

