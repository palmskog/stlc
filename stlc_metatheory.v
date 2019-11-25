(* generated from: ../tests/test10st.ott *)

Require Import List.  Require Import Arith.  Require Import Bool.
(** syntax *)
Definition termvar := nat.
Lemma eq_termvar: forall (x y : termvar), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Definition typvar := nat.
Lemma eq_typvar: forall (x y : typvar), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.


Inductive 
T : Set := 
   T_var : typvar -> T
 | T_arrow : T -> T -> T
.

Inductive 
t : Set := 
   t_Var : termvar -> t
 | t_Lam : termvar -> t -> t
 | t_App : t -> t -> t
.

Definition
G : Set := list (termvar*T)
.


(** library functions *)
Fixpoint list_mem (A:Set) (eq:forall a b:A,{a=b}+{a<>b}) (x:A) (l:list A) {struct l} : bool :=
  match l with
  | nil => false
  | cons h t => if eq h x then true else list_mem A eq x t
end.
Implicit Arguments list_mem.

Fixpoint list_minus (A:Set) (eq:forall a b:A,{a=b}+{a<>b}) (l1:list A) (l2:list A) {struct l1} : list A :=
  match l1 with
  | nil => nil
  | cons h t => if (list_mem (A:=A) eq h l2) then list_minus A eq t l2 else cons h (list_minus A eq t l2)
end.
Implicit Arguments list_minus.


(** subrules *)
Definition is_v_of_t (t_6:t) : Prop :=
  match t_6 with
  | (t_Var x) => False
  | (t_Lam x t5) => (True)
  | (t_App t5 t') => False
end.


(** free variables *)
Fixpoint fv_t (t_6:t) : list termvar :=
  match t_6 with
  | (t_Var x) => ((cons x nil))
  | (t_Lam x t5) => ((list_minus eq_termvar (fv_t t5) (cons x nil)))
  | (t_App t5 t') => (app (fv_t t5) (fv_t t'))
end.


(** substitutions *)
Fixpoint tsubst_t (t_6:t) (x5:termvar) (t__7:t) {struct t__7} : t :=
  match t__7 with
  | (t_Var x) => (if eq_termvar x x5 then t_6 else (t_Var x))
  | (t_Lam x t5) => t_Lam x (if list_mem eq_termvar x5 (cons x nil) then t5 else (tsubst_t t_6 x5 t5))
  | (t_App t5 t') => t_App (tsubst_t t_6 x5 t5) (tsubst_t t_6 x5 t')
end.


(** definitions *)
(* defns Jtype *)

Inductive
(* defn GtT *)

GtT : G -> t -> T -> Prop :=
 | GtT_value_name : forall G5 x T5,
      (exists G1, exists G2, (( G5  = (app G1 (cons ( x , T5 )  G2 ))) /\ not (In  x  (List.map (fun (h:termvar*T) => match h with (h1,h2) => h1 end) G1))))  ->
     GtT G5 (t_Var x) T5
 | GtT_apply : forall G5 t5 t' T2 T1,
     GtT G5 t5 (T_arrow T1 T2) ->
     GtT G5 t' T1 ->
     GtT G5 (t_App t5 t') T2
 | GtT_lambda : forall G5 x1 t5 T1 T_5,
     GtT  (cons ( x1 , T1 )  G5 )  t5 T_5 ->
     GtT G5 (t_Lam x1 t5) (T_arrow T1 T_5)

.
(* defns Jop *)

Inductive
(* defn reduce *)

reduce : t -> t -> Prop :=
 | ax_app : forall x t12 v2,
     is_v_of_t v2 ->
     reduce (t_App  (t_Lam x t12)  v2)  ( tsubst_t  v2   x   t12  ) 
 | ctx_app_fun : forall t1 t_5 t1',
     reduce t1 t1' ->
     reduce (t_App t1 t_5) (t_App t1' t_5)
 | ctx_app_arg : forall v5 t1 t1',
     is_v_of_t v5 ->
     reduce t1 t1' ->
     reduce (t_App v5 t1) (t_App v5 t1')

.

(* progress *)

Ltac caseEq f :=
  generalize (refl_equal f); pattern f at -1; case f. 

Theorem progress:
  forall (t0:t) (T0:T),
    GtT nil t0 T0 ->
    (is_v_of_t t0) \/ (exists t1, reduce t0 t1).
Proof.
  induction t0; intros T0 Ht.
(* Case Var *) 
  inversion Ht; clear Ht; subst.
  elim H1; clear H1; intros G1 H1.
  elim H1; clear H1; intros G2 H1.
  elim H1; clear H1; intros Ht1 Ht2.
  cut (nil <> G1 ++ (t0, T0) :: G2).
  2: apply app_cons_not_nil.
  intro Hc. rewrite Ht1 in Hc.
  contradiction Hc. trivial.
(* Case Lam *)
  left; red; trivial.
(* Case App *)
  right. inversion Ht; subst.
  elim IHt0_1 with (T0 := T_arrow T1 T0); 
    [ idtac 
    | intro; elim H; clear H; intros t1 H; exists (t_App t1 t0_2); apply ctx_app_fun; trivial
    | trivial ].
  caseEq t0_1; intros x t3; subst.
  (* want functional inversion over Ht0_1 instead of caseEq *)
  inversion H2; subst.
  elim H1; clear H1; intros G1 H1.
  elim H1; clear H1; intros G2 H1.
  elim H1; clear H1; intros Ht1 Ht2.
  cut (nil <> G1 ++ (x, T_arrow T1 T0) :: G2).
  intro Hc. rewrite Ht1 in Hc.
  contradiction Hc. trivial.
  apply app_cons_not_nil.
  (**)
  intros; subst.
  cut (is_v_of_t t0_2 \/ (exists t1 : t, reduce t0_2 t1)); eauto.
  intro. inversion H; clear H.
  generalize H0; clear H0.
  exists (tsubst_t t0_2 x t3).
  apply ax_app. trivial.
  elim H1. intro t1. intro H.
  exists (t_App (t_Lam x t3) t1).
  apply ctx_app_arg; trivial.
  (**)
  intro; subst.
  cut (is_v_of_t t0_2 \/ (exists t1 : t, reduce t0_2 t1)); eauto.
  intro; inversion H; clear H.
  unfold is_v_of_t. intro. contradiction H.
  elim H0; clear H0; intros t1 Ht1.
  exists (t_App (t_App x t3) t1).
  apply ctx_app_arg; trivial.
Qed.
  
