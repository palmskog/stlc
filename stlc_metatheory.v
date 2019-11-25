Require Import List.
Require Import STLC.stlc.
Import ListNotations.

Ltac caseEq f :=
  generalize (refl_equal f); pattern f at -1; case f.

Theorem progress:
  forall (t0:t) (T0:T),
    GtT nil t0 T0 ->
    (is_v_of_t t0 = true) \/ (exists t1, reduce t0 t1).
Proof.
  induction t0; intros T0 Ht.
(* Case Var *) 
  inversion Ht; clear Ht; subst.
  case H1; clear H1; intros G1 H1.
  case H1; clear H1; intros G2 H1.
  case H1; clear H1; intros Ht1 Ht2.
  cut ([] <> G1 ++ (x, T0) :: G2).
  2: apply app_cons_not_nil.
  intro Hc. rewrite Ht1 in Hc.
  contradiction Hc. trivial.
(* Case Lam *)
  left; simpl; trivial.
(* Case App *)
  right. inversion Ht; subst.
  elim IHt0_1 with (T0 := T_arrow T1 T0); 
    [ idtac 
    | intro; elim H; clear H; intros t1 H; exists (t_App t1 t0_2); apply ctx_app_fun; trivial
    | trivial ].
  caseEq t0_1; intros x t3; subst.
  (* want functional inversion over Ht0_1 instead of caseEq *)
  inversion H2; subst.
  case H1; clear H1; intros G1 H1.
  case H1; clear H1; intros G2 H1.
  case H1; clear H1; intros Ht1 Ht2.
  cut ([] <> G1 ++ (x, T_arrow T1 T0) :: G2).
  intro Hc. rewrite Ht1 in Hc.
  contradiction Hc. trivial.
  apply app_cons_not_nil.
  (**)
  intros; subst.
  cut (is_v_of_t t0_2 = true \/ (exists t1 : t, reduce t0_2 t1)); eauto.
  intro. inversion H; clear H.
  generalize H0; clear H0.
  exists (tsubst_t t0_2 x t3).
  apply ax_app. rewrite H1. simpl. trivial.
  case H1. intro t1. intro H.
  exists (t_App (t_Lam x t3) t1).
  apply ctx_app_arg; simpl; trivial.
  (**)
  intro; subst.
  cut (is_v_of_t t0_2 = true \/ (exists t1 : t, reduce t0_2 t1)); eauto.
  simpl; intros; congruence.
Qed.
