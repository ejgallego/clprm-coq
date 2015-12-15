(******************************************************************************)
(* Coq files for the paper:                                                   *)
(*                                                                            *)
(* Constraint Logic Programing with a Relational Machine                      *)
(* Emilio J. Gallego Arias, James Lipton, and Julio Mariño                    *)
(*                                                                            *)
(* Copyright (C) 2015, Emilio J. Gallego Arias                                *)
(*                                                                            *)
(* This program is free software: you can redistribute it and/or modify       *)
(* it under the terms of the GNU General Public License as published by       *)
(* the Free Software Foundation, either version 3 of the License, or          *)
(* (at your option) any later version.                                        *)
(*                                                                            *)
(* This program is distributed in the hope that it will be useful,            *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of             *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the              *)
(* GNU General Public License for more details.                               *)
(*                                                                            *)
(* You should have received a copy of the GNU General Public License          *)
(* along with this program.  If not, see <http://www.gnu.org/licenses/>.      *)
(******************************************************************************)

(******************************************************************************)
(* We formalize the system in Emilio's thesis and its weak normal form        *)
(* property                                                                   *)
(*                                                                            *)
(* Our main theorem is:                                                       *)
(*                                                                            *)
(*  Lemma NF : ∀ (r : R_State), started_from_base r ->                        *)
(*                (~ (exists r', (R: r ----> r')) <-> is_in_NF r).            *)
(*                                                                            *)
(* Which states that the the $R$ transition system can only perform a         *)
(* transition iff the state has not reached a normal form.                    *)
(*                                                                            *)
(* The started_from_base predicate (weakly) characterizes the image of the    *)
(* relational translation function.                                           *)
(*                                                                            *)
(* The is_in_NF predicate defines our notion of normal form:                  *)
(*                                                                            *)
(* - `fail       is in NF.                                                    *)
(* - `base Box`  is in NF.                                                    *)
(* - `par s1 s2` is in NF if s1 is in NF.                                     *)
(* - `sub s`     is in NF if s  is in NF and s not fail or box.               *)
(*                                                                            *)
(*    This last condition is what makes this form of normal form              *)
(*    weak, as we consider states (sub π₁ (sub π₂...(sub πₙ s))) to be in NF. *)
(*                                                                            *)
(* A stronger system will be found in the nf_strong.v file.                   *)
(*                                                                            *)
(* For the current version of our theorem we assume:                          *)
(*                                                                            *)
(* A type of formulas:                                                        *)
(*                                                                            *)
(*   form : Prop                                                              *)
(*   and  : form -> form -> form                                              *)
(*   tform : form                                                             *)
(*                                                                            *)
(* A boolean satisfiability relation:                                         *)
(*                                                                            *)
(*   is_sat   : form -> Prop                                                  *)
(*   is_unsat : form -> Prop                                                  *)
(*   sat_em   : forall p : form, is_sat p \/ is_unsat p                       *)
(*                                                                            *)
(* A type of predicate symbols, and their associated permutations             *)
(* and definitions coming from the translation (for defined                   *)
(* predicates).                                                               *)
(*                                                                            *)
(*   p_symbol : Set                                                           *)
(*   p_perm : p_symbol -> perm                                                *)
(*   p_rdef : p_symbol -> R_State                                             *)
(*                                                                            *)
(* The formula transformers from the paper:                                   *)
(*                                                                            *)
(*   Δ : nat -> perm -> form -> form                                          *)
(*   ν : nat -> perm -> form -> form -> form                                  *)
(*                                                                            *)
(* We also prove the relational and logical system to be in simulation, this  *)
(* proof also requires the translations of symbols to respect the iso R.      *)
(*                                                                            *)
(* R_def_iso : forall (re : res_elem) (d : is_def re),                        *)
(*             R (get_def d) = get_rdef d                                     *)
(*                                                                            *)
(* Rinv_def_iso : forall (re : res_elem) (d : is_def re),                     *)
(*                Rinv (get_rdef d) = get_def d                               *)
(*                                                                            *)
(******************************************************************************)

(* We have nothing specific of ssr here, so disabling for now. *)
(* Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq. *)
Notation erefl := eq_refl.

Require Import Vector.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variable p_symbol : Set.
Definition perm := list nat.

(* Logical constants *)
Variable form  : Prop.
Variable tform : form.
Variable and   : form -> form -> form.
(* Variable ex    : fo  -> form -> form. *)

(* Resolvents *)
(* Inductive res_kind := CS | Pred. *)

(* Inductive res_elem : res_kind -> Set := *)
(* | Res_Def   : p_symbol -> perm -> res_elem Pred *)
(* | Res_Const : form     -> perm -> res_elem CS *)
(* . *)

Inductive res_elem : Set :=
| Res_Def : p_symbol -> perm -> res_elem
| Res_CS  : form  -> perm -> res_elem
.

Definition get_cs (re : res_elem) :=
  match re with
    | Res_Def _ _ => tform
    | Res_CS f _  => f
  end.

(* Definition get_cs (re : res_elem CS) := *)
(*   match re return (match re with *)
(*                      | Res_Def   _ _ => True *)
(*                      | Res_Const _ _ => form *)
(*                    end) with *)
(*     | Res_Def _ _   => I *)
(*     | Res_Const f _ => f *)
(*   end. *)

(* Inductive is_def : res_elem Pred -> Prop := *)
(*   re_def : forall s p, is_def (Res_Def s p). *)

(* Inductive is_constr : res_elem CS -> Prop := *)
(*   re_constr : forall f p, is_constr (Res_Const f p). *)

Inductive is_def : res_elem -> Set :=
  re_def : forall s p, is_def (Res_Def s p).

Inductive is_constr : res_elem -> Set :=
  re_constr : forall f p, is_constr (Res_CS f p).

(* FIXME *)
Variable is_sat : form -> Prop.
Variable is_unsat : form -> Prop.

(* We need to assume decidability of constraint solving *)
Variable sat_em : forall p, is_sat p \/ is_unsat p.

(* Definition res n := t (forall k, res_elem k) n. *)
Definition res n := t res_elem n.

Definition r_nil := nil res_elem.

Inductive CR_State :=
| CR_fail : CR_State
(*   *)
| CR_base : forall n, nat ->         res n -> form -> CR_State
| CR_sel  : forall n, nat -> perm -> res n -> form -> CR_State -> CR_State
| CR_sub  : forall n, nat -> perm -> res n -> form -> CR_State -> CR_State
| CR_par  : CR_State -> CR_State -> CR_State
.

Hint Constructors CR_State.

Inductive R_State :=
| R_fail  : R_State
| R_base  : forall n, nat ->         res n -> form ->  R_State
| R_sel   : forall n, nat -> perm -> res n -> form ->  R_State ->  R_State
| R_sub   : forall n, nat -> perm -> res n -> form ->  R_State ->  R_State
| R_par   : R_State -> R_State -> R_State
.

Hint Constructors R_State.


Fixpoint R (s : CR_State) : R_State :=
  match s with
    | CR_fail              => R_fail
    | CR_base m n r f      => R_base n r f
    | CR_sel  m n p r f s  => R_sel  n p r f (R s)
    | CR_sub  m n p r f s  => R_sub  n p r f (R s)
    | CR_par s1 s2         => R_par (R s1) (R s2)
  end.

Fixpoint Rinv (r : R_State) : CR_State :=
  match r with
    | R_fail              => CR_fail
    | R_base m n r f      => CR_base n r f
    | R_sel  m n p r f s  => CR_sel  n p r f (Rinv s)
    | R_sub  m n p r f s  => CR_sub  n p r f (Rinv s)
    | R_par r1 r2         => CR_par (Rinv r1) (Rinv r2)
  end.

Lemma R_iso1 : forall r, R (Rinv r) = r.
Proof.
  induction r; simpl; auto.
  - rewrite IHr; reflexivity.
  - rewrite IHr; reflexivity.
  - rewrite IHr1;
    rewrite IHr2;
    reflexivity.
Qed.

Lemma R_iso2 : forall s, R (Rinv s) = s.
  induction s; simpl; auto.

  - rewrite IHs; reflexivity.
  - rewrite IHs; reflexivity.
  - rewrite IHs1;
    rewrite IHs2;
    reflexivity.
Qed.

Variable p_def  : p_symbol -> CR_State.
Variable p_perm : p_symbol -> perm.

Definition get_def (re : res_elem) (p : is_def re) : CR_State :=
  match p with
    | re_def p _ => p_def p
  end.

Variable p_rdef : p_symbol -> R_State.

Definition get_rdef (re : res_elem) (p : is_def re) : R_State :=
  match p with
    | re_def p _ => p_rdef p
  end.

Definition get_perm (re : res_elem) (p : is_def re) : perm :=
  match p with
    | re_def p _ => p_perm p
  end.

Variable Δ : nat -> perm -> form -> form.
Variable ν : nat -> perm -> form -> form -> form.

Reserved Notation "'CR:' t1 ----> t2"           (at level 8, t1, t2 at level 15).

(* Next section, transition systems. *)
Inductive CR_Trans : CR_State -> CR_State -> Prop :=
| crt_constraint   : forall m n (p : res (S m) ) φ,
                       is_constr (hd p) ->
                       is_sat (and (get_cs (hd p)) φ) ->
                       CR:
                         CR_base n p φ ---->
                         CR_base n (tl p) (and (get_cs (hd p)) φ)

| crt_constraint_f : forall m n (p : res (S m) ) φ,
                       is_constr (hd p) ->
                       is_unsat (and (get_cs (hd p)) φ) ->
                       CR:
                         CR_base n p φ ---->
                         CR_fail

| crt_call         : forall m n (p : res (S m)) φ (d : is_def (hd p)),
                       CR:
                         CR_base n p φ ---->
                         CR_sel n (get_perm d) (tl p) φ (get_def d)

| crt_select_1         : forall m n π (p : res m) φ m' h (q : res m') ψ,
                       CR:
                         CR_sel n π p φ (CR_base h q ψ) ---->
                         CR_sub n π p φ (CR_base h q (Δ h π ψ))

| crt_select           : forall m n π (p : res m) φ m' h (q : res m') ψ s,
                       CR:
                         CR_sel n π p φ (CR_par (CR_base h q ψ) s) ---->
                         CR_par (CR_sub n π p φ (CR_base h q (Δ h π ψ)))
                                (CR_sel n π p φ s)

| crt_ret          : forall m n π (p : res m) φ h ψ,
                       CR:
                         CR_sub n π p φ (CR_base h r_nil ψ) ---->
                         CR_base n p (ν h π φ ψ)

| crt_ret_fail     : forall m n π (p : res m) φ,
                       CR:
                         CR_sub n π p φ (CR_fail) ----> CR_fail

| crt_sub          : forall m n π (p : res m) φ s s',
                       (* Extra conditions in the paper are not needed, they are implied by the existance of the transition *)
                       CR: s ----> s' ->
                       CR:
                         CR_sub n π p φ s ---->
                         CR_sub n π p φ s'

| crt_backtrack    : forall s,
                       CR:
                         CR_par CR_fail s ---->
                         s

| crt_seq          : forall s s' t,
                       CR: s ----> s' ->
                       CR:
                         CR_par s  t ---->
                         CR_par s' t

 where "'CR:' t1 ----> t2" := (CR_Trans t1 t2).

Reserved Notation "'R:' t1 ----> t2"           (at level 8, t1, t2 at level 15).

(* The relational tran *)
Inductive R_Trans : R_State -> R_State -> Prop :=
| rt_constraint   : forall m n (p : res (S m) ) φ,
                       is_constr (hd p) ->
                       is_sat (and (get_cs (hd p)) φ) ->
                       R:
                         R_base n p φ ---->
                         R_base n (tl p) (and (get_cs (hd p)) φ)

| rt_constraint_f : forall m n (p : res (S m) ) φ,
                       is_constr (hd p) ->
                       is_unsat (and (get_cs (hd p)) φ) ->
                       R:
                         R_base n p φ ---->
                         R_fail

| rt_call         : forall m n (p : res (S m)) φ (d : is_def (hd p)),
                       R:
                         R_base n p φ ---->
                         R_sel n (get_perm d) (tl p) φ (get_rdef d)

| rt_select_1         : forall m n π (p : res m) φ m' h (q : res m') ψ,
                       R:
                         R_sel n π p φ (R_base h q ψ) ---->
                         R_sub n π p φ (R_base h q (Δ h π ψ))

| rt_select           : forall m n π (p : res m) φ m' h (q : res m') ψ s,
                       R:
                         R_sel n π p φ (R_par (R_base h q ψ) s) ---->
                         R_par (R_sub n π p φ (R_base h q (Δ h π ψ)))
                                (R_sel n π p φ s)

| rt_ret          : forall m n π (p : res m) φ h ψ,
                       R:
                         R_sub n π p φ (R_base h r_nil ψ) ---->
                         R_base n p (ν h π φ ψ)

| rt_ret_fail     : forall m n π (p : res m) φ,
                       R:
                         R_sub n π p φ (R_fail) ----> R_fail

(* This is to avoid problems with the old notion of NF *)
(* | rt_par          : forall m n π (p : res m) φ s1 s2, *)
(*                        R: *)
(*                          R_sub n π p φ (R_par s1 s2) ----> *)
(*                          R_par (R_sub n π p φ s1) *)
(*                                (R_sub n π p φ s2) *)

| rt_sub          : forall m n π (p : res m) φ s s',
                       (* Extra conditions in the paper are not needed, they are implied by the existance of the transition *)
                       R: s ----> s' ->
                       R:
                         R_sub n π p φ s ---->
                         R_sub n π p φ s'

| rt_backtrack    : forall s,
                       R:
                         R_par R_fail s ---->
                         s

| rt_seq          : forall s s' t,
                       R: s ----> s' ->
                       R:
                         R_par s  t ---->
                         R_par s' t

 where "'R:' t1 ----> t2" := (R_Trans t1 t2).

Hint Constructors R_Trans.

(* We assume, for now, that the translation of a predicate is in the
relation. *)

Lemma R_def : forall re (d : is_def re), R (get_def d) = get_rdef d.
admit.
Qed.

Lemma Rinv_def : forall re (d : is_def re), Rinv (get_rdef d) = get_def d.
admit.
Qed.

Lemma sim_R_CR : forall s s' r, r = R s -> (CR: s ----> s') ->
                                exists r', (R: r ----> r') /\ r' = R s'.
Proof.
  intros s s' r eqH Tr.

  generalize dependent r.
  induction Tr; intros; simpl in eqH; subst.

  - eexists;split.
    + constructor; auto.
    + simpl; auto.

  - eexists;split.
    + apply rt_constraint_f ; auto.
    + auto.

  - eexists;split.
    + apply rt_call.
    + simpl. rewrite R_def. eauto.

  - eexists;split.
    + apply rt_select_1.
    + auto.

  - eexists;split.
    + apply rt_select.
    + auto.

  - eexists;split.
    + apply rt_ret.
    + auto.

  - eexists;split.
    + apply rt_ret_fail.
    + auto.

  - specialize (IHTr (R s) erefl).
    destruct IHTr as [r' [TrIH EqIH]].
    eexists; split.
    + eapply rt_sub; eauto.
    + rewrite EqIH; auto.

  - eexists; split.
    + apply rt_backtrack.
    + auto.

  - specialize (IHTr (R s) erefl).
    destruct IHTr as [r' [TrIH EqIH]].
    eexists; split.
    + eapply rt_seq; eauto.
    + rewrite EqIH; auto.
Qed.

Print Assumptions sim_R_CR.

Lemma sim_CR_R : forall r r' s, s = Rinv r -> (R: r ----> r') ->
                                exists s', (CR: s ----> s') /\ s' = Rinv r'.
Proof.
  intros r r' s eqH Tr.

  generalize dependent s.
  induction Tr; intros; simpl in eqH; subst.

  - eexists;split.
    + constructor; auto.
    + simpl; auto.

  - eexists;split.
    + apply crt_constraint_f ; auto.
    + auto.

  - eexists;split.
    + apply crt_call.
    + simpl. rewrite Rinv_def. eauto.

  - eexists;split.
    + apply crt_select_1.
    + auto.

  - eexists;split.
    + apply crt_select.
    + auto.

  - eexists;split.
    + apply crt_ret.
    + auto.

  - eexists;split.
    + apply crt_ret_fail.
    + auto.

  (* Needed for the other rule *)
  (* - admit. *)

  - specialize (IHTr (Rinv s) erefl).
    destruct IHTr as [r' [TrIH EqIH]].
    eexists; split.
    + eapply crt_sub; eauto.
    + rewrite EqIH; auto.

  - eexists; split.
    + apply crt_backtrack.
    + auto.

  - specialize (IHTr (Rinv s) erefl).
    destruct IHTr as [r' [TrIH EqIH]].
    eexists; split.
    + eapply crt_seq; eauto.
    + rewrite EqIH; auto.
Qed.

Print Assumptions sim_CR_R.

(********************************************************************)
(* Caracterizations of normal forms.                                *)


(* Hack *)
Lemma res_elem_em : forall p, is_constr p + is_def p.
Proof.
  destruct p.
  - right. constructor.
  - left.  constructor.
Qed.

Definition is_fail (r : R_State) :=
  match r with
    | R_fail            => True
    | _                 => False
  end.

Definition is_box (r : R_State) :=
  match r with
    (* | R_fail            => True *)
    | R_base _ _ p _    => match p with
                             | nil => True
                             | _   => False
                           end
    | _ => False
  end.

(* Desired definiton *)
(* Fixpoint is_in_NF (r : R_State) := *)
(*   match r with *)
(*     | R_fail            => True *)
(*     | R_base _ _ _ _    => is_box_fail r *)
(*     | R_sel _ _ _ _ _ _ => False *)
(*     | R_sub _ _ _ _ _ _ => False *)
(*     | R_par R_fail s2   => False *)
(*     | R_par s1 s2       => is_box_fail s1 *)
(*   end. *)

(* Actual NF of the system in the paper:

   The (minor) problem here is that we have sub (sub states)

*)

Fixpoint is_in_NF (r : R_State) :=
  match r with
    | R_fail            => True
    | R_base _ _ _ _    => is_box r
    | R_sel _ _ _ _ _ _ => False
    | R_sub _ _ _ _ _ s => not (is_fail s) /\ not (is_box s) /\
                           is_in_NF s
    | R_par R_fail s2   => False
    | R_par s1 s2       => is_in_NF s1
  end.

Hint Unfold is_box.
Hint Unfold is_in_NF.

(* Transitive closure of R_Trans *)
Inductive R_Trans_Star : R_State -> R_State -> Prop :=
| R_One  : forall s r, R: s ----> r -> R_Trans_Star s r
| R_Next : forall s r t,
             R_Trans_Star s r ->
             R: r ----> t     ->
                R_Trans_Star s t
.

(* These are the arguments to select we need this for the NF proof. *)
Fixpoint is_par_base (r : R_State) :=
  match r with
    | R_base _ _ _ _            => True
    | R_par (R_base _ _ _ _) s2 => is_par_base s2
    | _                         => False
  end.

(* We also need to postulate what the translation outputs *)
Lemma rdef_wf : forall re (d : is_def re), is_par_base (get_rdef d).
Proof.
  (* From the properties of the translation *)
  admit.
Qed.

(* Skeleton for started from base states *)
Fixpoint started_from_base (r : R_State) :=
  match r with
    | R_fail            => True
    | R_base _ _ _ _    => True
    | R_sel _ _ _ _ _ s => is_par_base s
    | R_sub _ _ _ _ _ s => started_from_base s
    | R_par s1 s2       => started_from_base s1 /\
                           started_from_base s2
  end.
Hint Unfold started_from_base.

Lemma sfb_trans : forall r r',
                    started_from_base r ->
                    R: r ----> r' ->
                       started_from_base r'.
Proof.
  intros.

  induction H0; simpl in *; intuition.
  apply rdef_wf.
Qed.

Lemma start_characterization :
  forall m n (p : res m) φ s,
    R_Trans_Star (R_base n p φ) s ->
    started_from_base s.
Proof.

  intros.
  remember (R_base n p φ) as Hn.
  generalize dependent φ.
  generalize dependent p.
  generalize dependent n.
  generalize dependent m.

  induction H; intros; subst.

  - inversion H; auto; simpl.
    apply rdef_wf.

  - inversion H0; subst; simpl in *; intuition.
    * apply rdef_wf.
    * eauto.
    * eauto using sfb_trans.
    * eapply IHR_Trans_Star; eauto.
    * eapply sfb_trans; eauto;
      eapply IHR_Trans_Star; eauto.
    * eapply IHR_Trans_Star; eauto.
Qed.

Lemma R_base_stuck :
  forall n φ,
    (exists s,
      R: (R_base n (nil res_elem) φ) ----> s) -> False.
Proof.
  intros n φ.
  intros [w P].
  inversion P.
Qed.

Hint Resolve R_base_stuck.

(* A base state with one resolvent can always progress  *)
Lemma R_base_progress : forall m n h p φ, exists s,
                        R: R_base n (cons res_elem h m p) φ ---->
                           s.
Proof.
  intros.

  destruct (res_elem_em h).
  - destruct (sat_em (and (get_cs h) φ)).
    + eexists; apply rt_constraint; auto.
    + eexists; apply rt_constraint_f; auto.
  - exists (R_sel n (get_perm i) p φ (get_rdef i)).
    apply rt_call.
Qed.

Lemma R_sel_progress : forall m n π (p : res m) φ s,
                         started_from_base (R_sel n π p φ s) ->
                         exists r',
                           R: (R_sel n π p φ s) ----> r'.
Proof.
  intros.

  destruct s; simpl in *; subst; intuition.

  + eexists. apply rt_select_1.
  + destruct s1; simpl in *; eauto; intuition.
Qed.

Lemma sub_exists : forall m n π (p : res m) φ r,
                     (is_fail r \/
                      is_box r  \/
                      (exists r',
                         R: r ----> r')) ->
                     exists r'',
                       R: R_sub n π p φ r ----> r''.
Proof.
  intros.

  destruct H as [F | [B | R]].
  - destruct r; simpl in *; eauto; intuition.
  - destruct r; simpl in *; intuition.
    + destruct r.
      * eauto.
      * pose proof (R_base_progress n1 h r f) as [w P].
        exists (R_sub n π p φ w).
        auto.
  - destruct R as [r' P].
    exists (R_sub n π p φ r').
    auto.
Qed.

Hint Resolve sub_exists.

Lemma par_exists : forall r1 r2,
                     (exists r', R: r1 ----> r') \/
                     r1 = R_fail ->
                     exists r'',
                       R: R_par r1 r2 ----> r''.
Proof.
  intros.

  destruct H.
  - destruct H as [r' P].
    exists (R_par r' r2).
    auto.
  - exists r2.
    subst.
    constructor.
Qed.

Hint Resolve par_exists.

Lemma sub_progress : forall m n π (p : res m) φ s,
                       started_from_base (R_sub n π p φ s) ->
                       is_box s \/ is_fail s \/ ~ is_in_NF s ->
                       exists r',
                         R: (R_sub n π p φ s) ----> r'.
Proof.
  intros.

  apply sub_exists.
  generalize dependent φ.
  generalize dependent p.
  generalize dependent π.
  generalize dependent n.
  generalize dependent m.

  induction s; intros; unfold not in *; simpl in *;
  [ intuition |
    destruct r;
      intuition|..];
  right;right.

  - apply R_base_progress.
  - apply R_sel_progress;
    auto.
  - assert ((~ is_fail s /\ ~ is_box s /\ is_in_NF s -> False));[
    intuition|].
    assert (is_box s \/ is_fail s \/ (is_in_NF s -> False)).
    { induction s; unfold not in *; simpl in *.
      - auto.
      - destruct r0; auto.
      - auto.
      - right; right. auto.
      - right; right. auto.
    }
    eauto.

  (* In the par case, different things may happen *)
  - destruct s1.
    + eauto.
    + destruct r.
      * intuition.
      (* Eauto choose the wrong instantiation here *)
      * apply par_exists; left.
        apply R_base_progress.
    + specialize (IHs1 H0 n0 n1 p0 r f (proj1 H)).
      destruct IHs1 as [F | [F | [w P]]];
        [exfalso;auto|exfalso;auto|eauto].
    + specialize (IHs1 H0 n0 n1 p0 r f (proj1 H)).
      destruct IHs1 as [F | [F | [w P]]];
        [exfalso;auto|exfalso;auto|eauto].
    + specialize (IHs1 H0 m n π p φ (proj1 H)).
      destruct IHs1 as [F | [F | [w P]]]; simpl in *;
        [exfalso;auto|exfalso;auto|eauto].
Qed.

Lemma par_progress : forall s1 s2,
                       not (is_in_NF s1) ->
                       started_from_base (R_par s1 s2) ->
                       exists r',
                         R: R_par s1 s2 ----> r'.
Proof.
  intros.
  apply par_exists.
  generalize dependent s2.

  induction s1; intros; unfold not in *; simpl in *;
  [now right;auto|..]; left.

  + destruct r.
    - intuition.
    - apply R_base_progress.

  + apply R_sel_progress;
    intuition.

  + apply sub_progress;
    intuition.
    destruct s1; simpl in *; intuition.
    - destruct r0; intuition.

  + destruct s1_1; intuition; eauto.
Qed.

Lemma R_NF_p : forall r,
                 started_from_base r ->
                 not (is_in_NF r) -> exists r', R: r ----> r'.
Proof.
  intros.

  induction r; simpl in *.

  - intuition.
  - destruct r.
    + intuition.
    + apply R_base_progress.
  - apply R_sel_progress;
    auto.
  - destruct r0; unfold not in *; simpl in *; intuition.
    apply sub_progress; auto.
    destruct r0; intuition.
  - destruct r1; [eauto|..];
    apply par_progress; auto.
Qed.

Lemma NF_dec : forall r, is_in_NF r \/ not (is_in_NF r).
Proof.
  induction r; simpl in *; eauto.
  + destruct r; auto.
  + destruct r0; intuition.
  + destruct r1; eauto.
Qed.

(* This should be implied by R_NF_p, as is_in_NF is a classical
predicate*)

Lemma R_NF : forall r, started_from_base r ->
                       not (exists r', (R: r ----> r')) ->
                       is_in_NF r.
Proof.

  intros r SF H.

  induction r; simpl in *; auto.
  + destruct r.
    - auto.
    - apply H.
      apply R_base_progress.
  + apply H;
    apply R_sel_progress;
    auto.
  + intuition.
  + destruct r1; simpl in *; intuition.

Qed.

Lemma R_NF_i : forall r,
                 started_from_base r ->
                 is_in_NF r -> not (exists r', (R: r ----> r')).
Proof.
  intros.

  induction r; intro He.

  - inversion He; inversion H1.
  - destruct r; eauto.
  - auto.

  - simpl in H0.
    destruct H0 as [Hnfail [Hnbox Hnf]].
    apply IHr; auto.
    destruct He as [w P].
    inversion P; subst;
    intuition.
    exists s'. auto.

  - destruct r1; try assumption.
    + destruct r.
      * specialize (IHr1 (proj1 H) I).
        destruct He as [w P].
        inversion P; inversion H4.
      * assumption.
    + specialize (IHr1 (proj1 H) H0).
      apply IHr1.
      destruct He as [w P].
      inversion P; eauto.
    + specialize (IHr1 (proj1 H) H0).
      apply IHr1.
      destruct He as [w P].
      inversion P; eauto.
Qed.

Lemma NF : forall r,
             started_from_base r ->
               (~ (exists r', (R: r ----> r')) <-> is_in_NF r).
Proof.
  intros.
  split.
  - apply R_NF; auto.
  - apply R_NF_i; auto.
Qed.

Print Assumptions NF.

