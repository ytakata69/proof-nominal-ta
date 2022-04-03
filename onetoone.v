Require Import Ensembles.
Require Import gset.

(* Axiom of choice *)
Axiom axiom_of_choice :
  forall U : Type,
  exists choice_func : Ensemble U -> U,
  forall S : Ensemble U,
  Inhabited _ S -> In _ S (choice_func S).

Axiom in_ensemble_dec :
  forall U : Type,
  forall S : Ensemble U,
  forall a : U, {In _ S a} + {~ In _ S a}.

Axiom classic : forall P, ~ ~ P -> P.

Section InverseFunctions.

Variables A B : Type.

(* image of a subset S of domain A *)
Inductive Image (f : A -> B) (S : Ensemble A) : Ensemble B :=
  | Image_intro : forall s, In _ S s -> In _ (Image f S) (f s).

(* inverse image of an element b in codomain B *)
Inductive InvImage (f : A -> B) (b : B) : Ensemble A :=
  | InvImage_intro : forall a, f a = b -> In _ (InvImage f b) a.

Variable f : A -> B.

Local Lemma InvImage_elim :
  forall (b : B) (a : A),
    In _ (InvImage f b) a -> f a = b.
Proof.
  intros b a Hin.
  now inversion Hin.
Qed.

Local Lemma InvImage_f_x_is_inhabited :
  forall x : A,
    Inhabited _ (InvImage f (f x)).
Proof.
  intros x.
  apply Inhabited_intro with x.
  now apply InvImage_intro.
Qed.

Local Lemma InvImage_onto_f_is_inhabited :
  IsOnto f ->
  forall b : B, Inhabited _ (InvImage f b).
Proof.
  intros f_is_onto b.
  destruct (f_is_onto b) as [x H].
  apply Inhabited_intro with x.
  now apply InvImage_intro.
Qed.

Lemma injection_has_left_inverse :
  (exists g : B -> A, forall x, g (f x) = x)
  <-> IsOneToOne f.
Proof.
  split.
  - (* -> *)
  intros [g H].
  unfold IsOneToOne.
  intros x y Hfx.
  rewrite <- (H x).
  rewrite <- (H y).
  now rewrite Hfx.
  - (* <- *)
  intros f_is_one_to_one.
  destruct (axiom_of_choice A) as [choice_func Hchoice].
  exists (fun b => choice_func (InvImage f b)).
  intros x.
  apply f_is_one_to_one.
  apply InvImage_elim.
  apply Hchoice.
  apply InvImage_f_x_is_inhabited.
Qed.

Lemma injection_has_partial_inverse :
  IsOneToOne f ->
  exists g : B -> A,
    (forall x, g (f x) = x) /\
    (forall y, In _ (Image f (Full_set A)) y -> f (g y) = y).
Proof.
  intros f_is_one_to_one.
  destruct (axiom_of_choice A) as [choice_func Hchoice].
  exists (fun b => choice_func (InvImage f b)).
  split.
  - (* forall x, g (f x) = x *)
  intros x.
  apply f_is_one_to_one.
  apply InvImage_elim.
  apply Hchoice.
  apply InvImage_f_x_is_inhabited.
  - (* forall y, In _ (Image f (Full_set A)) y -> f (g y) = y *)
  intros y Hy.
  apply InvImage_elim.
  apply Hchoice.
  inversion Hy as [y' Hy' EQy'].
  apply InvImage_f_x_is_inhabited.
Qed.

Lemma surjection_has_right_inverse :
  (exists g : B -> A, forall y, f (g y) = y)
  <-> IsOnto f.
Proof.
  split.
  - (* -> *)
  intros [g H].
  unfold IsOnto.
  intros x.
  exists (g x).
  now rewrite -> (H x).
  - (* <- *)
  intros f_is_onto.
  destruct (axiom_of_choice A) as [choice_func Hchoice].
  exists (fun b => choice_func (InvImage f b)).
  intros y.
  apply InvImage_elim.
  apply Hchoice.
  now apply InvImage_onto_f_is_inhabited.
Qed.

End InverseFunctions.

Section MutualInjections.

Variables A B : Type.
Variable f : A -> B.
Variable g : B -> A.

Inductive Hole : Ensemble A :=
  | hole_O : forall x,
      (forall y, x <> g y) -> In _ Hole x
  | hole_S : forall x,
      In _ Hole x -> In _ Hole (g (f x))
  .

Lemma co_Hole_is_included_by_g_image :
  forall a,
    ~ In _ Hole a -> In _ (Image _ _ g (Full_set B)) a.
Proof.
  intros a Hna.
  apply classic.
  intros Hn.
  apply Hna.
  apply hole_O.
  intros y EQa.
  apply Hn.
  rewrite EQa.
  apply Image_intro.
  apply Full_intro.
Qed.

Hypothesis f_is_one_to_one : IsOneToOne f.
Hypothesis g_is_one_to_one : IsOneToOne g.

Theorem mutual_injections_generate_bijection :
  exists h : A -> B,
    IsOnto h /\ IsOneToOne h.
Proof.
  destruct (injection_has_partial_inverse _ _ g g_is_one_to_one)
    as [ginv [ginv_is_left_inverse ginv_is_right_inverse]].
  exists (fun a => if in_ensemble_dec _ Hole a
          then f a else ginv a).
  split.
  - (* IsOnto h *)
  unfold IsOnto.
  intros z.
  destruct (in_ensemble_dec _ Hole (g z)) as [Hz | Hz].
  + (* Hz: In _ Hole (g z) -> *)
  inversion Hz as [x Hz' EQx | x Hx EQx].
  * now assert (Hz'' := Hz' z).
  * exists x.
  apply g_is_one_to_one in EQx.
  case (in_ensemble_dec _ Hole x).
  -- intros; assumption.
  -- intros Hnx; now apply Hnx in Hx.
  + (* Hz: ~ In _ Hole (g z) -> *)
  exists (g z).
  case (in_ensemble_dec _ Hole (g z)).
  * intros Hz'; now apply Hz in Hz'.
  * intros _; apply ginv_is_left_inverse.

  - (* IsOneToOne h *)
  unfold IsOneToOne.
  intros x y Hhx.
  case_eq (in_ensemble_dec _ Hole x);
  case_eq (in_ensemble_dec _ Hole y);
  intros Hy EQy Hx EQx;
  rewrite EQx in Hhx;
  rewrite EQy in Hhx.
  + try now apply f_is_one_to_one.
  + assert (Hgfx : g (f x) = g (ginv y)).
  { now rewrite Hhx. }
  rewrite (ginv_is_right_inverse _ (co_Hole_is_included_by_g_image _ Hy)) in Hgfx.
  assert (Hy' := hole_S _ Hx).
  rewrite Hgfx in Hy'.
  now apply Hy in Hy'.
  + assert (Hgfy : g (ginv x) = g (f y)).
  { now rewrite Hhx. }
  rewrite (ginv_is_right_inverse _ (co_Hole_is_included_by_g_image _ Hx)) in Hgfy.
  assert (Hx' := hole_S _ Hy).
  rewrite <- Hgfy in Hx'.
  now apply Hx in Hx'.
  + assert (Hgginv : g (ginv x) = g (ginv y)).
  { now rewrite Hhx. }
  rewrite (ginv_is_right_inverse _ (co_Hole_is_included_by_g_image _ Hx)) in Hgginv.
  rewrite (ginv_is_right_inverse _ (co_Hole_is_included_by_g_image _ Hy)) in Hgginv.
  assumption.
Qed.

End MutualInjections.


Section MutualInjectionsOnGsets.

Variables A B : Gset.
Hypothesis A_is_Gset : IsGset A.
Hypothesis B_is_Gset : IsGset B.
Let Ad := domainG A.
Let Bd := domainG B.

Variable f : Ad -> Bd.
Variable g : Bd -> Ad.
Hypothesis f_is_equivariant : IsEquivariant f.
Hypothesis g_is_equivariant : IsEquivariant g.

Let Hole_fg := Hole _ _ f g.

Local Lemma Hole_is_equivariant_forward :
  forall (x : Ad) (pi : G),
    In _ Hole_fg x -> In _ Hole_fg (action x pi).
Proof.
  intros x pi.
  intros Hx.
  induction Hx as [x Hx | x Hx IHHx].
  + apply hole_O.
  intros y Hxpi.
  destruct (group_inverse _ G_is_group pi) as [pinv [Hpinv1 Hpinv2]].
  assert (Hypinv : g (action y pinv) = action (g y) pinv).
  { apply g_is_equivariant. }
  rewrite <- Hxpi in Hypinv.
  rewrite <- (Gset_comp _ _ _ A_is_Gset) in Hypinv.
  rewrite Hpinv2 in Hypinv.
  rewrite (Gset_unit _ _ _ A_is_Gset) in Hypinv.
  symmetry in Hypinv.
  now apply Hx in Hypinv.
  + rewrite <- g_is_equivariant.
  rewrite <- f_is_equivariant.
  now apply hole_S.
Qed.

Lemma Hole_is_equivariant :
  forall (x : Ad) (pi : G),
    In _ Hole_fg x <-> In _ Hole_fg (action x pi).
Proof.
  intros x pi.
  split.
  - (* -> *)
  apply Hole_is_equivariant_forward.
  - (* <- *)
  destruct (group_inverse _ G_is_group pi) as [pinv [Hpinv1 Hpinv2]].
  assert (EQx : x = action (action x pi) pinv).
  { rewrite <- (Gset_comp _ _ _ A_is_Gset).
  rewrite Hpinv2.
  now rewrite (Gset_unit _ _ _ A_is_Gset).
  }
  intros Hxpi.
  rewrite EQx.
  now apply Hole_is_equivariant_forward.
Qed.

Hypothesis f_is_one_to_one : IsOneToOne f.
Hypothesis g_is_one_to_one : IsOneToOne g.

Theorem mutual_equivariant_injections_generate_bijection :
  exists h : Ad -> Bd,
    IsOnto h /\ IsOneToOne h /\ IsEquivariant h.
Proof.
  destruct (injection_has_partial_inverse _ _ g g_is_one_to_one)
    as [ginv [ginv_is_left_inverse ginv_is_right_inverse]].
  exists (fun a => if in_ensemble_dec _ Hole_fg a
          then f a else ginv a).

  split; [| split].
  - (* IsOnto h *)
  unfold IsOnto.
  intros z.
  destruct (in_ensemble_dec _ Hole_fg (g z)) as [Hz | Hz].
  + (* Hz: In _ Hole (g z) -> *)
  inversion Hz as [x Hz' EQx | x Hx EQx].
  * now assert (Hz'' := Hz' z).
  * exists x.
  apply g_is_one_to_one in EQx.
  case (in_ensemble_dec _ Hole_fg x).
  -- intros; assumption.
  -- intros Hnx; now apply Hnx in Hx.
  + (* Hz: ~ In _ Hole (g z) -> *)
  exists (g z).
  case (in_ensemble_dec _ Hole_fg (g z)).
  * intros Hz'; now apply Hz in Hz'.
  * intros _; apply ginv_is_left_inverse.

  - (* IsOneToOne h *)
  unfold IsOneToOne.
  intros x y Hhx.
  case_eq (in_ensemble_dec _ Hole_fg x);
  case_eq (in_ensemble_dec _ Hole_fg y);
  intros Hy EQy Hx EQx;
  rewrite EQx in Hhx;
  rewrite EQy in Hhx.
  + try now apply f_is_one_to_one.
  + assert (Hgfx : g (f x) = g (ginv y)).
  { now rewrite Hhx. }
  rewrite (ginv_is_right_inverse _
    (co_Hole_is_included_by_g_image _ _ f g _ Hy))
    in Hgfx.
  assert (Hy' := hole_S _ _ f g _ Hx).
  rewrite Hgfx in Hy'.
  now apply Hy in Hy'.
  + assert (Hgfy : g (ginv x) = g (f y)).
  { now rewrite Hhx. }
  rewrite (ginv_is_right_inverse _
    (co_Hole_is_included_by_g_image _ _ f g _ Hx))
    in Hgfy.
  assert (Hx' := hole_S _ _ f g _ Hy).
  rewrite <- Hgfy in Hx'.
  now apply Hx in Hx'.
  + assert (Hgginv : g (ginv x) = g (ginv y)).
  { now rewrite Hhx. }
  rewrite (ginv_is_right_inverse _
    (co_Hole_is_included_by_g_image _ _ f g _ Hx))
    in Hgginv.
  rewrite (ginv_is_right_inverse _
    (co_Hole_is_included_by_g_image _ _ f g _ Hy))
    in Hgginv.
  assumption.

  - (* IsEquivariant h *)
  unfold IsEquivariant.
  intros x pi.
  destruct (in_ensemble_dec _ Hole_fg x) as [Hx | Hx];
  destruct (in_ensemble_dec _ Hole_fg (action x pi)) as [Hxpi | Hxpi].
  + apply f_is_equivariant.
  + now apply (Hole_is_equivariant x pi) in Hx.
  + now apply (Hole_is_equivariant x pi) in Hxpi.
  + apply g_is_one_to_one.
  rewrite g_is_equivariant.
  rewrite (ginv_is_right_inverse _
    (co_Hole_is_included_by_g_image _ _ f g _ Hx)).
  rewrite (ginv_is_right_inverse _
    (co_Hole_is_included_by_g_image _ _ f g _ Hxpi)).
  reflexivity.
Qed.

End MutualInjectionsOnGsets.
