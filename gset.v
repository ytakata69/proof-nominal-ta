(* Group G *)

Class Magma := mkMagma {
  carrier : Set;
  op : carrier -> carrier -> carrier;
  unit : carrier;
}.

Record IsGroup (M : Magma) := {
  group_associative :
    forall x y z, op (op x y) z = op x (op y z);
  group_unit_left  : forall x, op unit x = x;
  group_unit_right : forall x, op x unit = x;
  group_inverse :
    forall x, exists y, op y x = unit /\ op x y = unit;
}.

Parameter G : Set.
Parameter comp : G -> G -> G.
Parameter e : G.

Definition GMag := mkMagma G comp e.
Axiom G_is_group : IsGroup GMag.

(* G-set *)

Class SetWithAction (GM : Magma) `(IsGroup GM) := mkSetWithAction {
  domain : Type;
  action : domain -> carrier -> domain;
  orbit x y := exists pi : carrier, action x pi = y;
}.

Record IsSetWithAction (GM : Magma) `(HG : IsGroup GM)
                       (A : SetWithAction GM HG) := {
  Gset_unit : forall x, action x unit = x;
  Gset_comp :
    forall (x : domain) (pi sigma : carrier),
      action x (op pi sigma) = action (action x pi) sigma;
}.

Definition Gset := SetWithAction GMag G_is_group.
Definition mkGset := mkSetWithAction GMag G_is_group.
Definition IsGset := IsSetWithAction GMag G_is_group.
Definition domainG := @domain GMag G_is_group.
Definition actionG := @action GMag G_is_group.

Section GsetPrelude.

Variable A : Gset.
Hypothesis A_is_Gset : IsGset A.

Lemma transpose_inverse :
  forall pi pinv : G,
    comp pinv pi = e -> comp pi pinv = e ->
  forall x y : domainG A,
    action x pinv = y <-> x = action y pi.
Proof.
  intros pi pinv Hinv1 Hinv2 x y.
  split; intro H.
  - (* -> *)
  rewrite <- H.
  rewrite <- (Gset_comp _ _ _ A_is_Gset).
  simpl.
  rewrite Hinv1.
  now rewrite (Gset_unit _ _ _ A_is_Gset).
  - (* <- *)
  rewrite H.
  rewrite <- (Gset_comp _ _ _ A_is_Gset).
  simpl.
  rewrite Hinv2.
  now rewrite (Gset_unit _ _ _ A_is_Gset).
Qed.

Lemma in_the_same_orbit :
  forall y1 y2 : domainG A,
    (exists x, orbit x y1 /\ orbit x y2) <-> orbit y1 y2.
Proof.
  intros y1 y2.
  split.
  - (* -> *)
  unfold orbit.
  intros [x [[p1 H1] [p2 H2]]].
  assert (Hinv := group_inverse _ G_is_group p1).
  destruct Hinv as [p1inv [_ Hp1iv]].
  rewrite<- H1.
  rewrite<- H2.
  exists (comp p1inv p2).
  rewrite   (Gset_comp _ _ _ A_is_Gset).
  rewrite<- (Gset_comp _ _ _ A_is_Gset _ _ p1inv).
  rewrite Hp1iv.
  rewrite   (Gset_unit _ _ _ A_is_Gset).
  reflexivity.
  - (* <- *)
  intros H.
  exists y1.
  split.
  + exists unit.
  rewrite (Gset_unit _ _ _ A_is_Gset).
  reflexivity.
  + assumption.
Qed.

End GsetPrelude.

(* Equivariant functions *)

Section EquivariantFunctions.

Definition IsEquivariant {A B : Gset} (f : domainG A -> domainG B) :=
  forall (x : domainG A) (pi : G),
    f (action x pi) = action (f x) pi.
Definition IsOnto {A B : Type} (f : A -> B) :=
  forall z, exists x, f x = z.
Definition IsOneToOne {A B : Type} (f : A -> B) :=
  forall x y, f x = f y -> x = y.

Variables A B : Gset.
Hypothesis A_is_Gset : IsGset A.
Hypothesis B_is_Gset : IsGset B.

Variable f : domainG A -> domainG B.
Hypothesis f_is_equivariant : IsEquivariant f.

Lemma number_of_orbits_partial :
  forall y1 y2,
    orbit y1 y2 -> orbit (f y1) (f y2).
Proof.
  intros y1 y2.
  unfold orbit.
  intros [pi H].
  exists pi.
  rewrite<- f_is_equivariant.
  rewrite H.
  reflexivity.
Qed.

Section NumberOfOrbits.

Hypothesis f_is_one_to_one : IsOneToOne f.

Lemma number_of_orbits :
  forall y1 y2,
    orbit y1 y2 <-> orbit (f y1) (f y2).
Proof.
  intros y1 y2.
  split.
  - (* -> *)
  apply number_of_orbits_partial.
  - (* <- *)
  unfold orbit.
  intros [pi Hp].
  exists pi.
  apply f_is_one_to_one.
  rewrite f_is_equivariant.
  assumption.
Qed.

End NumberOfOrbits.

Section InverseFunctions.

Hypothesis f_is_one_to_one : IsOneToOne f.
Hypothesis f_is_onto : IsOnto f.

Variable finv : domainG B -> domainG A.
Hypothesis finv_is_inverse :
  forall x, finv (f x) = x.

Lemma f_finv_x_is_x :
  forall x, f (finv x) = x.
Proof.
  intros x.
  destruct (f_is_onto x) as [y Hy].
  rewrite<- Hy.
  rewrite finv_is_inverse.
  reflexivity.
Qed.

Lemma inverse_is_equivariant :
  IsEquivariant finv.
Proof.
  unfold IsEquivariant.
  intros x pi.
  assert (H := f_is_equivariant (finv x) pi).
  rewrite f_finv_x_is_x in H.
  rewrite<- H.
  rewrite finv_is_inverse.
  reflexivity.
Qed.

End InverseFunctions.
End EquivariantFunctions.

(* Compound G-sets *)

Require Import Ensembles.

Section EnsembleIsGset.

Variable A : Gset.
Hypothesis A_is_Gset : IsGset A.
Let Ad := domainG A.

Let EnAd := Ensemble Ad.
Inductive ensembleAct (S : EnAd) (pi : G) : EnAd :=
| mkEnsembleAct :
  forall a : Ad,
  In _ S a -> In _ (ensembleAct S pi) (action a pi).

Let EnsembleA := mkGset EnAd ensembleAct.
Let EAd := domainG EnsembleA.

Local Lemma Ensemble_unit :
  forall S : EAd, action S unit = S.
Proof.
  intros S.
  apply Extensionality_Ensembles.
  split; unfold Included.
  - (* Included _ (ensembleAct S e) S *)
  intros a Ha.
  inversion Ha as [a' Ha' EQa'].
  now rewrite (Gset_unit _ _ _ A_is_Gset).
  - (* Included _ S (ensembleAct S e) *)
  intros a Ha.
  rewrite <- (Gset_unit _ _ _ A_is_Gset).
  now apply mkEnsembleAct.
Qed.

Local Lemma Ensemble_comp :
  forall (S : EAd) (pi sigma : G),
    action S (comp pi sigma) = action (action S pi) sigma.
Proof.
  intros S pi sigma.
  apply Extensionality_Ensembles.
  split; unfold Included; simpl.
  - (* Included _ (action S (comp pi sigma)) (action (action S pi) sigma) *)
  intros a Ha.
  inversion Ha as [a' Ha' EQa'].
  rewrite (Gset_comp _ _ _ A_is_Gset).
  apply mkEnsembleAct.
  now apply mkEnsembleAct.
  - (* Included _ (action (action S pi) sigma) (action S (comp pi sigma)) *)
  intros a Ha.
  inversion Ha as [a' Ha' EQa'].
  inversion Ha' as [a'' Ha'' EQa''].
  rewrite <- (Gset_comp _ _ _ A_is_Gset).
  now apply mkEnsembleAct.
Qed.

Lemma Ensemble_is_Gset : IsGset EnsembleA.
Proof.
  unfold IsGset.
  apply {| Gset_unit := Ensemble_unit; Gset_comp := Ensemble_comp; |}.
Qed.

End EnsembleIsGset.

Section GProductIsGsets.

Definition GProduct (A B : Gset) :=
  mkGset (domainG A * domainG B)
    (fun ab pi => (action (fst ab) pi, action (snd ab) pi)).

Variable X A : Gset.
Hypothesis X_is_Gset : IsGset X.
Hypothesis A_is_Gset : IsGset A.

Let XA := GProduct X A.
Let XAd := domainG XA.

Local Lemma XA_unit :
  forall xa : XAd, action xa unit = xa.
Proof.
  intros xa.
  apply injective_projections.
  - apply (Gset_unit _ _ _ X_is_Gset).
  - apply (Gset_unit _ _ _ A_is_Gset).
Qed.

Local Lemma XA_comp :
  forall (xa : XAd) (pi sigma : G),
    action xa (comp pi sigma) = action (action xa pi) sigma.
Proof.
  intros xa pi sigma.
  apply injective_projections.
  - apply (Gset_comp _ _ _ X_is_Gset).
  - apply (Gset_comp _ _ _ A_is_Gset).
Qed.

Lemma GProduct_is_Gset : IsGset XA.
Proof.
  unfold IsGset.
  apply {| Gset_unit := XA_unit; Gset_comp := XA_comp; |}.
Qed.

End GProductIsGsets.

(* Equivariant subsets *)

Section EquivariantSubsets.

Definition IsEquivariantSubset {U : Gset} (Y : Ensemble (domainG U)) :=
  forall y pi, In _ Y y -> In _ Y (action y pi).

Inductive Product {A B : Type} (S : Ensemble A) (T : Ensemble B)
  : Ensemble (A * B) :=
  | mkProduct : forall (a : A) (b : B),
    In _ S a -> In _ T b -> In _ (Product S T) (a, b).

Variable X A : Gset.
Hypothesis X_is_Gset : IsGset X.
Hypothesis A_is_Gset : IsGset A.
Let Xd := domainG X.
Let Ad := domainG A.

Variable Y : Ensemble Xd.
Variable B : Ensemble Ad.
Hypothesis Y_is_equivariant : IsEquivariantSubset Y.
Hypothesis B_is_equivariant : IsEquivariantSubset B.

Let XA := GProduct X A.

Lemma YB_is_equivariant :
  @IsEquivariantSubset XA (Product Y B).
Proof.
  unfold IsEquivariantSubset.
  intros yb pi Hin.
  inversion Hin as [y b Hy Hb EQyb].
  simpl.
  apply mkProduct; auto.
Qed.

End EquivariantSubsets.

(* Supports *)

Section Support.

Variable D : Gset.
Hypothesis D_is_Gset : IsGset D.
Let Dd := domainG D.

Definition IsSupport {X : Gset}
  (x : domainG X) (C : Ensemble Dd) :=
  forall pi : G,
  (forall c : Dd, In _ C c -> action c pi = c) ->
  action x pi = x.

Definition IsLeastSupport {X : Gset}
  (x : domainG X) (C : Ensemble Dd) :=
  IsSupport x C /\
  forall C' : Ensemble Dd,
    IsSupport x C' -> Included _ C C'.

Variable X : Gset.
Hypothesis X_is_Gset : IsGset X.
Let Xd := domainG X.

Lemma larger_support :
  forall (x : Xd) (C C' : Ensemble Dd),
  IsSupport x C -> Included _ C C' -> IsSupport x C'.
Proof.
  intros x C C' HC HC'.
  unfold IsSupport.
  unfold IsSupport in HC.
  intros pi H'.
  unfold Included in HC'.
  apply (HC pi).
  intros c Hin.
  apply (H' c).
  apply (HC' c).
  assumption.
Qed.

Lemma least_support_is_unique :
  forall (x : Xd) (C C' : Ensemble Dd),
  IsLeastSupport x C /\ IsLeastSupport x C'
  -> C = C'.
Proof.
  unfold IsLeastSupport.
  intros x C C' [[HC HCl] [HC' HC'l]].
  apply Extensionality_Ensembles.
  unfold Same_set.
  split.
  - (* Included _ C C' *)
  now apply HCl.
  - (* Included _ C' C *)
  now apply HC'l.
Qed.

(* Same as [Bojanczyk+ 2014, Lemma 4.9] *)
Lemma action_preserves_support (pi : G) :
  forall (x : Xd) (C : Ensemble Dd),
  IsSupport x C -> IsSupport (action x pi) (ensembleAct _ C pi).
Proof.
  intros x C HC.
  unfold IsSupport.
  unfold IsSupport in HC.
  intros sigma Hc.
  destruct (group_inverse _ G_is_group pi) as [pinv [Hpinv1 Hpinv2]].
  assert (HC' := HC (comp (comp pi sigma) pinv)).
  rewrite (Gset_comp _ _ _ X_is_Gset) in HC'.
  rewrite (Gset_comp _ _ _ X_is_Gset) in HC'.
  apply-> (transpose_inverse _ X_is_Gset _ _ Hpinv1 Hpinv2).
  apply HC'.
  clear HC HC'.
  intros c HCc.
  rewrite (Gset_comp _ _ _ D_is_Gset).
  rewrite (Gset_comp _ _ _ D_is_Gset).
  apply<- (transpose_inverse _ D_is_Gset _ _ Hpinv1 Hpinv2).
  apply Hc.
  now apply mkEnsembleAct.
Qed.

Lemma action_preserves_least_support (pi : G) :
  forall (x : Xd) (C : Ensemble Dd),
  IsLeastSupport x C -> IsLeastSupport (action x pi) (ensembleAct _ C pi).
Proof.
  intros x C HC.
  unfold IsLeastSupport.
  unfold IsLeastSupport in HC.
  destruct HC as [HC HCm].
  split.
  - (* IsSupport *)
  now apply action_preserves_support.
  - (* minimality *)
  unfold Included.
  intros C' HC' d Hd.

  (* HC' : IsSupport x (ensembleAct _ C' pinv) *)
  destruct (group_inverse _ G_is_group pi) as [pinv [Hpinv1 Hpinv2]].
  apply (action_preserves_support pinv (action x pi)) in HC'.
  rewrite <- (Gset_comp _ _ _ X_is_Gset) in HC'.
  rewrite Hpinv2 in HC'.
  rewrite (Gset_unit _ _ _ X_is_Gset) in HC'.

  (* HCm' : Included _ C (ensembleAct _ C' pinv) *)
  assert (HCm' := HCm _ HC').
  unfold Included in HCm'.

  (* Hd': In _ C d' ; Goal: In _ C' (action d' pi) *)
  rewrite <- (Gset_unit _ _ _ D_is_Gset) in Hd.
  rewrite <- Hpinv1 in Hd.
  rewrite (Gset_comp _ _ _ D_is_Gset) in Hd.
  inversion Hd as [d' Hd' EQd'].
  rewrite <- (Gset_comp _ _ _ D_is_Gset) in EQd'.
  rewrite Hpinv1 in EQd'.
  rewrite (Gset_unit _ _ _ D_is_Gset) in EQd'.
  rewrite <- EQd'.
  clear d Hd EQd'.

  (* Hd' : In _ (ensembleAct _ C' pinv) d' *)
  apply HCm' in Hd'.
  clear HCm'.

  (* Hd : In _ C' d *)
  rewrite <- (Gset_unit _ _ _ D_is_Gset) in Hd'.
  rewrite <- Hpinv2 in Hd'.
  rewrite (Gset_comp _ _ _ D_is_Gset) in Hd'.
  inversion Hd' as [d Hd EQd].
  rewrite <- (Gset_comp _ _ _ D_is_Gset) in EQd.
  rewrite Hpinv2 in EQd.
  rewrite (Gset_unit _ _ _ D_is_Gset) in EQd.

  (* Goal : In _ C' d *)
  rewrite <- EQd.
  rewrite <- (Gset_comp _ _ _ D_is_Gset).
  rewrite Hpinv1.
  now rewrite (Gset_unit _ _ _ D_is_Gset).
Qed.

(* A fact used for proving [Bojanczyk+ 2014, Lemma 4.13] *)
Lemma support_connects_two_actions :
  forall (x : Xd) (C : Ensemble Dd),
    IsSupport x C ->
  forall pi sigma : G,
    (forall c, In _ C c -> action c pi = action c sigma)
    -> action x pi = action x sigma.
Proof.
  intros x C HC.
  intros pi sigma Hc.
  unfold IsSupport in HC.
  destruct (group_inverse _ G_is_group pi) as [pinv [Hpinv1 Hpinv2]].
  assert (HC' := HC (comp sigma pinv)).
  rewrite (Gset_comp _ _ _ X_is_Gset) in HC'.
  symmetry.
  apply-> (transpose_inverse _ X_is_Gset _ _ Hpinv1 Hpinv2).
  apply HC'.
  clear HC HC'.
  intros c HCc.
  rewrite (Gset_comp _ _ _ D_is_Gset).
  apply<- (transpose_inverse _ D_is_Gset _ _ Hpinv1 Hpinv2).
  symmetry.
  now apply Hc.
Qed.

Definition IsPartialFunc {Dom Codom : Type}
  (A : Ensemble Dom) (B : Ensemble Codom) (f : Dom -> Codom) :=
  forall x, In _ A x -> In _ B (f x).
Definition IsPartialOnto {Dom Codom : Type}
  (A : Ensemble Dom) (B : Ensemble Codom) (f : Dom -> Codom) :=
  forall z, In _ B z -> exists x, In _ A x /\ f x = z.
Definition IsPartialOneToOne {Dom Codom : Type}
  (A : Ensemble Dom) (B : Ensemble Codom) (f : Dom -> Codom) :=
  forall x y, In _ A x /\ In _ A y -> f x = f y -> x = y.

Lemma orbit_preserves_least_support :
  forall (x y : Xd) (C C' : Ensemble Dd),
    orbit x y ->
    IsLeastSupport x C /\ IsLeastSupport y C' ->
  exists f : Dd -> Dd,
    IsPartialFunc C C' f /\
    IsPartialOnto C C' f /\
    IsPartialOneToOne C C' f.
Proof.
  intros x y C C'.
  unfold orbit.
  intros [pi Ho] [Hsx Hsy].
  destruct (group_inverse _ G_is_group pi) as [pinv [Hpinv1 Hpinv2]].
  apply (action_preserves_least_support pi x) in Hsx.
  rewrite Ho in Hsx.
  assert (EqC': C' = ensembleAct D C pi).
  { apply (least_support_is_unique y). split; assumption. }

  exists (fun a => action a pi).
  split; [| split].
  - (* f's range is in C' *)
  unfold IsPartialFunc.
  intros c Hc.
  rewrite EqC'.
  now apply mkEnsembleAct.
  - (* f is onto *)
  unfold IsPartialOnto.
  intros d Hd.
  exists (action d pinv).
  split.
  + (* In _ C (action d pinv) *)
  rewrite EqC' in Hd.
  inversion Hd as [d' Hd' EQd'].
  rewrite<- (Gset_comp _ _ _ D_is_Gset).
  rewrite Hpinv2.
  now rewrite (Gset_unit _ _ _ D_is_Gset).
  + (* action (action d pinv) pi = d *)
  rewrite<- (Gset_comp _ _ _ D_is_Gset).
  rewrite Hpinv1.
  now rewrite (Gset_unit _ _ _ D_is_Gset).
  - (* f is one-to-one *)
  intros c1 c2 [Hc1 Hc2] Hcp.
  assert (Hcpi : action (action c1 pi) pinv = action (action c2 pi) pinv).
  { rewrite Hcp. reflexivity. }
  rewrite<- (Gset_comp _ _ _ D_is_Gset) in Hcpi.
  rewrite<- (Gset_comp _ _ _ D_is_Gset) in Hcpi.
  rewrite Hpinv2 in Hcpi.
  rewrite (Gset_unit _ _ _ D_is_Gset) in Hcpi.
  rewrite (Gset_unit _ _ _ D_is_Gset) in Hcpi.
  assumption.
Qed.

Variable Y : Gset.
Hypothesis Y_is_Gset : IsGset Y.
Let Yd := domainG Y.

Variable f : Xd -> Yd.
Hypothesis f_is_equivariant : IsEquivariant f.

(* Same as [Bojanczyk+ 2014, Lemma 4.8] *)
Lemma equivariant_f_preserves_support :
  forall (x : Xd) (C : Ensemble Dd),
  IsSupport x C -> IsSupport (f x) C.
Proof.
  intros x C HC.
  unfold IsSupport.
  unfold IsSupport in HC.
  intros pi Hc.
  apply (HC pi) in Hc.
  rewrite <- f_is_equivariant.
  now rewrite Hc.
Qed.

(* A corollary of the previous lemma *)
Lemma equivariant_f_reduces_least_support :
  forall (x : Xd) (C Cf : Ensemble Dd),
  IsLeastSupport x C /\ IsLeastSupport (f x) Cf
  -> Included _ Cf C.
Proof.
  intros x C Cf [HC HCf].
  destruct HC as [HC HCm].
  destruct HCf as [HCf HCfm].
  apply HCfm.
  now apply equivariant_f_preserves_support.
Qed.

Hypothesis f_is_one_to_one : IsOneToOne f.

Lemma equivariant_one_to_one_f_preserves_least_support :
  forall (x : Xd) (C Cf : Ensemble Dd),
  IsLeastSupport x C /\ IsLeastSupport (f x) Cf
  -> C = Cf.
Proof.
  intros x C Cf [HC HCf].
  apply Extensionality_Ensembles.
  unfold Same_set.
  split.
  - (* Included _ C Cf *)
  destruct HC as [HC HCm].
  destruct HCf as [HCf HCfm].
  apply HCm.
  unfold IsSupport.
  intros pi Hc.
  unfold IsSupport in HCf.
  apply f_is_one_to_one.
  rewrite f_is_equivariant.
  now apply HCf.
  - (* Included _ Cf C *)
  now apply (equivariant_f_reduces_least_support x).
Qed.

End Support.
