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

Class GroupSet (GM : Magma) `(IsGroup GM) := mkGroupSet {
  domain : Set;
  action : domain -> carrier -> domain;
  orbit x y := exists pi : carrier, action x pi = y;
}.

Record IsGroupSet (GM : Magma) `(HG : IsGroup GM) (A : GroupSet GM HG) := {
  Gset_unit : forall x, action x unit = x;
  Gset_comp :
    forall (x : domain) (pi sigma : carrier),
      action x (op pi sigma) = action (action x pi) sigma;
}.

Definition Gset := GroupSet GMag G_is_group.
Definition mkGset := mkGroupSet GMag G_is_group.
Definition IsGset := IsGroupSet GMag G_is_group.
Definition domainG := @domain GMag G_is_group.

Section InTheSameOrbit.

Variable D : Set.
Variable act : D -> G -> D.
Definition DG := mkGset D act.
Hypothesis D_is_Gset : IsGset DG.

Lemma in_the_same_orbit :
  forall y1 y2 : domainG DG,
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
  rewrite   (Gset_comp _ _ _ D_is_Gset).
  rewrite<- (Gset_comp _ _ _ D_is_Gset _ _ p1inv).
  rewrite Hp1iv.
  rewrite   (Gset_unit _ _ _ D_is_Gset).
  reflexivity.
  - (* <- *)
  intros H.
  exists y1.
  split.
  + exists unit.
  rewrite (Gset_unit _ _ _ D_is_Gset).
  reflexivity.
  + assumption.
Qed.

End InTheSameOrbit.

(* Equivariant functions *)

Section EquivariantFunctions.

Definition IsEquivariant {A B : Gset} (f : domainG A -> domainG B) :=
  forall (x : domainG A) (pi : G),
    f (action x pi) = action (f x) pi.
Definition IsOnto {A B : Set} (f : A -> B) :=
  forall z, exists x, f x = z.
Definition IsOneToOne {A B : Set} (f : A -> B) :=
  forall x y, f x = f y -> x = y.

Variables A B : Set.
Variable Aact : A -> G -> A.
Variable Bact : B -> G -> B.
Definition AG := mkGset A Aact.
Definition BG := mkGset B Bact.
Hypothesis A_is_Gset : IsGset AG.
Hypothesis B_is_Gset : IsGset BG.

Variable f : domainG AG -> domainG BG.
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

Variable finv : domainG BG -> domainG AG.
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
