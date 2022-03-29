Require Import gset.

Inductive Tree (A : Gset) :=
| leaf : Tree A
| tree : domainG A -> Tree A -> Tree A -> Tree A.

Fixpoint treeAct {A : Gset} (t : Tree A) (pi : G)
  : Tree A :=
  match t with
  | leaf _ => t
  | tree _ a first_child next_sibling =>
    tree _ (action a pi) (treeAct first_child pi) (treeAct next_sibling pi)
  end.

(* Tree(A) *)

Section TreeIsGset.

Variable A : Gset.
Hypothesis A_is_Gset : IsGset A.
Let Ad := domainG A.

Let TreeA := mkGset (Tree A) treeAct.
Let TAd := domainG TreeA.

Local Lemma Tree_unit :
  forall t : TAd, action t unit = t.
Proof.
  intros t.
  simpl.
  induction t as [| a t1 IHt1 t2 IHt2].
  - now simpl.
  - simpl.
  rewrite IHt1.
  rewrite IHt2.
  now rewrite (Gset_unit _ _ _ A_is_Gset).
Qed.

Local Lemma Tree_comp :
  forall (t : TAd) (pi sigma : G),
    action t (comp pi sigma) = action (action t pi) sigma.
Proof.
  intros t pi sigma.
  simpl.
  induction t as [| a t1 IHt1 t2 IHt2].
  - now simpl.
  - simpl.
  rewrite IHt1.
  rewrite IHt2.
  now rewrite (Gset_comp _ _ _ A_is_Gset).
Qed.

Lemma Tree_is_Gset : IsGset TreeA.
Proof.
  unfold IsGset.
  apply {| Gset_unit := Tree_unit; Gset_comp := Tree_comp; |}.
Qed.

End TreeIsGset.

Require Import Ensembles.

(* Next(S) *)

Section NextIsEquivariant.

Variable A : Gset.
Hypothesis A_is_Gset : IsGset A.
Let Ad := domainG A.

Let TreeA := mkGset (Tree A) treeAct.
Let TAd := domainG TreeA.

Inductive Next (S : Ensemble TAd)
  : Ensemble TAd :=
  | next_intro : forall (t1 t2 : TAd) (a : Ad),
    In _ S t1 -> In _ S t2 -> In _ (Next S) (tree _ a t1 t2).

Variable S : Ensemble TAd.
Hypothesis S_is_equivariant : IsEquivariantSubset S.

Lemma NextS_is_equivariant :
  IsEquivariantSubset (Next S).
Proof.
  unfold IsEquivariantSubset.
  intros t pi Ht.
  simpl.
  inversion Ht as [t1 t2 a Ht1 Ht2 EQt].
  simpl.
  apply next_intro;
  now apply S_is_equivariant.
Qed.

End NextIsEquivariant.

(* row(s) *)

Section RowIsEquivariant.

Variable A : Gset.
Hypothesis A_is_Gset : IsGset A.
Let Ad := domainG A.

Let TreeA := mkGset (Tree A) treeAct.
Let TAd := domainG TreeA.
Let TAact := actionG TreeA.

Variable L : Ensemble (domainG (GProduct TreeA TreeA)).
Hypothesis L_is_equivariant : IsEquivariantSubset L.

Let ETA := mkGset (Ensemble TAd) (ensembleAct TreeA).
Let ETAd := domainG ETA.
Inductive row (s : TAd) : ETAd :=
| row_intro : forall a : TAd,
  In _ L (a, s) -> In _ (row s) a.

Lemma row_is_equivariant :
  IsEquivariant row.
Proof.
  unfold IsEquivariant.
  intros t pi.
  destruct (group_inverse _ G_is_group pi) as [pinv [Hpinv1 Hpinv2]].
  assert (TA_is_Gset := Tree_is_Gset _ A_is_Gset).

  apply Extensionality_Ensembles.
  split; unfold Included; simpl.
  - (* Included _ (row (action t pi)) (action (row t) pi) *)
  intros t' Ht'.

  (* Rewrite goal using t' = action (action t pinv) pi *)
  rewrite <- (Gset_unit _ _ _ TA_is_Gset t').
  rewrite <- Hpinv1.
  rewrite (Gset_comp _ _ _ TA_is_Gset).
  apply ensembleAct_intro.
  (* In _ L (action t' pinv, t) *)
  apply row_intro.

  (* Rewrite Ht' to In _ L (t', action t pi) *)
  generalize (refl_equal (treeAct t pi)).
  pattern (treeAct t pi) at 2.
  case Ht'; clear t' Ht'.
  intros t' Ht' _.

  (* Rewrite goal using t = action (action t p) pinv *)
  rewrite <- (Gset_unit _ _ _ TA_is_Gset t).
  rewrite <- Hpinv2.
  rewrite (Gset_comp _ _ _ TA_is_Gset).
  apply (L_is_equivariant _ pinv) in Ht'.
  simpl in Ht'.
  apply Ht'.

  - (* Included _ (action (row t) pi) (row (action t pi)) *)
  intros t' Ht'.
  inversion Ht' as [a Ha EQa]; clear EQa t' Ht'.
  apply row_intro.

  (* Rewrite Ha to In _ L (a, t) *)
  generalize (refl_equal (action a pi)).
  pattern (action a pi) at 2.
  case Ha; clear a Ha.
  intros a Ha _.

  now apply (L_is_equivariant _ pi) in Ha.
Qed.

End RowIsEquivariant.
