Definition T : Type := forall A B : Prop, A -> (B -> A).

Goal forall a b:nat, T.
Proof.
    intros.
    unfold T.
    tauto.
Qed.