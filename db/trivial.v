Definition T : Type := forall A B : Prop, A -> (B -> A).

Goal forall a:nat, T.
Proof.
    intros.
    unfold T.
    intros.
    mlauto.
Qed.