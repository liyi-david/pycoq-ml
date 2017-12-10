Parameter A:Prop.

Goal forall a:nat, (match a with 0 => 1 | S _ => 0 end) >= 0.
Proof.
    intro a.
    induction a.
    auto. eauto.
Qed.