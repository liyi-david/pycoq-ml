(*==========timed data stream========*)
From Coq Require Import Arith.
From Coq Require Import List.
From Coq Require Import Reals.
From Coq Require Import Streams.

Open Scope type_scope.

Definition Time:=R.
Definition Data:=nat.
Definition TD:=Time*Data.
Definition PrL {A B: Type}(pair: A  * B) :=
  match pair with
  | (a, b) => a
  end.
Definition PrR {A B: Type}(pair: A * B ) :=
  match pair with
  | (a, b) => b
  end.


(*============judgement==========*)
Parameter Input : Stream TD.
Parameter Output : Stream TD.


Open Scope R_scope.
           (*increasing time moments*)
Axiom Inc_T : forall T: Stream TD,
  PrL (hd T)  < PrL (hd (tl T)).
           (*the judgement about time*)
Definition Teq(s1 s2:Stream TD) :Prop :=
  forall n:nat, PrL(Str_nth n s1) = PrL(Str_nth n s2).
Definition Tneq(s1 s2:Stream TD) : Prop :=
  forall n:nat, PrL(Str_nth n s1) <> PrL(Str_nth n s2).
Definition Tle(s1 s2:Stream TD) : Prop :=
  forall n:nat, PrL(Str_nth n s1) < PrL(Str_nth n s2).
Definition Tgt(s1 s2:Stream TD) : Prop :=
  forall n:nat, PrL(Str_nth n s1) > PrL(Str_nth n s2).
          (*the judgement about data*)
Definition Deq(s1 s2:Stream TD) : Prop :=
  forall n:nat, PrR(Str_nth n s1) = PrR(Str_nth n s2).


(*===========basic channel==========*)
Definition Sync (Input Output:Stream TD) : Prop:=
   (Teq Input Output)  /\  (Deq Input Output).

Definition SyncDrain (Input1 Input2:Stream TD) : Prop:=
   (Teq Input1 Input2).

Definition FIFO1(Input Output:Stream TD) : Prop:= ((Tle Input Output) /\ (Tle Output (tl Input)) /\ (Deq Input Output)).

Definition FIFO1e(Input Output :Stream TD)(e:Data):=
  (Tgt Input Output)
  /\
  PrR(hd Output)=e
  /\
  (Deq Input (tl Output)).



Parameter AsyncDrain: Stream TD -> Stream TD ->Prop.
Axiom AsyncDrain_coind:
  forall Input1 Input2: Stream TD,
  AsyncDrain Input1 Input2 ->

  (   (~PrL(hd Input1)  =  PrL (hd Input2))  )
  /\
  (
    (   (PrL(hd Input1)  <  PrL (hd Input2))  /\
      AsyncDrain (tl Input1) Input2        )
    /\
    (   (PrL(hd Input1)  >  PrL (hd Input2))  /\
      AsyncDrain Input1 (tl Input2)        )
  ).

Parameter LossySync: Stream TD -> Stream TD -> Prop.
Axiom LossySync_coind:
  forall Input Output: Stream TD,
  LossySync Input Output ->
  (
  (hd Output = hd Input  /\ LossySync (tl Input) (tl Output))
  \/
  LossySync (tl Input) Output
  ).



(*=============Operators============*)
Parameter merge:
Stream TD -> Stream TD ->Stream TD -> Prop.
Axiom merge_coind:
  forall s1 s2 s3:Stream TD,
  merge s1 s2 s3->(
  ~(PrL(hd s1) = PrL(hd s2))
  /\
  (
    (   (PrL(hd s1) < PrL(hd s2))  ->
       ( (hd s3 = hd s1)  /\ merge (tl s1) s2 (tl s3) )   )
    /\
    (   (PrL(hd s1) > PrL(hd s2))    ->
       ( (hd s3 = hd s2)  /\ merge s1 (tl s2) (tl s3))    )
  )
  ).

(*===========examples============*)
Variable A B C D E F G C1 C2 T S :Stream TD.
(*===============================*)
                    (*example 1*)
(*===============================*)
Theorem test1 : forall A B C:Stream TD,
   (Sync A B )-> (FIFO1 B C)
   ->  (Tle A C).
Proof.
intros.
destruct H.
destruct H0.
intro n.
rewrite H.
apply H0.
Qed.

(*===============================*)
                    (*example 2*)
(*===============================*)
Lemma transfer_eq:forall s1 s2 s3:Stream TD,
   (Teq s1 s2)  /\ (Teq s2 s3)  ->  (Teq s1 s3).
Proof.
admit.
Admitted.

Lemma transfer_eqtl: forall s1 s2:Stream TD,
   (Teq s1 s2)  ->  (Teq (tl s1) (tl s2)).
Proof.
admit.
Admitted.

Lemma transfer_leeq:forall s1 s2 s3:Stream TD,
   (Tle s1 s2) /\ (Teq s2 s3)   ->  (Tle s1 s3).
Proof.
admit.
Admitted.

Lemma transfer_hdle: forall s1 s2:Stream TD,
   (Tle s2 s1)  -> (PrL(hd s1) > PrL(hd s2)).
Proof.
admit.
Admitted.

Section Alt.
Hypothesis D1: SyncDrain A B.
Hypothesis D2: FIFO1 A C1.
Hypothesis D3: Sync B C2.
Theorem subtest:
   (Tle C2 C1)  /\  (Tle C1 (tl C2)).
Proof.
destruct D2.
destruct D3.
destruct H0.

split.
intros n.
rewrite  <- H1.
rewrite  <- D1.
apply H.

assert ( (Teq A B) /\ (Teq B C2) ).
split.
apply D1.
assumption.
assert ( Teq A C2 ).
generalize H4.
apply transfer_eq.
assert( Teq (tl A) (tl C2) ).
apply transfer_eqtl.
assumption.
assert( (Tle C1 (tl A)) /\ (Teq (tl A) (tl C2))  ).
split.
assumption.
assumption.
generalize H7.
(*T S are intermediate variable*)
assert ( T=(tl A) ).
admit.
rewrite <- H8.
assert ( S=(tl C2) ).
admit.
rewrite  <- H9.
apply transfer_leeq.
Admitted.


Hypothesis D4: merge C1 C2 C.
Theorem test:
   hd(C)=hd(C2) /\ merge C1 (tl C2) (tl C).
Proof.
destruct subtest.
assert( (PrL(hd C1) > PrL(hd C2)) ).
generalize H.
apply transfer_hdle.
generalize H1.
apply merge_coind.
apply D4.
Admitted.

End Alt.

(*===============================*)
                    (*example 3*)
(*===============================*)
Lemma Eq:forall A B:Stream TD,
  A=B <->  Sync A B.
Proof.
admit.
Admitted.

Theorem refinement : forall A C D: Stream TD,
  (exists B,
  (FIFO1 A B) /\ (Sync B C) /\ (Sync B D)
  )->
  (exists E,
  (Sync A E) /\ (FIFO1 E C) /\ (FIFO1 E D)
  ).
Proof.
intros A C D.
intros.

assert(E=A).
admit.
exists E.

split.
rewrite H0.
apply Eq.
reflexivity.

split.
destruct H.
destruct H.
destruct H1.
assert (x=C).
apply Eq.
assumption.
rewrite <- H3.
rewrite H0.
assumption.

destruct H.
destruct H.
destruct H1.
assert(x=D).
apply Eq.
assumption.
rewrite <- H3.
rewrite H0.
assumption.
Admitted.

(*===============================*)
                    (*example 4*)
(*===============================*)
Theorem equivalence: forall A B C,
  (exists E F G,
     (Sync A E) /\ ( FIFO1 E F) /\ (Sync F B) /\ (FIFO1 E G) /\ (Sync G C) /\ (SyncDrain F G)
  ) <->
  (exists D,
     (FIFO1 A D) /\ (Sync D B) /\ (Sync D C)
  ).
Proof.
intros A B C.
split.

intros.
destruct H as [E].
destruct H as [F].
destruct H as [G].

assert (D=F).
admit.
exists D.

split.
destruct H.
destruct H1.
assert ( FIFO1 E D ).
rewrite H0.
assumption.
assert (A=E).
apply Eq.
assumption.
rewrite H4.
assumption.

split.
destruct H.
destruct H1.
destruct H2.
rewrite H0.
assumption.

destruct H.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
rewrite H0.
assert (G=C).
apply Eq.
assumption.
rewrite <- H6.

split.
assumption.
destruct H1.
destruct H7.
destruct H3.
destruct H9.
assert (forall s1 s2 s3:Stream TD,
( (Deq s1 s2) /\ (Deq s1 s3) )  ->  (Deq s2 s3) ).  (*regard as lemma*)
admit.
assert ( (Deq E F) /\ (Deq E G) ).
split.
assumption.
assumption.
generalize H12.
apply H11.


intros.
destruct H as [D].
assert (E=A /\ F=D /\ G=D).
admit.
exists E.
exists F.
exists G.

split.
destruct H0.
apply Eq.
symmetry.
assumption.

split.
destruct H.
destruct H0.
destruct H2.
rewrite H0.
rewrite H2.
assumption.

split.
destruct H.
destruct H1.
destruct H0.
destruct H3.
rewrite H3.
assumption.

split.
destruct H.
destruct H0.
destruct H2.
rewrite H0.
rewrite H3.
assumption.

split.
destruct H.
destruct H1.
destruct H0.
destruct H3.
rewrite H4.
assumption.

assert (Teq F G).
destruct H0.
destruct H1.
rewrite H1.
rewrite H2.
admit.
assumption.
Admitted.