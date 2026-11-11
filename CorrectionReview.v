From Stdlib Require Import Arith Lia List.
Import ListNotations.

(* Finite tree metrics: abstract two-sweep argument                         *)
(*
   [TSpace] records only the finite metric facts needed by the diameter
   argument.  The later parent-list development constructs a value of this
   record from its recursively defined tree distance; the final theorem does
   not ask callers to assume tree geometry without proof.
*)

Definition Diam {V : Type} (L : list V) (d : V -> V -> nat) (a b : V) : Prop :=
  forall x y, In x L -> In y L -> d x y <= d a b.

(* Unlike Diam, this predicate also says that both endpoints belong to the
   finite tree. *)
Definition DiameterPair {V : Type} (L : list V) (d : V -> V -> nat)
    (a b : V) : Prop :=
  In a L /\ In b L /\ Diam L d a b.

Definition Far {V : Type} (L : list V) (d : V -> V -> nat) (r s : V) : Prop :=
  forall x, In x L -> d r x <= d r s.

(* A farthest-vertex choice includes the fact that both points are vertices. *)
Definition FarthestChoice {V : Type} (L : list V) (d : V -> V -> nat)
    (r s : V) : Prop :=
  In r L /\ In s L /\ Far L d r s.

Record TSpace {V : Type} (L : list V) (root : V) (d : V -> V -> nat) : Prop := {
  ts_root : In root L;
  ts_sym  : forall x y, d x y = d y x;
  ts_four : forall a b c e,
    d a b + d c e <= d a c + d b e \/ d a b + d c e <= d a e + d b c
}.

Fixpoint argmax {V : Type} (score : V -> nat) (fb : V) (xs : list V) : V :=
  match xs with
  | [] => fb
  | x :: rest =>
      let best := argmax score fb rest in
      if Nat.leb (score x) (score best) then best else x
  end.

Lemma argmax_spec {V : Type} (score : V -> nat) (fb : V) (xs : list V) (z : V) :
  In z xs \/ z = fb -> score z <= score (argmax score fb xs).
Proof.
  induction xs as [|x xs IH]; intros Hz.
  - simpl in Hz. destruct Hz as [Hfalse | Hfb].
    + contradiction.
    + subst z. apply Nat.le_refl.
  - simpl in Hz. cbn [argmax].
    destruct (Nat.leb (score x) (score (argmax score fb xs))) eqn:Hcmp.
    + apply Nat.leb_le in Hcmp.
      destruct Hz as [[Hzx | Hzrest] | Hfb].
      * subst z. exact Hcmp.
      * apply IH. left. exact Hzrest.
      * apply IH. right. exact Hfb.
    + apply Nat.leb_gt in Hcmp.
      destruct Hz as [[Hzx | Hzrest] | Hfb].
      * subst z. lia.
      * specialize (IH (or_introl Hzrest)). lia.
      * specialize (IH (or_intror Hfb)). lia.
Qed.

Lemma argmax_in {V : Type} (score : V -> nat) (fb : V) (xs : list V) :
  argmax score fb xs = fb \/ In (argmax score fb xs) xs.
Proof.
  induction xs as [|x xs IH].
  - left. reflexivity.
  - cbn [argmax].
    destruct (Nat.leb (score x) (score (argmax score fb xs))).
    + destruct IH as [E | Hin].
      * left. exact E.
      * right. simpl. right. exact Hin.
    + right. simpl. left. reflexivity.
Qed.

(* First sweep: every farthest choice is at diameter distance from some
   endpoint of a fixed diameter. *)
Lemma first_sweep {V : Type} {L : list V} {root : V} {d : V -> V -> nat}
    (H : TSpace L root d) (a b r s : V) :
  In a L -> In b L -> In s L ->
  Diam L d a b -> Far L d r s ->
  d s a = d a b \/ d s b = d a b.
Proof.
  intros Ha Hb Hs Hdiam Hfar.
  destruct (Nat.eq_dec (d s a) (d a b)) as [E | Na]; [left; exact E |].
  destruct (Nat.eq_dec (d s b) (d a b)) as [E | Nb]; [right; exact E |].
  pose proof (Hdiam s a Hs Ha) as H1.
  pose proof (Hdiam s b Hs Hb) as H2.
  pose proof (Hfar a Ha) as H3.
  pose proof (Hfar b Hb) as H4.
  pose proof (@ts_four V L root d H a b r s) as H5.
  pose proof (@ts_sym V L root d H a r) as S1.
  pose proof (@ts_sym V L root d H b s) as S2.
  pose proof (@ts_sym V L root d H a s) as S3.
  pose proof (@ts_sym V L root d H b r) as S4.
  lia.
Qed.

(* Abstract two-sweeps theorem, valid for every tie-breaking choice. *)
Theorem two_sweeps {V : Type} {L : list V} {root : V} {d : V -> V -> nat}
    (H : TSpace L root d) (a b r s t : V) :
  In a L -> In b L -> In s L ->
  Diam L d a b -> Far L d r s -> Far L d s t -> Diam L d s t.
Proof.
  intros Ha Hb Hs Hdiam H1 H2 x y Hx Hy.
  pose proof (Hdiam x y Hx Hy) as Hxy.
  destruct (first_sweep H a b r s Ha Hb Hs Hdiam H1) as [E | E].
  - pose proof (H2 a Ha) as H3. lia.
  - pose proof (H2 b Hb) as H3. lia.
Qed.

(* Finite argmax: existence of a diameter and executable farthest choices. *)
Definition farthest_vertex {V : Type} (L : list V) (root : V)
    (d : V -> V -> nat) (r : V) : V := argmax (d r) root L.

Definition ecc {V : Type} (L : list V) (root : V) (d : V -> V -> nat) (x : V) : nat :=
  d x (farthest_vertex L root d x).

Definition diam_left {V : Type} (L : list V) (root : V) (d : V -> V -> nat) : V :=
  argmax (ecc L root d) root L.

Definition diam_right {V : Type} (L : list V) (root : V) (d : V -> V -> nat) : V :=
  farthest_vertex L root d (diam_left L root d).

Lemma farthest_in {V : Type} {L : list V} {root : V} {d : V -> V -> nat}
    (H : TSpace L root d) (r : V) : In (farthest_vertex L root d r) L.
Proof.
  unfold farthest_vertex.
  destruct (argmax_in (d r) root L) as [E | Hin].
  - rewrite E. exact (@ts_root V L root d H).
  - exact Hin.
Qed.

Lemma farthest_far {V : Type} {L : list V} {root : V} {d : V -> V -> nat}
    (H : TSpace L root d) (r : V) : Far L d r (farthest_vertex L root d r).
Proof.
  intros x Hx. unfold farthest_vertex.
  apply (argmax_spec (d r) root L x). left. exact Hx.
Qed.

Lemma diam_left_in {V : Type} {L : list V} {root : V} {d : V -> V -> nat}
    (H : TSpace L root d) : In (diam_left L root d) L.
Proof.
  unfold diam_left.
  destruct (argmax_in (ecc L root d) root L) as [E | Hin].
  - rewrite E. exact (@ts_root V L root d H).
  - exact Hin.
Qed.

Lemma diam_right_in {V : Type} {L : list V} {root : V} {d : V -> V -> nat}
    (H : TSpace L root d) : In (diam_right L root d) L.
Proof. exact (farthest_in H _). Qed.

Lemma diameter_exists {V : Type} {L : list V} {root : V} {d : V -> V -> nat}
    (H : TSpace L root d) :
  Diam L d (diam_left L root d) (diam_right L root d).
Proof.
  intros x y Hx Hy.
  pose proof (farthest_far H x y Hy) as H1.
  pose proof (argmax_spec (ecc L root d) root L x (or_introl Hx)) as H2.
  exact (Nat.le_trans _ _ _ H1 H2).
Qed.

(* Forme algorithmique : deux balayages avec argmax. *)
Theorem two_sweep_algorithm {V : Type} {L : list V} {root : V}
    {d : V -> V -> nat} (H : TSpace L root d) (r : V) :
  Diam L d (farthest_vertex L root d r)
           (farthest_vertex L root d (farthest_vertex L root d r)).
Proof.
  apply (two_sweeps H (diam_left L root d) (diam_right L root d) r
           (farthest_vertex L root d r)
           (farthest_vertex L root d (farthest_vertex L root d r))).
  - exact (diam_left_in H).
  - exact (diam_right_in H).
  - exact (farthest_in H r).
  - exact (diameter_exists H).
  - exact (farthest_far H r).
  - exact (farthest_far H _).
Qed.

(* Metric facts preserved when one new leaf is attached                    *)

(* Distance after attaching a new leaf [l] to vertex [p]. *)
Definition ext (d : nat -> nat -> nat) (l p : nat) (x y : nat) : nat :=
  if Nat.eqb x l then (if Nat.eqb y l then 0 else S (d p y))
  else if Nat.eqb y l then S (d x p) else d x y.

Record Good (d : nat -> nat -> nat) : Prop := {
  g_refl : forall x, d x x = 0;
  g_sym  : forall x y, d x y = d y x;
  g_tri  : forall x y z, d x z <= d x y + d y z;
  g_four : forall a b c e,
    d a b + d c e <= d a c + d b e \/ d a b + d c e <= d a e + d b c
}.

Lemma ext_good (d : nat -> nat -> nat) (l p : nat) :
  Good d -> Good (ext d l p).
Proof.
  intros G. constructor.
  - (* réflexivité *)
    intros x. unfold ext.
    destruct (Nat.eqb x l); cbn.
    + reflexivity.
    + apply (@g_refl d G x).
  - (* symétrie *)
    intros x y. unfold ext.
    destruct (Nat.eqb x l); destruct (Nat.eqb y l); cbn;
      pose proof (@g_sym d G p y); pose proof (@g_sym d G x p);
      pose proof (@g_sym d G x y); lia.
  - (* inégalité triangulaire *)
    intros x y z. unfold ext.
    destruct (Nat.eqb x l); destruct (Nat.eqb y l); destruct (Nat.eqb z l); cbn;
      pose proof (@g_tri d G p y z); pose proof (@g_tri d G x y p);
      pose proof (@g_tri d G x p z); pose proof (@g_tri d G x y z); lia.
  - (* condition des quatre points : 16 cas selon quels arguments valent l *)
    intros a b c e. unfold ext.
    destruct (Nat.eqb a l); destruct (Nat.eqb b l);
    destruct (Nat.eqb c l); destruct (Nat.eqb e l); cbn;
      pose proof (@g_four d G a b c e);
      pose proof (@g_four d G p b c e); pose proof (@g_four d G a p c e);
      pose proof (@g_four d G a b p e); pose proof (@g_four d G a b c p);
      pose proof (@g_tri d G a p b); pose proof (@g_tri d G a p c);
      pose proof (@g_tri d G a p e); pose proof (@g_tri d G b p c);
      pose proof (@g_tri d G b p e); pose proof (@g_tri d G c p e);
      pose proof (@g_sym d G a p); pose proof (@g_sym d G b p);
      pose proof (@g_sym d G c p); pose proof (@g_sym d G e p);
      pose proof (@g_sym d G a b); pose proof (@g_sym d G a c);
      pose proof (@g_sym d G a e); pose proof (@g_sym d G b c);
      pose proof (@g_sym d G b e); pose proof (@g_sym d G c e);
      lia.
Qed.

(* Concrete tree metric from a parent-list leaf construction               *)

(* [ps = [p_k; ...; p_1]] records the parent choices in reverse
   construction order. The newly added vertex [S (length ps')] is attached
   to [p]. The vertices are [0, ..., length ps], with [0] as root. *)
Fixpoint tdist (ps : list nat) : nat -> nat -> nat :=
  match ps with
  | [] => fun _ _ => 0
  | p :: ps' => ext (tdist ps') (S (length ps')) p
  end.

Lemma tdist_good : forall ps, Good (tdist ps).
Proof.
  induction ps as [|p ps IH].
  - constructor; intros; cbn; lia.
  - exact (ext_good (tdist ps) (S (length ps)) p IH).
Qed.

Lemma tdist_space (ps : list nat) :
  TSpace (seq 0 (S (length ps))) 0 (tdist ps).
Proof.
  pose proof (tdist_good ps) as G.
  constructor.
  - simpl. left. reflexivity.
  - exact (@g_sym (tdist ps) G).
  - exact (@g_four (tdist ps) G).
Qed.

(* The new leaf is at distance one from its parent. *)
Lemma tdist_leaf (p : nat) (ps : list nat) :
  p <= length ps -> tdist (p :: ps) (S (length ps)) p = 1.
Proof.
  intros Hp.
  change (ext (tdist ps) (S (length ps)) p (S (length ps)) p = 1).
  unfold ext. rewrite Nat.eqb_refl.
  assert (E : Nat.eqb p (S (length ps)) = false)
    by (apply Nat.eqb_neq; lia).
  rewrite E. rewrite (@g_refl (tdist ps) (tdist_good ps) p). reflexivity.
Qed.

(* A parent sequence is a genuine leaf-by-leaf construction when every new
   vertex is attached to a vertex that already exists.  At a step p :: ps,
   the old vertices are 0,...,length ps and the new vertex is S(length ps). *)
Fixpoint valid_parents (ps : list nat) : Prop :=
  match ps with
  | [] => True
  | p :: ps' => p <= length ps' /\ valid_parents ps'
  end.

(* The recursively extended distance separates vertices in the declared
   finite set when the parent sequence is valid. *)
Lemma tdist_separates_vertices : forall ps,
  valid_parents ps -> forall x y,
    In x (seq 0 (S (length ps))) ->
    In y (seq 0 (S (length ps))) ->
    tdist ps x y = 0 -> x = y.
Proof.
  induction ps as [|p ps IH]; intros Hvalid x y Hx Hy Hzero.
  - simpl in Hx, Hy. destruct Hx as [Hx | Hx]; [subst x | contradiction].
    destruct Hy as [Hy | Hy]; [subst y | contradiction]. reflexivity.
  - destruct Hvalid as [Hp Hvalid].
    assert (Hx_bound : x < S (S (length ps))).
    { apply in_seq in Hx. simpl in Hx. lia. }
    assert (Hy_bound : y < S (S (length ps))).
    { apply in_seq in Hy. simpl in Hy. lia. }
    change (ext (tdist ps) (S (length ps)) p x y = 0) in Hzero.
    destruct (Nat.eqb x (S (length ps))) eqn:Ex;
      destruct (Nat.eqb y (S (length ps))) eqn:Ey;
      unfold ext in Hzero; rewrite Ex, Ey in Hzero.
    + apply Nat.eqb_eq in Ex. apply Nat.eqb_eq in Ey. subst. reflexivity.
    + apply Nat.eqb_eq in Ex. subst x. lia.
    + apply Nat.eqb_eq in Ey. subst y. lia.
    + assert (Exne : x <> S (length ps)) by (apply Nat.eqb_neq; exact Ex).
      assert (Eyne : y <> S (length ps)) by (apply Nat.eqb_neq; exact Ey).
      assert (Hx_old : In x (seq 0 (S (length ps)))) by
        (apply in_seq; split; lia).
      assert (Hy_old : In y (seq 0 (S (length ps)))) by
        (apply in_seq; split; lia).
      eapply IH; eauto.
Qed.

Theorem two_sweeps_exact {V : Type} {L : list V} {root : V}
    {d : V -> V -> nat} (H : TSpace L root d) (a b r s t : V) :
  DiameterPair L d a b -> FarthestChoice L d r s ->
  FarthestChoice L d s t -> DiameterPair L d s t.
Proof.
  intros [Ha [Hb Hdiam]] [Hr [Hs Hfirst]] [_ [Ht Hsecond]].
  split; [exact Hs |]. split; [exact Ht |].
  exact (two_sweeps H a b r s t Ha Hb Hs Hdiam Hfirst Hsecond).
Qed.

(* Theorem 3.3 for trees built by successive leaf attachment. *)
Theorem theorem_3_3 (ps : list nat) (r s t : nat) :
  valid_parents ps ->
  FarthestChoice (seq 0 (S (length ps))) (tdist ps) r s ->
  FarthestChoice (seq 0 (S (length ps))) (tdist ps) s t ->
  DiameterPair (seq 0 (S (length ps))) (tdist ps) s t.
Proof.
  intros Hparents Hfirst Hsecond.
  pose proof (tdist_space ps) as H.
  pose proof (diameter_exists H) as Hdiam.
  pose proof (diam_left_in H) as Ha.
  pose proof (diam_right_in H) as Hb.
  exact (two_sweeps_exact H _ _ r s t
    (conj Ha (conj Hb Hdiam)) Hfirst Hsecond).
Qed.

Theorem theorem_3_3_algorithm (ps : list nat) (r : nat) :
  valid_parents ps -> In r (seq 0 (S (length ps))) ->
  DiameterPair (seq 0 (S (length ps))) (tdist ps)
    (farthest_vertex (seq 0 (S (length ps))) 0 (tdist ps) r)
    (farthest_vertex (seq 0 (S (length ps))) 0 (tdist ps)
       (farthest_vertex (seq 0 (S (length ps))) 0 (tdist ps) r)).
Proof.
  intros Hparents Hr.
  pose proof (tdist_space ps) as H.
  refine (@two_sweeps_exact nat (seq 0 (S (length ps))) 0 (tdist ps) H
    (diam_left (seq 0 (S (length ps))) 0 (tdist ps))
    (diam_right (seq 0 (S (length ps))) 0 (tdist ps)) r
    (farthest_vertex (seq 0 (S (length ps))) 0 (tdist ps) r)
    (farthest_vertex (seq 0 (S (length ps))) 0 (tdist ps)
       (farthest_vertex (seq 0 (S (length ps))) 0 (tdist ps) r)) _ _ _).
  - repeat split.
    + apply diam_left_in; exact H.
    + apply diam_right_in; exact H.
    + apply diameter_exists; exact H.
  - repeat split.
    + exact Hr.
    + apply farthest_in; exact H.
    + apply farthest_far; exact H.
  - repeat split.
    + apply farthest_in; exact H.
    + apply farthest_in; exact H.
    + apply farthest_far; exact H.
Qed.

Print Assumptions theorem_3_3.
Print Assumptions theorem_3_3_algorithm.
