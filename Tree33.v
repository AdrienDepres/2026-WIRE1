From Stdlib Require Import Arith Lia List.
Require Import CorrectionReview.
Import ListNotations.

(* Theorem 3.3: concrete finite tree graph and shortest-path distance.

   A tree is built from the one-vertex tree by repeatedly attaching one new
   leaf to an existing vertex.  [ps] records those parent choices;
   [valid_parents ps] says each parent was already present when its child was
   added.  This is a concrete finite undirected tree representation.  The
   metric facts used by the proof are derived from that construction in
   [CorrectionReview.v], rather than postulated here. *)

Definition tree_vertices (ps : list nat) : list nat :=
  seq 0 (S (length ps)).

Record FiniteTree := {
  finite_tree_parents : list nat;
  finite_tree_valid : valid_parents finite_tree_parents
}.

(* The graph is the unit-edge skeleton of the recursively constructed tree.
   Its edge relation is undirected by the symmetry of [tdist]. *)
Definition tree_edge (ps : list nat) (x y : nat) : Prop :=
  In x (tree_vertices ps) /\ In y (tree_vertices ps) /\ tdist ps x y = 1.

Inductive Walk (E : nat -> nat -> Prop) : nat -> list nat -> nat -> Prop :=
| walk_single : forall x, Walk E x [x] x
| walk_cons : forall x y z rest,
    E x y -> Walk E y (y :: rest) z -> Walk E x (x :: y :: rest) z.

Lemma Walk_mono (E F : nat -> nat -> Prop)
    (HEF : forall x y, E x y -> F x y) :
  forall x path y, Walk E x path y -> Walk F x path y.
Proof.
  intros x path y Hwalk. induction Hwalk.
  - constructor.
  - eapply walk_cons; eauto.
Qed.

Lemma Walk_snoc (E : nat -> nat -> Prop) x path y z :
  Walk E x path y -> E y z -> Walk E x (path ++ [z]) z.
Proof.
  intros Hwalk. induction Hwalk as [u | x y v rest Hxy Htail IH]; intro Hyz.
  - simpl. eapply walk_cons; [exact Hyz | constructor].
  - simpl. eapply walk_cons; [exact Hxy | apply IH; exact Hyz].
Qed.

Lemma Walk_prepend (E : nat -> nat -> Prop) x y path z :
  Walk E y path z -> E x y -> Walk E x (x :: path) z.
Proof.
  intros Hpath Hxy. inversion Hpath; subst.
  - simpl. eapply walk_cons; [exact Hxy | constructor].
  - simpl. eapply walk_cons; eassumption.
Qed.

Lemma tdist_old (ps : list nat) (p x y : nat) :
  x <= length ps -> y <= length ps ->
  tdist (p :: ps) x y = tdist ps x y.
Proof.
  intros Hx Hy.
  change (ext (tdist ps) (S (length ps)) p x y = tdist ps x y).
  unfold ext.
  assert (Ex : Nat.eqb x (S (length ps)) = false).
  { apply Nat.eqb_neq. lia. }
  assert (Ey : Nat.eqb y (S (length ps)) = false).
  { apply Nat.eqb_neq. lia. }
  rewrite Ex, Ey. reflexivity.
Qed.

Lemma tree_edge_sym (ps : list nat) x y :
  tree_edge ps x y -> tree_edge ps y x.
Proof.
  intros [Hx [Hy Hd]]. unfold tree_edge. split; [exact Hy |].
  split; [exact Hx |].
  rewrite (@g_sym (tdist ps) (tdist_good ps) y x). exact Hd.
Qed.

Lemma tree_edge_irrefl (ps : list nat) x : ~ tree_edge ps x x.
Proof.
  intros [_ [_ Hdist]].
  rewrite (@g_refl (tdist ps) (tdist_good ps) x) in Hdist. discriminate.
Qed.

Lemma tree_edge_old_preserved (ps : list nat) (p x y : nat) :
  In x (tree_vertices ps) -> In y (tree_vertices ps) ->
  tree_edge ps x y -> tree_edge (p :: ps) x y.
Proof.
  intros Hx Hy [_ [_ Hd]].
  apply in_seq in Hx. apply in_seq in Hy.
  unfold tree_edge, tree_vertices. repeat split.
  - apply in_seq. simpl. lia.
  - apply in_seq. simpl. lia.
  - rewrite tdist_old by (simpl in *; lia). exact Hd.
Qed.

Lemma tree_edge_new_parent (ps : list nat) (p : nat) :
  p <= length ps ->
  tree_edge (p :: ps) (S (length ps)) p.
Proof.
  intros Hp. unfold tree_edge, tree_vertices. repeat split.
  - apply in_seq. simpl. lia.
  - apply in_seq. simpl. lia.
  - apply tdist_leaf. exact Hp.
Qed.

Lemma tree_vertex_old_of_neq_new (ps : list nat) (p x : nat) :
  In x (tree_vertices (p :: ps)) -> x <> S (length ps) ->
  In x (tree_vertices ps).
Proof.
  intros Hx Hneq. unfold tree_vertices in *.
  apply in_seq in Hx. apply in_seq. simpl in *. lia.
Qed.

Lemma tree_edge_leaf_decomposition (ps : list nat) (p : nat) :
  valid_parents (p :: ps) ->
  forall x y,
  tree_edge (p :: ps) x y <->
    ((x <> S (length ps) /\ y <> S (length ps) /\ tree_edge ps x y) \/
     (x = S (length ps) /\ y = p) \/
     (x = p /\ y = S (length ps))).
Proof.
  intros [Hp Hvalid] x y. split.
  - intros [Hx [Hy Hd]].
    set (leaf := S (length ps)).
    assert (Hxb : x <= leaf).
    { apply in_seq in Hx. unfold tree_vertices in Hx. simpl in Hx. lia. }
    assert (Hyb : y <= leaf).
    { apply in_seq in Hy. unfold tree_vertices in Hy. simpl in Hy. lia. }
    destruct (Nat.eq_dec x leaf) as [Ex | Ex].
    + subst x. destruct (Nat.eq_dec y leaf) as [Ey | Ey].
      * subst y. rewrite (@g_refl (tdist (p :: ps))
          (tdist_good (p :: ps)) leaf) in Hd. discriminate.
      * assert (Hyold : In y (tree_vertices ps)).
        { unfold tree_vertices. apply in_seq. apply in_seq in Hy.
          unfold tree_vertices in Hy. simpl in *. lia. }
        assert (Hpold : In p (tree_vertices ps)).
        { unfold tree_vertices. apply in_seq. simpl. lia. }
        unfold tdist in Hd. unfold leaf in Hd. unfold ext in Hd.
        rewrite Nat.eqb_refl in Hd.
        assert (Eyl : Nat.eqb y (S (length ps)) = false) by
          (apply Nat.eqb_neq; exact Ey).
        rewrite Eyl in Hd. simpl in Hd.
        assert (Hzero : tdist ps p y = 0) by (injection Hd; auto).
        pose proof (tdist_separates_vertices ps Hvalid p y Hpold Hyold Hzero)
          as Hpy.
        right. left. split; [reflexivity | symmetry; exact Hpy].
    + destruct (Nat.eq_dec y leaf) as [Ey | Ey].
      * subst y.
        assert (Hxold : In x (tree_vertices ps)).
        { unfold tree_vertices. apply in_seq. apply in_seq in Hx.
          unfold tree_vertices in Hx. simpl in *. lia. }
        assert (Hpold : In p (tree_vertices ps)).
        { unfold tree_vertices. apply in_seq. simpl. lia. }
        unfold tdist in Hd. unfold leaf in Hd. unfold ext in Hd.
        assert (Exl : Nat.eqb x (S (length ps)) = false) by
          (apply Nat.eqb_neq; exact Ex).
        rewrite Exl, Nat.eqb_refl in Hd. simpl in Hd.
        assert (Hzero : tdist ps x p = 0) by (injection Hd; auto).
        pose proof (tdist_separates_vertices ps Hvalid x p Hxold Hpold Hzero)
          as Hxp.
        right. right. split; [exact Hxp | reflexivity].
      * assert (Hxold : In x (tree_vertices ps)).
        { unfold tree_vertices. apply in_seq. apply in_seq in Hx.
          unfold tree_vertices in Hx. simpl in *. lia. }
        assert (Hyold : In y (tree_vertices ps)).
        { unfold tree_vertices. apply in_seq. apply in_seq in Hy.
          unfold tree_vertices in Hy. simpl in *. lia. }
        rewrite tdist_old in Hd by (simpl; lia).
        left. repeat split; assumption.
  - intros [[Hxneq [Hyneq Hedge]] | [[Ex Ey] | [Ex Ey]]].
    + destruct Hedge as [Hxold [Hyold Hdist]].
      unfold tree_edge. repeat split.
      * unfold tree_vertices in *. apply in_seq in Hxold. apply in_seq.
        simpl in *. lia.
      * unfold tree_vertices in *. apply in_seq in Hyold. apply in_seq.
        simpl in *. lia.
      * rewrite tdist_old by
          (unfold tree_vertices in Hxold, Hyold; apply in_seq in Hxold;
           apply in_seq in Hyold; simpl in *; lia).
        exact Hdist.
    + subst x y. apply tree_edge_new_parent. exact Hp.
    + subst x y. apply tree_edge_sym. apply tree_edge_new_parent. exact Hp.
Qed.

(* The next two results connect the recursive distance with the graph
   interpretation used in the paper: every pair has a geodesic walk, and no
   walk between the pair is shorter. *)

(* Every pair of vertices has a graph walk of exactly its recursively defined
   distance in edges. *)
Lemma tree_geodesic_walk : forall ps,
  valid_parents ps ->
  forall x y, In x (tree_vertices ps) -> In y (tree_vertices ps) ->
    exists path, Walk (tree_edge ps) x path y /\
      length path = S (tdist ps x y).
Proof.
  induction ps as [|p ps IH]; intros Hvalid x y Hx Hy.
  - simpl in Hx, Hy. destruct Hx as [Hx | Hx]; [subst x | contradiction].
    destruct Hy as [Hy | Hy]; [subst y | contradiction].
    exists [0]. split; [constructor | reflexivity].
  - destruct Hvalid as [Hp Hvalid].
    set (leaf := S (length ps)).
    assert (Hx_bound : x <= leaf).
    { apply in_seq in Hx. unfold tree_vertices in Hx. simpl in Hx. lia. }
    assert (Hy_bound : y <= leaf).
    { apply in_seq in Hy. unfold tree_vertices in Hy. simpl in Hy. lia. }
    destruct (Nat.eq_dec x leaf) as [Ex | Ex].
    + subst x.
      destruct (Nat.eq_dec y leaf) as [Ey | Ey].
      * subst y. exists [leaf]. split; [constructor |].
        rewrite (@g_refl (tdist (p :: ps)) (tdist_good (p :: ps)) leaf).
        reflexivity.
      * assert (Hy_old : In y (tree_vertices ps)).
        { unfold tree_vertices. apply in_seq. apply in_seq in Hy.
          unfold tree_vertices in Hy. simpl in *. lia. }
        assert (Hp_old : In p (tree_vertices ps)).
        { unfold tree_vertices. apply in_seq. simpl. lia. }
        destruct (IH Hvalid p y Hp_old Hy_old) as [path [Hpath Hlen]].
        exists (leaf :: path). split.
        -- eapply Walk_prepend.
           ++ eapply Walk_mono; [| exact Hpath].
              intros u v [Hu [Hv Hd]].
              eapply tree_edge_old_preserved; [exact Hu | exact Hv |].
              repeat split; assumption.
           ++ apply tree_edge_new_parent. exact Hp.
        -- simpl.
           change (length (leaf :: path) =
             S (ext (tdist ps) leaf p leaf y)).
           unfold ext. rewrite Nat.eqb_refl.
           assert (Eyl : Nat.eqb y leaf = false) by
             (apply Nat.eqb_neq; exact Ey).
           rewrite Eyl. simpl. lia.
    + assert (Hx_old : In x (tree_vertices ps)).
      { unfold tree_vertices. apply in_seq. apply in_seq in Hx.
        unfold tree_vertices in Hx. simpl in *. lia. }
      destruct (Nat.eq_dec y leaf) as [Ey | Ey].
      * subst y.
        assert (Hp_old : In p (tree_vertices ps)).
        { unfold tree_vertices. apply in_seq. simpl. lia. }
        destruct (IH Hvalid x p Hx_old Hp_old) as [path [Hpath Hlen]].
        exists (path ++ [leaf]). split.
        -- eapply Walk_snoc.
           ++ eapply Walk_mono; [| exact Hpath].
              intros u v [Hu [Hv Hd]].
              eapply tree_edge_old_preserved; [exact Hu | exact Hv |].
              repeat split; assumption.
           ++ apply tree_edge_sym. apply tree_edge_new_parent. exact Hp.
        -- rewrite length_app. simpl.
           change (length path + 1 =
             S (ext (tdist ps) leaf p x leaf)).
           unfold ext. assert (Exl : Nat.eqb x leaf = false) by
             (apply Nat.eqb_neq; exact Ex).
           rewrite Exl, Nat.eqb_refl. simpl. lia.
      * assert (Hy_old : In y (tree_vertices ps)).
        { unfold tree_vertices. apply in_seq. apply in_seq in Hy.
          unfold tree_vertices in Hy. simpl in *. lia. }
        destruct (IH Hvalid x y Hx_old Hy_old) as [path [Hpath Hlen]].
        exists path. split.
        -- eapply Walk_mono; [| exact Hpath].
           intros u v [Hu [Hv Hd]].
           eapply tree_edge_old_preserved; [exact Hu | exact Hv |].
           repeat split; assumption.
        -- rewrite tdist_old by (simpl; lia). exact Hlen.
Qed.

(* Any graph walk has at least the recursively defined distance in edges.
   This follows by adding the unit length of each edge and the triangle law. *)
Lemma tree_walk_lower_bound (ps : list nat) :
  forall x path y, Walk (tree_edge ps) x path y ->
    tdist ps x y <= length path - 1.
Proof.
  intros x path y Hwalk. induction Hwalk.
  - rewrite (@g_refl (tdist ps) (tdist_good ps) x). simpl. lia.
  - simpl.
    destruct H as [_ [_ Hedge]].
    pose proof (@g_tri (tdist ps) (tdist_good ps) x y z) as Htri.
    rewrite Hedge in Htri. simpl in IHHwalk. lia.
Qed.

Theorem tdist_is_graph_shortest_path (ps : list nat) :
  valid_parents ps ->
  forall x y, In x (tree_vertices ps) -> In y (tree_vertices ps) ->
    (exists path, Walk (tree_edge ps) x path y /\
       length path = S (tdist ps x y)) /\
    (forall path, Walk (tree_edge ps) x path y ->
       tdist ps x y <= length path - 1).
Proof.
  intros Hvalid x y Hx Hy. split.
  - apply tree_geodesic_walk; assumption.
  - intros path Hpath. exact (tree_walk_lower_bound ps x path y Hpath).
Qed.

(* Algorithmic Theorem 3.3: on the finite tree graph, two farthest-vertex
   sweeps return a diameter.  Ties are handled by [argmax]. *)
Theorem theorem_3_3_graph (ps : list nat) (r : nat) :
  valid_parents ps -> In r (tree_vertices ps) ->
  DiameterPair (tree_vertices ps) (tdist ps)
    (farthest_vertex (tree_vertices ps) 0 (tdist ps) r)
    (farthest_vertex (tree_vertices ps) 0 (tdist ps)
       (farthest_vertex (tree_vertices ps) 0 (tdist ps) r)).
Proof.
  intros Hparents Hr. unfold tree_vertices.
  apply theorem_3_3_algorithm; assumption.
Qed.

(* Relational form: the result holds for every farthest choice, including
   every possible tie-breaking choice in either sweep. *)
Theorem theorem_3_3_graph_relational (ps : list nat) (r s t : nat) :
  valid_parents ps ->
  FarthestChoice (tree_vertices ps) (tdist ps) r s ->
  FarthestChoice (tree_vertices ps) (tdist ps) s t ->
  DiameterPair (tree_vertices ps) (tdist ps) s t.
Proof.
  intros Hparents Hfirst Hsecond.
  exact (theorem_3_3 ps r s t Hparents Hfirst Hsecond).
Qed.

Theorem theorem_3_3_finite_tree (T : FiniteTree) (r : nat) :
  In r (tree_vertices (finite_tree_parents T)) ->
  DiameterPair (tree_vertices (finite_tree_parents T))
    (tdist (finite_tree_parents T))
    (farthest_vertex (tree_vertices (finite_tree_parents T)) 0
       (tdist (finite_tree_parents T)) r)
    (farthest_vertex (tree_vertices (finite_tree_parents T)) 0
       (tdist (finite_tree_parents T))
       (farthest_vertex (tree_vertices (finite_tree_parents T)) 0
          (tdist (finite_tree_parents T)) r)).
Proof.
  intro Hr. apply theorem_3_3_graph; [exact (finite_tree_valid T) | exact Hr].
Qed.

Theorem theorem_3_3_finite_tree_relational
    (T : FiniteTree) (r s t : nat) :
  FarthestChoice (tree_vertices (finite_tree_parents T))
    (tdist (finite_tree_parents T)) r s ->
  FarthestChoice (tree_vertices (finite_tree_parents T))
    (tdist (finite_tree_parents T)) s t ->
  DiameterPair (tree_vertices (finite_tree_parents T))
    (tdist (finite_tree_parents T)) s t.
Proof.
  intros Hfirst Hsecond.
  exact (theorem_3_3_graph_relational (finite_tree_parents T) r s t
    (finite_tree_valid T) Hfirst Hsecond).
Qed.

Print Assumptions tdist_is_graph_shortest_path.
Print Assumptions theorem_3_3_graph.
Print Assumptions theorem_3_3_graph_relational.
Print Assumptions theorem_3_3_finite_tree.
Print Assumptions theorem_3_3_finite_tree_relational.
