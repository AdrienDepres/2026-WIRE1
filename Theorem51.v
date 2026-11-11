From Stdlib Require Import Arith Bool Lia List Sorting.Permutation.
Require Import CorrectionReview Tree33 Theorem36.
Import ListNotations.

(* Theorem 5.1: certificate verification for DASAS.

   An instance is represented by two valid parent lists of
   equal length.  A parent list constructs a tree by repeatedly adjoining a
   new leaf to an old vertex.  The office tree is [pb], and the collaborator
   tree is [pc].  Both therefore have S (length _) vertices. *)

(* ------------------------------------------------------------------------- *)
(* Tree-edge encoding and objective function                                *)
(* ------------------------------------------------------------------------- *)

(* The oriented edge list stores each edge exactly once: the new vertex at
   each parent-list step is paired with the vertex to which it is attached. *)
Fixpoint parent_edges (ps : list nat) : list (nat * nat) :=
  match ps with
  | [] => []
  | p :: rest => (S (length rest), p) :: parent_edges rest
  end.

Lemma parent_edges_length (ps : list nat) :
  length (parent_edges ps) = length ps.
Proof. induction ps; simpl; congruence. Qed.

Lemma tree_vertices_nodup (ps : list nat) : NoDup (tree_vertices ps).
Proof. unfold tree_vertices. apply seq_NoDup. Qed.

Lemma dasas_tree_sizes_equal (pc pb : list nat) :
  length pc = length pb ->
  length (tree_vertices pc) = length (tree_vertices pb).
Proof. intro Hlen. rewrite !tree_vertices_length. now rewrite Hlen. Qed.

Lemma parent_edges_endpoint_bound (ps : list nat) :
  valid_parents ps -> forall x y,
    In (x, y) (parent_edges ps) -> x <= length ps /\ y <= length ps.
Proof.
  induction ps as [|p ps IH]; intros Hvalid x y Hedge.
  - contradiction.
  - destruct Hvalid as [Hp Hvalid]. simpl in Hedge.
    destruct Hedge as [Heq | Hedge].
    + inversion Heq; subst. simpl. split; [lia|lia].
    + destruct (IH Hvalid x y Hedge) as [Hx Hy]. simpl. lia.
Qed.

Lemma parent_edges_first_bound (ps : list nat) :
  forall x y, In (x, y) (parent_edges ps) -> 1 <= x /\ x <= length ps.
Proof.
  induction ps as [|p ps IH]; intros x y Hedge.
  - contradiction.
  - simpl in Hedge. destruct Hedge as [Heq | Hedge].
    + inversion Heq; subst. simpl. lia.
    + destruct (IH x y Hedge) as [Hx Hbound]. simpl. lia.
Qed.

Lemma parent_edges_nodup (ps : list nat) : NoDup (parent_edges ps).
Proof.
  induction ps as [|p ps IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      pose proof (parent_edges_first_bound ps (S (length ps)) p Hin) as [_ Hbound].
      simpl in Hbound. lia.
    + exact IH.
Qed.

Lemma parent_edges_child_gt_parent (ps : list nat) :
  valid_parents ps -> forall child parent,
    In (child, parent) (parent_edges ps) -> parent < child.
Proof.
  induction ps as [|p ps IH]; intros Hvalid child parent Hedge.
  - contradiction.
  - destruct Hvalid as [Hp Hvalid]. simpl in Hedge.
    destruct Hedge as [Heq | Hedge].
    + inversion Heq; subst. simpl. lia.
    + specialize (IH Hvalid child parent Hedge). lia.
Qed.

(* The encoded edges are exactly the undirected unit-distance edges of the
   finite tree from Tree33.v.  This connects the QAP edge sum below to the
   graph-theoretic edge set in the statement of Theorem 5.1. *)
Theorem parent_edges_characterize_tree_edge : forall ps,
  valid_parents ps -> forall x y,
    tree_edge ps x y <->
      In (x, y) (parent_edges ps) \/ In (y, x) (parent_edges ps).
Proof.
  induction ps as [|p ps IH]; intros Hvalid x y.
  - simpl. split.
    + intros Hedge. destruct Hedge as [Hx [Hy Hdist]].
      simpl in Hx, Hy. destruct Hx as [Hx | Hx]; [|contradiction].
      destruct Hy as [Hy | Hy]; [|contradiction]. subst x y.
      rewrite (@g_refl (tdist []) (tdist_good []) 0) in Hdist. discriminate.
    + intros [Hedge | Hedge]; contradiction.
  - destruct Hvalid as [Hp Hvalid].
    rewrite tree_edge_leaf_decomposition by (split; assumption).
    simpl. split.
    + intros [[Hxnew [Hynew Hedge]] | [[Ex Ey] | [Ex Ey]]].
      * destruct (proj1 (IH Hvalid x y) Hedge) as [Hxy | Hyx].
        -- left. right. exact Hxy.
        -- right. right. exact Hyx.
      * subst x y. left. left. reflexivity.
      * subst x y. right. left. reflexivity.
    + intros [Hedge | Hedge].
      * simpl in Hedge. destruct Hedge as [Heq | Hedge].
        -- inversion Heq; subst. right. left. split; reflexivity.
        -- assert (Hbounds := parent_edges_endpoint_bound ps Hvalid x y Hedge).
           destruct Hbounds as [Hx Hy].
           left. split; [lia|]. split; [lia|].
           apply (proj2 (IH Hvalid x y)). now left.
      * simpl in Hedge. destruct Hedge as [Heq | Hedge].
        -- inversion Heq; subst. right. right. split; reflexivity.
        -- assert (Hbounds := parent_edges_endpoint_bound ps Hvalid y x Hedge).
           destruct Hbounds as [Hy Hx].
           left. split; [lia|]. split; [lia|].
           apply tree_edge_sym.
           apply (proj2 (IH Hvalid y x)). now left.
Qed.

Theorem parent_edges_oriented_once : forall ps,
  valid_parents ps -> forall x y,
    tree_edge ps x y ->
    (In (x, y) (parent_edges ps) /\ ~ In (y, x) (parent_edges ps)) \/
    (~ In (x, y) (parent_edges ps) /\ In (y, x) (parent_edges ps)).
Proof.
  intros ps Hvalid x y Hedge.
  destruct (proj1 (parent_edges_characterize_tree_edge ps Hvalid x y) Hedge)
    as [Hxy | Hyx].
  - left. split; [exact Hxy|].
    intro Hyx. pose proof (parent_edges_child_gt_parent ps Hvalid x y Hxy).
    pose proof (parent_edges_child_gt_parent ps Hvalid y x Hyx). lia.
  - right. split; [|exact Hyx].
    intro Hxy. pose proof (parent_edges_child_gt_parent ps Hvalid y x Hyx).
    pose proof (parent_edges_child_gt_parent ps Hvalid x y Hxy). lia.
Qed.

Lemma dasas_edge_cost_symmetric (office sigma : list nat) (u v : nat) :
  tdist office (nth u sigma 0) (nth v sigma 0) =
    tdist office (nth v sigma 0) (nth u sigma 0).
Proof. apply (@g_sym (tdist office) (tdist_good office)). Qed.

(* Sum a distance for each collaborator-tree edge, after moving its endpoints
   through the proposed bijection [sigma] into the office tree.  This is the
   report's objective f(sigma) = sum_{ {a,b} in A_C } d_B(sigma(a),sigma(b)). *)
Fixpoint edge_image_score (office sigma : list nat)
    (es : list (nat * nat)) : nat :=
  match es with
  | [] => 0
  | (u, v) :: rest =>
      tdist office (nth u sigma 0) (nth v sigma 0) +
        edge_image_score office sigma rest
  end.

Definition dasas_score (pc pb sigma : list nat) : nat :=
  edge_image_score pb sigma (parent_edges pc).

Lemma dasas_score_parent_sum (pc pb sigma : list nat) :
  dasas_score pc pb sigma =
    edge_image_score pb sigma (parent_edges pc).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* Certificate relation and verifier                                        *)
(* ------------------------------------------------------------------------- *)

(* Boolean membership, duplicate, and inclusion tests used to check that the
   certificate is a permutation of the office vertices. *)
Fixpoint mem_nat (x : nat) (xs : list nat) : bool :=
  match xs with
  | [] => false
  | y :: rest => Nat.eqb x y || mem_nat x rest
  end.

Lemma mem_nat_true_iff (x : nat) (xs : list nat) :
  mem_nat x xs = true <-> In x xs.
Proof.
  induction xs as [|y ys IH]; simpl.
  - split; [discriminate | contradiction].
  - rewrite orb_true_iff, Nat.eqb_eq, IH. simpl. intuition congruence.
Qed.

Lemma mem_nat_false_iff (x : nat) (xs : list nat) :
  mem_nat x xs = false <-> ~ In x xs.
Proof.
  destruct (mem_nat x xs) eqn:E; simpl.
  - split; [discriminate |]. intro Hnot. exfalso. apply Hnot.
    apply mem_nat_true_iff. exact E.
  - split.
    + intros _ Hin. apply mem_nat_true_iff in Hin. congruence.
    + intros _. reflexivity.
Qed.

Fixpoint nodup_natb (xs : list nat) : bool :=
  match xs with
  | [] => true
  | x :: rest => negb (mem_nat x rest) && nodup_natb rest
  end.

Lemma nodup_natb_correct (xs : list nat) :
  nodup_natb xs = true <-> NoDup xs.
Proof.
  induction xs as [|x xs IH]; simpl.
  - split; [intro; constructor | intro; reflexivity].
  - rewrite andb_true_iff, negb_true_iff, mem_nat_false_iff, IH.
    split.
    + intros [Hnot Hnd]. constructor; assumption.
    + intro H. inversion H; subst. split; assumption.
Qed.

Fixpoint incl_natb (xs ys : list nat) : bool :=
  match xs with
  | [] => true
  | x :: rest => mem_nat x ys && incl_natb rest ys
  end.

Lemma incl_natb_correct (xs ys : list nat) :
  incl_natb xs ys = true <-> incl xs ys.
Proof.
  induction xs as [|x xs IH]; simpl.
  - split.
    + intros _. unfold incl. intros z Hz. contradiction.
    + intros _. reflexivity.
  - rewrite andb_true_iff, mem_nat_true_iff, IH.
    split.
    + intros [Hx Hrest] z [-> | Hz]; [exact Hx|].
      apply Hrest. exact Hz.
    + intro H. split.
      * apply H. now left.
      * intros z Hz. apply H. now right.
Qed.

Definition permutation_check (xs ys : list nat) : bool :=
  nodup_natb xs && incl_natb xs ys && incl_natb ys xs.

Lemma permutation_check_correct (xs ys : list nat) :
  NoDup ys -> (permutation_check xs ys = true <-> Permutation xs ys).
Proof.
  intro Hys. unfold permutation_check.
  rewrite !andb_true_iff, nodup_natb_correct,
    incl_natb_correct, incl_natb_correct.
  split.
  - intros [[Hxs Hxy] Hyx].
    apply NoDup_Permutation; [exact Hxs | exact Hys |].
    intro z. split; [apply Hxy | apply Hyx].
  - intro Hperm. split.
    + split.
      * eapply Permutation_NoDup.
        -- apply Permutation_sym. exact Hperm.
        -- exact Hys.
      * intros z Hz. eapply Permutation_in; [exact Hperm | exact Hz].
    + intros z Hz. eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hz].
Qed.

Definition DASAS_yes (pc pb : list nat) (K : nat) : Prop :=
  valid_parents pc /\ valid_parents pb /\ length pc = length pb /\
  exists sigma,
    Permutation sigma (tree_vertices pb) /\ dasas_score pc pb sigma <= K.

(* The verifier checks the input encodings, equal tree sizes, the certificate
   bijection, and finally the QAP score threshold. *)
Definition dasas_verify (pc pb : list nat) (K : nat)
    (sigma : list nat) : bool :=
  if valid_parents_check pc then
    if valid_parents_check pb then
      if Nat.eqb (length pc) (length pb) then
        if permutation_check sigma (tree_vertices pb) then
          Nat.leb (dasas_score pc pb sigma) K
        else false
      else false
    else false
  else false.

Theorem dasas_verify_correct (pc pb : list nat) (K : nat) (sigma : list nat) :
  dasas_verify pc pb K sigma = true <->
  valid_parents pc /\ valid_parents pb /\ length pc = length pb /\
  Permutation sigma (tree_vertices pb) /\ dasas_score pc pb sigma <= K.
Proof.
  unfold dasas_verify.
  destruct (valid_parents_check pc) eqn:Hpc.
  2: { split; [discriminate|]. intros [Hvalidpc _].
       apply (proj2 (valid_parents_check_correct pc)) in Hvalidpc.
       congruence. }
  destruct (valid_parents_check pb) eqn:Hpb.
  2: { split; [discriminate|]. intros [_ [Hvalidpb _]].
       apply (proj2 (valid_parents_check_correct pb)) in Hvalidpb.
       congruence. }
  assert (Hpcvalid : valid_parents pc) by
    (apply (proj1 (valid_parents_check_correct pc)); exact Hpc).
  assert (Hpbvalid : valid_parents pb) by
    (apply (proj1 (valid_parents_check_correct pb)); exact Hpb).
  destruct (Nat.eqb (length pc) (length pb)) eqn:Hlength.
  2: { split; [discriminate|]. intros [_ [_ [Hlen _]]].
       apply Nat.eqb_neq in Hlength. congruence. }
  apply Nat.eqb_eq in Hlength.
  destruct (permutation_check sigma (tree_vertices pb)) eqn:Hperm.
  2: { split; [discriminate|]. intros [_ [_ [_ [Hperm' _]]]].
       pose proof (proj2 (permutation_check_correct sigma (tree_vertices pb)
         (tree_vertices_nodup pb)) Hperm') as Htrue.
       congruence. }
  apply (proj1 (permutation_check_correct sigma (tree_vertices pb)
    (tree_vertices_nodup pb))) in Hperm.
  destruct (Nat.leb (dasas_score pc pb sigma) K) eqn:Hscore.
  2: { split; [discriminate|]. intros [_ [_ [_ [_ Hbound]]]].
       apply Nat.leb_gt in Hscore. lia. }
  apply Nat.leb_le in Hscore.
  split.
  - intros _. repeat split; assumption.
  - intros _. reflexivity.
Qed.

Theorem theorem_5_1_verifier (pc pb : list nat) (K : nat) :
  DASAS_yes pc pb K <-> exists sigma, dasas_verify pc pb K sigma = true.
Proof.
  unfold DASAS_yes. split.
  - intros [Hpc [Hpb [Hlen [sigma [Hperm Hscore]]]]].
    exists sigma. apply (proj2 (dasas_verify_correct pc pb K sigma)).
    repeat split; assumption.
  - intros [sigma Hverify].
    apply (proj1 (dasas_verify_correct pc pb K sigma)) in Hverify.
    destruct Hverify as [Hpc [Hpb [Hlen [Hperm Hscore]]]].
    repeat split; try assumption. eauto.
Qed.

Theorem theorem_5_1 (pc pb : list nat) (K : nat) :
  DASAS_yes pc pb K <-> exists sigma, dasas_verify pc pb K sigma = true.
Proof. apply theorem_5_1_verifier. Qed.

(* The certificate contains one office label for each office, as required by
   the report's family of permutations S_n. *)
Theorem dasas_certificate_length (pc pb sigma : list nat) :
  Permutation sigma (tree_vertices pb) -> length sigma = S (length pb).
Proof.
  intro Hperm. pose proof (Permutation_length Hperm) as Hlen.
  rewrite tree_vertices_length in Hlen. exact Hlen.
Qed.

Theorem dasas_accepted_certificate_length (pc pb : list nat) (K : nat)
    (sigma : list nat) :
  dasas_verify pc pb K sigma = true -> length sigma = S (length pb).
Proof.
  intro Hverify.
  apply (proj1 (dasas_verify_correct pc pb K sigma)) in Hverify.
  destruct Hverify as [_ [_ [_ [Hperm _]]]].
  exact (dasas_certificate_length pc pb sigma Hperm).
Qed.

Theorem dasas_edge_images_are_offices (pc pb sigma : list nat) :
  valid_parents pc -> length pc = length pb ->
  Permutation sigma (tree_vertices pb) ->
  forall u v, In (u, v) (parent_edges pc) ->
    In (nth u sigma 0) (tree_vertices pb) /\
    In (nth v sigma 0) (tree_vertices pb).
Proof.
  intros Hpc Hlen Hperm u v Hedge.
  pose proof (parent_edges_endpoint_bound pc Hpc u v Hedge) as [Hu Hv].
  pose proof (dasas_certificate_length pc pb sigma Hperm) as Hsiglen.
  assert (Huindex : u < length sigma) by (rewrite Hsiglen; lia).
  assert (Hvindex : v < length sigma) by (rewrite Hsiglen; lia).
  split.
  - eapply Permutation_in.
    + exact Hperm.
    + apply nth_In. exact Huindex.
  - eapply Permutation_in.
    + exact Hperm.
    + apply nth_In. exact Hvindex.
Qed.

(* ------------------------------------------------------------------------- *)
(* Explicit polynomial structural-work model                                 *)
(* ------------------------------------------------------------------------- *)

(* The following cost model counts list-cell visits and treats comparisons,
   additions, and Boolean operations as unit-cost structural steps, as in the
   report's O(n^3) verifier argument.  [mem_nat_work] is the worst-case scan
   cost for one membership test. *)
Fixpoint nodup_check_work (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | _ :: rest => S (length rest) + nodup_check_work rest
  end.

Lemma nodup_check_work_bound (xs : list nat) :
  nodup_check_work xs <= (length xs) ^ 2.
Proof.
  induction xs as [|x xs IH]; simpl.
  - lia.
  - cbn [Nat.pow] in *. nia.
Qed.

Fixpoint inclusion_check_work (xs : list nat) (target_length : nat) : nat :=
  match xs with
  | [] => 0
  | _ :: rest => S target_length + inclusion_check_work rest target_length
  end.

Lemma inclusion_check_work_exact (xs : list nat) (m : nat) :
  inclusion_check_work xs m = length xs * S m.
Proof. induction xs; simpl; lia. Qed.

(* One parent-validation step computes the remaining suffix length, compares
   the proposed parent with that bound, and recurses.  The same suffix-length
   cost models construction of the indexed edge list below. *)
Fixpoint parent_list_pass_work (ps : list nat) : nat :=
  match ps with
  | [] => 0
  | _ :: rest => S (length rest) + parent_list_pass_work rest
  end.

Lemma parent_list_pass_work_bound (ps : list nat) :
  parent_list_pass_work ps <= (length ps) ^ 2.
Proof.
  induction ps as [|p ps IH]; simpl.
  - lia.
  - cbn [Nat.pow] in *. nia.
Qed.

Definition permutation_check_work (xs ys : list nat) : nat :=
  nodup_check_work xs +
  inclusion_check_work xs (length ys) +
  inclusion_check_work ys (length xs).

Lemma permutation_check_work_bound (xs ys : list nat) :
  permutation_check_work xs ys <=
    (length xs) ^ 2 + length xs * S (length ys) +
      length ys * S (length xs).
Proof.
  unfold permutation_check_work.
  rewrite inclusion_check_work_exact, inclusion_check_work_exact.
  pose proof (nodup_check_work_bound xs). lia.
Qed.

(* A score term performs one distance query, two [nth] lookups in the
   certificate, and one addition.  Each lookup scans at most [length sigma]
   cells. *)
Fixpoint edge_score_work (office sigma : list nat)
    (es : list (nat * nat)) : nat :=
  match es with
  | [] => 0
  | (u, v) :: rest =>
      tree_distance_work office (nth u sigma 0) (nth v sigma 0) +
        2 * length sigma + 1 + edge_score_work office sigma rest
  end.

Lemma edge_score_work_bound (office sigma : list nat) (es : list (nat * nat)) :
  edge_score_work office sigma es <=
    length es * (S (length office) + 2 * length sigma + 1).
Proof.
  induction es as [|[u v] es IH]; simpl.
  - lia.
  - pose proof (tree_distance_work_bound office (nth u sigma 0) (nth v sigma 0)). lia.
Qed.

Definition dasas_verifier_work (pc pb sigma : list nat) : nat :=
  parent_list_pass_work pc + parent_list_pass_work pb +
  parent_list_pass_work pc +
  2 * S (length pb) + length pc + length pb +
  permutation_check_work sigma (tree_vertices pb) +
  edge_score_work pb sigma (parent_edges pc) + 4.

Definition dasas_input_size (pc pb sigma : list nat) : nat :=
  2 + length pc + length pb + length sigma.

(* This bound applies to every input and certificate, including rejected
   ones.  It accounts for the suffix lengths read by parent validation and
   edge-list construction, building the canonical office-vertex list,
   checking the bijection, and evaluating all edge distances.  Comparisons
   and arithmetic are unit-cost, as in the report's polynomial-time argument. *)
Theorem dasas_verifier_polynomial_work (pc pb sigma : list nat) :
  dasas_verifier_work pc pb sigma <=
    12 * (dasas_input_size pc pb sigma) ^ 2 +
      8 * dasas_input_size pc pb sigma + 8.
Proof.
  unfold dasas_input_size.
  set (n := 2 + length pc + length pb + length sigma).
  assert (Hpc : length pc <= n) by (unfold n; lia).
  assert (Hpb : S (length pb) <= n) by (unfold n; lia).
  assert (Hpb2 : S (S (length pb)) <= n) by (unfold n; lia).
  assert (Hsig : S (length sigma) <= n) by (unfold n; lia).
  pose proof (parent_list_pass_work_bound pc) as Hpcwork.
  pose proof (parent_list_pass_work_bound pb) as Hpbwork.
  pose proof (permutation_check_work_bound sigma (tree_vertices pb)) as Hpermwork.
  rewrite tree_vertices_length in Hpermwork.
  pose proof (edge_score_work_bound pb sigma (parent_edges pc)) as Hscorework.
  rewrite parent_edges_length in Hscorework.
  assert (Hpcpow : (length pc) ^ 2 <= n ^ 2).
  { cbn [Nat.pow].
    apply Nat.mul_le_mono; lia. }
  assert (Hpbpow : (length pb) ^ 2 <= n ^ 2).
  { cbn [Nat.pow].
    apply Nat.mul_le_mono; lia. }
  assert (Hpcpass : parent_list_pass_work pc <= n ^ 2).
  { eapply Nat.le_trans; [exact Hpcwork|exact Hpcpow]. }
  assert (Hpbpass : parent_list_pass_work pb <= n ^ 2).
  { eapply Nat.le_trans; [exact Hpbwork|exact Hpbpow]. }
  assert (Hpermle : permutation_check_work sigma (tree_vertices pb) <= 3 * n ^ 2).
  { eapply Nat.le_trans; [exact Hpermwork|].
    assert (Hs : length sigma <= n) by lia.
    assert (Hs2 : length sigma * length sigma <= n * n).
    { apply Nat.mul_le_mono; assumption. }
    assert (Hprod1 : length sigma * S (S (length pb)) <= n * n).
    { apply Nat.mul_le_mono; [exact Hs|exact Hpb2]. }
    assert (Hprod2 : S (length pb) * S (length sigma) <= n * n).
    { apply Nat.mul_le_mono; [exact Hpb|exact Hsig]. }
    cbn [Nat.pow]. lia. }
  assert (Hscorele : edge_score_work pb sigma (parent_edges pc) <=
      3 * n ^ 2 + n).
  { eapply Nat.le_trans; [exact Hscorework|].
    assert (Hs : length sigma <= n) by lia.
    assert (Hfactor : S (length pb) + 2 * length sigma + 1 <= 3 * n + 1)
      by lia.
    assert (Hprod : length pc *
      (S (length pb) + 2 * length sigma + 1) <= n * (3 * n + 1)).
    { apply Nat.mul_le_mono; assumption. }
    cbn [Nat.pow]. nia. }
  unfold dasas_verifier_work.
  cbn [Nat.pow] in *.
  lia.
Qed.

Print Assumptions theorem_5_1_verifier.
Print Assumptions theorem_5_1.
Print Assumptions dasas_verifier_polynomial_work.
