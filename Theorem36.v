From Stdlib Require Import Arith Bool Lia List Sorting.Permutation.
Require Import CorrectionReview Tree33.
Import ListNotations.

(* The chain on n collaborators is represented by the consecutive indices
   0,...,n-1.  A placement is therefore a list of the office vertices, in
   collaborator order. *)
Fixpoint path_score (ps order : list nat) : nat :=
  match order with
  | [] => 0
  | x :: rest =>
      match rest with
      | [] => 0
      | y :: _ => tdist ps x y + path_score ps rest
      end
  end.

Definition PathPlacement (ps order : list nat) : Prop :=
  Permutation order (tree_vertices ps).

(* ------------------------------------------------------------------------- *)
(* List and distance lemmas for adding one leaf                              *)
(* ------------------------------------------------------------------------- *)

Definition other_vertex (ps : list nat) (p : nat) : nat :=
  if Nat.eqb p 0 then 1 else 0.

(* Distance equations for the new leaf in a parent-list tree. *)
Lemma tdist_new_leaf_l (ps : list nat) (p y : nat) :
  y <= length ps ->
  tdist (p :: ps) (S (length ps)) y = S (tdist ps p y).
Proof.
  intro Hy. change (ext (tdist ps) (S (length ps)) p
    (S (length ps)) y = S (tdist ps p y)).
  unfold ext. rewrite Nat.eqb_refl.
  assert (E : Nat.eqb y (S (length ps)) = false).
  { apply Nat.eqb_neq. lia. }
  now rewrite E.
Qed.

Lemma tdist_new_leaf_r (ps : list nat) (p x : nat) :
  x <= length ps ->
  tdist (p :: ps) x (S (length ps)) = S (tdist ps x p).
Proof.
  intro Hx. change (ext (tdist ps) (S (length ps)) p
    x (S (length ps)) = S (tdist ps x p)).
  unfold ext.
  assert (E : Nat.eqb x (S (length ps)) = false).
  { apply Nat.eqb_neq. lia. }
  now rewrite E, Nat.eqb_refl.
Qed.

Lemma path_score_old (ps : list nat) (parent : nat) (order : list nat) :
  (forall z, In z order -> z <= length ps) ->
  path_score (parent :: ps) order = path_score ps order.
Proof.
  induction order as [|x order IH]; intro Hb; [reflexivity|].
  destruct order as [|y ys]; [reflexivity|].
  change (tdist (parent :: ps) x y + path_score (parent :: ps) (y :: ys) =
    tdist ps x y + path_score ps (y :: ys)).
  rewrite tdist_old by (apply Hb; simpl; auto).
  rewrite IH by (intros z Hz; apply Hb; simpl; now right).
  reflexivity.
Qed.

Lemma tree_vertices_leaf (ps : list nat) (p : nat) :
  tree_vertices (p :: ps) = tree_vertices ps ++ [S (length ps)].
Proof.
  unfold tree_vertices. rewrite seq_S. simpl. f_equal.
Qed.

Lemma in_tree_vertices_bound (ps : list nat) (x : nat) :
  In x (tree_vertices ps) -> x <= length ps.
Proof.
  unfold tree_vertices. intro H. apply in_seq in H. lia.
Qed.

Lemma tree_vertices_leaf_cases (ps : list nat) (p x : nat) :
  In x (tree_vertices (p :: ps)) ->
  x = S (length ps) \/ In x (tree_vertices ps).
Proof.
  rewrite tree_vertices_leaf. intro H. apply in_app_or in H.
  destruct H as [H | H].
  - right. exact H.
  - simpl in H. destruct H as [H | H].
    + left. now symmetry.
    + contradiction.
Qed.

Lemma in_tree_vertices_leaf_old (ps : list nat) (p x : nat) :
  In x (tree_vertices ps) -> In x (tree_vertices (p :: ps)).
Proof.
  rewrite tree_vertices_leaf. intro H. apply in_or_app. now left.
Qed.

Lemma tree_vertices_leaf_new (ps : list nat) (p : nat) :
  In (S (length ps)) (tree_vertices (p :: ps)).
Proof.
  rewrite tree_vertices_leaf. apply in_or_app. right. simpl. now left.
Qed.

Fixpoint insert_after (p leaf : nat) (xs : list nat) : list nat :=
  match xs with
  | [] => [leaf]
  | x :: rest =>
      if Nat.eqb x p then x :: leaf :: rest
      else x :: insert_after p leaf rest
  end.

Lemma insert_after_unfold (p leaf x : nat) (xs : list nat) :
  insert_after p leaf (x :: xs) =
    if Nat.eqb x p then x :: leaf :: xs else x :: insert_after p leaf xs.
Proof. reflexivity. Qed.

Lemma last_cons_nonempty (x : nat) (xs : list nat) (d : nat) :
  xs <> [] -> last (x :: xs) d = last xs d.
Proof. destruct xs; simpl; congruence. Qed.

Lemma insert_after_nonempty (p leaf : nat) (xs : list nat) :
  insert_after p leaf xs <> [].
Proof.
  destruct xs as [|x xs]; [simpl; discriminate|].
  unfold insert_after at 1. destruct (Nat.eqb x p); discriminate.
Qed.

Lemma move_head_to_end (x : nat) (xs : list nat) :
  Permutation (x :: xs) (xs ++ [x]).
Proof.
  induction xs as [|y ys IH].
  - simpl. constructor. constructor.
  - simpl. eapply Permutation_trans.
    + apply perm_swap.
    + apply perm_skip. exact IH.
Qed.

Lemma insert_after_permutation (p leaf : nat) (xs : list nat) :
  In p xs -> Permutation (insert_after p leaf xs) (xs ++ [leaf]).
Proof.
  induction xs as [|x xs IH]; intro Hp.
  - contradiction.
  - simpl in Hp. destruct (Nat.eqb x p) eqn:Ex.
    + apply Nat.eqb_eq in Ex. subst x. cbn [insert_after].
      rewrite Nat.eqb_refl. simpl. apply perm_skip. apply move_head_to_end.
    + apply Nat.eqb_neq in Ex. assert (Htail : In p xs).
      { destruct Hp as [Hp | Hp]; [congruence | exact Hp]. }
      specialize (IH Htail). cbn [insert_after].
      assert (E : Nat.eqb x p = false) by (apply Nat.eqb_neq; exact Ex).
      rewrite E. simpl. apply perm_skip. exact IH.
Qed.

Lemma NoDup_app_singleton (xs : list nat) (x : nat) :
  NoDup xs -> ~ In x xs -> NoDup (xs ++ [x]).
Proof.
  intros Hnd. induction Hnd; intro Hx.
  - simpl. constructor; [simpl; tauto | constructor].
  - simpl. constructor.
    + intro Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * apply H. exact Hin.
      * simpl in Hin. destruct Hin as [Heq | Hfalse].
        -- subst x0. apply Hx. now left.
        -- contradiction.
    + apply IHHnd. intro Hin. apply Hx. now right.
Qed.

Lemma insert_after_nodup (p leaf : nat) (xs : list nat) :
  NoDup xs -> In p xs -> ~ In leaf xs ->
  NoDup (insert_after p leaf xs).
Proof.
  intros Hnd Hp Hleaf.
  apply Permutation_NoDup with (l := xs ++ [leaf]).
  - apply Permutation_sym. now apply insert_after_permutation.
  - apply NoDup_app_singleton; assumption.
Qed.

Lemma insert_after_head (p leaf : nat) (xs : list nat) :
  In p xs -> hd_error (insert_after p leaf xs) = hd_error xs.
Proof.
  induction xs as [|x xs IH]; intro Hp; [contradiction|].
  simpl. destruct (Nat.eqb x p); reflexivity.
Qed.

Lemma insert_after_hd (p leaf : nat) (xs : list nat) :
  xs <> [] -> In p xs -> hd 0 (insert_after p leaf xs) = hd 0 xs.
Proof.
  destruct xs as [|x xs]; intros Hne Hp; [contradiction|].
  cbn [insert_after]. destruct (Nat.eqb x p); reflexivity.
Qed.

Lemma path_score_cons_nonempty (ps : list nat) (x : nat) (ys : list nat) :
  ys <> [] ->
  path_score ps (x :: ys) = tdist ps x (hd 0 ys) + path_score ps ys.
Proof. destruct ys; intros H; [contradiction|reflexivity]. Qed.

Lemma path_score_app (ps xs ys : list nat) :
  path_score ps (xs ++ ys) =
    path_score ps xs + path_score ps ys +
      (match xs, ys with
       | [], _ => 0
       | _, [] => 0
       | _, _ => tdist ps (last xs 0) (hd 0 ys)
       end).
Proof.
  revert ys. induction xs as [|x xs IH]; intros ys; destruct ys as [|y ys].
  - simpl. lia.
  - simpl. lia.
  - rewrite app_nil_r. simpl. lia.
  - destruct xs as [|z zs].
    + simpl. lia.
    + change (tdist ps x z + path_score ps ((z :: zs) ++ y :: ys) =
        (tdist ps x z + path_score ps (z :: zs)) +
          path_score ps (y :: ys) + tdist ps (last (z :: zs) 0) y).
      rewrite (IH (y :: ys)). simpl. lia.
Qed.

Lemma hd_in_nonempty (xs : list nat) : xs <> [] -> In (hd 0 xs) xs.
Proof. destruct xs; simpl; intros; [contradiction|now left]. Qed.

Lemma last_in_nonempty (xs : list nat) : xs <> [] -> In (last xs 0) xs.
Proof.
  induction xs as [|x xs IH]; intro H; [contradiction|].
  destruct xs as [|y ys].
  - simpl. now left.
  - simpl. right. apply IH. discriminate.
Qed.

Lemma hd_app_nonempty (xs ys : list nat) :
  xs <> [] -> hd 0 (xs ++ ys) = hd 0 xs.
Proof. destruct xs; simpl; intros; [contradiction|reflexivity]. Qed.

Lemma last_app_nonempty (xs ys : list nat) :
  ys <> [] -> last (xs ++ ys) 0 = last ys 0.
Proof.
  induction xs as [|x xs IH]; intros Hys; [reflexivity|].
  assert (Hne : xs ++ ys <> []).
  { intro E. apply app_eq_nil in E. destruct E as [_ Eys]. contradiction. }
  change (last (x :: (xs ++ ys)) 0 = last ys 0).
  rewrite last_cons_nonempty by exact Hne.
  apply IH. exact Hys.
Qed.

Lemma tree_vertices_nonempty (ps : list nat) : tree_vertices ps <> [].
Proof. unfold tree_vertices. destruct ps; simpl; discriminate. Qed.

Lemma permutation_list_nonempty (xs ys : list nat) :
  Permutation xs ys -> ys <> [] -> xs <> [].
Proof.
  intros Hperm Hys Heq. subst xs.
  pose proof (Permutation_length Hperm) as Hlen.
  destruct ys; [contradiction|simpl in Hlen; discriminate].
Qed.

Lemma insert_after_last (p leaf : nat) (xs : list nat) :
  In p xs -> p <> last xs 0 ->
  last (insert_after p leaf xs) 0 = last xs 0.
Proof.
  induction xs as [|x xs IH]; intros Hp Hnot; [contradiction|].
  destruct xs as [|y ys].
  - simpl in Hp. destruct Hp as [Hp | Hfalse]; [subst p | contradiction].
    simpl in Hnot. contradiction.
  - simpl in Hp. destruct (Nat.eqb x p) eqn:Ecmp.
    + apply Nat.eqb_eq in Ecmp. subst p.
      rewrite insert_after_unfold, Nat.eqb_refl. simpl. reflexivity.
    + assert (Ex : x <> p) by (apply Nat.eqb_neq; exact Ecmp).
      destruct Hp as [Hp | Hp]; [congruence|].
      destruct ys as [|z zs].
      * simpl in Hp. destruct Hp as [Hp | Hfalse]; [subst p | contradiction].
        simpl in Hnot. contradiction.
      * rewrite insert_after_unfold, Ecmp.
        rewrite last_cons_nonempty by apply insert_after_nonempty.
        rewrite last_cons_nonempty by discriminate.
        apply IH; [exact Hp | simpl in Hnot; exact Hnot].
Qed.

Lemma insert_after_score (ps : list nat) (p leaf : nat) (xs : list nat) :
  leaf = S (length ps) ->
  In p xs -> p <> last xs 0 ->
  (forall z, In z xs -> z <= length ps) ->
  path_score (p :: ps) (insert_after p leaf xs) =
    path_score ps xs + 2.
Proof.
  induction xs as [|x xs IH]; intros Eleaf Hp Hnot Hbounds; [contradiction|].
  subst leaf.
  destruct xs as [|y ys].
  - simpl in Hp. destruct Hp as [Hp | Hfalse]; [subst p | contradiction].
    simpl in Hnot. contradiction.
  - simpl in Hp. destruct (Nat.eqb x p) eqn:Ex.
    + apply Nat.eqb_eq in Ex. subst x.
      rewrite insert_after_unfold, Nat.eqb_refl.
      change (tdist (p :: ps) p (S (length ps)) +
        (tdist (p :: ps) (S (length ps)) y +
         path_score (p :: ps) (y :: ys)) =
        (tdist ps p y + path_score ps (y :: ys)) + 2).
      rewrite tdist_new_leaf_r by (apply Hbounds; simpl; auto).
      rewrite tdist_new_leaf_l by (apply Hbounds; simpl; auto).
      assert (Htail_bounds : forall z, In z (y :: ys) -> z <= length ps).
      { intros z Hz. apply Hbounds. simpl.
        destruct Hz as [Hz | Hz]; [right; left | right; right]; exact Hz. }
      rewrite (path_score_old ps p (y :: ys) Htail_bounds).
      rewrite (@g_refl (tdist ps) (tdist_good ps) p). lia.
    + apply Nat.eqb_neq in Ex.
      destruct Hp as [Hp | Hp]; [congruence|].
      assert (Htail_bounds : forall z, In z (y :: ys) -> z <= length ps).
      { intros z Hz. apply Hbounds. simpl.
        destruct Hz as [Hz | Hz]; [right; left | right; right]; exact Hz. }
      rewrite insert_after_unfold, (proj2 (Nat.eqb_neq x p) Ex).
      destruct (Nat.eqb y p) eqn:Eyp.
      * apply Nat.eqb_eq in Eyp. subst y.
        destruct ys as [|z zs].
        -- simpl in Hnot. contradiction.
        -- rewrite insert_after_unfold, Nat.eqb_refl.
           change (tdist (p :: ps) x p +
             (tdist (p :: ps) p (S (length ps)) +
              (tdist (p :: ps) (S (length ps)) z +
               path_score (p :: ps) (z :: zs))) =
             tdist ps x p +
             (tdist ps p z + path_score ps (z :: zs)) + 2).
           rewrite tdist_new_leaf_r by (apply Hbounds; simpl; auto; lia).
           rewrite tdist_new_leaf_l by (apply Hbounds; simpl; auto; lia).
           rewrite (path_score_old ps p (z :: zs)).
           2: { intros q Hq. apply Hbounds. simpl. right; right. simpl.
                destruct Hq as [-> | Hq]; [now left|now right]. }
           rewrite tdist_old by (apply Hbounds; simpl; auto; lia).
           rewrite (@g_refl (tdist ps) (tdist_good ps) p). lia.
      * apply Nat.eqb_neq in Eyp.
        assert (Hnot_tail : p <> last (y :: ys) 0).
        { simpl in Hnot. exact Hnot. }
        change (path_score (p :: ps)
          (x :: insert_after p (S (length ps)) (y :: ys)) =
          path_score ps (x :: y :: ys) + 2).
        rewrite path_score_cons_nonempty by apply insert_after_nonempty.
        rewrite insert_after_hd; [| discriminate | exact Hp].
        cbn [path_score].
        rewrite tdist_old by (apply Hbounds; simpl; auto).
        rewrite (IH eq_refl Hp Hnot_tail Htail_bounds). simpl. lia.
Qed.

(* Filtering a permutation by a Boolean predicate preserves permutation. *)
Lemma Permutation_refl_nat (xs : list nat) : Permutation xs xs.
Proof. induction xs; [constructor|constructor; assumption]. Qed.

Lemma Permutation_filter_nat (f : nat -> bool) (xs ys : list nat) :
  Permutation xs ys -> Permutation (filter f xs) (filter f ys).
Proof.
  intro H. induction H as
    [| x l l' Hperm IH | x y l | l l' l'' H1 IH1 H2 IH2].
  - constructor.
  - simpl. destruct (f x); simpl.
    + constructor. exact IH.
    + exact IH.
  - simpl. destruct (f x) eqn:Ex; destruct (f y) eqn:Ey; simpl.
    + apply perm_swap.
    + apply Permutation_refl_nat.
    + apply Permutation_refl_nat.
    + apply Permutation_refl_nat.
  - eapply Permutation_trans; eassumption.
Qed.

Lemma filter_identity_of_notin (f : nat -> bool) (xs : list nat) :
  (forall x, In x xs -> f x = true) -> filter f xs = xs.
Proof.
  induction xs as [|x xs IH]; intro H; [reflexivity|].
  simpl. rewrite H by (simpl; auto). f_equal. apply IH.
  intros y Hy. apply H. simpl. now right.
Qed.

Lemma NoDup_middle_absent (xs : list nat) (x : nat) (ys : list nat) :
  NoDup (xs ++ x :: ys) -> ~ In x xs /\ ~ In x ys.
Proof.
  induction xs as [|z zs IH]; intro Hnd.
  - simpl in Hnd. inversion Hnd; subst. split; [tauto|assumption].
  - simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnot Htail].
    destruct (IH Htail) as [Hleft Hright]. split.
    + intro Hin. simpl in Hin. destruct Hin as [E | Hin].
      * subst z. apply Hnot. apply in_or_app. right. simpl. now left.
      * exact (Hleft Hin).
    + exact Hright.
Qed.

Lemma permutation_remove_leaf (ps : list nat) (p : nat) (order : list nat) :
  valid_parents (p :: ps) ->
  Permutation order (tree_vertices (p :: ps)) ->
  exists pre post,
    order = pre ++ S (length ps) :: post /\
    Permutation (pre ++ post) (tree_vertices ps).
Proof.
  intros Hvalid Hperm.
  set (leaf := S (length ps)).
  assert (Hnd : NoDup order).
  { apply Permutation_NoDup with (l := tree_vertices (p :: ps));
      [apply Permutation_sym; exact Hperm|].
    unfold tree_vertices. apply seq_NoDup. }
  assert (Hleaf : In leaf order).
  { eapply Permutation_in; [apply Permutation_sym; exact Hperm|].
    rewrite tree_vertices_leaf.
    apply in_or_app. right. simpl. now left. }
  destruct (in_split leaf order Hleaf) as [pre [post Horder]].
  exists pre, post. split; [exact Horder|].
  assert (Hmiddle : NoDup (pre ++ leaf :: post)).
  { rewrite <- Horder. exact Hnd. }
  destruct (NoDup_middle_absent pre leaf post Hmiddle) as [Hpre Hpost].
  assert (Hfilter_order :
    filter (fun z => negb (Nat.eqb z leaf)) order = pre ++ post).
  { rewrite Horder, filter_app. simpl. rewrite Nat.eqb_refl. simpl.
    assert (Hfpre : filter (fun z => negb (Nat.eqb z leaf)) pre = pre).
    { apply filter_identity_of_notin. intros z Hz.
      apply negb_true_iff, Nat.eqb_neq. intro E. subst z. contradiction. }
    assert (Hfpost : filter (fun z => negb (Nat.eqb z leaf)) post = post).
    { apply filter_identity_of_notin. intros z Hz.
      apply negb_true_iff, Nat.eqb_neq. intro E. subst z. contradiction. }
    rewrite Hfpre, Hfpost. reflexivity. }
  assert (Hfilter_vertices :
    filter (fun z => negb (Nat.eqb z leaf)) (tree_vertices (p :: ps)) =
      tree_vertices ps).
  { rewrite tree_vertices_leaf, filter_app. simpl. rewrite Nat.eqb_refl. simpl.
    assert (Hfold : filter (fun z => negb (Nat.eqb z leaf))
        (tree_vertices ps) = tree_vertices ps).
    { apply filter_identity_of_notin. intros z Hz.
      apply negb_true_iff, Nat.eqb_neq. intro E. subst z.
      pose proof (in_tree_vertices_bound ps leaf Hz). unfold leaf in *. lia. }
    unfold tree_vertices in Hfold |- *. simpl in Hfold. simpl.
    rewrite app_nil_r. exact Hfold. }
  pose proof (Permutation_filter_nat
    (fun z => negb (Nat.eqb z leaf)) order
    (tree_vertices (p :: ps)) Hperm) as Hfiltered.
  rewrite Hfilter_order, Hfilter_vertices in Hfiltered. exact Hfiltered.
Qed.

Lemma placement_vertex_bound (ps order : list nat) :
  Permutation order (tree_vertices ps) ->
  forall z, In z order -> z <= length ps.
Proof.
  intros Hperm z Hz. apply in_tree_vertices_bound.
  eapply Permutation_in; [exact Hperm|exact Hz].
Qed.

Lemma in_tree_vertices_of_bound (ps : list nat) (x : nat) :
  x <= length ps -> In x (tree_vertices ps).
Proof. intro H. unfold tree_vertices. apply in_seq. lia. Qed.

Lemma other_vertex_spec (ps : list nat) (p : nat) :
  0 < length ps -> p <= length ps ->
  other_vertex ps p <= length ps /\ other_vertex ps p <> p.
Proof.
  intros Hlen Hp. unfold other_vertex.
  destruct (Nat.eqb p 0) eqn:E.
  - apply Nat.eqb_eq in E. subst p. simpl. lia.
  - apply Nat.eqb_neq in E. simpl. lia.
Qed.

Lemma path_score_prepend_leaf (ps : list nat) (p : nat) (order : list nat) :
  order <> [] ->
  (forall z, In z order -> z <= length ps) ->
  path_score (p :: ps) (S (length ps) :: order) =
    path_score ps order + 1 + tdist ps p (hd 0 order).
Proof.
  intros Hne Hb.
  rewrite path_score_cons_nonempty by exact Hne.
  rewrite tdist_new_leaf_l by (apply Hb; apply hd_in_nonempty; exact Hne).
  rewrite path_score_old with (parent := p) (order := order) by exact Hb.
  lia.
Qed.

Lemma path_score_append_leaf (ps : list nat) (p : nat) (order : list nat) :
  order <> [] ->
  (forall z, In z order -> z <= length ps) ->
  path_score (p :: ps) (order ++ [S (length ps)]) =
    path_score ps order + 1 + tdist ps (last order 0) p.
Proof.
  intros Hne Hb.
  destruct order as [|x xs]; [contradiction|].
  rewrite path_score_app.
  change (path_score (p :: ps) (x :: xs) + path_score (p :: ps) [S (length ps)] +
    tdist (p :: ps) (last (x :: xs) 0) (S (length ps)) =
      path_score ps (x :: xs) + 1 + tdist ps (last (x :: xs) 0) p).
  rewrite path_score_old with (parent := p) (order := x :: xs) by exact Hb.
  rewrite (@tdist_new_leaf_r ps p (last (x :: xs) 0)) by
    (apply Hb; apply last_in_nonempty; discriminate).
  simpl. lia.
Qed.

Lemma permutation_prepend_leaf (ps : list nat) (leaf : nat) (order : list nat) :
  Permutation order (tree_vertices ps) ->
  Permutation (leaf :: order) (tree_vertices ps ++ [leaf]).
Proof.
  intro Hperm. eapply Permutation_trans.
  - apply perm_skip. exact Hperm.
  - apply move_head_to_end.
Qed.

Lemma permutation_append_leaf (ps : list nat) (leaf : nat) (order : list nat) :
  Permutation order (tree_vertices ps) ->
  Permutation (order ++ [leaf]) (tree_vertices ps ++ [leaf]).
Proof.
  intro Hperm. apply Permutation_app; [exact Hperm|].
  constructor. constructor.
Qed.

(* ------------------------------------------------------------------------- *)
(* Theorem 3.1: lower bound by counting the tree edges crossed              *)
(* ------------------------------------------------------------------------- *)

(* Every Hamilton path through the offices pays at least twice each tree
   edge, except for the edges on the path between its own endpoints.  This
   list-induction lemma is the quantitative form used below. *)
Theorem path_score_lower_bound : forall ps,
  valid_parents ps -> forall order,
    Permutation order (tree_vertices ps) ->
    2 * length ps <=
      path_score ps order + tdist ps (hd 0 order) (last order 0).
Proof.
  induction ps as [|p ps IH]; intros Hvalid order Hperm.
  - assert (Hlen : length order = 1).
    { pose proof (Permutation_length Hperm) as H.
      unfold tree_vertices in H. simpl in H. exact H. }
    assert (Hzero : In 0 order).
    { eapply Permutation_in; [apply Permutation_sym; exact Hperm|].
      unfold tree_vertices. simpl. now left. }
    destruct order as [|x xs]; [simpl in Hlen; discriminate|].
    destruct xs as [|y ys]; [|simpl in Hlen; lia].
    simpl in Hzero. destruct Hzero as [->|[]].
    simpl. lia.
  - destruct Hvalid as [Hp HvalidOld].
    destruct (permutation_remove_leaf ps p order (conj Hp HvalidOld) Hperm)
      as [pre [post [Horder Holdperm]]].
    subst order.
    assert (Hold_nonempty : pre ++ post <> []).
    { eapply permutation_list_nonempty; [exact Holdperm|apply tree_vertices_nonempty]. }
    destruct pre as [|a pre].
    + assert (Hpost : post <> []).
      { simpl in Hold_nonempty. exact Hold_nonempty. }
      assert (Hfirst : hd 0 post <= length ps).
      { apply placement_vertex_bound with (order := post); [exact Holdperm|].
        apply hd_in_nonempty. exact Hpost. }
      assert (Hlast : last post 0 <= length ps).
      { apply placement_vertex_bound with (order := post); [exact Holdperm|].
        apply last_in_nonempty. exact Hpost. }
      pose proof (IH HvalidOld post Holdperm) as Hold.
      rewrite app_nil_l.
      rewrite last_cons_nonempty by exact Hpost.
      change (2 * S (length ps) <=
        path_score (p :: ps) (S (length ps) :: post) +
        tdist (p :: ps) (S (length ps)) (last post 0)).
      rewrite path_score_cons_nonempty by exact Hpost.
      rewrite path_score_old with (parent := p) (order := post).
      2: { intros z Hz. apply placement_vertex_bound with (order := post);
           [exact Holdperm|exact Hz]. }
      rewrite tdist_new_leaf_l by exact Hfirst.
      rewrite tdist_new_leaf_l by exact Hlast.
      pose proof (@g_tri (tdist ps) (tdist_good ps)
        (hd 0 post) p (last post 0)) as Htri.
      pose proof (@g_sym (tdist ps) (tdist_good ps)
        (hd 0 post) p) as Hsym.
      simpl. rewrite Hsym in Htri. lia.
    + destruct post as [|b post].
      * assert (Hpre : a :: pre <> []). discriminate.
        rewrite app_nil_r in Holdperm.
        assert (Hfirst : hd 0 (a :: pre) <= length ps).
        { apply placement_vertex_bound with (order := a :: pre); [exact Holdperm|].
          apply hd_in_nonempty. exact Hpre. }
        assert (Hlast : last (a :: pre) 0 <= length ps).
        { apply placement_vertex_bound with (order := a :: pre); [exact Holdperm|].
          apply last_in_nonempty. exact Hpre. }
        pose proof (IH HvalidOld (a :: pre) Holdperm) as Hold.
        rewrite path_score_app. rewrite last_last. cbn [hd].
        change (2 * S (length ps) <=
          path_score (p :: ps) (a :: pre) + 0 +
          tdist (p :: ps) (last (a :: pre) 0) (S (length ps)) +
          tdist (p :: ps) (hd 0 (a :: pre)) (S (length ps))).
        rewrite path_score_old with (parent := p).
        2: { intros z Hz. apply in_tree_vertices_bound.
             eapply Permutation_in; [exact Holdperm|exact Hz]. }
        rewrite (@tdist_new_leaf_r ps p (last (a :: pre) 0)) by exact Hlast.
        rewrite (@tdist_new_leaf_r ps p (hd 0 (a :: pre))) by exact Hfirst.
        pose proof (@g_tri (tdist ps) (tdist_good ps)
          (hd 0 (a :: pre)) p (last (a :: pre) 0)) as Htri.
        pose proof (@g_sym (tdist ps) (tdist_good ps)
          p (last (a :: pre) 0)) as Hsym.
        simpl in Hold, Htri, Hsym. rewrite Hsym in Htri. simpl. lia.
      * assert (Hpre : a :: pre <> []). discriminate.
        assert (Hpost : b :: post <> []). discriminate.
        assert (Hleft : forall z, In z (a :: pre) -> z <= length ps).
        { intros z Hz. apply placement_vertex_bound with
            (order := (a :: pre) ++ b :: post); [exact Holdperm|].
          apply in_or_app. now left. }
        assert (Hright : forall z, In z (b :: post) -> z <= length ps).
        { intros z Hz. apply placement_vertex_bound with
            (order := (a :: pre) ++ b :: post); [exact Holdperm|].
          apply in_or_app. now right. }
        assert (Hleft_last : last (a :: pre) 0 <= length ps).
        { apply Hleft. apply last_in_nonempty. exact Hpre. }
        assert (Hright_first : hd 0 (b :: post) <= length ps).
        { apply Hright. apply hd_in_nonempty. exact Hpost. }
        pose proof (IH HvalidOld ((a :: pre) ++ b :: post) Holdperm) as Hold.
        rewrite path_score_app.
        rewrite path_score_app in Hold.
        rewrite path_score_cons_nonempty with
          (ps := p :: ps) (x := S (length ps)) (ys := b :: post) by exact Hpost.
        rewrite path_score_old with (parent := p) (order := a :: pre) by exact Hleft.
        rewrite path_score_old with (parent := p) (order := b :: post) by exact Hright.
        rewrite tdist_new_leaf_r by exact Hleft_last.
        rewrite tdist_new_leaf_l by exact Hright_first.
        rewrite hd_app_nonempty with (xs := a :: pre) (ys := S (length ps) :: b :: post)
          by discriminate.
        rewrite last_app_nonempty with (xs := a :: pre) (ys := S (length ps) :: b :: post)
          by discriminate.
        rewrite (last_cons_nonempty (S (length ps)) (b :: post) 0 Hpost).
        rewrite hd_app_nonempty with (xs := a :: pre) (ys := b :: post)
          in Hold by discriminate.
        rewrite last_app_nonempty with (xs := a :: pre) (ys := b :: post)
          in Hold by discriminate.
        rewrite tdist_old.
        2: { apply Hleft. apply hd_in_nonempty. exact Hpre. }
        2: { apply Hright. apply last_in_nonempty. exact Hpost. }
        pose proof (@g_tri (tdist ps) (tdist_good ps)
          (last (a :: pre) 0) p (hd 0 (b :: post))) as Htri.
        pose proof (@g_sym (tdist ps) (tdist_good ps)
          p (hd 0 (b :: post))) as Hsym.
        simpl in Hold, Htri, Hsym. rewrite Hsym in Htri. simpl. lia.
Qed.

(* Theorem 3.1, in the report's notation n = S (length ps).  Natural-number
   subtraction makes the displayed lower bound directly executable. *)
Theorem theorem_3_1 (ps : list nat) :
  valid_parents ps -> forall order,
    Permutation order (tree_vertices ps) ->
    2 * length ps - tdist ps (hd 0 order) (last order 0) <=
      path_score ps order.
Proof.
  intros Hvalid order Hperm.
  pose proof (path_score_lower_bound ps Hvalid order Hperm).
  lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* Theorem 3.4: construct a diameter-guided depth-first placement            *)
(* ------------------------------------------------------------------------- *)

(* Diameter-guided depth-first ordering for the leaf-attachment encoding.
   The recursion removes the newest leaf.  If that leaf is a prescribed
   endpoint, it extends the corresponding end of the order.  Otherwise it
   belongs to a side branch: insert it immediately after its parent, before
   the rest of that branch is traversed.  The reversed case handles the
   same detour when the prescribed endpoint orientation is reversed. *)
Fixpoint diameter_dfs_order (ps : list nat) (u v : nat) : list nat :=
  match ps with
  | [] => [0]
  | p :: old =>
      let leaf := S (length old) in
      if Nat.eqb u leaf then
        if Nat.eqb v p then
          leaf :: diameter_dfs_order old (other_vertex old p) p
        else leaf :: diameter_dfs_order old p v
      else if Nat.eqb v leaf then
        if Nat.eqb u p then
          diameter_dfs_order old p (other_vertex old p) ++ [leaf]
        else diameter_dfs_order old u p ++ [leaf]
      else if Nat.eqb u p then
        insert_after p leaf (diameter_dfs_order old p v)
      else if Nat.eqb v p then
        rev (insert_after p leaf (diameter_dfs_order old p u))
      else insert_after p leaf (diameter_dfs_order old u v)
  end.

Lemma diameter_dfs_order_cons_unfold (ps : list nat) (p u v : nat) :
  diameter_dfs_order (p :: ps) u v =
    if Nat.eqb u (S (length ps)) then
      if Nat.eqb v p then
        S (length ps) :: diameter_dfs_order ps (other_vertex ps p) p
      else S (length ps) :: diameter_dfs_order ps p v
    else if Nat.eqb v (S (length ps)) then
      if Nat.eqb u p then
        diameter_dfs_order ps p (other_vertex ps p) ++ [S (length ps)]
      else diameter_dfs_order ps u p ++ [S (length ps)]
    else if Nat.eqb u p then
      insert_after p (S (length ps)) (diameter_dfs_order ps p v)
    else if Nat.eqb v p then
      rev (insert_after p (S (length ps)) (diameter_dfs_order ps p u))
    else insert_after p (S (length ps)) (diameter_dfs_order ps u v).
Proof. reflexivity. Qed.

Definition EndpointPlacement (ps : list nat) (u v : nat) (order : list nat) : Prop :=
  Permutation order (tree_vertices ps) /\
  hd 0 order = u /\ last order 0 = v /\
  path_score ps order + tdist ps u v <= 2 * length ps.

Lemma endpoint_prepend_leaf (ps : list nat) (p x v : nat) (order : list nat) :
  EndpointPlacement ps x v order ->
  (x = p \/ v = p) ->
  EndpointPlacement (p :: ps) (S (length ps)) v
    (S (length ps) :: order).
Proof.
  intros [Hperm [Hhd [Hlast Hscore]]] Hcase.
  assert (Hnonempty : order <> []).
  { eapply permutation_list_nonempty; [exact Hperm|apply tree_vertices_nonempty]. }
  assert (Hvbound : v <= length ps).
  { apply placement_vertex_bound with (order := order); [exact Hperm|].
    rewrite <- Hlast. apply last_in_nonempty. exact Hnonempty. }
  assert (Hbound : forall z, In z order -> z <= length ps).
  { exact (placement_vertex_bound ps order Hperm). }
  unfold EndpointPlacement. split.
  - rewrite tree_vertices_leaf. apply permutation_prepend_leaf. exact Hperm.
  - split; [reflexivity|]. split.
    + rewrite last_cons_nonempty by exact Hnonempty. exact Hlast.
    + rewrite path_score_prepend_leaf by assumption.
      rewrite tdist_new_leaf_l by exact Hvbound.
      simpl in Hhd. subst x.
      destruct Hcase as [Hstart|Hfinish].
      * rewrite Hstart in *. rewrite (@g_refl (tdist ps) (tdist_good ps) p).
        simpl. lia.
      * subst v. rewrite Hfinish in *.
        rewrite (@g_refl (tdist ps) (tdist_good ps) p).
        rewrite (@g_sym (tdist ps) (tdist_good ps) p (hd 0 order)).
        simpl. lia.
Qed.

Lemma endpoint_append_leaf (ps : list nat) (p u x : nat) (order : list nat) :
  EndpointPlacement ps u x order ->
  (u = p \/ x = p) ->
  EndpointPlacement (p :: ps) u (S (length ps))
    (order ++ [S (length ps)]).
Proof.
  intros [Hperm [Hhd [Hlast Hscore]]] Hcase.
  assert (Hnonempty : order <> []).
  { eapply permutation_list_nonempty; [exact Hperm|apply tree_vertices_nonempty]. }
  assert (Hubound : u <= length ps).
  { apply placement_vertex_bound with (order := order); [exact Hperm|].
    rewrite <- Hhd. apply hd_in_nonempty. exact Hnonempty. }
  assert (Hbound : forall z, In z order -> z <= length ps).
  { exact (placement_vertex_bound ps order Hperm). }
  unfold EndpointPlacement. split.
  - rewrite tree_vertices_leaf. apply permutation_append_leaf. exact Hperm.
  - split.
    + rewrite hd_app_nonempty by exact Hnonempty. exact Hhd.
    + split.
      * rewrite last_last. reflexivity.
      * rewrite path_score_append_leaf by
          assumption.
        rewrite tdist_new_leaf_r by exact Hubound.
        destruct Hcase as [Hstart|Hfinish].
        -- subst u. rewrite Hstart in Hscore. rewrite Hstart.
           rewrite <- Hlast in Hscore.
           rewrite (@g_sym (tdist ps) (tdist_good ps) p (last order 0)) in Hscore.
           rewrite (@g_refl (tdist ps) (tdist_good ps) p). simpl. lia.
        -- subst x. rewrite Hfinish in *.
           rewrite (@g_refl (tdist ps) (tdist_good ps) p). simpl. lia.
Qed.

Lemma endpoint_insert_leaf (ps : list nat) (p u v : nat) (order : list nat) :
  EndpointPlacement ps u v order ->
  In p (tree_vertices ps) -> p <> v ->
  EndpointPlacement (p :: ps) u v
    (insert_after p (S (length ps)) order).
Proof.
  intros [Hperm [Hhd [Hlast Hscore]]] Hp Hpv.
  assert (Hbound : forall z, In z order -> z <= length ps).
  { exact (placement_vertex_bound ps order Hperm). }
  assert (Horderne : order <> []).
  { eapply permutation_list_nonempty; [exact Hperm|apply tree_vertices_nonempty]. }
  assert (Hpin : In p order).
  { eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Hp]. }
  assert (Hplast : p <> last order 0).
  { rewrite Hlast. exact Hpv. }
  assert (Hubound : u <= length ps).
  { apply Hbound. rewrite <- Hhd. apply hd_in_nonempty. exact Horderne. }
  assert (Hvbound : v <= length ps).
  { apply Hbound. rewrite <- Hlast. apply last_in_nonempty. exact Horderne. }
  unfold EndpointPlacement. split.
  - rewrite tree_vertices_leaf. eapply Permutation_trans.
    + apply insert_after_permutation. exact Hpin.
    + apply permutation_append_leaf. exact Hperm.
  - split.
    + rewrite insert_after_hd; assumption.
    + split.
      * rewrite insert_after_last; assumption.
      * rewrite insert_after_score with (ps := ps) (p := p)
          (leaf := S (length ps)) (xs := order); try assumption; try reflexivity.
        rewrite tdist_old by assumption.
        simpl. lia.
Qed.

Lemma path_score_snoc (ps : list nat) (order : list nat) (x : nat) :
  path_score ps (order ++ [x]) =
    path_score ps order +
      match order with [] => 0 | _ => tdist ps (last order 0) x end.
Proof.
  rewrite path_score_app. destruct order; simpl; lia.
Qed.

Lemma hd_rev_last (order : list nat) :
  hd 0 (rev order) = last order 0.
Proof.
  induction order using rev_ind.
  - reflexivity.
  - rewrite rev_app_distr. simpl. rewrite last_last. reflexivity.
Qed.

Lemma path_score_reverse (ps order : list nat) :
  path_score ps (rev order) = path_score ps order.
Proof.
  induction order using rev_ind.
  - reflexivity.
  - rewrite rev_app_distr, path_score_snoc.
    destruct order as [|a rest].
    + simpl. reflexivity.
    + change (path_score ps (x :: rev (a :: rest)) =
        path_score ps (a :: rest) + tdist ps (last (a :: rest) 0) x).
      rewrite path_score_cons_nonempty.
      * rewrite IHorder, hd_rev_last.
        rewrite (@g_sym (tdist ps) (tdist_good ps) x (last (a :: rest) 0)).
        lia.
      * intro Hempty. apply (f_equal (@rev nat)) in Hempty.
        rewrite rev_involutive in Hempty. discriminate.
Qed.

Lemma endpoint_reverse (ps : list nat) (u v : nat) (order : list nat) :
  EndpointPlacement ps u v order ->
  EndpointPlacement ps v u (rev order).
Proof.
  intros [Hperm [Hhd [Hlast Hscore]]].
  assert (Hnonempty : order <> []).
  { eapply permutation_list_nonempty; [exact Hperm|apply tree_vertices_nonempty]. }
  unfold EndpointPlacement. split.
  - eapply Permutation_trans.
    + apply Permutation_sym. apply Permutation_rev.
    + exact Hperm.
  - split.
    + rewrite hd_rev_last. exact Hlast.
    + split.
      * rewrite <- (hd_rev_last (rev order)), rev_involutive. exact Hhd.
      * rewrite path_score_reverse.
        rewrite (@g_sym (tdist ps) (tdist_good ps) v u).
        exact Hscore.
Qed.

(* A Hamilton ordering can be chosen so that its route cost plus the distance
   between its endpoints is at most twice the number of tree edges. *)
Theorem path_score_upper_bound : forall ps,
  valid_parents ps -> forall u v,
    In u (tree_vertices ps) -> In v (tree_vertices ps) ->
    (u <> v \/ ps = []) ->
    exists order, EndpointPlacement ps u v order.
Proof.
  induction ps as [|p ps IH]; intros Hvalid u v Hu Hv Huv.
  - simpl in Hu, Hv.
    destruct Hu as [Hu|[]]. subst u.
    destruct Hv as [Hv|[]]. subst v.
    exists [0]. unfold EndpointPlacement. simpl.
    split; [apply Permutation_refl_nat|].
    split; [reflexivity|]. split; [reflexivity|]. lia.
  - destruct Hvalid as [Hp HvalidOld].
    set (leaf := S (length ps)).
    assert (HpIn : In p (tree_vertices ps)).
    { apply in_tree_vertices_of_bound. exact Hp. }
    assert (HleafU : u = leaf \/ In u (tree_vertices ps)).
    { exact (tree_vertices_leaf_cases ps p u Hu). }
    assert (HleafV : v = leaf \/ In v (tree_vertices ps)).
    { exact (tree_vertices_leaf_cases ps p v Hv). }
    destruct ps as [|q qs].
    + assert (Hp0 : p = 0) by (simpl in Hp; lia). subst p.
      assert (Huv0 : u <> v).
      { destruct Huv as [Huv0|Hempty]; [exact Huv0|discriminate]. }
      assert (Hu01 : u = 0 \/ u = 1).
      { change (In u [0; 1]) in Hu. simpl in Hu.
        destruct Hu as [E|[E|[]]]; [left; symmetry|right; symmetry]; exact E. }
      assert (Hv01 : v = 0 \/ v = 1).
      { change (In v [0; 1]) in Hv. simpl in Hv.
        destruct Hv as [E|[E|[]]]; [left; symmetry|right; symmetry]; exact E. }
      assert (Hd10 : tdist [0] 1 0 = 1).
      { apply tdist_leaf. simpl. lia. }
      assert (Hd01 : tdist [0] 0 1 = 1).
      { rewrite (@g_sym (tdist [0]) (tdist_good [0]) 0 1). exact Hd10. }
      destruct Hu01 as [Hu0|Hu1]; destruct Hv01 as [Hv0|Hv1]; subst u v;
        try (exfalso; apply Huv0; reflexivity).
      * exists [0; 1]. unfold EndpointPlacement. simpl.
        split; [apply Permutation_refl_nat|].
        split; [reflexivity|]. split; [reflexivity|].
        vm_compute. lia.
      * exists [1; 0]. unfold EndpointPlacement. simpl.
        split; [apply perm_swap|].
        split; [reflexivity|]. split; [reflexivity|].
        vm_compute. lia.
    + assert (Hlenpos : 0 < length (q :: qs)) by (simpl; lia).
      assert (HuvNe : u <> v).
      { destruct Huv as [Hne|Hempty]; [exact Hne|discriminate]. }
      assert (Hother : other_vertex (q :: qs) p <= length (q :: qs) /\
                       other_vertex (q :: qs) p <> p).
      { apply other_vertex_spec; [exact Hlenpos|exact Hp]. }
      destruct Hother as [HotherBound HotherNe].
      assert (HotherIn : In (other_vertex (q :: qs) p) (tree_vertices (q :: qs))).
      { apply in_tree_vertices_of_bound. exact HotherBound. }
      destruct (Nat.eq_dec u leaf) as [HuLeaf|HuOld].
      * subst u.
        assert (HvNotLeaf : v <> leaf).
        { intro E. apply HuvNe. now rewrite E. }
        destruct (Nat.eq_dec v p) as [Hvp|Hvp].
        -- subst v.
           destruct (IH HvalidOld (other_vertex (q :: qs) p) p
             HotherIn HpIn (or_introl HotherNe)) as [old_order Hold].
           exists (leaf :: old_order).
           eapply endpoint_prepend_leaf; [exact Hold|right; reflexivity].
        -- assert (HvIn : In v (tree_vertices (q :: qs))).
           { apply tree_vertex_old_of_neq_new with (p := p); assumption. }
              destruct (IH HvalidOld p v HpIn HvIn
             (or_introl (fun E => Hvp (eq_sym E)))) as [old_order Hold].
           exists (leaf :: old_order).
           eapply endpoint_prepend_leaf; [exact Hold|left; reflexivity].
      * destruct (Nat.eq_dec v leaf) as [HvLeaf|HvOld].
        -- subst v.
           assert (HuNotLeaf : u <> leaf) by exact HuOld.
           destruct (Nat.eq_dec u p) as [Hup|Hup].
           ++ subst u.
              destruct (IH HvalidOld p (other_vertex (q :: qs) p)
                HpIn HotherIn (or_introl (fun E => HotherNe (eq_sym E))))
                as [old_order Hold].
              exists (old_order ++ [leaf]).
              eapply endpoint_append_leaf; [exact Hold|left; reflexivity].
           ++ assert (HuIn : In u (tree_vertices (q :: qs))).
              { apply tree_vertex_old_of_neq_new with (p := p); assumption. }
              destruct (IH HvalidOld u p HuIn HpIn
                (or_introl Hup)) as [old_order Hold].
              exists (old_order ++ [leaf]).
              eapply endpoint_append_leaf; [exact Hold|right; reflexivity].
        -- assert (HuIn : In u (tree_vertices (q :: qs))).
           { apply tree_vertex_old_of_neq_new with (p := p); assumption. }
           assert (HvIn : In v (tree_vertices (q :: qs))).
           { apply tree_vertex_old_of_neq_new with (p := p); assumption. }
           destruct (Nat.eq_dec u p) as [Hup|Hup].
           ++ subst u.
              destruct (IH HvalidOld p v HpIn HvIn
                (or_introl HuvNe)) as [old_order Hold].
              exists (insert_after p leaf old_order).
              apply endpoint_insert_leaf; [exact Hold|exact HpIn|exact HuvNe].
           ++ destruct (Nat.eq_dec v p) as [Hvp|Hvp].
              ** subst v.
                 assert (Hpu : p <> u).
                 { intro E. apply HuvNe. symmetry. exact E. }
                 destruct (IH HvalidOld p u HpIn HuIn
                   (or_introl Hpu)) as [old_order Hold].
                 exists (rev (insert_after p leaf old_order)).
                 apply endpoint_reverse.
                 apply endpoint_insert_leaf; [exact Hold|exact HpIn|exact Hpu].
              ** destruct (IH HvalidOld u v HuIn HvIn
                   (or_introl HuvNe)) as [old_order Hold].
                 exists (insert_after p leaf old_order).
                 apply endpoint_insert_leaf; [exact Hold|exact HpIn|].
                 intro E. apply Hvp. symmetry. exact E.
Qed.

(* The constructive endpoint-order procedure itself satisfies the same
   endpoint and score specification.  This connects the executable order
   to the optimality argument below, instead of relying only on an
   existentially chosen permutation. *)
Theorem diameter_dfs_order_correct (ps : list nat) :
  valid_parents ps -> forall u v,
    In u (tree_vertices ps) -> In v (tree_vertices ps) ->
    (u <> v \/ ps = []) ->
    EndpointPlacement ps u v (diameter_dfs_order ps u v).
Proof.
  induction ps as [|p ps IH]; intros Hvalid u v Hu Hv Huv.
  - simpl in Hu, Hv. destruct Hu as [Hu|[]]. subst u.
    destruct Hv as [Hv|[]]. subst v.
    change (EndpointPlacement [] 0 0 [0]).
    unfold EndpointPlacement. simpl.
    split; [apply Permutation_refl_nat|].
    split; [reflexivity|]. split; [reflexivity|lia].
  - destruct Hvalid as [Hp HvalidOld].
    assert (HpIn : In p (tree_vertices ps)).
    { apply in_tree_vertices_of_bound. exact Hp. }
    assert (HuvNe : u <> v).
    { destruct Huv as [Hne|Hempty]; [exact Hne|discriminate]. }
    destruct ps as [|q qs].
    + assert (Hp0 : p = 0) by (simpl in Hp; lia). subst p.
      assert (Hu01 : u = 0 \/ u = 1).
      { change (In u [0; 1]) in Hu. simpl in Hu.
        destruct Hu as [E|[E|[]]]; [left; symmetry|right; symmetry]; exact E. }
      assert (Hv01 : v = 0 \/ v = 1).
      { change (In v [0; 1]) in Hv. simpl in Hv.
        destruct Hv as [E|[E|[]]]; [left; symmetry|right; symmetry]; exact E. }
      destruct Hu01 as [Hu0|Hu1]; destruct Hv01 as [Hv0|Hv1];
        try (exfalso; apply HuvNe; congruence); subst u v.
      * change (EndpointPlacement [0] 0 1 [0; 1]).
        unfold EndpointPlacement. simpl.
        split; [apply Permutation_refl_nat|].
        split; [reflexivity|]. split; [reflexivity|]. vm_compute; lia.
      * change (EndpointPlacement [0] 1 0 [1; 0]).
        unfold EndpointPlacement. simpl.
        split; [apply perm_swap|].
        split; [reflexivity|]. split; [reflexivity|]. vm_compute; lia.
    + assert (Hlenpos : 0 < length (q :: qs)) by (simpl; lia).
      set (leaf := S (length (q :: qs))).
      assert (Hother : other_vertex (q :: qs) p <= length (q :: qs) /\
                       other_vertex (q :: qs) p <> p).
      { apply other_vertex_spec; [exact Hlenpos|exact Hp]. }
      destruct Hother as [HotherBound HotherNe].
      assert (HotherIn : In (other_vertex (q :: qs) p) (tree_vertices (q :: qs))).
      { apply in_tree_vertices_of_bound. exact HotherBound. }
      destruct (Nat.eq_dec u leaf) as [HuLeaf|HuOld].
      * subst u.
        assert (HvNotLeaf : v <> leaf).
        { intro E. apply HuvNe. now rewrite E. }
        destruct (Nat.eq_dec v p) as [Hvp|Hvp].
        -- subst v.
           specialize (IH HvalidOld (other_vertex (q :: qs) p) p
             HotherIn HpIn (or_introl HotherNe)).
           rewrite diameter_dfs_order_cons_unfold.
           rewrite Nat.eqb_refl, Nat.eqb_refl.
           eapply endpoint_prepend_leaf; [exact IH|right; reflexivity].
        -- assert (HvIn : In v (tree_vertices (q :: qs))).
           { apply tree_vertex_old_of_neq_new with (p := p); assumption. }
           assert (HpNeV : p <> v) by congruence.
           specialize (IH HvalidOld p v HpIn HvIn (or_introl HpNeV)).
           rewrite diameter_dfs_order_cons_unfold.
           rewrite Nat.eqb_refl.
           assert (Evp : Nat.eqb v p = false) by (apply Nat.eqb_neq; exact Hvp).
           rewrite Evp.
           eapply endpoint_prepend_leaf; [exact IH|left; reflexivity].
      * destruct (Nat.eq_dec v leaf) as [HvLeaf|HvOld].
        -- subst v.
           assert (HuNotLeaf : u <> leaf) by exact HuOld.
           destruct (Nat.eq_dec u p) as [Hup|Hup].
           ++ subst u.
              specialize (IH HvalidOld p (other_vertex (q :: qs) p)
                HpIn HotherIn (or_introl (fun E => HotherNe (eq_sym E)))).
              rewrite diameter_dfs_order_cons_unfold.
              assert (EpLeaf : Nat.eqb p (S (length (q :: qs))) = false).
              { apply Nat.eqb_neq. exact HuOld. }
              rewrite EpLeaf, Nat.eqb_refl, Nat.eqb_refl.
              eapply endpoint_append_leaf; [exact IH|left; reflexivity].
           ++ assert (HuIn : In u (tree_vertices (q :: qs))).
              { apply tree_vertex_old_of_neq_new with (p := p); assumption. }
              specialize (IH HvalidOld u p HuIn HpIn (or_introl Hup)).
              rewrite diameter_dfs_order_cons_unfold.
              assert (EuLeaf : Nat.eqb u (S (length (q :: qs))) = false).
              { apply Nat.eqb_neq. exact HuOld. }
              assert (Eup : Nat.eqb u p = false) by (apply Nat.eqb_neq; exact Hup).
              rewrite EuLeaf, Nat.eqb_refl, Eup.
              eapply endpoint_append_leaf; [exact IH|right; reflexivity].
        -- assert (HuIn : In u (tree_vertices (q :: qs))).
           { apply tree_vertex_old_of_neq_new with (p := p); assumption. }
           assert (HvIn : In v (tree_vertices (q :: qs))).
           { apply tree_vertex_old_of_neq_new with (p := p); assumption. }
           destruct (Nat.eq_dec u p) as [Hup|Hup].
           ++ subst u.
              specialize (IH HvalidOld p v HpIn HvIn (or_introl HuvNe)).
              rewrite diameter_dfs_order_cons_unfold.
              assert (Epleaf : Nat.eqb p (S (length (q :: qs))) = false).
              { apply Nat.eqb_neq. exact HuOld. }
              assert (Evleaf : Nat.eqb v (S (length (q :: qs))) = false).
              { apply Nat.eqb_neq. exact HvOld. }
              rewrite Epleaf, Evleaf, Nat.eqb_refl.
              apply endpoint_insert_leaf; [exact IH|exact HpIn|].
              exact HuvNe.
           ++ destruct (Nat.eq_dec v p) as [Hvp|Hvp].
              ** subst v.
                 assert (Hpu : p <> u) by congruence.
                 specialize (IH HvalidOld p u HpIn HuIn (or_introl Hpu)).
                 rewrite diameter_dfs_order_cons_unfold.
                 assert (Euleaf : Nat.eqb u (S (length (q :: qs))) = false).
                 { apply Nat.eqb_neq. exact HuOld. }
                 assert (Epleaf : Nat.eqb p (S (length (q :: qs))) = false).
                 { apply Nat.eqb_neq. exact HvOld. }
                 assert (Eup : Nat.eqb u p = false) by (apply Nat.eqb_neq; exact Hup).
                 rewrite Euleaf, Epleaf, Eup, Nat.eqb_refl.
                 apply endpoint_reverse.
                 apply endpoint_insert_leaf; [exact IH|exact HpIn|exact Hpu].
              ** specialize (IH HvalidOld u v HuIn HvIn (or_introl HuvNe)).
                 rewrite diameter_dfs_order_cons_unfold.
                 assert (Euleaf : Nat.eqb u (S (length (q :: qs))) = false).
                 { apply Nat.eqb_neq. exact HuOld. }
                 assert (Evleaf : Nat.eqb v (S (length (q :: qs))) = false).
                 { apply Nat.eqb_neq. exact HvOld. }
                 assert (Eup : Nat.eqb u p = false) by (apply Nat.eqb_neq; exact Hup).
                 assert (Evp : Nat.eqb v p = false) by (apply Nat.eqb_neq; exact Hvp).
                 rewrite Euleaf, Evleaf, Eup, Evp.
                 apply endpoint_insert_leaf; [exact IH|exact HpIn|].
                 intro E. apply Hvp. symmetry. exact E.
Qed.

(* ------------------------------------------------------------------------- *)
(* Two sweeps, diameter bound, and the optimal placement                     *)
(* ------------------------------------------------------------------------- *)

(* These are the two choices made by the algorithm in Theorem 3.3. *)
Definition sweep_left (ps : list nat) : nat :=
  farthest_vertex (tree_vertices ps) 0 (tdist ps) 0.

Definition sweep_right (ps : list nat) : nat :=
  farthest_vertex (tree_vertices ps) 0 (tdist ps) (sweep_left ps).

Definition sweep_diameter (ps : list nat) : nat :=
  let s := sweep_left ps in
  let t := farthest_vertex (tree_vertices ps) 0 (tdist ps) s in
  tdist ps s t.

Lemma two_sweep_diameter (ps : list nat) :
  valid_parents ps ->
  Diam (tree_vertices ps) (tdist ps) (sweep_left ps) (sweep_right ps).
Proof.
  intro Hvalid. unfold sweep_left, sweep_right.
  exact (two_sweep_algorithm (tdist_space ps) 0).
Qed.

Lemma sweep_endpoints_in (ps : list nat) :
  In (sweep_left ps) (tree_vertices ps) /\
  In (sweep_right ps) (tree_vertices ps).
Proof.
  split.
  - unfold sweep_left. apply farthest_in. exact (tdist_space ps).
  - unfold sweep_right. apply farthest_in. exact (tdist_space ps).
Qed.

(* Corollary 3.2: every placement costs at least twice the number of tree
   edges minus the tree diameter.  The diameter is supplied by Theorem 3.3's
   two-sweep construction above. *)
Corollary corollary_3_2 (ps : list nat) :
  valid_parents ps -> forall order,
    Permutation order (tree_vertices ps) ->
    2 * length ps - sweep_diameter ps <= path_score ps order.
Proof.
  intros Hvalid order Hperm.
  pose proof (path_score_lower_bound ps Hvalid order Hperm) as Hlower.
  assert (Horderne : order <> []).
  { eapply permutation_list_nonempty; [exact Hperm|apply tree_vertices_nonempty]. }
  assert (Hfirst : In (hd 0 order) (tree_vertices ps)).
  { eapply Permutation_in; [exact Hperm|apply hd_in_nonempty; exact Horderne]. }
  assert (Hlast : In (last order 0) (tree_vertices ps)).
  { eapply Permutation_in; [exact Hperm|apply last_in_nonempty; exact Horderne]. }
  pose proof (two_sweep_diameter ps Hvalid (hd 0 order) (last order 0)
    Hfirst Hlast) as Hdiam.
  unfold Diam in Hdiam.
  unfold sweep_diameter, sweep_right in *.
  lia.
Qed.

Lemma sweep_endpoints_distinct_or_empty (ps : list nat) :
  valid_parents ps -> sweep_left ps <> sweep_right ps \/ ps = [].
Proof.
  intro Hvalid. destruct ps as [|p ps].
  - right. reflexivity.
  - left.
    set (leaf := S (length ps)).
    assert (Hroot : In 0 (tree_vertices (p :: ps))).
    { unfold tree_vertices. simpl. left. reflexivity. }
    assert (Hleaf : In leaf (tree_vertices (p :: ps))).
    { unfold leaf. apply tree_vertices_leaf_new. }
    assert (Hroot_leaf : 0 <> leaf) by (unfold leaf; lia).
    assert (Hpositive : 0 < tdist (p :: ps) 0 leaf).
    { destruct (tdist (p :: ps) 0 leaf) eqn:E; [|lia].
      exfalso. apply Hroot_leaf.
      eapply tdist_separates_vertices; eauto. }
    assert (Hroot_to_left :
      0 < tdist (p :: ps) 0 (sweep_left (p :: ps))).
    { pose proof (farthest_far (tdist_space (p :: ps)) 0) as Hfar.
      unfold Far in Hfar.
      specialize (Hfar leaf Hleaf).
      unfold sweep_left. eapply Nat.lt_le_trans; [exact Hpositive|exact Hfar]. }
    intro E.
    assert (Hleft_to_root :
      0 < tdist (p :: ps) (sweep_left (p :: ps)) 0).
    { rewrite (@g_sym (tdist (p :: ps)) (tdist_good (p :: ps))). exact Hroot_to_left. }
    pose proof (farthest_far (tdist_space (p :: ps))
      (sweep_left (p :: ps))) as Hfar.
    unfold Far in Hfar.
    specialize (Hfar 0 Hroot).
    unfold sweep_right, tree_vertices in E.
    unfold tree_vertices in Hfar.
    rewrite <- E in Hfar.
    rewrite (@g_refl (tdist (p :: ps)) (tdist_good (p :: ps))) in Hfar.
    lia.
Qed.

(* Begin at one two-sweep endpoint, make the depth-first detours, and finish
   at the other endpoint. *)
Definition sweep_order (ps : list nat) : list nat :=
  diameter_dfs_order ps (sweep_left ps) (sweep_right ps).

Theorem sweep_order_correct (ps : list nat) :
  valid_parents ps ->
  EndpointPlacement ps (sweep_left ps) (sweep_right ps) (sweep_order ps).
Proof.
  intro Hvalid. unfold sweep_order.
  destruct (sweep_endpoints_in ps) as [Hleft Hright].
  apply diameter_dfs_order_correct; try assumption.
  apply sweep_endpoints_distinct_or_empty. exact Hvalid.
Qed.

Lemma tdist_bounded_by_edges : forall ps,
  valid_parents ps -> forall x y,
    x <= length ps -> y <= length ps -> tdist ps x y <= length ps.
Proof.
  induction ps as [|p ps IH]; intros Hvalid x y Hx Hy.
  - simpl in *. lia.
  - destruct Hvalid as [Hp HvalidOld].
    set (leaf := S (length ps)).
    destruct (Nat.eq_dec x leaf) as [Ex|Ex].
    + subst x. destruct (Nat.eq_dec y leaf) as [Ey|Ey].
      * subst y. rewrite (@g_refl (tdist (p :: ps)) (tdist_good (p :: ps))).
        simpl. lia.
      * assert (Hyold : y <= length ps) by (unfold leaf in Ey; simpl in Hy; lia).
        rewrite tdist_new_leaf_l by exact Hyold.
        specialize (IH HvalidOld p y Hp Hyold). simpl. lia.
    + destruct (Nat.eq_dec y leaf) as [Ey|Ey].
      * subst y. assert (Hxold : x <= length ps) by (unfold leaf in Ex; simpl in Hx; lia).
        rewrite tdist_new_leaf_r by exact Hxold.
        specialize (IH HvalidOld x p Hxold Hp). simpl. lia.
      * assert (Hxold : x <= length ps) by (unfold leaf in Ex; simpl in Hx; lia).
        assert (Hyold : y <= length ps) by (unfold leaf in Ey; simpl in Hy; lia).
        rewrite tdist_old by assumption.
        specialize (IH HvalidOld x y Hxold Hyold). simpl. lia.
Qed.

Theorem sweep_order_score_exact (ps : list nat) :
  valid_parents ps ->
  path_score ps (sweep_order ps) +
    tdist ps (sweep_left ps) (sweep_right ps) = 2 * length ps.
Proof.
  intro Hvalid.
  pose proof (sweep_order_correct ps Hvalid) as Hconstruct.
  unfold EndpointPlacement in Hconstruct.
  destruct Hconstruct as [Hperm [Hhd [Hlast Hupper]]].
  destruct (sweep_endpoints_in ps) as [Hleft Hright].
  assert (Hdiam_le :
    tdist ps (sweep_left ps) (sweep_right ps) <= length ps).
  { eapply tdist_bounded_by_edges; [exact Hvalid| |].
    - apply in_tree_vertices_bound. exact Hleft.
    - apply in_tree_vertices_bound. exact Hright. }
  pose proof (path_score_lower_bound ps Hvalid (sweep_order ps) Hperm) as Hlower.
  rewrite Hhd, Hlast in Hlower.
  lia.
Qed.

(* This is the cost specification for the diameter-guided DFS: its route
   makes one pass along the diameter and a round trip through every side
   branch.  [path_score_lower_bound] gives the matching per-edge lower bound;
   equality below certifies that the construction attains it. *)
Definition DiameterDFSPlacement (ps : list nat) (u v : nat)
    (order : list nat) : Prop :=
  Permutation order (tree_vertices ps) /\
  hd 0 order = u /\ last order 0 = v /\
  path_score ps order + tdist ps u v = 2 * length ps.

Theorem sweep_order_is_diameter_dfs (ps : list nat) :
  valid_parents ps ->
  DiameterDFSPlacement ps (sweep_left ps) (sweep_right ps) (sweep_order ps).
Proof.
  intro Hvalid.
  pose proof (sweep_order_correct ps Hvalid) as Hplacement.
  pose proof (sweep_order_score_exact ps Hvalid) as Hcost.
  unfold DiameterDFSPlacement, EndpointPlacement in *.
  destruct Hplacement as [Hperm [Hfirst [Hlast _]]].
  repeat split; assumption.
Qed.

Definition OptimalPathScore (ps : list nat) (score : nat) : Prop :=
  (exists order, Permutation order (tree_vertices ps) /\
     path_score ps order = score) /\
  (forall order, Permutation order (tree_vertices ps) ->
     score <= path_score ps order).

Theorem path_tree_optimal_score (ps : list nat) :
  valid_parents ps ->
  OptimalPathScore ps
    (2 * length ps - tdist ps (sweep_left ps) (sweep_right ps)).
Proof.
  intro Hvalid. unfold OptimalPathScore. split.
  - pose proof (sweep_order_is_diameter_dfs ps Hvalid) as Hdfs.
    unfold DiameterDFSPlacement in Hdfs.
    destruct Hdfs as [Hperm [_ [_ Hscore]]].
    exists (sweep_order ps). split; [exact Hperm|]. lia.
  - intros order Hperm.
    assert (Horderne : order <> []).
    { eapply permutation_list_nonempty; [exact Hperm|apply tree_vertices_nonempty]. }
    assert (Hfirst : In (hd 0 order) (tree_vertices ps)).
    { eapply Permutation_in; [exact Hperm|apply hd_in_nonempty; exact Horderne]. }
    assert (Hlast : In (last order 0) (tree_vertices ps)).
    { eapply Permutation_in; [exact Hperm|apply last_in_nonempty; exact Horderne]. }
    pose proof (path_score_lower_bound ps Hvalid order Hperm) as Hlower.
    pose proof (two_sweep_diameter ps Hvalid (hd 0 order) (last order 0)
      Hfirst Hlast) as Hdiam.
    assert (Hdiam_le :
      tdist ps (sweep_left ps) (sweep_right ps) <= length ps).
    { eapply tdist_bounded_by_edges; [exact Hvalid| |].
      - apply in_tree_vertices_bound. exact (proj1 (sweep_endpoints_in ps)).
      - apply in_tree_vertices_bound. exact (proj2 (sweep_endpoints_in ps)). }
    lia.
Qed.

(* Theorem 3.4: the computed diameter-guided order is an optimal placement.
   Its leaf-recursive construction implements the proof's DFS rule by placing
   each side-branch leaf beside its parent.  The theorem below proves the
   resulting placement and score properties. *)
Theorem theorem_3_4 (ps : list nat) :
  valid_parents ps ->
  Permutation (sweep_order ps) (tree_vertices ps) /\
  path_score ps (sweep_order ps) =
    2 * length ps - sweep_diameter ps /\
  OptimalPathScore ps
    (2 * length ps - sweep_diameter ps).
Proof.
  intro Hvalid.
  pose proof (sweep_order_correct ps Hvalid) as Hplacement.
  unfold EndpointPlacement in Hplacement.
  destruct Hplacement as [Hperm [_ [_ _]]].
  pose proof (sweep_order_score_exact ps Hvalid) as Hcost.
  assert (Hdiam_le : sweep_diameter ps <= length ps).
  { unfold sweep_diameter.
    eapply tdist_bounded_by_edges; [exact Hvalid| |].
    - apply in_tree_vertices_bound. exact (proj1 (sweep_endpoints_in ps)).
    - apply in_tree_vertices_bound. exact (proj2 (sweep_endpoints_in ps)). }
  assert (Hscore : path_score ps (sweep_order ps) =
      2 * length ps - sweep_diameter ps).
  { unfold sweep_diameter, sweep_right in *.
    lia. }
  split; [exact Hperm|].
  split; [exact Hscore|].
  exact (path_tree_optimal_score ps Hvalid).
Qed.

(* ------------------------------------------------------------------------- *)
(* Theorem 3.6: decision procedure and structural work bound                 *)
(* ------------------------------------------------------------------------- *)

(* The decision problem asks whether some ordering of the offices has route
   score at most K.  The tree is encoded by its valid parent sequence. *)
Definition PathDecisionYesAt (ps : list nat) (K : nat) : Prop :=
  valid_parents ps /\
  exists order, Permutation order (tree_vertices ps) /\ path_score ps order <= K.

Theorem path_tree_decision_characterization (ps : list nat) (K : nat) :
  PathDecisionYesAt ps K <->
  (valid_parents ps /\ 2 * length ps <= K + sweep_diameter ps).
Proof.
  split.
  - intros [Hvalid [order [Hperm Hscore]]]. split; [exact Hvalid|].
    pose proof (path_score_lower_bound ps Hvalid order Hperm) as Hlower.
    assert (Horderne : order <> []).
    { eapply permutation_list_nonempty; [exact Hperm|apply tree_vertices_nonempty]. }
    assert (Hfirst : In (hd 0 order) (tree_vertices ps)).
    { eapply Permutation_in; [exact Hperm|].
      apply hd_in_nonempty. exact Horderne. }
    assert (Hlast : In (last order 0) (tree_vertices ps)).
    { eapply Permutation_in; [exact Hperm|].
      apply last_in_nonempty. exact Horderne. }
    pose proof (two_sweep_diameter ps Hvalid) as Hdiam.
    pose proof (Hdiam (hd 0 order) (last order 0) Hfirst Hlast) as Henddist.
    unfold sweep_right in Henddist.
    unfold sweep_diameter in Henddist |- *. lia.
  - intros [Hvalid Hthreshold]. split; [exact Hvalid|].
    pose proof (sweep_order_correct ps Hvalid) as Hconstruct.
    unfold EndpointPlacement in Hconstruct.
    destruct Hconstruct as [Hperm [Hhd [Hlast Hupper]]].
    exists (sweep_order ps). split; [exact Hperm|].
    unfold sweep_diameter, sweep_right in *. lia.
Qed.

Fixpoint valid_parents_check (ps : list nat) : bool :=
  match ps with
  | [] => true
  | p :: ps' => Nat.leb p (length ps') && valid_parents_check ps'
  end.

Lemma valid_parents_check_correct (ps : list nat) :
  valid_parents_check ps = true <-> valid_parents ps.
Proof.
  induction ps as [|p ps IH]; simpl.
  - tauto.
  - rewrite andb_true_iff, Nat.leb_le, IH. tauto.
Qed.

Definition decide_path_tree (ps : list nat) (K : nat) : bool :=
  if valid_parents_check ps
  then Nat.leb (2 * length ps) (K + sweep_diameter ps)
  else false.

Theorem decide_path_tree_correct (ps : list nat) (K : nat) :
  decide_path_tree ps K = true <-> PathDecisionYesAt ps K.
Proof.
  unfold decide_path_tree.
  destruct (valid_parents_check ps) eqn:Hcheck.
  - rewrite Nat.leb_le. rewrite valid_parents_check_correct in Hcheck.
    rewrite path_tree_decision_characterization. tauto.
  - split; [discriminate|]. intros [Hvalid _].
    assert (Htrue : valid_parents_check ps = true).
    { apply (proj2 (valid_parents_check_correct ps)). exact Hvalid. }
    rewrite Hcheck in Htrue. discriminate.
Qed.

(* Structural work model.  A distance query pays one unit for each parent
   layer it visits, including the base layer.  The branch structure mirrors
   [tdist]/[ext]: at most one recursive distance query is made per layer. *)
Fixpoint tree_distance_work (ps : list nat) (x y : nat) : nat :=
  match ps with
  | [] => 1
  | p :: ps' =>
      S (if Nat.eqb x (S (length ps')) then
           if Nat.eqb y (S (length ps')) then 0
           else tree_distance_work ps' p y
         else if Nat.eqb y (S (length ps')) then
           tree_distance_work ps' x p
         else tree_distance_work ps' x y)
  end.

Lemma tree_distance_work_bound (ps : list nat) (x y : nat) :
  tree_distance_work ps x y <= S (length ps).
Proof.
  revert x y. induction ps as [|p ps IH]; intros x y; simpl; [lia|].
  destruct (Nat.eqb x (S (length ps))) eqn:Ex.
  - destruct (Nat.eqb y (S (length ps))) eqn:Ey; simpl; [lia|].
    specialize (IH p y). lia.
  - destruct (Nat.eqb y (S (length ps))) eqn:Ey; simpl.
    + specialize (IH x p). lia.
    + specialize (IH x y). lia.
Qed.

(* Count the comparison and the two score evaluations at each [argmax]
   cell, plus the recursive scan of the tail.  This follows the definition
   in [CorrectionReview.v]. *)
Fixpoint argmax_work {V : Type} (score : V -> nat) (fb : V)
    (score_work : V -> nat) (xs : list V) : nat :=
  match xs with
  | [] => 0
  | x :: rest => argmax_work score fb score_work rest + 1 +
      score_work x + score_work (argmax score fb rest)
  end.

Lemma argmax_work_bound {V : Type} (score : V -> nat) (fb : V)
    (score_work : V -> nat) (xs : list V) (T : nat) :
  (forall z, In z xs \/ z = fb -> score_work z <= T) ->
  argmax_work score fb score_work xs <= length xs * (1 + 2 * T).
Proof.
  induction xs as [|x xs IH]; intros Hwork; simpl.
  - lia.
  - assert (Htail : forall z, In z xs \/ z = fb -> score_work z <= T).
    { intros z [Hz|Hz].
      - apply Hwork. left. simpl. now right.
      - apply Hwork. now right. }
    assert (Hx : score_work x <= T).
    { apply Hwork. left. simpl. now left. }
    assert (Hbest : score_work (argmax score fb xs) <= T).
    { apply Hwork. destruct (argmax_in score fb xs) as [E|Hin].
      - now right.
      - left. simpl. now right. }
    specialize (IH Htail). lia.
Qed.

Lemma tree_vertices_length (ps : list nat) :
  length (tree_vertices ps) = S (length ps).
Proof. unfold tree_vertices. apply length_seq. Qed.

Definition farthest_scan_work (ps : list nat) (r : nat) : nat :=
  argmax_work (tdist ps r) 0 (tree_distance_work ps r) (tree_vertices ps).

Lemma farthest_scan_work_bound (ps : list nat) (r : nat) :
  farthest_scan_work ps r <= S (length ps) * (1 + 2 * S (length ps)).
Proof.
  unfold farthest_scan_work.
  eapply Nat.le_trans.
  - apply argmax_work_bound. intros z _. apply tree_distance_work_bound.
  - rewrite tree_vertices_length. apply Nat.le_refl.
Qed.

(* The measured total includes both farthest-vertex scans, a linear pass to
   check the parent encoding, and the final threshold comparison. *)
Definition path_tree_decision_work (ps : list nat) : nat :=
  2 * S (length ps) * (1 + 2 * S (length ps)) + S (length ps) + 1.

Fixpoint parent_check_work (ps : list nat) : nat :=
  match ps with [] => 0 | _ :: ps' => S (parent_check_work ps') end.

Lemma parent_check_work_exact (ps : list nat) :
  parent_check_work ps = length ps.
Proof. induction ps; simpl; congruence. Qed.

Definition measured_decision_work (ps : list nat) : nat :=
  farthest_scan_work ps 0 + farthest_scan_work ps (sweep_left ps) +
    parent_check_work ps + 1.

Theorem decide_path_tree_work_bound (ps : list nat) :
  measured_decision_work ps <= path_tree_decision_work ps.
Proof.
  unfold measured_decision_work, path_tree_decision_work.
  rewrite parent_check_work_exact.
  pose proof (farthest_scan_work_bound ps 0).
  pose proof (farthest_scan_work_bound ps (sweep_left ps)). lia.
Qed.

Theorem path_tree_decision_work_quadratic (ps : list nat) :
  path_tree_decision_work ps <= 4 * (S (length ps)) ^ 2 +
    3 * S (length ps) + 1.
Proof.
  set (n := S (length ps)). unfold path_tree_decision_work.
  cbn [Nat.pow]. nia.
Qed.

(* Theorem 3.6: the decision problem is solved by the verified Boolean
   algorithm above, with a quadratic number of structural work units. *)
Theorem theorem_3_6 (ps : list nat) (K : nat) :
  decide_path_tree ps K = true <-> PathDecisionYesAt ps K.
Proof. apply decide_path_tree_correct. Qed.

Theorem theorem_3_6_polynomial_work (ps : list nat) :
  measured_decision_work ps <= 4 * (S (length ps)) ^ 2 +
    3 * S (length ps) + 1.
Proof.
  eapply Nat.le_trans; [apply decide_path_tree_work_bound|].
  apply path_tree_decision_work_quadratic.
Qed.

Print Assumptions theorem_3_6.
Print Assumptions theorem_3_6_polynomial_work.
Print Assumptions theorem_3_1.
Print Assumptions corollary_3_2.
Print Assumptions theorem_3_4.
