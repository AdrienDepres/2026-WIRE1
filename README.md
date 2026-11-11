# Rocq formalisation for the paper

This directory contains the Rocq source files for the results formalised in
the paper. The development uses Rocq 9.2 and the Rocq standard library only.
It has no external graph-library dependency, `Admitted`, or additional axioms.

## Build

From this directory, with Rocq 9.2 available on `PATH`, run:

```sh
make
```

If Rocq is installed in an opam switch, activate the switch first with
`eval "$(opam env)"`. To pass an explicit executable, run
`make ROCQ=/path/to/rocq`. The files compile in this order:

1. `CorrectionReview.v`
2. `Tree33.v`
3. `Theorem36.v`
4. `Theorem51.v`

The `Print Assumptions` commands at the end of the principal files report
`Closed under the global context` for the headline theorems and work bounds.

## Where each paper result is stated

The line numbers below point to the Rocq declaration, rather than to a proof
step. After uploading this directory to GitHub, each paper symbol can link to
the corresponding file with a URL fragment such as
`blob/main/rocq-paper-proofs/Theorem36.v#L<line>`.

| Paper result | Rocq statement | What the statement establishes |
| --- | --- | --- |
| Theorem 3.1 | `Theorem36.v`, line **623** (`theorem_3_1`) | Every placement has score at least twice the number of tree edges minus the distance between its first and last offices. |
| Corollary 3.2 | `Theorem36.v`, line **1115** (`corollary_3_2`) | Replacing the endpoint distance by the tree diameter gives a lower bound for every placement. |
| Theorem 3.3 | `Tree33.v`, line **296** (`theorem_3_3_graph`) | From any vertex, two farthest-vertex scans return a diameter of the finite tree graph. The relational theorem at line 309 also covers every tie choice. |
| Theorem 3.4 | `Theorem36.v`, line **1292** (`theorem_3_4`) | The constructed diameter-guided order is a bijective placement, attains the stated score, and is optimal. |
| Corollary 3.5 | — | The linear-time running-time claim is not proved by this development. The verified list-based decision procedure has a quadratic structural-work bound. |
| Theorem 3.6 | `Theorem36.v`, line **1497** (`theorem_3_6`) | The Boolean decision procedure accepts exactly the positive path--tree instances in the parent-list encoding. Its structural work is polynomial, with the explicit quadratic bound in `theorem_3_6_polynomial_work` at line 1501. |
| Theorem 5.1 | `Theorem51.v`, line **325** (`theorem_5_1`) | DASAS instances in the parent-list encoding are positive exactly when the certificate verifier accepts some placement. The verifier's polynomial structural-work bound is stated at line 469. |
| Theorems 5.2--5.3 | — | The Exact Cover by 3-Sets reduction and the resulting NP-hardness/NP-completeness claims are not formalised here. |

Theorem 3.1 is also proved in the stronger additive form
`path_score + endpoint_distance >= 2 * number_of_edges` by
`path_score_lower_bound`. Theorem 3.4's order is computed by
`diameter_dfs_order`, whose leaf-recursive correctness is stated in
`diameter_dfs_order_correct`. The proof produces an optimal order by inserting
side-branch leaves next to their parent in the current order. The development
proves the placement and score properties used by the theorem; it does not
prove a running-time bound for this order construction or a separate
step-by-step equivalence to a generic DFS implementation.

## Tree and problem encodings

For a parent list `ps`, the vertices are `0, ..., length ps`. Each list entry
records the parent of a newly attached leaf, and `valid_parents ps` ensures
that the parent already exists. This inductively constructs a finite
undirected tree. `Tree33.v` defines its unit-edge relation and proves that
`tdist` is the graph's shortest-path distance. The four-point metric fact
needed by the two-sweeps proof is derived from the leaf-attachment recursion
in `CorrectionReview.v`; it is not assumed for the final graph theorem.

`Theorem36.v` models a path placement as a permutation of the office vertices
and sums the tree distance between consecutive offices. `Theorem51.v` models
DASAS using two equal-size parent lists. A certificate is a permutation of
office vertices, and its score sums office-tree distances over the
collaborator-tree edges.

The parent-list encoding represents trees built by leaf attachment. The
development does not formalise a conversion from an arbitrary graph given by
an adjacency list to this representation. Likewise, the polynomial work
theorems use explicit structural cost models with unit-cost arithmetic; they
are not bit-level Turing-machine complexity proofs. In particular, Corollary
3.5's linear-time bound for a depth-first implementation is not proved here.

Theorem 5.4 is cited as the standard NP-hardness result for Exact Cover by
3-Sets; it is not proved in this Rocq development.
