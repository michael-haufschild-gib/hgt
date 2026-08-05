# Common-kernel-corrected visible recovery law

- **ID:** common-kernel-corrected-visible-recovery-law
- **Stage:** 2 — fully proven
- **Type:** THEOREM (paper)
- **Parent:** `visible-kernel-recovery-hall-law.md`
- **Status:** `[PROVED HERE] [FORMAL-SOURCE-CHECKED] [NOVELTY NOT CLAIMED]`

## Exact theorem

Use the two-layer setting of visible-kernel recovery: disjoint ambient layers
`S,W`, inputs `U_S <= S`, `U_W <= W`, forward output `C <= W`, detector
`F : U_S -> Z`, and recovery `R : ker F -> S`. Assume

\[
 \operatorname{rank}F+\dim U_W\le\dim(U_W+C)
\]

and total output contains `(U_W+C)+range R`. Injectivity of `R` is not
required. Then

\[
 \boxed{\dim(U_S+U_W)
 \le \dim Y_{out}+\dim\ker R.}                         \tag{1}
\]

If every recovery-zero direction belongs to a specified subspace `N <= S`,
then the sharper intrinsic form is

\[
 \boxed{\dim(U_S+U_W)
 \le \dim Y_{out}+\dim(U_S\cap N).}                   \tag{2}
\]

Thus a family with unavoidable common kernel `N` satisfies exact Hall
expansion after quotienting `N`; equivalently its only possible dimension
defect is the part of input already lying in `N`.

## Proof

The two output layers are disjoint, so

\[
 \dim((U_W+C)+\operatorname{range}R)
 =\dim(U_W+C)+\operatorname{rank}R.
\]

Rank-nullity for `F` and `R` gives

\[
 \dim U_S=\operatorname{rank}F+\dim\ker F,
 \qquad
 \dim\ker F=\operatorname{rank}R+\dim\ker R.
\]

Combining these equalities with visible rank yields (1). If recovery-zero
directions land in `N`, the forgetful map `ker R -> U_S cap N` is injective,
so `dim ker R <= dim(U_S cap N)`, proving (2).

## Physical consequence

For two replicas on a connected graph, take `R` to be the positive graph
edge Casimir on detector-kernel directions. The exact graph energy theorem
proves

\[
 \ker R\subseteq
 \operatorname{span}\{I^{\otimes V},F^{\otimes V}\}.
\]

Its q-local shadow theorem proves the recovery output is literal one-step
Pauli output. Combining these facts with (2) gives the concrete theorem, for
every `q >= 2`,

\[
 \dim(U_S+U_W)\le
 \dim\operatorname{span}\{[H,X]:H\text{ is }q\text{-local Pauli},
 X\in U_S+U_W\}
 +\dim(U_S\cap N),                                      \tag{3}
\]

whenever the visible-rank, hidden-image, and `U_W`-reproduction premises of
the mixed recovery lemma hold. Here `N` is exactly the span of global
identity and global replica swap. Thus the physical singlet recovery
mechanism loses no dimension beyond the two universal modes. This is the
correct unconditional statement; unreduced all-subspaces Hall is false on
any subspace containing either mode.

## Hostile audit

- No quotient is hidden in notation: (2) states exact correction in ambient
  space and is equivalent to quotient Hall only because the family kills `N`.
- `dim N` is not charged globally; only `dim(U_S cap N)` is charged.
- If recovery has extra zero modes outside `N`, hypothesis fails and theorem
  gives no false Hall conclusion.
- Equation (3) is not yet the unconditional all-subspace Hall theorem: its
  visible-rank, hidden-image, and nonsinglet-reproduction premises must still
  be derived for the canonical product-Clifford decomposition.

## Formal status

`HTGeometry/VisibleKernelRecoveryCommonKernel.lean` proves the exact
recovery-kernel correction and its common-kernel specialization as
`visibleKernelRecovery_subspace_finrank_with_kernel` and
`visibleKernelRecovery_subspace_finrank_mod_commonKernel`. Targeted source
elaboration passes. Both axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`. Final umbrella build remains deferred
to final audit.

`HTGeometry/TwoReplicaGraphVisibleRecovery.lean` instantiates the recovery
map with the connected physical graph Casimir and proves (3) as
`finiteTwoReplica_graphVisibleRecovery_finrank_mod_synchronized`. Targeted
source elaboration passes; its axiom audit and the audit of graph-Casimir
swap-range preservation report only the same three standard axioms.

## Log

- 2026-08-05 — dependency-closed proof extracted from hostile audit of the
  unavoidable identity/global-swap kernel.
- 2026-08-05 — formal source and axiom audit complete.
- 2026-08-05 — physical connected-graph mixed recovery theorem formalized
  for every `q >= 2`; remaining premises isolated exactly.
