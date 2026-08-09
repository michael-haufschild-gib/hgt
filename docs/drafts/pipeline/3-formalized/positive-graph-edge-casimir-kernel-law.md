# Positive graph edge-Casimir kernel law

- **ID:** positive-graph-edge-casimir-kernel-law
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Parent:** `visible-kernel-recovery-hall-law.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL] [NOVELTY NOT CLAIMED]`
- **Lean certificate:** `positive-graph-edge-casimir-kernel-law-formalized.md`

## Exact theorem

Let `V` be a finite nonempty set of qubit sites and let `G` be a preconnected
simple graph on `V`. On the doubled matrix algebra, let

\[
 A_{uv;ab}=\operatorname{ad}_{P_{uv;ab}\otimes I+I\otimes P_{uv;ab}}
\]

for every ordered adjacent pair `(u,v)` and Pauli axes `a,b in {1,2,3}`. Put

\[
 K_G=\sum_{(u,v):u\sim v}\sum_{a,b=1}^{3}A_{uv;ab}^{,2}.
\]

Let `S_x` be the product of local replica swaps selected by a Boolean word
`x : V -> {0,1}`, and let `iota(c)=sum_x c_x S_x`. Then

\[
 K_G\,\iota(c)=0
 \quad\Longleftrightarrow\quad
 c=a\,\delta_{\mathbf 0}+b\,\delta_{\mathbf 1}
\]

for some complex `a,b`. Thus one graph-summed operator, not a family of
separate edge equations, has exactly global identity and global replica swap
as its kernel on the complete product-Clifford singlet sector.

Moreover every summand is a literal square of one weight-two collective Pauli
commutator. If a subspace `W` contains every first image
`A_{uv;ab}s`, then `K_G s` belongs to the one-step shadow
`sum_{uv;ab} A_{uv;ab}W`. Hence `K_G` is the recovery map required by the
visible-kernel argument after removing its two universal zero modes.

## Proof

Equip the matrix algebra with its Hilbert--Schmidt inner product. For a
Hermitian matrix `H`, cyclicity of trace gives

\[
 \langle [H,X],Y\rangle_{HS}=\langle X,[H,Y]\rangle_{HS}.
\]

Every doubled collective Pauli generator is Hermitian, so every
`A_{uv;ab}` is self-adjoint as a superoperator. Therefore

\[
 \langle X,K_GX\rangle_{HS}
   =\sum_{(u,v):u\sim v}\sum_{a,b}
      \|A_{uv;ab}X\|_{HS}^{2}.                    \tag{1}
\]

If `K_G X=0`, the left side of (1) vanishes. Every summand on the right is
nonnegative, so every `A_{uv;ab}X` vanishes. Consequently each literal edge
Casimir `K_{uv}=sum_{a,b} A_{uv;ab}^2` vanishes. For `X=iota(c)`, the already
proved physical edge-Casimir intertwinement says this is equivalent to
`c_x=0` whenever `x_u != x_v`. Connectedness then forces support only on the
two constant Boolean words. Conversely those two words are annihilated by
every edge Casimir, hence by their graph sum.

Finally, if every first image of `s` is in `W`, then each
`A_{uv;ab}^2s=A_{uv;ab}(A_{uv;ab}s)` is in the corresponding image of `W`.
Summing proves the shadow-containment statement. No cancellation, spectral
gap, or unproved positivity premise is used.

## Hostile audit

- Common-kernel information alone would not imply the kernel of a sum. Exact
  Hilbert--Schmidt energy identity (1) supplies missing noncancellation.
- Graph sum is over ordinary weight-two collective Pauli commutators; no
  coefficient-space surrogate enters theorem statement.
- Kernel classification is restricted to exact product-Clifford singlet
  range. It does not claim `K_G` has only two zero modes on full matrix space.
- Recovery is injective only after deleting global identity and global swap.
  Quotient/complement implementation remains separate.
- This theorem closes singlet recovery only. It does not prove nonsinglet
  Hall expansion, circuit anti-concentration, complexity growth, plateau, or
  recurrence scales.

## Formal status

`HTGeometry/TwoReplicaPositiveGraphEdgeCasimir.lean` proves:

- the matrix-to-Euclidean Hilbert equivalence and exact Hilbert--Schmidt inner
  product identity;
- trace-cyclic self-adjointness of Hermitian commutators;
- self-adjointness and squared-energy identity for literal collective Pauli
  commutators;
- the ordered-edge graph Casimir and exact sum-of-squares graph energy;
- the connected singlet-sector kernel classification for the single graph
  sum;
- q-local shadow containment for every `q >= 2`;
- the physical synchronized two-mode submodule and exact identity
  `ker K_G cap range(iota) = span{global identity, global swap}`.

`HTGeometry/GraphEdgeCasimirSingletKernelRank.lean` adds the two facts the "after removing its two
universal zero modes" clause needs, and restates the classification on the singlet sector as the
card names it:

- `finiteTwoReplicaGlobalSynchronizedMap_injective` and
  `finrank_finiteTwoReplicaGlobalSynchronizedSubmodule` — the global identity and the global replica
  swap are independent on a nonempty register, so the synchronized sector is *exactly*
  two-dimensional.  Independence is injectivity of the coefficient embedding together with
  `twoReplicaAllIdentity ≠ twoReplicaAllSwap`; nothing about the Casimir enters.
- `finiteTwoReplicaPhysicalGraphCasimir_ker_inf_twirlRange` and its rank — the same classification
  with the singlet sector written as the product-Clifford twirl range, which is what the card means
  by "the complete product-Clifford singlet sector".  The two descriptions agree by
  `finiteProductCliffordTwoReplicaTwirl_range_eq`.

Umbrella build passes; the axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Log

- 2026-08-05 — dependency-closed paper proof after corpus audit found finite
  master-constraint and positive-operator machinery in HTGeometry/RHTower.
- 2026-08-05 — formal source and axiom audit complete.
- 2026-08-09 — umbrella build closed; the two universal zero modes counted, and the
  classification restated on the twirl range.
