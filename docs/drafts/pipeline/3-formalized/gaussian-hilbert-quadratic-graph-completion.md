# Gaussian Hilbert quadratic graph completion law

- **ID:** gaussian-hilbert-quadratic-graph-completion
- **Stage:** 3-formalized
- **Type:** FAILURE-DRIVEN MULTIVARIABLE SURVIVOR (Lean)
- **Novelty:** `[NOVELTY CANDIDATE PENDING EQUIVALENCE AUDIT]`; no discovery claim
- **Parent card:** `gaussian-hilbert-fano-curvature`

## Statement

Let `E` and `W` be finite-dimensional real Hilbert spaces, let

\[
 T\subseteq\operatorname{Sym}^2(E),\qquad e=\dim E,\qquad m=\dim T,
\]

and let `L : T -> W` be any linear map.  In the symmetric Fock space over `E direct-sum W`,
put

\[
 S_L=\mathbb R\Omega\oplus E\oplus\{q+Lq:q\in T\}.
\]

Then `S_L` is invariant under every annihilation operator.  If `Z_L(t)` is the squared norm of
its top exterior vector after homogeneous degree `n` is scaled by `t^(n/2)`, then

\[
 Z_L(t)=t^{e+m}\det(tI_T+L^*L).                            \tag{1}
\]

If `lambda_1,...,lambda_m` are the eigenvalues of `L^*L` and

\[
 p_j(t)=\frac{t}{t+\lambda_j},
\]

the induced degree variable has the exact law

\[
 D\;\overset{\rm law}=\;e+m+\sum_{j=1}^m B_j,
 \qquad B_j\sim\operatorname{Bernoulli}(p_j(t))
\]

with independent `B_j`.  In particular,

\[
 \mathbb E_tD-\operatorname{Var}_t(D)
   =e+m+\sum_{j=1}^m p_j(t)^2.                             \tag{2}
\]

Thus every nontrivial quadratic graph completion is strictly sub-Poisson at every positive
scale.

## Dependency-closed proof

### 1. Annihilation invariance

The vacuum is killed by every annihilator.  Annihilation in a direction of `E` maps
`q+Lq` to the first-degree vector obtained by differentiating `q`, hence into `E`.
Annihilation in a direction of `W` kills `q` and maps the first-degree vector `Lq` to a scalar
multiple of the vacuum.  Annihilation maps `E` to the vacuum.  Therefore all annihilators
preserve `S_L`.

Conversely, this is the canonical form of every nonzero finite polynomial subspace `S` of
symmetric Fock space that is invariant under all annihilators and has maximal degree at most
two.  Indeed, repeated differentiation puts the vacuum in `S`.  If `E` is its degree-one symbol
and `T` its degree-two symbol, invariance forces every contraction of `T` into `E`, hence
`T subset Sym^2(E)`.  The kernel of the top-symbol map is `R Omega direct-sum E`.  Changing a
section by this kernel removes its constant and `E`-linear corrections; the remaining linear
correction is a uniquely gauged map `L : T -> E^perp`.  Taking `W=E^perp` gives the displayed
form.  Thus the theorem covers the entire annihilation-invariant quadratic stratum, not merely
a selected graph family.

### 2. Orthogonal graph Gram operator

The vacuum, `E`, `T`, and `W` lie in mutually orthogonal Fock channels except that the graph
vector combines one vector of `T` with one of `W`.  Degree dilation sends

\[
 q+Lq\longmapsto tq+\sqrt t\,Lq.
\]

For `q,r in T`, orthogonality of `T` and `W` gives

\[
 \langle tq+\sqrt tLq,tr+\sqrt tLr\rangle
 =\langle q,(t^2I+tL^*L)r\rangle.
\]

The `e` first-degree vectors in `E` contribute `t^e` to the squared exterior norm.  The graph
block contributes the determinant of its Gram operator, so

\[
 Z_L(t)=t^e\det(t^2I+tL^*L)
       =t^{e+m}\det(tI+L^*L),
\]

which proves (1).

### 3. Bernoulli factorisation

The spectral theorem gives an orthonormal eigenbasis of the positive operator `L^*L`, with
nonnegative eigenvalues `lambda_j`.  Therefore

\[
 Z_L(t)=t^{e+m}\prod_j(t+\lambda_j).
\]

After normalisation at a fixed `t>0`, each factor contributes independently either no extra
degree, with weight `lambda_j`, or one extra degree, with weight `t`.  Hence its success
probability is `p_j(t)=t/(t+lambda_j)`, proving the asserted degree law.

### 4. Exact Fano margin

Independence gives

\[
 \mathbb E_tD=e+m+\sum_jp_j(t),\qquad
 \operatorname{Var}_t(D)=\sum_jp_j(t)(1-p_j(t)).
\]

Subtracting yields

\[
 \mathbb E_tD-\operatorname{Var}_t(D)
 =e+m+\sum_jp_j(t)^2,
\]

which is (2).  It is strictly positive whenever `e+m>0`.

## Anti-theatre audit

- Determinants of graph Gram operators, the finite-dimensional spectral theorem, and sums of
  independent Bernoulli variables are parent theory.
- The scientific candidate is the **completion mechanism**: flattening the quadratic lowering
  weights inside a standard Fock metric necessarily creates transverse annihilation channels,
  and their exact contribution turns the false radial commuting-tuple defect into (2).
- This is not yet the unrestricted annihilation-invariant law.  It completely closes the
  maximal-degree-two polynomial stratum, including every rank, ambient dimension, and non-graded
  correction, and supplies the induction model for higher filtered inverse systems.
- An exact equivalence-level literature audit is still required before any novelty claim.

## Lean ownership

Formalise in three layers:

1. the finite graph Gram identity `t^2 I + t L^T L` and determinant factorisation;
2. the Bernoulli mean--variance square law;
3. the connector identifying the graph exterior-volume degree law with those two layers.

`[LEAN-PROVED PARENT LAYERS]` Layers 1 and 2 compile unconditionally in
`GaloisForLFunctions.HilbertMetric.QuadraticGraphCompletion`.

`[LEAN-PROVED]` The exterior-volume half of layer 3 now compiles in
`GaloisForLFunctions.HilbertMetric.QuadraticGraphFockConnector` (imported by
`GaloisForLFunctions.HilbertMetric`; no warnings; `#print axioms` = `propext, Classical.choice,
Quot.sound`).

The module realises the truncated symmetric Fock space of degrees at most two over the mode set
`E ⊕ W` as `QuadFockIdx e κ = Sym (Fin e ⊕ κ) 0 ⊕ Sym (Fin e ⊕ κ) 1 ⊕ Sym (Fin e ⊕ κ) 2`, with the
three homogeneous channels `quadDegZero`, `quadDegOne`, `quadDegTwo` and the degree dilation
`quadFockDilate t` (degree `n` scaled by `t^(n/2)`).  All six mutual channel inner products are
computed (`quadFockInner_degZero_degOne`, `quadFockInner_degOne_degTwo`, …), with
`quadFockInner_degOne_degOne` transporting the degree-one sum along `Sym.oneEquiv`.

* `quadFockFamily q L t` — the dilated spanning family of `S_L`: the vacuum, the `e` base modes,
  and the graph vectors `q r + L (q r)` with `q r` a degree-two vector and `L (q r)` transverse;
* `quadFockGram_quadFockFamily` — its Gram is exactly
  `fromBlocks 1 0 0 (fromBlocks (t • 1) 0 0 (quadraticGraphGram L t))`, i.e. the three channels are
  mutually orthogonal and the graph block is the layer-1 Gram `t² I + t LᵀL`;
* `quadraticFockVolume_eq` — hence
  `Z_L(t) = t^(e+m) * det (t • 1 + Lᵀ L)`, which is `(1)` of this card.

The only hypothesis on the degree-two family is orthonormality
(`∀ r s, ∑ β, q r β * q s β = if r = s then 1 else 0`); no rank, genericity, or graded-splitting
assumption is used, so this covers the whole annihilation-invariant quadratic stratum in the sense
of the paper proof.

### Annihilation invariance

The mode annihilators are assembled from the canonical symmetric-Fock lowering matrices of
`SymmetricFockShadow`:

```lean
quadFockAnnihilation (i : QuadMode e κ) (v : QuadFockIdx e κ → ℝ) : QuadFockIdx e κ → ℝ
  | Sum.inl a       => ∑ α, symmetricFockAnnihilationMatrix 0 i a α * v (Sum.inr (Sum.inl α))
  | Sum.inr (inl α) => ∑ β, symmetricFockAnnihilationMatrix 1 i α β * v (Sum.inr (Sum.inr β))
  | Sum.inr (inr _) => 0
```

* `quadFockAnnihilation_add`, `quadFockAnnihilation_smul` — linearity;
* `quadFockAnnihilation_degZero` — the vacuum is killed;
* `quadFockAnnihilation_degOne` — `a_i` sends `quadDegOne u` to `quadDegZero (u i)`, i.e. a one-mode
  vector to the corresponding multiple of the vacuum;
* `quadFockAnnihilation_degTwo` — `a_i` sends `quadDegTwo w` to `quadDegOne (quadLower i w)`;
* `quadLower_transverse_eq_zero` — a degree-two vector supported on base multisets lowers into the
  base modes, which is exactly why the transverse channel is not re-entered;
* `quadraticGraphSubspace q L` — the subspace `S_L` itself;
* `quadFockAnnihilation_mem_quadraticGraphSubspace` — **`S_L` is invariant under every mode
  annihilator**, by span induction over the three generator kinds;
* `quadraticGraphCompletion_invariant_and_volume` — invariance and the volume law in one statement.

The support hypothesis `∀ r β, (∃ k : κ, Sum.inr k ∈ (β : Multiset _)) → q r β = 0` says exactly
that `T ⊆ Sym²(E)`; the Gram half does not need it.

## Log

- 2026-07-19 -- extracted from the exact failure of the arbitrary commuting-tuple
  strengthening in eight modes; completed the basis-free paper proof of the standard-Fock
  quadratic graph completion law.
- 2026-07-19 -- compiled the graph Gram/determinant factorisation and the Bernoulli Fano
  identity; the symmetric-Fock exterior connector remains to be formalised.
- 2026-07-26 -- compiled the exterior-volume half of layer 3: the truncated symmetric Fock model,
  the channel inner products, the exact block Gram of the dilated graph family, and the volume law
  `Z_L(t) = t^(e+m) det (t I + Lᵀ L)`.  Annihilation invariance of the span is the only remaining
  Lean item on this card.
- 2026-07-26 -- closed layer 3: assembled the canonical mode annihilators on the truncated Fock
  space, proved `S_L` annihilation invariant, and packaged invariance with the volume law.  Card
  moved to `3-formalized`.
