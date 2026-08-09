# Gapped-eigenstate uniform shortcut floor — Lean certificate

- **ID:** `gapped-eigenstate-uniform-shortcut-floor-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `gapped-eigenstate-uniform-shortcut-floor.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Capstones

`GaloisForLFunctions.HTGeometry.pureStateTraceDistance_pauliEnsembleOp_le` — the card's boxed
`(10)`.  For `n, q ≥ 1`, every coefficient vector within `ε²/(16 m_{n,q})` of the diagonal centre of
the fixed-locality Pauli ensemble, and **every real time** `t`,

    d_tr([e^{-itH_n(J)}Φ], [Φ]) ≤ ε/2 ,        Φ = |0⟩^{⊗n} .

`HTGeometry.eventually_rarityExponent_lt_rampExponent` — the card's `(12)`.  For every `q ≥ 1`,
every time exponent `c > 0`, every exponent deficit `η < 1` and every `ε > 0`, eventually in `n`

    m_{n,q} · log(8 m_{n,q}/(c₀ε²))  <  (1−η) · v_{n,q} · c n log 2 ,

so the Gaussian box floor eventually exceeds the conjectured ramp bound and the bound fails.

## Module map

| Card claim | Module | Principal declaration |
|---|---|---|
| `(1)`--`(2)` | `HTGeometry/GappedEigenlineStability.lean` | `exists_hasEigenvector_of_gap` |
| `(3)` | `HTGeometry/GappedEigenlineTimeUniformFloor.lean` | `pureStateTraceDistance_apply_le_of_gap` |
| `(3)` at `e^{-itH}` | `HTGeometry/SelfAdjointPropagator.lean`, `HTGeometry/GappedEigenlinePropagatorFloor.lean` | `pureStateTraceDistance_propagator_le_of_gap` |
| `(5)` | `HTGeometry/NonidentityPauliWordCount.lean` | `card_nonidentityPauliWords` |
| `(6)` | `HTGeometry/PauliZSetLabels.lean`, `HTGeometry/PauliZGappedHamiltonian.lean` | `diagCLM_zProfile_eq` |
| `(7)` | `HTGeometry/EuclideanDiagonalGappedForm.lean`, `HTGeometry/PauliZGappedHamiltonian.lean` | `zProfile_le_of_ne`, `reApplyInnerSelf_zProfile_le` |
| `(8)`--`(9)` | `HTGeometry/PauliEnsembleBoxNorm.lean` | `norm_pauliEnsembleOp_sub_center_le` |
| `(10)` | `HTGeometry/PauliGaussianBoxShortcutFloor.lean` | `pureStateTraceDistance_pauliEnsembleOp_le` |
| `(11)` | `HTGeometry/GaussianProductBoxFloor.lean` | `gaussianBox_prob_ge` |
| `(12)` | `HTGeometry/PolyLogBeatenByOneMorePower.lean`, `HTGeometry/PauliCountOrderBounds.lean`, `HTGeometry/GaussianBoxBeatsPolynomialRamp.lean` | `eventually_rarityExponent_lt_rampExponent` |
| `(13)` | as `(11)`, plus `HTGeometry/GaussianBoxBeatsPolynomialRamp.lean` | `eventually_rarityExponent_le_polyLog` |

All declarations depend on exactly `[propext, Classical.choice, Quot.sound]`.

## Where the Lean proof departs from the paper proof

**The eigenvector is a Rayleigh maximizer, not an eigenbasis element.**  The card chooses an
orthonormal eigenbasis of `H` and argues that some eigenvalue must exceed `λ₀ − δ`, because
otherwise the convex combination with weights `|c_j|²` would be smaller.  In Lean the unit sphere of
a finite-dimensional space is compact, so the quadratic form attains a maximum there and mathlib's
Rayleigh theory makes the maximizer an eigenvector.  Comparing its Rayleigh value against the value
at `Φ` gives the bound directly.  No eigenbasis, no convex combination, no resolvent.

**The trace distance is inherited, not proved.**  The corpus already owned the pure-state trace
distance and its identification with the density distance up to `√2`, so the triangle inequality
comes from the metric it is a rescaling of.  `(3)` is proved for an arbitrary linear isometry with
an invariant line — that is what makes it uniform in time, since nothing about `e^{-itH}` beyond
fixing the eigenline is used and `t` never appears on the right.

**Unitarity of the propagator needed a missing mathlib instance.**
`NormedSpace.exp_mem_unitary_of_mem_skewAdjoint` requires `NormedAlgebra ℚ 𝔸`, which does not exist
for `E →L[ℂ] E`.  It is supplied rather than worked around: the operator algebra of a complex normed
space carries no rational structure by default — not even a `SMul ℚ` — so there is no diamond, and
the rational algebra is defined through the complex scalars with the norm inequality inherited.  The
instances are scoped.

**The ensemble size is a cardinality, not only a formula.**  `m_{n,q}` is proved to be the literal
number of nonidentity Pauli strings of weight at most `q`, by counting strings of prescribed support
with `Fintype.piFinset` (choice set `univ.erase none`, so `3^{|S|}`) and then grouping by support
and by weight.  Both readings of `m` are used — as the normalisation in `(7)` and as the number of
summands in `(9)`.

**The gap needs only a crude bound.**  The card argues that every non-singleton term "lowers the top
energy by either zero or the same positive amount".  Only the difference from the top matters, so
`zSetSign ≤ 1` suffices: the singleton `Z` string at any occupied site contributes `−1` against `+1`
at the top, and no other term can do better than `+1`.

**The operator-norm bound sees no matrix entries.**  Every Pauli string is a Hermitian involution;
`star` transports through `Matrix.toEuclideanCLM` because it is a star algebra equivalence, and
`P·P = 1` makes the operator unitary, hence of norm at most one.  The triangle inequality over the
`m` terms then gives `(9)`.

**`(11)` is stated in `ℝ≥0∞`**, so no integrability side condition enters: the coordinate estimate
is a lower Lebesgue integral of the density against the constant floor, and `Measure.pi_pi` turns
the box into a product.  The card's `w ≤ 1/16` is not needed — half-width at most one suffices.

**`(12)` fixes the ramp parameters before `n`.**  `c` and `η` enter only through constants, so no
choice of them rescues the conjecture.  That is exactly the card's "false for every proposed
exponential-time window, regardless of its polynomial lower threshold".

## Reusable infrastructure produced

- `HTGeometry/EuclideanDiagonalGappedForm.lean` — diagonal operators on Euclidean space with a real
  symbol: self-adjointness, coordinate action, quadratic form, and the gap inequality at a dominant
  coordinate.  Nothing about qubits.
- `HTGeometry/NonidentityPauliWordCount.lean` — support and weight counts for Pauli strings on a
  finite register.
- `HTGeometry/PauliZSetLabels.lean` — the `Z` string of an arbitrary support, its diagonal form,
  injectivity in the support, and the recovery of an all-`Z` string from its support.
- `HTGeometry/SelfAdjointPropagator.lean` — `NormedAlgebra ℚ (E →L[ℂ] E)` and the propagator of a
  self-adjoint generator as a linear isometry fixing every eigenline.
- `HTGeometry/PauliEnsembleBoxNorm.lean` — unitarity and unit operator norm of every Pauli string,
  and Lipschitz dependence of a Pauli ensemble on its coefficients.
