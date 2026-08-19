# Landed Lean modules for the five-card goal (2026-08-19)

All under `formal/GaloisForLFunctions/HTGeometry/`, umbrella-wired, `lake build` green,
`#print axioms` = `propext`/`Classical.choice`/`Quot.sound`, lint reports no proof debt.

## Card 5 — markovian return recovery (CLOSED, promoted to 3-formalized)
`HermitianTraceNorm`, `PositiveTraceContraction`, `AncillaBlockMatrix`,
`PositiveMapTraceNormContraction`, `QuantumChannelDiamond`, `MarkovianReturnRecovery`,
`CompletelyPositiveSchwarz`, `UnitalCPInverseRigidity`, `MatrixStarAutomorphismInner`,
`ChannelInverseRigidity`, `MarkovianExactReturn`.
Details: memory `quantum_recurrence/markovian_channel_lean_stack_2026_08_19`.

## Card 1 — fixed-shell angular dephasing (Theorem A)
- `QuadraticRateOrbitPolynomialField` — labeling-orbit obstruction over any characteristic-zero
  **integral domain** (generality is what allows the rate to be a variable: instantiate at
  `K := MvPolynomial θ ℂ`).
- `QuadraticRateMatrixObstruction` — pullback through the characteristic coefficients; one complex
  witness ⇒ nonzero somewhere in every nonempty open set of real parameters.
- `QuadraticRateAnalyticEscape` — chart escape via the finite-product identity theorem.
- `LocalExtensionQuadraticRateFlatCollapse` — **Lemma A2 unconditional** (`hL` removed);
  `exists_localField_quadraticRate_not_eventually` is the `hlabel` interface.
- `BellEndpointCompleteBasis` — **Lemma A1 base case**: `reducedTransition ψ φ =
  reshape φ * (reshape ψ)ᴴ`, so a maximally entangled orthonormal basis is endpoint complete;
  `exists_endpointComplete_twoQubit_witness`.
- `EndpointCompleteGenericIntersection` — the induction step as an intersection of an open
  endpoint-completeness condition with a dense/residual genericity set.

Remaining: match the genericity theorem and the openness theorem in one parameter space; the
rate-as-variable instantiation (needs base-change naturality of `MvPolynomial.esymmAlgEquiv`,
absent from mathlib); the `(z,g)`-chart to `Fin m → ℂ` bridge.

## Card 2 — fixed-shell transversality
- `AggregatedOscillatoryMass` — `oscFactor`, `sum_norm_setIntegral_le_measure` (**the discarded
  region costs one copy of its measure, not that times the number of terms** — the load-bearing use
  of Theorem A), `norm_integral_sub_diagonal_le`,
  `norm_integral_sub_diagonal_le_measureReal_add` = **`(17)` in aggregated form**.
Remaining: supply the two ingredient families (good-region bounds from `abs_oscillatory_le`,
mass from `replica_variation_le_one`) for the actual fixed-shell spectral data; then `(18a)–(18c)`,
Theorem C, Corollary D.

## Card 4 — determinant defect
- `MicroSpectrumMomentAssembly` — **`(M)` assembled**: `rootBlockMultiset`,
  `exists_block_realizing`, `exists_multiset_moment_realization` (all moments `1..n`, `n < p`,
  inside any Schatten-`p` budget).  Cost identity is exponent-free:
  `kN‖t‖^p = ‖R‖·‖t‖^{p−k}`.
- `FiniteRankTracePrescription` — `HilbertSchmidt.diagBlock` and
  `exists_finiteSupport_hsNorm_sub_lt_and_hsTraceDiag_eq`: **finite-rank HS approximation with any
  prescribed diagonal trace** = the `p = 2` sufficiency of `(DC)`.
Remaining: `det_p` on Schatten `p` (Simon's `R_p` route) and the necessity direction of `(DC)`.
For `p = 2` the corpus already owns `entireDet2` and its HS-continuity, so the `p = 2` necessity is
a short argument: `D_n(z) = det₂(1−zK_n)e^{−z tr K_n}`, `D_n'(0) = −tr K_n` because `det₂` has no
linear term, so locally uniform convergence pins the trace.

## Card 3 — cusp spectrum radius
No new work this session.  Only gap: Kaczorowski–Perelli standard-twist continuation for a general
Selberg-class member.  The corpus has no Selberg-class structure at all.
