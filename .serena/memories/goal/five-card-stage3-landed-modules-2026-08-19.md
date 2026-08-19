# Landed Lean modules for the five-card goal (2026-08-19)

All under `formal/GaloisForLFunctions/HTGeometry/`, umbrella-wired, `lake build` green,
`#print axioms` = `propext`/`Classical.choice`/`Quot.sound`.

## Card 5 — markovian return recovery (CLOSED, promoted to 3-formalized)
`HermitianTraceNorm`, `PositiveTraceContraction`, `AncillaBlockMatrix`,
`PositiveMapTraceNormContraction`, `QuantumChannelDiamond`, `MarkovianReturnRecovery`,
`CompletelyPositiveSchwarz`, `UnitalCPInverseRigidity`, `MatrixStarAutomorphismInner`,
`ChannelInverseRigidity`, `MarkovianExactReturn`.
Details: memory `quantum_recurrence/markovian_channel_lean_stack_2026_08_19`.

## Card 1 — fixed-shell angular dephasing (Theorem A)
Algebraic layer: `QuadraticRateOrbitPolynomialField` (works over any char-0 integral domain),
`QuadraticRateMatrixObstruction` (constant rate), `QuadraticRateAnalyticEscape`,
`LocalExtensionQuadraticRateFlatCollapse` (**Lemma A2 unconditional**),
`BellEndpointCompleteBasis` (**Lemma A1 base case**), `EndpointCompleteGenericIntersection`.

NEW this session:
- `SymmetricDescentBaseChange` — **`map_esymmAlgEquiv_symm`**, naturality of the fundamental
  theorem of symmetric polynomials (a real mathlib gap), plus naturality of the whole
  quadratic-rate stack. Proof: forward substitution is natural + `esymmAlgHom` injective.
- `VariableRateMatrixObstruction` — the obstruction with the rate carried as a polynomial;
  `eval_variableRateObstructionPullback`, and the payoff
  `exists_mem_forall_relabelled_quadraticRate_ne_zero`.

Remaining for Theorem A: (a) state the dense maximally-projective set and the open
endpoint-completeness condition in ONE parameter space and intersect (induction step);
(b) feed the Lemma A2 chart into `exists_mem_forall_relabelled_quadraticRate_ne_zero`
as `z₀ / energy₀ / hfail`. Then Theorems B and C.

## Card 2 — fixed-shell transversality
Card is far along: both named blockers were already closed by earlier work
(`abs_oscillatory_le` = `(17b)` via the sphere divergence theorem; `exists_toSphere_sublevel_le`).
NEW this session:
- `AggregatedOscillatoryMass` — `(17)` in aggregated form.
- `SpectralDiscriminantPolynomial` — **`Disc` is a real homogeneous MvPolynomial of degree
  `D(D−1)` in θ**, via the Hankel matrix of power traces `= VᵀV`; reality from Hermiticity;
  `exists_toSphere_spectralDiscriminant_sublevel_le` = **`(18a)`**.
Remaining: `(18b)` (sublevel of `‖∇φ_k‖²`, NOT polynomial — needs either elimination to a
polynomial or the weaker limit `(13)` from card 1's nonflatness); then `(17)`'s ingredient
families, Theorem C, Corollary D.
**`(13)`/`(18b)` is blocked on card 1's fixed-shell nonflatness — do card 1 first.**

## Card 4 — determinant defect
`MicroSpectrumMomentAssembly` (`(M)` at every moment), `FiniteRankTracePrescription`
(`p = 2` free trace), plus NEW:
- `RegularizedDeterminantTraceRecovery` — `det₂` is flat at 0 (`detCoeff_one_eq_zero`,
  `deriv_entireDet2_zero`), `completedDet2`, **`deriv_completedDet2_zero : D'(0) = −c`**,
  `completedDet2_inj`, **`tendsto_completionCoefficient` = necessity of `(DC)` at p=2**.
- `FiniteRankDeterminantCompletion` — `det(1 − z·K|ₛ) = det₂(1−zK)e^{−z·tr K}`
  (`det_one_sub_smul_blockMatrix`) and **`exists_finiteRank_det_tendsto_completedDet2`
  = sufficiency of `(DC)` at p=2**.
So **`(DC)` is closed in both directions at `p = 2`, `dim V = 1`.** Remaining: general `p`
(needs `det_p` on Schatten-`p`, Simon's `R_p` route — big) and `dim V > 1` (fibre is a
polynomial; reduces to the 1-D case by restriction to lines — cheap upgrade, not yet done).
`(RE)`, the trichotomy and the micro-spectrum selection were already closed earlier.

## Card 3 — cusp spectrum radius
No new work. Only gap: Kaczorowski–Perelli standard-twist continuation for a general
Selberg-class member. The corpus has no Selberg-class structure at all. Hardest of the five.

## Traps hit this session
- `simpa using <HasDerivAt combinator>` rewrites the FUNCTION into Pi form (`-fun y => …`,
  `f * g`) and then fails to match. Use `HasDerivAt.congr_deriv h (by ring/simp)` instead,
  and never chain `.congr_deriv` through a metavariable target — break into `have`s.
- `ext i j` on a `Matrix _ _ (MvPolynomial …)` goal keeps going into `coeff`. Use
  `refine Matrix.ext fun i j => ?_`.
- `MvPolynomial.induction_on` case tags are `C`, `add`, `mul_X`.
- `ℝ≥0∞` needs `open scoped ENNReal` in the file itself.
