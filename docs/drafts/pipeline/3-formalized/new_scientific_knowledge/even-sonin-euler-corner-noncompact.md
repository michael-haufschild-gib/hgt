# Even Sonin Euler corner is noncompact

- **ID:** even-sonin-euler-corner-noncompact
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper source:** `../../2-fully-proven/new_scientific_knowledge/sonin-euler-metric-corner-noncompact.md`
- **Lean endpoint:** `formal/GaloisForLFunctions/RHTower/HardyTitchmarshEulerConcrete.lean`

## Statement

Let `a > 0` and `p > 1`. On `L²(ℝ)^ev`, let `A_a` be the central-interval indicator
projection, let `R_a = F⁻¹ A_a F`, and let `Q_a` be the orthogonal projection onto

`ker(A_a) ∩ ker(R_a)`.

For the normalized dilation `U_p f(x) = sqrt(p) f(px)`, the restricted lower corner

`(1 - Q_a) (U_p + U_p⁻¹) Q_a`

is not compact. The positive Euler corner is exactly its nonzero scalar multiple

`-(sqrt(p))⁻¹ (1 - Q_a) (U_p + U_p⁻¹) Q_a`,

and is therefore noncompact. This holds for every real scale `p > 1`; the Lean theorem also
exports the specialization to every prime natural number.

The paper source now strengthens this formalized theorem to

`||(1-Q_a)(U_p+U_p⁻¹)Q_a||_ess=1`

and

`||(1-Q_a)E_pQ_a||_ess=p^(-1/2)`.

Those equalities use an explicit Calkin partial-isometry computation. The companion module
`SoninEulerCalkinPartialIsometry.lean` formalizes the exact initial/final shell projections and
the Calkin partial-isometry law, while `SoninEulerQuadraticCorner.lean` formalizes the sharp lower
half: for every compact `K`,

`1 <= ||(1-Q_a)(U_p+U_p⁻¹)Q_a-K||`,

and the corresponding positive Euler coefficient lower bound.

Both equalities are now unconditional Lean theorems. `SoninCalkinNormBound.lean` defines
`essentialNorm` as the distance to the compact ideal and proves the quotient-free upper bound
from the compact congruence; `SoninEulerEssentialNorm.lean` proves the one-scale
initial-projection law `L^*L =_K Σ(a, pa)`, the one-scale Calkin partial isometry, and the exact
equalities `essentialNorm L = 1`, `essentialNorm C_p = (sqrt p)⁻¹`, and
`essentialNorm (archimedeanPrimeEulerCorner a p) = (sqrt p)⁻¹`, with prime specializations.

## Formal surface

The endpoint module proves:

- `evenCentralSoninProjection_eq_starProjection`
- `evenCentralSoninDilationCorner_eq_crossBoundary`
- `evenCentralSoninDilationCorner_not_isCompactOperator`
- `evenCentralPositiveEulerCorner_eq_smul`
- `evenCentralPositiveEulerCorner_not_isCompactOperator`
- `evenCentralPrimePositiveEulerCorner_not_isCompactOperator`
- `archimedeanDualHardyTitchmarshUnitary_evenDilation`
- `archimedeanPrimeLocalFactor_ae`
- `hardyTitchmarshLocalFactor_archimedean_eq`
- `archimedeanPrimeEulerWeight_eq_norm_sq`
- `archimedeanPrimeEulerGram_ae`
- `archimedeanPrimeEulerCorner_pullback`
- `archimedeanPrimeEulerCorner_not_isCompactOperator`
- `archimedeanPrimeEulerCorner_natPrime_not_isCompactOperator`

The companion sharp-distance module additionally proves:

- `one_le_norm_evenCentralSoninDilationCorner_sub_compact`
- `norm_eulerCoefficient_le_norm_evenCentralPositiveEulerCorner_sub_compact`

The companion Calkin-complement module additionally proves:

- `soninIntersectionProjection_eq_resolventFormula`
- `isCompactOperator_soninIntersectionProjection_sub_complement`
- `isCompactOperator_centralSoninProjection_sub_complement`
- `isCompactOperator_evenCentralSoninProjection_sub_complement`

The companion Calkin partial-isometry module additionally proves:

- `evenCentralSoninQuadraticCorner_adjoint_mul_compactEq_shell`
- `evenCentralSoninQuadraticCorner_mul_adjoint_compactEq_shell`
- `evenTwoPolarizationShell_isCalkinProjection`
- `evenCentralSoninQuadraticCorner_isCalkinPartialIsometry`

The companion essential-norm modules additionally prove:

- `essentialNorm` with `essentialNorm_eq_of_bounds`, `essentialNorm_smul`,
  `essentialNorm_unitaryPush`
- `exists_isCompactOperator_norm_sub_le_one_add` and
  `isCompactOperator_of_adjoint_mul_compactEq_zero` (the quotient-free cut arguments)
- `evenCentralSoninDilationCorner_adjoint_mul_compactEq_shell`
- `evenCentralSoninDilationCorner_isCalkinPartialIsometry`
- `essentialNorm_evenCentralSoninDilationCorner` (`= 1`)
- `essentialNorm_evenCentralPositiveEulerCorner` (`= (sqrt p)⁻¹`)
- `essentialNorm_archimedeanPrimeEulerCorner` and
  `essentialNorm_archimedeanPrimeEulerCorner_natPrime`

The proof is internal to the even carrier. It constructs an orthonormal sequence of symmetric
shell indicators, projects it into the two-constraint Sonin carrier, proves that the correction
tends to zero, and obtains a uniform lower bound on the crossed image of the resulting bounded
weakly-null sequence. It does not infer restricted noncompactness from the ambient full-`L²`
theorem.

The imported analytic chain supplies every premise:

- `L2FourierIntegralBridge.lean` identifies the unitary `L²` Fourier transform with the classical
  Fourier integral on integrable representatives.
- `BoundedSupportFourierUncertainty.lean` and `L2FourierUncertainty.lean` prove that simultaneous
  bounded physical and Fourier support forces an `L²` function to vanish.
- `FiniteTimeBandFourierCompact.lean` proves compactness of the finite time-band block by finite-rank
  approximation of its `L²` functional field.
- `SoninAlternatingBlockStrict.lean` converts compactness and absence of a `1`-eigenvector into the
  strict norm bound needed by `SoninProjectionCorrection.lean`.
- `SoninL2Model.lean` and `SoninL2ShellNull.lean` construct the cutoffs, normalized dilations,
  symmetric shell sequence, and asymptotically null Fourier constraint.
- `L2FourierReflection.lean` proves Fourier/reflection compatibility, allowing every operator and
  witness to be restricted to `L²(ℝ)^ev`.
- `L2MellinUnitary.lean` constructs Mellin--Plancherel from multiplicative Haar `L²`, including the
  exact `2π` normalization and the dilation-to-`p^(is)` intertwining identity.
- `EvenL2LogUnitary.lean` constructs the exact Jacobian unitary from even physical `L²(dx)` to
  additive logarithmic `L²(dt)`.
- `HardyTitchmarshBetaInfinity.lean` constructs multiplication by
  `Gamma_R(1/2+is)` as a unitary into `L²(ds/|Gamma_R(1/2+is)|²)` and transports the prime phases.
- `HardyTitchmarshSourceTransport.lean` builds the source-image carrier projection, local-factor
  Gram, corner pullback, and preservation of noncompactness under unitary transport.
- `HardyTitchmarshEulerConcrete.lean` composes these maps into the concrete archimedean dual
  Hardy--Titchmarsh unitary and proves the pointwise local-factor and `M_(w_p)` formulas.

## Verification

- The endpoint module passes a targeted Lean build.
- `#print axioms` for the projection identity, both noncompactness theorems, the scalar identity,
  and the prime specialization reports only `propext`, `Classical.choice`, and `Quot.sound`.
- The endpoint contains no `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration.
- No full project build is part of this card's verification.

## Exact boundary

This card formalizes both the unconditional analytic theorem on the exact even Sonin carrier and
its concrete archimedean dual Hardy--Titchmarsh transport. Lean constructs the logarithmic
Jacobian, Mellin--Plancherel normalization, `beta_infinity`, weighted critical-line space, prime
phase multipliers, pointwise local factor, positive Euler multiplier `M_(w_p)`, source-image
projection, exact pullback, and source noncompactness.

It does not separately construct the de Branges entire-function object `B_lambda` or prove that
the source-image carrier equals an independently defined entire-function realization. It also does
not encode the full `{infinity,p}` space and the `theta_p`/`iota'_p` cancellation square. Those
identifications are not used as assumptions in the formal source theorem: its carrier is the actual
unitary image of the exact even Sonin carrier. General Schatten ideals are not represented in the
current Lean layer, so the consequence that a noncompact operator lies in no finite Schatten class
remains a paper-level corollary. The exact numerical essential norms are formal:
`SoninCalkinNormBound.lean` carries the in-tree `essentialNorm` and its quotient-free upper-bound
machinery, and `SoninEulerEssentialNorm.lean` states the equalities `||L||_ess=1` and
`||C_p||_ess=p^(-1/2)` through the literal archimedean source operator. The operator identity is
also formal: `SoninProjectionCalkin.lean` proves `Q_a = 1-A_a-R_a` modulo compact operators on the
actual even carrier, and `SoninEulerCalkinPartialIsometry.lean` identifies both shell projections
and proves the mixed Gram entry is a partial isometry modulo compacts. The separate module
`SoninEulerQuadraticCorner.lean` formalizes the sharp lower distance from compact operators for both
the one-scale corner and every ordered quadratic product.

## Dual gate

- **NOVEL:** The common Sonin constraint does not regularize the prime-dilation shell crossing.
  This is stronger than ambient support crossing and is proved for every real scale `p > 1`, with
  primes as a specialization.
- **SIGNIFICANT:** The result closes the unsmoothed positive Euler corner as a compact or trace-ideal
  seam on the fixed-cutoff even carrier. Any viable determinant construction needs additional
  smoothing or a different relative operator.

## Gates

- [x] 0 -> 1: fixed-cutoff even carrier, operator normalization, and degenerate parameters isolated.
- [x] 1 -> 2: corrected-shell proof completed on paper.
- [x] 2 -> 3: analytic theorem and prime specialization formalized unconditionally in Lean.
- [x] Strengthened 2 -> 3: the projection complement, cutoff/dilation multiplication, exact shell
  projections, Calkin partial-isometry law, and the exact essential-norm equalities `1` and
  `p^(-1/2)` (dilation, Euler, and concrete source forms) are formalized.
- [ ] 3 -> 4: requires the separate `B_lambda` entire-function identification and an independent
  publication audit; the concrete source-unitary transport is complete.
