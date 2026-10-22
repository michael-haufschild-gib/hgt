# Xi reciprocal-square source universality law

- **ID:** xi-reciprocal-square-source-universality-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper-proved and Lean-formalized)
- **Source:** Post-Law-22 scan of terminal reciprocal-square operator and source classifiers
- **Statement:** Self-adjointness of the squared reciprocal Xi operator is
  equivalent simultaneously to unsquared self-adjointness, Clifford polarization, quadratic
  reality on the full continued-Cauchy core, rank-one Cauchy family, and countable
  Gaussian-rational family, vanishing of all countable scalar orientation defects, reality of all
  centered reciprocal-square coordinates, and both target and continued prime--Gamma sector signs.

## Gates

- [x] 0 → 1 in-progress: theorem-first component and exact hypotheses
- [x] Complete paper proof with no open dependency
- [x] Lean direct check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Lean inputs read

1. `xiReciprocalSquareOperator_isSelfAdjoint_iff_riemannHypothesis` is the squared-operator base.
2. `xiReciprocalOperator_isSelfAdjoint_iff_rh` and
   `xiReciprocalCliffordPolarization_iff_riemannHypothesis` give unsquared and Clifford charts.
3. Continued-core, rank-one, and Gaussian-rational Cauchy quadratic-reality predicates are each
   separately equivalent to RH.
4. Gaussian-rational scalar orientation-defect vanishing is separately equivalent to RH.
5. `xiHurwitzOrientationEnergy_eq_zero_iff_centralSpectrum_real` gives complete centered
   reciprocal-square coordinate reality; zero orientation energy is exact for RH.
6. Target-coordinate and continued prime--Gamma reciprocal-square upper-sector nonnegativity are
   each separately equivalent to RH.

## Internal noncollision audit

`scripts/formal_tools.py research "Xi reciprocal square Clifford Gaussian rational orientation
Cauchy quadratic self adjoint"` returned the individual bridge modules but no common consumer.
Direct symbol-use search shows every terminal classifier except the local Gaussian-rational bridge
is unused outside its defining file.

## Paper proof

Squared reciprocal-Xi self-adjointness implies RH by the existing exact classifier. RH then gives
unsquared self-adjointness, Clifford polarization, each of the three Cauchy-source quadratic-reality
predicates, Gaussian-rational orientation-defect vanishing, and the target and continued
prime--Gamma sector inequalities through their existing biconditionals. RH also forces zero Hurwitz
orientation energy, and the exact zero-energy/central-spectrum theorem makes every centered
reciprocal-square coordinate real. Conversely, the certificate contains unsquared reciprocal-Xi
self-adjointness; its exact classifier gives RH, hence squared self-adjointness.

For the complementary phase, non-RH negates the exact unsquared and Clifford classifiers. Negating
the Gaussian-rational defect and both sector predicates exposes explicit defect, target-sector, and
source-sector witnesses. Positive Hurwitz orientation energy is exact for non-RH; its off-critical
zero witness, together with the centered-coordinate reality classifier, supplies a nonreal centered
reciprocal-square coordinate. Conversely, the certificate's non-self-adjoint unsquared operator
contradicts the operator supplied by RH.

## Lean formalization

`RHTower/XiReciprocalSquareSourceUniversalityLaw.lean` defines
`XiReciprocalSquareSourceUniversalCertificate` and
`XiReciprocalSquareSourceFailureUniversalCertificate`, and proves
`xiReciprocalSquareOperator_isSelfAdjoint_iff_sourceUniversalCertificate` and
`not_riemannHypothesis_iff_reciprocalSquareSourceFailureUniversalCertificate`. Exact direct check:

```text
lake env lean GaloisForLFunctions/RHTower/XiReciprocalSquareSourceUniversalityLaw.lean
```

passed without warnings.

## Hostile literature noncollision audit

Queries targeted `reciprocal square` plus RH/self-adjointness, Clifford polarization, Gaussian-
rational Cauchy quadratic reality, and Hurwitz/Stieltjes sector signs. No source located the claimed
nine-chart equivalence or six-witness failure synchronization. Nearest operator-theoretic work is
Connes--Consani's scaling/Hilbert-space program
([arXiv:1910.14368](https://arxiv.org/abs/1910.14368)); nearest reciprocal/criterion and Hurwitz-
Stieltjes coefficient work is Coffey
([arXiv:math-ph/0608050](https://arxiv.org/abs/math-ph/0608050),
[arXiv:0706.0343](https://arxiv.org/abs/0706.0343)). These do not contain the Lean corpus's
Clifford, Gaussian-rational defect, centered reciprocal-square, or paired target/source sector
closure. This is a noncollision audit, not a priority claim.

## Log

- 2026-07-22 — Found after Law22 restart by reading exact reciprocal-square operator, Cauchy-source,
  Clifford, countable-defect, and prime--Gamma sector files plus all downstream uses.
- 2026-07-22 — Paper proof closed; positive and failure laws formalized and warning-clean under the
  exact direct Lean command. Hostile literature audit found no collision. Final global audit remains.
