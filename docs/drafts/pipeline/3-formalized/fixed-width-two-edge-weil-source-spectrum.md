# Fixed-width two-edge Weil detector and prime--Gamma source spectrum

- **ID:** `fixed-width-two-edge-weil-source-spectrum`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / PUBLICATION SYNTHESIS
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [NOT AN RH PROOF]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [SURVIVES PRELIMINARY ATTACK]`
  `[INDEPENDENT PRIORITY REVIEW STILL REQUIRED]`
- **Statement:** For every fixed admissible boundary width, false RH makes the Weil quadratic form
  cofinally unbounded below for every profile in a residual set of fixed smooth two-edge profiles.
  For the sharp rectangular profile, one ordinary Dirichlet series recovers every right
  off-critical Xi zero and its analytic multiplicity.  Every admissible logarithmic sample equals
  an explicit finite prime--Gamma coefficient, so every admissible source tail has the identical
  polar divisor; its negative-part Dirichlet abscissa is `⊥` under RH and exactly
  `1 + xiRightTransverseSup` under false RH, and its cumulative negative mass has the matching
  exact supercritical power-growth threshold.

## Goal

Produce one focused publication proving fixed-width detector completeness, exact sharp
prime--Gamma realization, and quantitative source/divisor spectrum. The paper must distinguish:

1. detector completeness, which is proved;
2. source identity and exact transverse exponent, which are proved;
3. source positivity at the critical endpoint, which is equivalent to RH and is not claimed.

No rightmost zero, maximal off-line layer, transverse gap, simple-zero premise, numerical evidence,
or unformalized source estimate may enter.

## Gates

- [x] 0 → 1: exact source-pure claim and hostile failure modes identified
- [x] 1 → 2: dependency-closed paper proofs recorded in parent cards
- [x] 2 → 3: exact Lean theorems exist with standard axioms only
- [ ] 3 → 4: focused standalone manuscript, current primary-literature audit, exact claim trace,
  final Lean/lint/build audit, and hostile general-journal referee pass

## Exact Lean surface

- `LSeries_xiRectangularWeilLogCoefficient_eq_fullContinuation`
- `meromorphicOrderAt_xiRectangularWeilFullContinuation_eq_neg_one_iff`
- `normalizedFullObservableResidue_eq_xiRightMultiplicity`
- `riemannHypothesis_iff_fullObservableContinuation_analytic_rightOne`
- `xiRectangularPrimeGammaTailDirichletCoefficient_eq_weil`
- `LSeries_xiRectangularPrimeGammaTailDirichletCoefficient_eq_continuation`
- `meromorphicOrderAt_xiRectangularPrimeGammaTailContinuation_eq_neg_one_iff`
- `normalizedPrimeGammaTailResidue_eq_xiRightMultiplicity`
- `riemannHypothesis_iff_primeGammaTailContinuation_analytic_rightOne`
- `not_riemannHypothesis_implies_generic_smoothProfile_weil_cofinally_unbounded_below`
- `riemannHypothesis_iff_generic_smoothProfile_logSample_weil_nonneg`
- `riemannHypothesis_iff_generic_smoothProfile_logSample_weil_eventually_bddBelow`
- `riemannHypothesis_iff_smoothProfile_logSample_weil_nonneg`
- `riemannHypothesis_iff_smoothProfile_logSample_weil_eventually_bddBelow`
- `xiWeilPolarization_rectangular_eq_prime_add_arch`
- `xiRectangularPrimeGammaLogCoefficient_eq_weilLogCoefficient_re`
- `xiRectangularPrimeGammaTailNegativePart_abscissa_dichotomy`
- `xiZeroHalfPlaneBound_iff_primeGammaCumulativeNegativeMassGrowth`
- `primeGammaCumulativeNegativeMass_exactPowerOrder_of_not_rh`
- `riemannHypothesis_iff_primeGammaCumulativeNegativeMassCriticalGrowth`

## Parent cards

- `new_scientific_knowledge/cofinal-two-edge-weil-completeness-landau-oscillation.md`
- `complete-sharp-rectangular-guinand-weil-prime-gamma-law.md`
- `sharp-prime-gamma-rh-spectrum.md`
- `ccm-cumulative-negative-mass-spectrum.md`

## Hostile frontier

- `[LITERATURE]` Weil positivity already characterizes RH on the full compactly supported test
  class.
- `[LITERATURE]` Yoshida, Bombieri, Suzuki, Connes--Consani, and CCM study fixed-support
  restrictions, screw kernels, semilocal positivity, and finite spectral approximants.
- `[LOCAL-RESEARCH]` Existing publication manuscript combines many later theorem families and is
  too broad to make this fixed-width theorem auditable as one scientific contribution.
- `[LITERATURE]` Current primary-source audit includes Barner's explicit formula,
  Connes--Consani semilocal positivity, CCM finite zeta spectral triples, Suzuki's screw/Hilbert
  formulations and 2026 localized-operator synthesis, and Groskin's 2026 finite
  Galerkin--Guinand--Weil dictionary.
- `[PRELIMINARY PRIORITY RESULT]` None of those sources states completeness or cofinal lower
  divergence for one fixed-width translated two-edge geometry, nor the exact finite prime--Gamma
  negative-part abscissa and cumulative-growth classification proved here. Full-text searches of
  the current Suzuki, CCM, and Groskin preprints found no Landau/cofinal/two-edge collision.
- `[BRIDGE]` Meromorphic recovery of a zeta divisor from a shifted-zeta or logarithmic-derivative
  series is routine parent theory and is not a novelty claim.  Its role here is to prove that the
  same finite source sequence loses no off-critical location or multiplicity.
- `[PRIORITY LIMIT]` Search absence is not proof of global priority. Candidate-new status requires
  independent specialist review before publication.

## Fields-medalist conjecture attack

The strongest tempting conjecture is:

```text
The explicit finite prime--Gamma negative source satisfies the critical
O_epsilon(X^(1+epsilon)) cumulative bound.
```

Its consequence is RH, but as a paper thesis it is circular: the proved spectrum theorem makes
that estimate equivalent to RH, and no independent prime-side mechanism establishes it. Verdict:
`[CIRCULAR AS AN RH ROUTE]`.

The failure-driven survivor asks for a complete classification rather than the missing critical
estimate:

```text
For one fixed width, identify exactly which horizontal zero-free region is
equivalent to each polynomial lower-loss or cumulative negative-mass exponent,
and prove unavoidable cofinal oscillation whenever that region fails.
```

This survivor is `[LEAN-PROVED]`, needs no rightmost zero, and is strictly more informative than a
bare RH-equivalent positivity reformulation: it recovers every transverse half-plane bound and
quantifies failure by the exact divisor supremum. It is the manuscript's central theorem.

## Antagonist rejection criteria

Reject publication claim if any of the following holds:

1. two-edge completeness is a direct stated corollary in prior literature;
2. Landau step assumes an attained rightmost off-line zero or hides a real-axis singularity;
3. sharp source formula exceeds formalized regularity;
4. source coefficient contains divisor data by definition;
5. abscissa/cumulative theorem is only a renamed classical Dirichlet-series fact with no new
   Xi/CCM consequence;
6. manuscript implies RH, whole-CCM impossibility, or a source estimate not proved in Lean.

## Log

- 2026-07-27 — Selected after internal capstone audit. Publication and priority audit opened.
- 2026-07-27 — Strengthened the paper with cutoff-free full-observable and source-tail
  multiplicity-exact divisor tomography; added and targeted-checked
  `CCMPrimeGammaSourceDivisorTomography.lean`.
