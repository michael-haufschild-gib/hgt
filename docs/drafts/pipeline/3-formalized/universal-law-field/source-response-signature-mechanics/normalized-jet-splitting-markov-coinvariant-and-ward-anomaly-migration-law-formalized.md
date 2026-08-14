# Normalized jet splitting, Markov coinvariants, and Ward-anomaly migration — Lean certification

- **ID:** ULF-SRSM-9-LEAN
- **Paper source:**
  `docs/drafts/pipeline/3-formalized/universal-law-field/source-response-signature-mechanics/normalized-jet-splitting-markov-coinvariant-and-ward-anomaly-migration-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveNormalizedJetWardMigration`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-FORMALIZED FULL] [UNCONDITIONAL ACTIVE SUPPORT] [NO SORRY]`
  `[NO ADDED AXIOMS] [NO COMPUTATION CERTIFICATES] [NOT RH]`

## Certified theorem surface

Lean certifies the complete dependency-closed paper surface:

1. `normalizedFormedJet`, `normalizedJetFormation`, and
   `levelwiseJetRecovery_normalizedJetFormation` implement `(NJS.1)`--`(NJS.4)` literally, with
   binomial Leibniz coefficients and exact recovery at every jet level;
2. `commonRecovery_normalizedFormedJet_component`,
   `normalizedJetFormation_injective`, `normalizedJetProjection_idempotent`,
   `normalizedJetProjection_range`, and `normalizedJetProjection_ker` certify the exact recovered
   coefficient, injection, and projection clauses;
3. `normalizedJetFormation_isCompl_ker_recovery` and `normalizedJet_decomposition` certify the
   direct-sum splitting `(NJS.5)` and its explicit horizontal/vertical decomposition;
4. `finiteJet_triangle_reindex`, `normalizedJetColumnWeight`, `normalizedJetBound`, and
   `exists_normalizedJetColumnWeight_eq_bound` construct and attain the paper's exact finite-order
   constant
   `C_N = max_j sum_k choose(j+k,k) ‖M_k‖`;
5. `normalizedJetFormation_l1_lower_bound`, `normalizedFormedJet_l1_upper_bound`, and
   `normalizedJetFormation_l1_bounds` certify both sum-norm estimates `(NJS.9)`--`(NJS.10)` and
   the inverse norm bound;
6. `normalizedJetFormationCLM_hasLeftInverse` and `isClosed_range_normalizedFormedJet` construct
   continuous formation/recovery maps and prove the formed-jet range closed without a completeness
   premise;
7. `invariant_reporter_iff_responseRadical_le_ker` identifies reporters with the dual of the
   response coinvariant quotient for an arbitrary refinement family;
8. `linearResponseRadical_allRecoveryPreserving_eq_ker`,
   `invariant_under_allRecoveryPreserving_iff_factors`, and `allRecoveryCoinvariantEquiv` certify
   the coordinatewise/common-recovery version: every universally natural reporter factors through
   the recovered horizontal space and the quotient is canonically that space;
9. `linearResponseRadical_allMassPreserving_eq_ker_finiteMass`,
   `allMassCoinvariantEquiv`, and
   `invariant_under_allMassPreserving_iff_factors_finiteMass` specialize `(NJS.16)`--`(NJS.17)`
   to the mass line and prove annihilation of every zero-mass normalized shape;
10. `finiteScoreConnection_add_sq`, `finiteJetExpectation_score_eq_zero`,
    `finiteJetExpectation_connection_add_score_sq_eq_zero`, and
    `finiteFisherMass_eq_neg_meanScoreConnection` certify the pointwise Riccati and
    Bartlett--Ward identities `(NJS.20)`--`(NJS.22)`;
11. `affineBernoulliTwoJet_bartlett_countermodel` certifies `(NJS.23)`--`(NJS.24)` exactly:
    Fisher mass one, mean connection minus one, and zero total Ward current;
12. `activeObservedKernel` and `observedActiveProbabilityTwoJet` canonically restrict every finite
    Markov kernel to its nonzero observed support, deriving positivity instead of requiring it;
13. `observedActive_score_conditional_identity`, `finiteFisherWardMigration_active`, and
    `finiteFisherLoss_active_eq_zero_iff_score_observed` certify `(NJS.25)`--`(NJS.27)`, including
    the conditional-score identity, exact Fisher defect, exact connection migration,
    nonnegativity, and the almost-sure equality classification.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveNormalizedJetWardMigration.lean`
  passes.
- `lake build GaloisForLFunctions.HTGeometry.ConstitutiveNormalizedJetWardMigration` passes
  (`8677/8677` jobs); no full build was run.
- Wired umbrella source elaboration passes.
- Scoped scan contains no `sorry`, `admit`, project `axiom`, `opaque`, `unsafe`, `decide`,
  `native_decide`, `norm_num`, or `omega`.
- Axiom prints for splitting, stability, closed range, both quotient classifications, Bartlett,
  active-support migration/equality, and the countermodel report only `propext`,
  `Classical.choice`, and `Quot.sound` (one factorization theorem uses only `propext` and
  `Quot.sound`).

## Exact formal boundary

The theorem proves an all-order finite-jet mechanism, not a uniform infinite analytic-jet theorem:
growth of `C_N` remains an independent source-admission problem, exactly as stated on paper. It
also proves the selector no-go and its migration survivor; it does not construct a restricted
arithmetic Markov semigroup, a nonconstant harmonic reporter, physical Xi landing, or RH.
