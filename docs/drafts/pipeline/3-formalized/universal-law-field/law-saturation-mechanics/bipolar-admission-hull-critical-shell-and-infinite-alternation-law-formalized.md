# Bipolar admission hull, analytic critical shell, and infinite alternation — Lean certification

- **Paper source:**
  `docs/drafts/pipeline/3-formalized/universal-law-field/law-saturation-mechanics/bipolar-admission-hull-critical-shell-and-infinite-alternation-law.md`
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveAnalyticAdmissionHull`,
  `GaloisForLFunctions.HTGeometry.ConstitutiveOneEndedAdmissionCriticalShell`,
  `GaloisForLFunctions.HTGeometry.ConstitutiveClosedAdmissionHull`,
  `GaloisForLFunctions.HTGeometry.ConstitutiveBoundedAlternation`,
  `GaloisForLFunctions.HTGeometry.ConstitutiveTwoEndedAdmissionCriticalShell`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [FORMALIZED FULL] [NO SORRY] [NO ADDED AXIOMS] [NO COMPUTATION CERTIFICATES]
  [NOT RH]

## Certified theorem surface

Lean proves the complete dependency-closed paper surface:

1. `analyticAdmissionRel_least_closed_equivalence` and
   `analyticAdmissionRel_le_closedSetoid_iff`: analytic admission is the least closed equivalence
   containing the primitive relation, with quotient factorization and uniqueness;
2. `analyticAdmissionRel_extensive`, `analyticAdmissionRel_mono`,
   `analyticAdmissionRel_idempotent`, and `analyticAdmissionRel_union_admissions`: exact hull
   closure and join laws;
3. `algebraicObserverConflict_iff`, `analyticObserverConflict_iff`, and
   `conflict_analytic_obstruction_eq_criticalShell`: exact algebraic/analytic conflict criteria and
   critical-shell set difference;
4. `analyticCriticalShell_dirac_totalVariation` and
   `analyticCriticalShell_pushforward_totalVariation_zero`: exact finitely-supported Dirac TV drop
   from one to zero;
5. `isClosed_boundedAlternationJoin`, `eqvGen_union_iff_exists_boundedAlternationJoin`, and
   `boundedAlternation_firstShell_depthDivergence`: every finite alternation layer is closed, their
   union is the algebraic join, and first-shell convergence forces unbounded minimal depth;
6. `TwoEndedInt`, `twoEndedEvenFormation`, and `twoEndedOddFormation`: the exact compact two-ended
   integer carrier and its continuous idempotent alternating source formations;
7. `twoEnded_joinedUnitization_eqvGen_iff`, `twoEnded_analyticAdmission_total`, and
   `twoEnded_endpoints_analyticCriticalShell`: exactly three algebraic classes, total analytic
   admission, and the endpoint critical pair;
8. `finiteTwoEndedEvenFormation`, `finiteTwoEndedOddFormation`, and their idempotence and endpoint
   laws: exact finite source truncations rather than abstract reporter substitutes;
9. `finiteTwoEnded_join_eqvGen_iff` and `finiteTwoEnded_join_isClosed`: the sole nonsingleton finite
   class is exactly `I_N = {-2N-1, ..., 2N+1}`, and the finite joined relation is closed;
10. `finiteTwoEndedReporter_unitizes_even`, `finiteTwoEndedReporter_unitizes_odd`, and
    `finiteTwoEndedReporter_exact_margin`: every finite stage has a continuous common reporter with
    endpoint margin one;
11. `finiteTwoEndedReporter_tendsto_setReporter`,
    `finiteTwoEndedReporter_not_equicontinuousAt_posInfinity`, and
    `finiteTwoEndedReporter_not_equicontinuousAt_negInfinity`: exact pointwise convergence to the
    discontinuous lossless reporter and failure of equicontinuity at both ends;
12. `twoEndedReporterUniformError_sInf`: exact best constant analytic replacement gap `1/2`;
13. `twoEndedAlternationPower_exact_int` and `tendsto_twoEndedAlternationDepth_pairs`: the literal
    embedded pairs `(-m,m)` converge to the endpoint conflict and have minimal primitive
    `E/F`-path length exactly `2m`;
14. `closedAnalyticAdmissionHull_capstone`, `boundedAlternation_capstone`, and
    `twoEndedAdmissionCriticalShell_capstone`: bundled theorem-level certification.

## Verification

- Direct foreground elaboration passes for all three added modules and the wired
  `HTGeometry.UniversalLawField` umbrella.
- Targeted builds pass for `ConstitutiveClosedAdmissionHull`, `ConstitutiveBoundedAlternation`, and
  `ConstitutiveTwoEndedAdmissionCriticalShell`; no full build was run.
- Scoped scans contain no `sorry`, `admit`, project `axiom`, `opaque`, `unsafe`, `decide`,
  `native_decide`, `norm_num`, or `omega`.
- Axiom prints for all three capstones and the exact-depth theorem report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Repository lint reaches only unrelated shared `RHTower` umbrella-ownership failures; this card's
  modules are wired and pass the scoped lint and source/build checks.

## Exact formal boundary

No dependency-closed mathematical clause from Sections 3–6 remains paper-only. The Stage-1
transfinite higher-admission-rank problem explicitly excluded by Theorem 5.1 remains outside this
card and is not implied by this certification.
