# Bipolar admission hull and analytic critical shell — Lean certification

- **Paper source:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/law-saturation-mechanics/bipolar-admission-hull-critical-shell-and-infinite-alternation-law.md`
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveAnalyticAdmissionHull`,
  `GaloisForLFunctions.HTGeometry.ConstitutiveOneEndedAdmissionCriticalShell`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [FORMALIZED CORE] [NO SORRY] [NO ADDED AXIOMS] [NOT RH]

## Certified theorem surface

Lean proves:

1. `eqvGen_observer_eq`: every observer respecting a primitive relation respects its algebraic
   equivalence saturation;
2. `analyticAdmissionObserverLift` and `analyticAdmissionObserverLift_mk`: every continuous
   Hausdorff-valued unitizing observer factors through algebraic saturation followed by the maximal
   Hausdorff quotient;
3. `analyticAdmissionRel_erases_every_continuous_T2_observer`: analytic admission erases exactly
   the distinctions unavailable to all such observers;
4. `analyticAdmissionRel_iff_continuous_real_observers`: on compact Hausdorff sources, the analytic
   relation is exactly equality under all continuous real-valued unitizing reporters;
5. `evenRetraction` and `oddRetraction`: explicit continuous cofinal source retractions on the
   one-point compactified natural ray;
6. `jointlyUnitizing_nat_constant` and `continuous_jointlyUnitizing_constant`: their algebraic join
   connects every finite point, while continuity forces the same value at infinity;
7. `oneEnded_analyticAdmission_total`: the resulting analytic admission relation is total;
8. `oneEndedSetReporter_not_continuous`: the nonconstant algebraic endpoint reporter unitizes both
   operations but is analytically inadmissible;
9. `finiteAdmissionReporter_exact_margin`, the aperture-unitization lemmas, and the pointwise
   stabilization lemmas: every finite aperture has a continuous reporter with exact margin one,
   while the reporters converge pointwise to the inadmissible global reporter;
10. `oneEndedSetReporter_constant_gap_lower` and
    `oneEndedSetReporter_half_constant_exact`: the best constant analytic replacement has exact
    uniform gap `1/2`;
11. `oneEndedAdmissionCriticalShell`: unconditional bundled capstone.

## Verification

- Direct foreground elaboration passes for both new modules.
- `scripts/formal_tools.py lint` passes with no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
  declaration.
- Final `lake build GaloisForLFunctions.HTGeometry.UniversalLawField` passes (11,525 jobs).  Replay
  warnings are confined to pre-existing modules; both new modules build cleanly.
- Axiom audit on the scalar bipolar theorem, observer-erasure theorem, continuous-collapse theorem,
  total-admission theorem, reporter inadmissibility, finite margin, half-gap, and bundled capstone
  reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact formal boundary

Lean certifies the coordinate-free scalar-bipolar mechanism and the cofinal one-ended critical
shell.  The paper's general least-closed-equivalence reformulation, measure-theoretic Dirac-TV
statement, two-ended integer model, non-equicontinuity proof, and bounded-alternation closure theorem
remain paper-only.  They do not count as formally proved and are not implied by this certification.
