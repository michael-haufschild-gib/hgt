# CCM exterior-gauge coercive compact reduction

- **ID:** ccm-exterior-gauge-coercive-compact-reduction
- **Stage:** 3-formalized
- **Type:** THEOREM PACKAGE
- **Source:** `CCMActualHeadExteriorCosineMeasureGauge.lean`,
  `CCMPrimeFreeApertureCharacteristicPair.lean`,
  `HardyZPhaseAsymptotic.lean`
- **Formal module:**
  `GaloisForLFunctions.RHTower.CCMActualHeadExteriorGaugeCoerciveCompactReduction`
- **Labels:** `[BRIDGE] [FORMALIZED] [NEW FORMAL SYNTHESIS] [NOT AN RH PROOF]`

## Goal

Prove that corrected CCM symbols remain coercive after arbitrary signed finite exterior-measure
gauges. Deduce that global nonnegativity of a candidate representative is a compact-frequency
problem.

## Closed theorem package

1. The legacy explicit `ccmCorrectedSymbol` equals the source-faithful `correctedCCMSymbol` at every
   aperture and frequency.
2. The finite prime cosine channel and polar--prime Stieltjes symbol have explicit uniform absolute
   bounds.
3. `correctedCCMSymbol a xi` tends to positive infinity as `xi -> +infinity` and, by evenness, as
   `xi -> -infinity`.
4. A finite-measure cosine gauge is uniformly bounded by total measure and is even.
5. Every signed finite exterior-measure representative tends to positive infinity at both tails.
6. For every fixed candidate pair of measures there exists a compact symmetric interval outside
   which the representative is strictly positive.
7. Global representative nonnegativity is equivalent to nonnegativity on that compact interval.

All conjectures are closed in Lean. Seventeen theorems and two definitions establish the symbol
bridge, finite-channel budgets, two-sided coercivity, finite-measure gauge bounds, and exact compact
reduction.

## Strongest positive statement

For every positive aperture `a` and every two finite measures `mu`, `nu`, there exists `R > 0` such
that

`correctedCCMSymbol(a, 2*pi*xi) + G_mu(xi) - G_nu(xi) > 0`

whenever `R <= |xi|`. Consequently

`(forall |xi| <= R, representative(xi) >= 0)`

is equivalent to global pointwise nonnegativity of that representative.

## Universal interpretation

The corrected CCM symbol is a coercive Gamma backbone modulo a bounded Fourier--Stieltjes algebra.
Exterior-gauge freedom cannot damage either tail. Any obstruction to a positive representative is
therefore localized to a compact core, not spread across unbounded frequency. This changes the
producer problem from global sign control to compact lifting with coefficient-norm control.

## Lean audit

- Source `lake env lean` — pass.
- Target-only
  `lake build GaloisForLFunctions.RHTower.CCMActualHeadExteriorGaugeCoerciveCompactReduction`
  — pass. No umbrella build run.
- `#print axioms` on all seventeen theorems — only `propext`, `Classical.choice`, `Quot.sound`.
- Forbidden declaration scan — no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.
- Wired into `GaloisForLFunctions/RHTower.lean`; umbrella intentionally not built.

## Hostile audit

- Tail coercivity does not construct a positive representative on the compact core.
- Compact reduction is useful only if high-frequency cosine approximation has enough
  coefficient-norm control; plain density without norm control may be circular.
- The finite-prime bound includes every cutoff atom and does not use the prime-free special case.
- Exterior measure support is irrelevant to coercivity but remains essential to quadratic-gauge
  nullity.
- This package does not prove RH.

## Log

- 2026-08-21 — conjectured from corpus search: Gamma phase-rate coercivity plus bounded finite
  Fourier--Stieltjes perturbations.
- 2026-08-21 — all conjectures closed, audited, and promoted to Stage 3. External novelty not
  claimed; classification is conservative pending dedicated literature comparison.
