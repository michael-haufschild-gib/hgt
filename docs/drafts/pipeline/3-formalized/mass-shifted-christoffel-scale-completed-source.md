# Mass-shifted Christoffel-scale-completed arithmetic source

- **ID:** `mass-shifted-christoffel-scale-completed-source`
- **Status:** Formalised in Lean 4
- **Date:** 2026-08-11
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3, Conjecture 67
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionScaleCompletedArithmeticSource.lean`

## Problem

Source divided by admitted norm still carries coordinate weight two. Any fixed positive contraction
of a fully positive canonical arcsine moment form defeats `source/norm > degree` cofinally. Find
admission-sensitive coordinate normalization without adding orientation or a fixed reporter.

## Conjecture loop

1. **Norm division removes all gauge.** Failed by exact coordinate dilation.
2. **A degree-independent neighborhood of arcsine suffices.** Failed: exact survival window is
   inverse-degree, `8n(1-r²) < 3r²`.
3. **Next current Christoffel ratio has matching coordinate weight.** Proved.
4. **Christoffel completion is exactly dilation invariant.** Proved on every nonzero dilated
   positive arcsine canonical admission.
5. **Positive chamber supplies a recession-free covariant lower bound.** Proved:
   `(n+1)β_(n+1) < R_n`.

## Paper proof

Let `N_n` be squared norm of current canonical admission and put

`κ_n = 16 N_(n+1)/N_n = 16 β_(n+1)`, `C_n = R_n/κ_n`.

One `(n+2)` positive Hankel block identifies both inverse-Hankel admissions with monic orthogonal
polynomials and makes `β_(n+1)>0`. Exact arithmetic-source localization gives

`C_n = E_n/(16 β_(n+1)) > 0`.

Under moment coordinate dilation `c_k ↦ r^k c_k`, norm has weight `2n`, adaptive source has weight
`2n+2`, and next norm ratio has weight two. Hence `κ_n=r²` on transported arcsine admissions and
`C_n=n+3/8` for every `r≠0` and every positive degree.

Finally, Jacobi energy contains boundary term

`(n+1)(β_n+β_(n+1))`

and all other terms are nonnegative. Since `β_n>0`,

`(n+1)β_(n+1) < E_n = R_n`, so `(n+1)/16 < C_n` without recession or degree restriction.

## Formal capstones

- `XiShiftedCanonicalAdmission.admissionChristoffelScaleSq_eq_sixteen_mul_monicOrthoBeta`
- `XiShiftedCanonicalAdmission.scaleCompletedRelativeArithmeticSource_eq_jacobiEnergy_div_christoffel`
- `XiShiftedCanonicalAdmission.succ_mul_nextBeta_lt_relativeArithmeticSource`
- `XiShiftedCanonicalAdmission.succ_div_sixteen_lt_scaleCompletedRelativeArithmeticSource`
- `XiShiftedCanonicalAdmission.tendsto_admissionChristoffelScaleSq`
- `XiShiftedCanonicalAdmission.tendsto_scaleCompletedRelativeArithmeticSource`
- `XiShiftedArcsineAdmission.coordinateDilatedAdmissionChristoffelScaleSq_eq`
- `XiShiftedArcsineAdmission.coordinateDilated_scaleCompletedSource_eq`

## Exact survivor and open core

Amplitude and coordinate gauges are closed. Remaining obstruction is shape-only admission holonomy:
frozen amplitude emitted at a crossing need not remain current admission later. A stronger calibrated
bound `C_n>n` is exactly `E_n>16nβ_(n+1)` and is not supplied by generic positivity. Sign-based
closure instead needs outgoing-ray transport covariant under current Christoffel scale.

## Verification

- Direct `lake env lean` passed.
- Wired into `RHTower.lean`.
- Targeted module build passed.
- Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound` for audited capstones.
- Full formal lint reached only unrelated concurrent un-wired modules; neither module on this card
  appeared in lint errors.
- No RH hypothesis, `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or numerical computation.
