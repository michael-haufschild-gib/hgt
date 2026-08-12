# Mass-shifted projective arithmetic surplus

- **ID:** mass-shifted-projective-arithmetic-surplus
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 exact open core
- **Statement:** Current adaptive mixed/completed arithmetic source has a strictly positive nonlinear projective surplus, and its source-normalized recession velocity tends exactly to one.

## Goal

Charge positive-chamber free flight by literal admission-sensitive `P^sharp` source formed before
reflection aggregation. Replace sign/orientation and arbitrary shear gauges by intrinsic nonlinear
work relative to cumulative Jacobi flux.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, hostile-tested
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem names, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem and proof

## Conjecture/proof loop

Let `c=2n+1`, `F_n` be cumulative Jacobi flux, `D_n` cumulative Jacobi dissipation,
`alpha_n` current Jacobi drift, `h_n` admitted norm, and `P_n^sharp` literal adaptive
mixed/completed arithmetic source.

1. **Fixed shear capacity — failed.** Optimizing `-Q/W` on odd-contact two-plane removes arbitrary
   completion gauge, but homogeneous projective capacity can still collapse with transverse odd
   coupling. It does not prevent summably negligible renewal prices.
2. **Raw Riccati budget — failed.** `U_n'= -D_n/c < -U_n^2` gives positivity and contraction, but
   positive hyperbolic decay survives on complete right ray and raw dissipation is integrable.
3. **Relative arithmetic coercivity — survives.** New corpus theorem identifies fixed-degree source
   collapse as monic-norm collapse: normalized literal source tends `n+3/8`. Generic coordinate
   dilation proves no degree-uniform neighborhood of arcsine face suffices.
4. **Projective arithmetic surplus — candidate.** Define
   `S_n = c*(P_n^sharp/h_n - alpha_n*F_n - 2*n*alpha_n^2) - F_n^2`.
   Exact source Riccati identity gives `S_n=c*D_n-F_n^2`; strict weighted Cauchy gives `S_n>0`.
   For normalized recession variables, arcsine limits give
   `F_n→c/2`, `D_n→c/2`, hence `S_n→c^2/4` and `S_n/F_n^2→1`.
5. **Higher principle.** Arithmetic source does not merely orient contact. After subtracting
   endogenous admission drift and dividing by squared flux amplitude, it is exact excess velocity
   of reciprocal projective clock `U_n^{-1}-y`. Every fixed-degree terminal chamber therefore has
   asymptotically one unit of arithmetic projective work per unit mass.

## Literature audit

Varying-weight orthogonal-polynomial literature obtains diagonal recurrence asymptotics only after
specific real-positive weight and regularity assumptions, commonly through Riemann–Hilbert or Toda
analysis. Those hypotheses do not apply to shifted-Xi conjugation-folded reciprocal moments before
RH. No audited source supplies Xi-specific uniform diagonal control. Generic moment positivity is
explicitly insufficient by corpus coordinate-dilation countermodel.

## Exact remaining burden

Transport projective work across cofinal degree renewals or prove an Xi-specific upper budget that
contradicts one-unit recession. Fixed-degree divergence alone does not close RH because terminal
thresholds may escape diagonally with degree.

## Formalization

Module:
`formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionProjectiveArithmeticSurplus.lean`.

Main capstones:

- `dimensionlessProjectiveArithmeticSurplus_eq_cauchyGap`;
- `dimensionlessProjectiveArithmeticSurplus_pos`;
- `tendsto_dimensionlessProjectiveArithmeticWorkRate_one`;
- `xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_eq_cauchyGap`;
- `xiShiftedCanonicalAdmissionProjectiveArithmeticSurplus_pos`;
- `mul_flux_sq_lt_mul_relativeCompletedSource`;
- `hasDerivAt_xiShiftedCanonicalAdmissionArithmeticProjectiveClock_eq_sourceWorkRate`;
- `deriv_xiShiftedCanonicalAdmissionArithmeticProjectiveClock_pos`;
- closed `all_positiveAdmissionBlocks_carry_projectiveArithmeticSurplus`.

Direct Lean and targeted module build pass. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-12 — created in stage 1 after source-relative and hostile dilation audit.
- 2026-08-12 — paper proof closed, formalized, umbrella-wired, and targeted build/axiom audit passed.
