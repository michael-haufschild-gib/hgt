# Mass-shifted canonical relative source coercivity

- **ID:** `mass-shifted-canonical-relative-source-coercivity`
- **Status:** Formalised in Lean 4
- **Date:** 2026-08-11
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3, Conjecture 66
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionRelativeSourceCoercivity.lean`

## Problem

Existing canonical arcsine source margin is positive but decays like `n * 16⁻ⁿ`. Read absolutely,
this appeared to require exponentially precise control of growing-degree inverse-Hankel admission.
Test whether collapse is intrinsic or caused by monic coordinate normalization.

## Conjecture loop

1. **Absolute margin is intrinsic cofinal obstruction.** Failed.
2. **Divide source by admitted orthogonal norm.** Succeeded exactly.
3. **Fixed-degree relative recession closes cofinal drift.** Failed: convergence remains nonuniform
   in degree, and pointwise moment convergence has delayed high-moment counterexamples.

## Paper proof

For shifted monic Chebyshev admission

`p_n(X) = 2^(1-2n) T_n(2X-1)`, `n ≥ 1`,

arcsine orthogonality gives

`L_c(p_n²) = (monicScale n)² / 2`.

Existing adaptive-shear evaluation gives `11/64` in degree one and
`(monicScale n)²(8n+3)/16` for `n ≥ 2`. Both cases unify as

`L_c(A(p_n)) = (n + 3/8) L_c(p_n²)`.

Therefore `n L_c(p_n²) < L_c(A(p_n))`: relative source coercivity grows linearly.

For actual dimensionless admission `Q_(n,w)`, coefficientwise recession of `Q_(n,w)` and normalized
moments gives convergence of both `L_(t_w)(A(Q_(n,w)))` and `L_(t_w)(Q_(n,w)²)`. Positive arcsine
norm permits division. Exact mass dilation identifies numerator with literal mass-scaled completed
rational–Gamma minus von Mangoldt source. Hence, for fixed `n ≥ 1`, relative arithmetic source tends
to `n + 3/8` and is eventually greater than `n`.

## Formal capstones

- `XiShiftedArcsineAdmission.momentFunctional_amplitude_sq`
- `XiShiftedArcsineAdmission.momentFunctional_adaptiveShear_amplitude_eq_norm_mul_linear`
- `XiShiftedArcsineAdmission.degree_mul_momentFunctional_amplitude_sq_lt_adaptiveShear`
- `XiShiftedCanonicalAdmission.tendsto_normalizedAdmissionNorm`
- `XiShiftedCanonicalAdmission.tendsto_normalizedAdmissionSource_div_norm`
- `XiShiftedCanonicalAdmission.relativeArithmeticSource_eq_normalizedAdmissionSource_div_norm`
- `XiShiftedCanonicalAdmission.tendsto_relativeArithmeticSource`
- `XiShiftedCanonicalAdmission.relativeArithmeticSource_eventually_gt_degree`

## Exact survivor and open core

Absolute target `error < n * 16⁻ⁿ` was wrong gauge. Sufficient intrinsic diagonal target is

`|R_(n(w))(w) - (n(w) + 3/8)| < 3/8`.

Tolerance is degree-independent. Missing theorem is now degree-uniform relative arithmetic-source
control along actual least-defect schedule, or equivalent source-specific Jacobi/Christoffel
conditioning. Fixed-degree limits, compactness, orientation maps, and fixed reporters cannot supply
it.

## Verification

- Direct `lake env lean` passed.
- Targeted module build and axiom audit pending final session audit.
- No RH hypothesis, `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or numerical computation.
