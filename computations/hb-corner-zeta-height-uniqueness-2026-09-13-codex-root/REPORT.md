# Complete-corner uniqueness at actual zero heights

## Question

After a validated zeta zero fixes the ordinate, is the critical-line point the unique real-part solution of the complete derived moving-characteristic corner diagnostic? The computation tests this without treating the corner diagnostic as the still-unassembled complete causal action.

## Computation

- Inputs: validated zero ordinates 1--128 and 257--320.
- Scales frozen before execution: `L in {2e, 6, 10, 30}`.
- Domain: full symmetry-reduced half-strip `0 <= Re rho <= 1/2`.
- Diagnostic: pole-free normalized cross numerator `-Im(W_R conjugate(W_Delta))/(|W_R||W_Delta|)`.
- Both complete corner coefficients retain `D_star f33`, source-polynomial terms, complementary ordering, and exact finite radial primitives.
- Every case was scanned on 96- and 192-interval grids. Every candidate was refined independently at 120 and 180 decimal digits. Reflection was checked as a positive control.
- Pod A processed ordinates 1--128. Pod B processed 257--320 plus 1--8 as an execution overlap.

## Result

At `L=2e`, 191 of the 192 distinct tested zero ordinates have exactly one off-critical root in the lower half-strip and hence one reflected upper-half-strip partner. The first zero, at ordinate approximately `14.13472514`, is the sole exception. Both grids agreed in every case.

At each of `L=6`, `L=10`, and `L=30`, no off-critical root was found at any of the 192 ordinates. This is finite bounded survival only, not uniqueness proof.

The two pod slices reported 127 and 71 candidates respectively; seven are deliberately duplicated overlap cases, giving 191 distinct candidates. All 198 executed validations converged at both precisions. Maximum 120/180-digit root displacement was `1.75e-119` in the low cohort and `4.85e-119` in the distant cohort. Pod-overlap records agreed exactly. Distant-cohort minimum coefficient magnitudes were `|W_R| > 61.64` and `|W_Delta| > 0.0345`; maximum recorded reflection defect was `2.20e-121`.

Wall times were 256.64 seconds for the 128-zero slice and 152.63 seconds for the distant-plus-overlap slice.

## Interpretation

The complete derived corner receiver is sharply scale-dependent at actual source zeros. At `L=2e`, critical-line occurrence does not select the critical real part: false off-line matches are nearly universal across both cohorts. The first zero is exceptional, not representative. The three larger frozen scales survive this finite test, but no source law in this computation selects them, so they cannot be promoted to an HB Selection result.

This kills scale-independent uniqueness for this corner diagnostic while exposing a concrete survivor: determine whether existing source geometry fixes a scale on the no-extra-root side of the observed switch. No scale was retuned after seeing results.

## Limits

This is the complete currently derived moving-characteristic corner term, not the complete physical HB action. Other faces, angular realization, onset matching, and independent SS/SV/VV sectors remain outside the computed object. Absence of roots on two finite grids is not a certified global nonexistence result.
