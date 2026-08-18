# Source-horizontal indefinite endpoint annihilation firewall (2026-08-18)

Formalized new cross-corpus Route-P/Euler-Wold/Krein/bilateral classification.

## Files
- Lean: formal/GaloisForLFunctions/RHTower/SourceHorizontalEulerWoldIndefiniteEndpointAnnihilation.lean
- Card: docs/drafts/pipeline/3-formalized/source-horizontal-euler-wold-indefinite-endpoint-annihilation.md
- Wired import in formal/GaloisForLFunctions/RHTower.lean (umbrella deliberately not built).

## Exact results
Let P(c) be primitive budget, R_N literal endpoint response, T_N transverse source-budgeted reporter.
- Unique diagonal counterleg retaining first corner R_N and trace T_N is K_N=T_N-R_N.
- For c≠0, cofinally 0<T_N<P(c)<R_N, hence R_N>0>K_N: genuine indefinite annihilation.
- Signed block S_N=diag(R_N,K_N) has trace T_N exactly.
- Fundamental symmetry J=diag(1,-1) gives tr(J S_N)=2R_N-T_N>P(c) cofinally. Physical rotation restores/amplifies excess.
- Nonzero scalar multiplication preserves/reflexes bilateralModerate.
- Endpoint-energy-scaled Hardy ± halves have exactly cancelling bilateral sewing defects.
- Both scaled halves are moderate iff Re rho=1/2.
- For actual strict-right Xi copies, exact sewing cancellation holds but both-half moderation fails.
- Actual Gamma-Julia coefficient is copy-independent and positive/negative scaled half fibre sums restore xiSupportMultiplicity.

Capstone: sourceHorizontalActualXiIndefiniteEndpointAnnihilation_capstone.
Other key theorems:
- sourceHorizontalEulerWoldEndpointCounterleg_unique
- eventually_sourceBudget_lt_sourceHorizontalEulerWoldPhysicalEndpointBlock_trace
- sourceHorizontalEndpointScaledHardy_both_moderate_iff_re_eq_half

## Verdict
Nonlinear/order-indefinite endpoint annihilation itself is solved and coefficient/multiplicity faithful, but it is not a route to RH: cancellation does not survive positive physical rotation or off-line bilateral source admission. Retire scalar/Krein endpoint-correction branch. Next valid producer must be non-scalar source-topology descent admitting both Hardy orientations simultaneously (which the proved selector makes criticality-forcing).

## Verification
- lake env lean exact file: PASS
- lake build exact module: PASS 13564/13564
- axioms: propext, Classical.choice, Quot.sound only
- formal lint: new target clean/reachable; unrelated concurrently unwired modules remain.
