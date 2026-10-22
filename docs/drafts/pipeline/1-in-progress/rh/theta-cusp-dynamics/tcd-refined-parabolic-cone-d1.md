# Refined parabolic cone forces rank-three D1

- **ID:** TCD-REFINED-CONE-D1
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `rh-current-frontier-map.md` · TCD
- **Statement:** Every source-positive state in `StrictSourcePositiveRefinedParabolicClockCone` has strictly positive `modularThetaSourcePositiveReflectedEighthPolynomial`.

## Goal

Discharge finite TCD D1 gate. Actual missing theta interval lies in this cone; cone positivity plus seam and far-half theorems gives global D1. Remaining TCD burden is then cofinal theta–Xi source/divisor incidence before Weil positivity and RH.

## Gates

- [x] 0 → 1 in-progress: exact corpus-defined cone, D1, physical landing, and RH chain
- [ ] 1 → 2 fully-proven: dependency-closed exact algebraic proof
- [ ] 2 → 3 formalized: Lean theorem, targeted build, axiom audit
- [ ] 3 → 4 publication-ready

## Approach

Transport to Lyapunov/projective coordinates
`S=R(v-z)`, `A=R²(1-z²)`, `W=R(z+2v)/3`; use sparse Schur D1 form. Prove scale reduction from `R²>191/10+(37/5)z²`, then close projective boundary using the two refined parabolic walls and `0<z<3/10`. Avoid recursive polynomial expansion in final proof.

## No-go closure

If false, formalize an exact cone counterstate and retain the sharpest strengthened survivor.
