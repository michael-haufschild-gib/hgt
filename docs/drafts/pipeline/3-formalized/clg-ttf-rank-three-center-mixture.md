# Strict rank-three center mixture of the actual theta source

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** At every physical aperture `0<a<1/2`, the signed rank-three Hankel determinant formed from the actual center-mixed density derivatives of orders `0,2,4,6,8` at zero is strictly positive.
- **Capstone:** `RHTower.thetaCuspCenterMixedDensity_iteratedDeriv_eighthHankel_pos` in `HedenmalmCenterMixedEighthHankelClosure`.

## Dependency-closed proof

For a symmetric Hankel matrix with entries `p0,p2,p4,p6,p8`, let `d=p0*p4−p2²` and `D` be its determinant. Its quadratic form satisfies the exact identity

`p0*d*Q(x,y,z) = d*(p0*x+p2*y+p4*z)² + (d*y+(p0*p6−p2*p4)*z)² + p0*D*z²`.

Positive first entry, second leading minor, and determinant therefore imply `Q>0` whenever `z≠0`. For the integrated entries `A,B,C,D,E`, evaluate the pointwise form at `(B*D−C²,B*C−A*D,A*C−B²)`. Its integral is the integrated second minor times the integrated determinant. The existing strict rank-two integration theorem gives a positive second minor. Positive mass and almost-everywhere strictness make the quadratic integral positive. Hence the integrated determinant is positive, with no uniform pointwise spectral gap.

`GaloisForLFunctions.HTGeometry.integral_threeByThree_det_pos` proves that general result in `RankThreeHankelMixture`.

For the literal theta source, global D1 supplies the pointwise determinant. The positive weight is exactly `r*sinh(a*r)`. All five weighted jets are integrable by the existing all-order derivative-product estimate. The existing shared seventh/eighth derivative-product chain, ordinary differentiation, reflection-center exchange, and integration identify the eighth entry with the actual eighth derivative. Every source premise is discharged.

## RH scope

Global native D1 and its actual rank-three mixture are closed. The actual equispaced five-point cusp is also proved in `ThetaCuspCenterMixedFivePointCusp`. Theta-specific general-packet incidence and cofinal no-escape remain before the Weil criterion proves RH. This theorem is not an all-packet or all-order positivity claim.

## Verification

- Both new production modules passed direct `lake env lean` checks without warnings.
- The actual-derivative capstone axiom audit returns only `propext`, `Classical.choice`, `Quot.sound`.
- Formal lint passed; corpus indexes refreshed; both new modules wired into their area umbrellas.
- Only new capstones were axiom-audited. No full/umbrella build or numerical source certificate was used.
