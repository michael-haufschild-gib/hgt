# Boundary moment recovery at two heights

- **ID:** SELBERG-BOUNDARY-MOMENT-TWO-HEIGHT
- **Stage:** 3-formalized
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycles 6–8.
- **Scope:** Exact local recovery for four explicit boundary half-densities. The full Selberg conjecture remains unproved.

## Fields and theorem

Take the logarithms of the quarter half-densities based at infinity, zero, one, and minus one. Their gradients at `i` are respectively `(0,1/2)`, `(0,-1/2)`, `(1/2,0)`, and `(-1/2,0)`. These formulas are proved from actual Frechet derivatives in Lean.

For arbitrary real coefficients `c=(a,b,c,d)`, write `S=a+b+c+d`, let `L_c` be their signed sum of the four logarithms, and put `c'=c-S/4`. Define

`E=|grad L_c(i)|^2`,

`T=sum c_j*((partial_y log H_j(i))^2-(partial_x log H_j(i))^2)`,

`D=partial_y L_c'(2i)-(partial_y L_c'(i))/2`.

The closed identities are

`sum c_j^2-S^2/4 = 2*E+4*T^2 = 2*E+(400/9)*D^2`,

`T=(10/3)*D`.

The left side is proved equal to the squared norm of the centered coefficient vector. It vanishes exactly when all four coefficients agree. In contrast, the first moment alone loses every vector constant within each opposite pair. The vector `(1,1,-1,-1)` has `S=0`, `E=0`, `T=1`, and centered squared norm four. Consequently no positive constant makes `E` bound the centered coefficient norm below.

## Dependency-closed paper proof

Set `Y=a-b`, `X=c-d`, and `Q=a+b-c-d`. The first gradient at `i` is `(X/2,Y/2)`, while the directional second moment is `Q/4`. Expanding squares gives

`sum c_j^2 = S^2/4+(X^2+Y^2)/2+Q^2/4`.

For centered coefficients, the vertical derivative at height two is `Y/4+3*Q/40`; at height one it is `Y/2`. Their prescribed difference is therefore `3*Q/40`. Substitution proves the second recovery identity. The kernel classifications follow from sums of squares, and the displayed alternating vector disproves a positive first-moment lower bound.

## Implementation

Module: `GaloisForLFunctions.RHTower.SelbergBoundaryMomentChannels`.

The module imports `SelbergGeometricBlend`. That module now also exports `log_realField_hasFDerivAt`, proved from its previously verified differential. Translation and the chain rule give each logarithmic channel's actual derivative. Neither derivatives, positivity, nor recovery are supplied as hypotheses.

Capstones: `centeredNorm_eq_moments`, `centeredNorm_eq_twoHeight`, `centeredNorm_eq_zero_iff`, `squaredNorm_center`, and `no_positive_firstEnergy_bound`.

## Verification

- Foreground scratch check passed without warnings.
- Final `lake env lean GaloisForLFunctions/RHTower/SelbergBoundaryMomentChannels.lean` passed without warnings.
- `lake build GaloisForLFunctions.RHTower.SelbergBoundaryMomentChannels` passed; only the new target was rebuilt.
- Six scratch `#print axioms` checks, including the reused logarithmic differential, report only `propext`, `Classical.choice`, and `Quot.sound`.
- The new module is wired into the `RHTower` umbrella; no umbrella build is requested.
- Generated indexes were refreshed; formal lint passed with existing large-file warnings. Whitespace and process cleanup checks passed.

## What remains

This exact finite recovery law supplies an alternative to the failed first-gradient covariance proposal. A congruence proof would still require an appropriate boundary realization, estimates uniform over the configurations used there, and a justified passage from local recovery to global cusp energy. None of those statements is asserted by this module.
