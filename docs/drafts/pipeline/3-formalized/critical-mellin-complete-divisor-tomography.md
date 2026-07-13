# Complete critical-Mellin divisor tomography

- **ID:** critical-mellin-complete-divisor-tomography
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Connes-route critical-Mellin continuation
- **Statement:** The regularized critical-Mellin defect is meromorphic on
  \(\Re u>-1\), and its multiplicity-weighted simple-pole divisor is canonically the affine
  image \(\rho\mapsto\rho-1\) of the complete nontrivial Xi divisor.

## Status

`[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`

## Theorem

Let
\[
 \widetilde D(u)=\frac1{u+1}+\frac{Z_*'(u+1)}{Z_*(u+1)},
\]
where \(Z_*\) is the pole-filled Riemann zeta function. Then:

1. \(\widetilde D\) is meromorphic on \(\Re u>-1\).
2. In that half-plane,
   \[
   \operatorname{ord}_u\widetilde D=-1
   \iff
   u=\rho-1
   \quad\text{for a nontrivial Xi zero }\rho.
   \]
3. If \(m(\rho)\) is the analytic multiplicity, then
   \[
   \operatorname*{Res}_{u=\rho-1}\widetilde D(u)=m(\rho).
   \]
4. The affine map \(\rho\mapsto\rho-1\) is a canonical equivalence from the complete
   nontrivial Xi divisor support to the simple-pole support of \(\widetilde D\).
5. Pointwise on \(\Re u>-1\), holomorphy of \(\widetilde D\) is equivalent to
   \(Z_*(u+1)\ne0\).
6. Consequently,
   \[
   \mathrm{RH}
   \iff
   \text{every pole lies on }\Re u=-\frac12
   \iff
   \widetilde D\text{ is holomorphic on }\Re u>-\frac12.
   \]

## Positive carrier law

The critical-Mellin coordinate already carries the complete arithmetic divisor with exact
multiplicity. A successful Connes realization must therefore force the intrinsic pole carrier
\(\rho\mapsto\rho-1\) onto \(\Re u=-1/2\), equivalently prove the required half-plane
holomorphy. No additional divisor reconstruction theorem remains.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.CCMCriticalMellinDivisorTomography`
- Main declaration:
  `criticalMellinDivisorTomography_capstone`
- Canonical equivalence:
  `criticalMellinXiDivisorEquivSimplePoleSupport`
- Pole-line criterion:
  `riemannHypothesis_iff_criticalMellin_poles_on_line`
- Exact module build:
  `lake build GaloisForLFunctions.RHTower.CCMCriticalMellinDivisorTomography`
- Allowed axioms:
  `[propext, Classical.choice, Quot.sound]`.

## Novelty boundary

This is a strengthened intrinsic presentation of already formalized source-divisor tomography
and the classical logarithmic-derivative principle. It is bridge infrastructure rather than a
new-science claim. The remaining RH-bearing theorem is pole confinement, or equivalently
holomorphic continuation to \(\Re u>-1/2\).
