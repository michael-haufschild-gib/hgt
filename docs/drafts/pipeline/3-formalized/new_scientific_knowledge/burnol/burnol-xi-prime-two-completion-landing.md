# Burnol--Xi prime-two completion landing

- **Status:** `[LEAN-PROVED]`
- **Date:** 2026-08-08
- **Lean:** `RHTower/RouteRBurnolXiPrimeTwoCompletionLanding.lean`
- **Route:** R

## Frontier question

Can fixed pre-divisor Burnol co-Poisson atom be carried coefficient-faithfully to genuine completed-Xi first-divided vector, without critical-line placement or a same-fibre norm hypothesis?

## Conjecture cycle

### C1 — diagonal completion signs fixed Burnol current `[FAILED]`

Multiplication by completion factor is diagonal on critical Mellin line. It commutes with Cartier zero-transfer multiplier, so it cannot change strict accretive sign of forward Cauchy shift. This mechanism cannot prove `J_rho <= 0`.

### C2 — prime-two completion gives exact divisor landing `[PROVED]`

For fixed atom from window `[1/2,1]`, define

\[
F(w)=\mathcal M_{\Gamma}f_0(w),\qquad
C_2(w)=\frac{w^2(w-1)}{2(2^w-1)}.
\]

Inside `0 < Re w < 1`, source Mellin formula gives

\[
F(w)=\Gamma_{\mathbb R}(w)(2^w-1)\frac{\zeta(w)}w,
\qquad C_2(w)F(w)=\xi(w).
\]

Both factors are nonzero where division is used. If `xi(rho)=0`, then `F(rho)=0`; differentiating product at confluent point or using ordinary divided differences away from it gives

\[
C_2(s)\,[F]_{\rho,s}=[\xi]_{\rho,s}.
\]

After centered affine coordinate `s=1/2+ix`, exact orientation is

\[
Q^{\Xi}_{\rho}(x)
= i\,C_2(1/2+ix)\,[F]_{\rho,1/2+ix}.
\]

This holds at multiple zeros: `dslope` uses derivative at confluent point.

### C3 — completed graph is automatically symmetric `[FAILED]`

Genuine completed graph carries rank-two theta Green flux

\[
\pi M B_\theta(q)=\operatorname{Im}(\alpha_q)\|Q_q^\Xi\|_2^2.
\]

It is nonzero and negative at every hypothetical right-half zero. Symmetry would therefore assume endpoint conclusion. Correct surviving statement is exact weighted Green law, not automatic flatness.

## Lean theorems

- `burnolFixedAtomCompletedMellin_eq`
- `burnolXiCompletionMultiplier_mul_fixedAtomMellin`
- `burnolXiCompletionMultiplier_mul_dslope_fixedAtomMellin`
- `completedXiFirstDividedFunction_eq_completionMultiplier_mul_burnolDslope`
- `integral_burnolFixedAtomCompletedDividedDensity_eq_norm_sq`
- `integral_burnolFixedAtomCompletedDividedDensity_pos`
- `thetaXiRankTwoBoundaryFlux_eq_burnolFixedAtomCompletedDividedDensity`

All are unconditional. Final Green law says

\[
\pi M B_\theta(q)=\operatorname{Im}(\alpha_q)
\int_{\mathbb R}|C_2(1/2+ix)[F]_{\rho,1/2+ix}|^2\,dx.
\]

## Exact remaining Route-R burden

Analytic/source-to-Xi landing and non-erasure are closed. Sign of Burnol fixed-aperture current does **not** follow from diagonal completion or completed graph symmetry. Remaining non-circular producer must control boundary contribution of noncommuting pair

\[
[P_{1/2},C_2],
\]

where `P_{1/2}` is fixed physical aperture reading and `C_2` is prime-two completion. Needed theorem is a pre-divisor Euler--Gamma--Stokes boundary law whose physical marginal is `J_rho`; it cannot be replaced by multiplier factorization or positivity of completed energy.

## Axiom audit

Target theorem chain uses only `[propext, Classical.choice, Quot.sound]` after Lean audit.
