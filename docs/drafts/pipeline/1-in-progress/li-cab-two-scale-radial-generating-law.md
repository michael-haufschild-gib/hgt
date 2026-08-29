# LI-CAB two-scale radial generating law

- **ID:** LI-GF1
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `rh-current-frontier-map.md` route LI; `LiEvenCrossCompletedAbelInteriorFirstZero.lean`; `SquaredXiCompleteMonotonicity.lean`
- **Statement:** For `v > 0` and `0 < s < 1`, the ordinary generating function of the complete adjacent currents at `t = s²` is an exact divided difference of the first dilation derivative of the squared-Xi radial logarithmic derivative at reciprocal scales `a v` and `v/a`, where `a = ((1+s)/(1-s))²`.

## Goal

Replace LI-CAB5's infinite-divisor/all-mode current by two values and first derivatives of the actual completed-Xi radial source. Exact proof chain under attack:

two-scale source law plus coefficientwise source orientation
`=> liEvenCrossSquareMassAdjacentCurrent v n > 0` for every `n` and `0 < v ≤ 1/4`
`=>` LI-CAB6 interior zero exclusion
`=>` endpoint completed-Abel nonnegativity
`=>` positive even Li coefficients
`=>` RH.

Hostile branch: if the divided difference forces a negative Taylor coefficient or an interior zero, LI-CAB5 is false and the LI completed-Abel mass-flow route is retired. No finite Xi packet, numerical zero data, or assumed divisor location is allowed.

## Gates

- [x] 0 → 1  in-progress: corpus-derived, source-pure, exact algebraic attack, RH chain fixed
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper theorem and proof

## Approach

Let `b = xiSquaredNode q`, `r = (b+v)⁻¹`, and

`P_n(x) = -(n+1)(1-x) U_(2n+1)(2x-1)`.

The corpus identifies the complete current with `Re sum_q r P_n(vr)`. The odd-Chebyshev recurrence gives, for `|t| < 1`,

`sum_(n≥0) P_n(x)t^n = -2(1-x)(2x-1)(1-t²) / ((1-t)²+16tx(1-x))²`.

At `t=s²`, set `a=((1+s)/(1-s))²`, `A=av`, `B=v/a`. Since `AB=v²`, the atom denominator factors as

`((1-t)²+16tvr(1-vr)) = (1-t)² (b+A)(b+B)/(b+v)²`.

Writing `F(y)=Re xiShiftedReciprocalMoment y 0` and `K(y)=F(y)+yF'(y)`, the expected exact aggregate is

`sum_(n≥0) current(v,n)t^n = 2(1+t)/(1-t)^3 * (A*K(A)-B*K(B))/(A-B)`.

The paper proof must justify the Chebyshev series, divisor/mode interchange, conjugation reality, resolvent differentiation, and the `s→0` diagonal limit separately. Sign extraction must be hostile-tested: positivity of the generating function alone does not imply coefficientwise positivity.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** pending
- **Strongest positive survivor:** pending
- **New insight:** pending
- **Status:** internal corpus audit complete; primary-literature audit found generalized Li/Bombieri-Lagarias transforms but not this squared-mass two-scale radial divided difference. Paper proof in progress.

## Log

- 2026-08-29 — conjectured from exact LI flux quotient, shifted reciprocal moments, and squared-Xi radial-field identities.
