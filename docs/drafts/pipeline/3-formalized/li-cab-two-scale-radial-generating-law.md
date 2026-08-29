# LI-CAB two-scale radial generating law

- **ID:** LI-GF1
- **Stage:** 3-formalized
- **Type:** THEOREM `[PROVED HERE]`
- **Source:** `rh-current-frontier-map.md` route LI; `LiEvenCrossCompletedAbelInteriorFirstZero.lean`; `SquaredXiCompleteMonotonicity.lean`
- **Statement:** For `0 < v ≤ 1/4` and `0 < s < 1/5`, put
  `A=v((1+s)/(1-s))²`, `B=v((1-s)/(1+s))²`, and
  `D(y)=y(Re M₀(y)-y Re M₁(y))`, where `M_k` is the complete shifted
  reciprocal-square Xi-divisor moment. Then

  `Σ_{n≥0} current(v,n)s^(2n)
   = 2(1+s²)/(1-s²)³ · (D(A)-D(B))/(A-B)`.

  Both sums are over the actual multiplicity-exact infinite Xi divisor; no
  finite packet, zero-location hypothesis, or computational input occurs.

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
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper theorem and proof

## Approach

Let `b = xiSquaredNode q`, `r = (b+v)⁻¹`, and

`P_n(x) = -(n+1)(1-x) U_(2n+1)(2x-1)`.

The corpus identifies the complete current with `Re sum_q r P_n(vr)`. The odd-Chebyshev recurrence gives, for `|t| < 1`,

`sum_(n≥0) P_n(x)t^n = -2(1-x)(2x-1)(1-t²) / ((1-t)²+16tx(1-x))²`.

At `t=s²`, set `a=((1+s)/(1-s))²`, `A=av`, `B=v/a`. Since `AB=v²`, the atom denominator factors as

`((1-t)²+16tvr(1-vr)) = (1-t)² (b+A)(b+B)/(b+v)²`.

Writing `F(y)=Re xiShiftedReciprocalMoment y 0` and `K(y)=F(y)+yF'(y)`, the exact aggregate is

`sum_(n≥0) current(v,n)t^n = 2(1+t)/(1-t)^3 * (A*K(A)-B*K(B))/(A-B)`.

The proof closes each nonformal step:

1. odd-Chebyshev generating series, first pointwise in every Xi-divisor copy;
2. phase-to-resolvent conversion and reciprocal-scale denominator factorization;
3. an explicit product majorant, giving absolute summability on
   `XiZeroCopy × ℕ` and legal Fubini interchange;
4. partial-fraction collapse to
   `Σ_q b/(b+y)²=M₀(y)-yM₁(y)` at `y=A,B`;
5. conjugation reality and descent to the actual real adjacent current.

The radius `s<1/5` is the unconditional uniform disk supplied by the corpus
hard-edge phase bound. Sign extraction remains hostile-tested: positivity of
the generating function alone does not imply coefficientwise positivity.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** not falsified. The conjectured
  full-divisor/full-mode identity is true on the proved uniform disk.
- **Strongest positive survivor:** exact two-scale source reduction above.
- **New insight:** LI-CAB5's infinite divisor/mode transform is not the open
  burden. Its entire generating tower is one radial divided difference. The
  remaining burden is precisely coefficientwise orientation of this actual Xi
  source germ; aggregate positivity alone is insufficient.
- **Status:** significant premise discharged on paper and in Lean. Internal
  corpus and primary-literature audits found generalized Li/Bombieri-Lagarias
  transforms, but no prior squared-mass two-scale radial divided-difference law.

## Formalization

- Module:
  `GaloisForLFunctions.RHTower.LiEvenCrossTwoScaleRadialGeneratingLaw`
- Capstone:
  `liEvenCrossSquareMassAdjacentCurrent_generating_eq_radialResponse_divDiff`
- Targeted check: `lake env lean` PASS.
- Targeted build: PASS (`lake build GaloisForLFunctions.RHTower.LiEvenCrossTwoScaleRadialGeneratingLaw`).
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`; no added axiom.
- Umbrella: wired into `GaloisForLFunctions.RHTower` without running an umbrella build.
- Global lint: new module reachable; repository lint remains red only from
  unrelated pre-existing unreachable modules.

## Log

- 2026-08-29 — conjectured from exact LI flux quotient, shifted reciprocal moments, and squared-Xi radial-field identities.
- 2026-08-29 — paper proof and Lean formalization completed; LI-CAB5
  full-divisor/full-mode transform discharged.
