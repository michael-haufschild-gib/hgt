# FZZ completed-response real-axis anchor gauge no-go

- **ID:** FZZ-CRRAG-NG
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / FALSIFIED route premise
- **Source:** `rh-current-frontier-map.md` FZZ-P route (read-only ledger)
- **Statement:** Completed Schwarzschild/FZZ samples, Xi reflection, Schwarz reality, order-one growth, exact values at completed `s = 0, 1/2, 1`, and zero-freeness on the full real axis still admit a nonreal off-critical zero in the open critical strip.

## Goal

Kill strongest purely real-axis repair of the FZZ-P source-selection chain

`physical all-order completed response -> unique Xi continuation / zero control -> completed Ward bound -> RH`.

Corpus endpoint `thetaPhysicalEndpointCompletedResponseWardBound_iff_riemannHypothesis` makes the
last implication exact. This falsifier attacks only proposed source-selection premise and assumes no
RH-strength property.

## Frozen proof-chain candidate

Let response coordinate be `z = s - 2`, canonical source `X(z) = xi(z+2)`, and corpus two-ladder
null generator

`K(z) = Gamma(-z)^(-1) Gamma(z+3)^(-1)`.

Put

`A(z) = (z+1)(z+2)(z+3/2)^2`, `B(z) = A(z)K(z)`.

At `a = -5/4 + i`, let `t = i/B(a)`,
`beta = 2 Im(t)`, `alpha = Re(t) + 15 Im(t)/8`, and

`P(z) = alpha + beta (z+3/2)^2`.

Then `P(a)B(a)=i`. Define

`G(z) = 1 + (P(z)B(z))^2`, `F(z)=X(z)G(z)`.

Candidate conclusion: `F` is entire, order-one, reflection-symmetric, Schwarz-real, matches every
completed physical sample, equals `X` at response coordinates `-2,-3/2,-1`, is nonzero at every
real response coordinate, and vanishes at `a`; completed zero `a+2=3/4+i` is in open critical strip
and off critical line.

## Corpus basis

- `isEntireCompletedBlackHoleSymmetricInterpolant_iff_twoLadderGammaNull`: exact reciprocal-Gamma
  null ideal for completed physical samples.
- `exists_xi_symmetric_entire_offcritical_countermodel` and
  `centeredQuartetGauge_real_pos`: positive real-axis gauges can insert nonreal off-line quartets.
- `riemannXi_ne_zero_of_ofReal`: Xi is nonzero on full real axis.
- `OrderOneEnvelope.mul` and `OrderOneEnvelope.add`: finite polynomial/Gamma gauge algebra remains
  in global order-one envelope.
- `differentiable_mul_ne_zero`: nonzero entire factors have nonzero product, used to certify
  noncanonicity without assuming Xi nonvanishing at `3/4+i`.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, explicit proof-chain falsifier, corpus basis
- [x] 1 -> 2 fully-proven: complete hostile-audited paper proof, `[PROVED HERE]`
- [x] 2 -> 3 formalized: Lean theorem `completed_response_anchors_realAxis_route_noGo`, targeted `lake build` green, axiom audit clean
- [ ] 3 -> 4 publication-ready: standalone theorem, proof, Lean certificate, novelty audit

## Approach

1. Prove `B(a) != 0` from reciprocal-Gamma zero classification and nonzero polynomial factors.
2. Verify exact two-real-parameter interpolation `P(a)=i/B(a)`.
3. Show `A`, `P`, `B`, `G` inherit response reflection and Schwarz reality.
4. Natural ladder zeros of `K` make `G=1`; zeros of `A` make `G=1` at completed anchors.
5. For real `z`, `P(z)B(z)` is real, so `Re G(z)=1+(P(z)B(z)).re^2>0`.
6. `G(a)=0` implants off-critical zero while preserving full package.
7. Prove `F != X` by no-zero-divisors for entire functions, avoiding any unknown assertion about
   `xi(3/4+i)`.

## Paper proof `[PROVED HERE]`

Write `a=-5/4+i`. None of `a+1`, `a+2`, or `a+3/2` vanishes because each has imaginary part one.
Likewise neither `-a=5/4-i` nor `a+3=7/4+i` is a nonpositive integer, so both reciprocal-Gamma
factors are nonzero. Hence `B(a) != 0`.

Set `t=i/B(a)`. Since

`(a+3/2)^2 = (1/4+i)^2 = -15/16+i/2`,

the real-coefficient reflection-even polynomial

`P(z)=Re(t)+2 Im(t)((z+3/2)^2+15/16)`

obeys `P(a)=Re(t)+i Im(t)=t`. Therefore `P(a)B(a)=i` and
`G(a)=1+i^2=0`.

Both `A` and `P` are fixed by `z |-> -3-z`: the first two factors of `A` swap with two minus
signs, and the centered square is fixed. They have real coefficients. Corpus generator `K` has the
same reflection and Schwarz symmetries. Thus `B`, `P B`, `G`, and `F=XG` inherit both symmetries.
Every factor is entire. Corpus order-one envelope is closed under constants, affine polynomials,
sums, and finite products, so `F` remains order one.

At every natural response order `m`, `K(m)=0`, whence `B(m)=0`, `G(m)=1`, and `F(m)=X(m)`, equal to
the completed physical Schwarzschild/FZZ sample. At response coordinates `-2,-1,-3/2`, `A=0`, so
the same identity gives exact canonical completed values at `s=0,1,1/2`.

For real response coordinate `x`, Schwarz reality makes `P(x)B(x)` real. If its real value is `y`,
then `G(x)=1+y^2` is a positive real number. Hence `F(x)=G(x)X(x)` is a strictly positive real
multiple of canonical response. Corpus theorem `riemannXi_ne_zero_of_ofReal` gives `X(x)!=0`, so
`F(x)!=0` on the full real axis.

Completed point `a+2=3/4+i` lies in the open critical strip and off critical line, while `F(a)=0`.
Reflection and conjugation produce its full quartet. Finally, if `F=X` as entire functions, then
`X(G-1)` is identically zero. Function `X` is not identically zero (for example its real values are
nonzero), and `G-1` is not identically zero because `(G-1)(a)=-1`. Corpus entire no-zero-divisor
theorem gives contradiction. Thus `F!=X`.

This proves the frozen falsifier and the stronger relative statement: the countermodel agrees with
canonical real-axis phase/sign everywhere, differing only by a strictly positive real multiplier.

## Hostile audit

- **Unknown Xi value at witness:** not used; gauge zero forces product zero.
- **Endpoint-only weakness:** rejected; witness has completed real part `3/4` and nonzero ordinate.
- **Real-axis condition:** global over all real response coordinates, not only open strip.
- **Identity theorem:** no conflict; exact equalities occur on a discrete ladder plus three finite
  anchors, while real-axis condition is positivity of a quotient, not pointwise equality.
- **Growth loophole:** no; only finite products of corpus order-one-envelope functions occur.
- **Fake noncanonicity:** excluded through no-zero-divisors for entire functions.
- **Symmetry orbit:** response reflection and conjugation force all four off-line zeros.

## No-go closure

- **Exact killing theorem/mechanism:** Lean theorem `completed_response_anchors_realAxis_route_noGo` gives an explicit positive square-gauge countermodel and kills completed-sample + FE + Schwarz + order-one + three canonical anchors + full real-axis zero-free source selection, even after requiring the canonical positive phase ray everywhere on the real axis.
- **Strongest positive survivor:** Lean theorem `completedResponsePositiveSquareGauge_package` classifies the infinite constructive cone `1+(P A K)^2`: every reflection-symmetric Schwarz-real entire order-one `P` preserves all samples and anchors and is strictly positive on the full real axis.
- **New insight:** Real-axis positivity is compatible with the full reciprocal-Gamma null ideal after squaring. Standard completion anchors and all real-axis zero data do not touch nonreal interpolation freedom.
- **Status:** Paper and Lean proved in `GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZSchwarzschildCompletedResponseRealAxisAnchorNoGo`. Direct `lake env lean` and targeted module `lake build` pass. Axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`. Module is wired into `RHTower.lean`; global lint failure contains only unrelated pre-existing unreachable modules and does not list this module. Corpus exact-query repetition found no prior combined theorem. Literature audit found classical Carlson uniqueness only under much smaller exponential type and classical reciprocal-Gamma/prescribed-zero machinery, but no exact FZZ/Schwarzschild sample-and-anchor positive-square theorem.

## Log

- 2026-08-30 — frozen as Stage 1 falsifier candidate after corpus collision audit.
- 2026-08-30 — `[PROVED HERE]`; hostile audit passed and promoted to Stage 2.
- 2026-08-30 — Lean formalization, umbrella wiring, targeted build, and axiom audit complete; promoted to Stage 3.
