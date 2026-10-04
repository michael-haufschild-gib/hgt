# Actual nonlinear source barrier on the lower-clock ray

- **ID:** tt-nonlinear-source-low-clock
- **Parent:** tt-nonlinear-critical-source-barrier (C72)
- **Route:** TT, global actual normalized third-minor slope
- **Stage:** 3-formalized
- **Claim:** For every actual source point x>0 with h=1/k(x)≤2/3,
  q−Tq²>1/12−7h/72, where T=9−u² and q=(u−3J)/(ukT).
- **Not claimed:** positivity on 2/3<h<4/5, global third-minor slope,
  full source quadratic, transported fourth Schur gap, all-rank closure, RH.

## Corpus basis and novelty

C70 proves q>b(h)=1/12−7h/72 on the entire actual ray. C71 proves this
affine constraint still admits negative third-slope states; the exact
second transverse threshold is 54C(144a−r²). The present quadratic
constraint removes that precise adverse term on a complete source region.
No extra source-sign premise is introduced. Searches and unsuccessful
forcing trials are recorded on the parent card.

## Dependency-closed proof

Use the already formalized source ODEs and constraints
0<h<4/5, 0<V=u²<9, q≥0, Tq<h, T≤(361/25)h², q>b,
and the source limits h→0, V→9, q→1/12, kT→0,
k(q−1/12)→−7/72. Define y=q−Tq²−b and w=Tq.
Let H denote 6u/k times source differentiation. Exact polynomial algebra
provides

    Hy=6T R+6(1−2Tq)A y,
    R=(1−2Tq)(D+q²A)+(7/216)q Hh+2Vq²,
    Hh=−(4/3)h(3+h)V(h−Tq).

D and A are the previously audited C70 field polynomials.

1. On y≤0, q(1−h)≤b. The exact identity
   4/441−h²b=(h−4/7)²(7h+2)/72 gives h²b≤4/441.
   Together with the kinetic constraint, this proves 1−2w>0
   (split h≤2/3 and h>2/3). Also w(1−w)≤Tb≤(361/25)*(4/441)<5/36.
   The selected branch w<1/2 therefore has w<1/6.

2. At y=0, q=b/(1−w), V=9−w(1−w)/b. Exact denominator clearing gives
   (1−w)²R=P(h,w), with

       P=pTail+w*c1+w²*c2+w³*c3,
       pTail=−7h/16+125h²/288+49h³/288+49h⁴/2592,
       c1=4/9+37h/432−647h²/864−665h³/2592,
       c2=−1/2+71h/108+17h²/81−7h³/324,
       c3=−1/9+h/36+7h²/324.

3. For 0<h≤2/3 and 0≤w≤1/6 set
   B=4/9+253h/1296+(−647/864+17/486)h²−665h³/2592≥0.
   The exact nonnegative-remainder identity is

       pTail+wB−P =
         w²(1/2+7h³/324)
         +w(1/6−w)(71h/108+17h²/81)
         +w³(1/9−h/36−7h²/324) ≥0.

   Kinetic incidence gives w(1−w)≤(361/25)h²b and hence w≤18h²b.
   Put a=3h/2, d=1−a. Then

       pTail+18h²bB = −h[
         (7/16)d⁵+(157/108)ad⁴+(3071/1944)a²d³
         +(2347/2916)a³d²+(103015/314928)a⁴d
         +(4195/157464)a⁵] <0.

   Thus P<0, R<0 and y′<0 at every zero in the entire lower-clock region.
   All coefficients are from Lean-verified symbolic identities, not external
   evaluation or a finite numerical sign test.

4. Exact first-order assembly of R from the corpus limits proves kR→−7/16.
   With E=y/T, source differentiation gives

       E′=(k/u)(rate*E+R), rate=(1−2Tq)A+2V→54.

   C70 supplies E≥−q², and q is bounded on x≥1. Hence E is bounded below.
   Eventually R<0, rate>30, k/u≥1/3; whenever E≤0 we have E′<10E.
   The corpus bounded-escape theorem excludes an eventually negative E.
   Equality is excluded by its strictly negative derivative and eventual
   nonnegativity. Therefore E>0, and hence y>0, eventually.

5. k is increasing, so h≤2/3 remains true forward along the source.
   Suppose y(a)≤0 at a point of that region. The scalar comparison theorem,
   using y′<0 whenever y=0, forces y≤0 at all later points. This contradicts
   the positive tail. Therefore y(a)>0 throughout the entire region.

## Open continuation

The complementary interval is now closed by the global theorem in
`tt-global-nonlinear-source-barrier.md`. The new second forcing completion,
seam limit and two-function trap prove the same strict inequality for
every x>0. Global third-slope positivity remains the next hard target.

## Lean audit

Nine production leaves under `formal/GaloisForLFunctions/RHTower/`:

- `ThetaCuspRatioQuadraticBarrierAlgebra`
- `ThetaCuspRatioQuadraticBarrierBranch`
- `ThetaCuspRatioQuadraticBoundaryPolynomial`
- `ThetaCuspRatioQuadraticBoundaryLowClock`
- `ThetaCuspRatioQuadraticBarrierDynamics`
- `ThetaCuspRatioQuadraticBarrierForcingTail`
- `ThetaCuspRatioQuadraticBarrierNormalized`
- `ThetaCuspRatioQuadraticBarrierTail`
- `ThetaCuspRatioQuadraticBarrierLowClock`

Every leaf passed `lake --old env lean`; no full/umbrella build. Seventeen imported
capstones passed the separate /tmp axiom audit, each with only propext,
Classical.choice, Quot.sound. All nine leaves wired into RHTower.lean; index
exit0. Logs: /tmp/tt_c72_prod_*.log, /tmp/tt_c72_production_axioms.log,
/tmp/tt_c72_index.log. Lint exit1 solely from 17 unrelated missing umbrella imports; no C72 findings. Log: /tmp/tt_c72_lint.log.
