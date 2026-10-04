# Global nonlinear modular-source barrier

- ID: tt-global-nonlinear-source-barrier
- Parent: tt-nonlinear-critical-source-barrier (C72)
- Route: TT
- Stage: 3-formalized
- Theorem: every actual source point x>0 satisfies
  q−Tq²>1/12−7/(72k), where T=9−u² and q=(u−3J)/(ukT).
- No added source-sign or RH premise. This theorem does not establish
  global third-slope positivity, the full source quadratic, the transported
  fourth Schur gap, join/all-rank closure, or RH.

## Novelty and source basis

C70 established q>b(h), h=1/k and b(h)=1/12−7h/72. C71 exposed the
negative second transverse slope term left by that affine constraint.
The new nonlinear barrier controls that term throughout the actual ray.
Its lower-clock part h≤2/3 is already fully formalized in
`tt-nonlinear-source-low-clock.md`. The new proof closes the complementary
region by a second exact completion of the forcing field.

## Dependency-closed argument

Use V=u², T=9−V, y=q−Tq²−b, f=1−2Tq, and H=(6u/k)d/dx.
The audited source system gives

    Hy=6TR+6fAy,
    R=f(D+q²A)+(7/216)qHh+2Vq²,
    Hh=V m, m=−(4/3)h(3+h)(h−Tq).

A,D are the exact C70 polynomials in QuadraticBarrierAlgebra. The
lower-clock result gives y>0 when h≤2/3 and eventually as x→∞.
On y≤0, the already audited kinetic branch theorem gives Tq<1/6.
C70 gives q>b≥0. Hence q(1−Tq)≤b implies q<(6/5)b.

### Middle-clock exclusion

For 2/3≤h<3/4, 0≤V<9, b≤q<(6/5)b, introduce nonnegative s,t,z by

    h=(2/3+(3/4)s)/(1+s), V=9t/(1+t),
    q=b(h)*(1+(6/5)z)/(1+z).

The denominators are positive. Expanding the exact expression
−(1+s)^7(1+t)^3(1+z)^4 R produces a polynomial with nonnegative
coefficients and strictly positive constant. This proves R<0 on the
whole box. The projective identity and sign are checked symbolically by
Lean; no sampled sign or external algebra output is used.

Thus an actual point with y≤0,R=0 must have h≥3/4. The source constraints
and q<(6/5)b place it in the high-clock box

    3/4≤h≤4/5, 0≤V≤9, 0≤q≤1/80.

### Second forcing completion

Write Rh,RV,Rq for the exact partial derivatives of R. The first
completion, with L=qDerivativeRemainder and K=completedForcingRemainder,
is

    f HR=(6T Rq−12ATy)R+12qf²A²y+VK.

Set E0=−7m/72−12Tq² and M=mRh+12T RV+2qA E0. The new exact identities are

    L=−(7/162)h(3+h)[h−2Tq(1−Tq)]
        +4q(1−Tq)+f²q²*(2/3)(1+h/3)T,
    fK=f²M+L(VE0+6fAy)−2TR E0.

On the high-clock box f≥31/40>0. On y≤0, q(1−Tq)≤b≤1/96,
Tb≤3/32, so h−2Tq(1−Tq)≥9/16; the displayed L is strictly negative.
C70 also gives y≥−Tq². Using A≤(25/4)V, f≤1,
−m≥153/64 and Tq²≤9/6400 proves VE0+6fAy≥0.

The remaining term has the cancellation

    M=m(fDh−7qA/36+7Tq/18)+fmq²Ah+(7/216)Vq m mh
      +12TfDV+12Tfq²AV+(7/18)VTq mv+24Tq²+24TqD,

where mh=−(4/3)[(3+2h)(h−Tq)+h(3+h)] and
mv=−(4/3)h(3+h)q. Two summands are nonpositive. Bounds

    −m∈[153/64,13/4], 0≤−mh≤9,
    A≤48, Ah≥0, AV≤25/4,
    D≤1/30, Dh≥7/12, 0≤DV≤19/25920

bound the main term above by −(153/64)(161/480); the five positive
upper bounds sum to less than 1/2. Hence M<0. At R=0 the second
completion yields K<0; the first then yields HR<0 since V>0 and y≤0.
Exact source-field incidence proves R′<0 at every actual y≤0,R=0.

### Seam and global propagation

Source differentiation at zero gives

    (u−3J)'(0)=12+27k0−27k0², u'(0)=9k0,
    q(0+)=4h0²/27+h0/3−1/3, h0=1/k0∈[15/19,4/5].

The limit q0 obeys 1/50≤q0≤1/30 and b(h0)≤1/144, hence
q0−9q0²−b(h0)>0. Thus y>0 near the seam, as well as in the tail.
The corpus two-function trap applies because y′=(k/u)TR when y=0,
the weight is positive, and R′<0 whenever y≤0,R=0. It gives y≥0
between any positive seam and tail points, hence everywhere on x>0.

If y(x)=0, it is a local minimum. Then y′=0, forcing R=0. Differentiating
the exact speed split y′=(k/u)fAy+(k/u)TR gives y″=(k/u)TR′<0 there.
The audited second-derivative minimum theorem contradicts this. Thus y>0.

## Audit and integration

All scratch capstones, including `quadraticSourceError_pos` and
`boundaryRatio_gt_quadratic_barrier`, passed direct Lean checking with
only propext, Classical.choice and Quot.sound. All fourteen production leaves passed `lake --old env lean`, one foreground
leaf at a time. All are wired into RHTower.lean. Twenty imported capstones
also passed a separate axiom audit with only the standard three axioms.
Index exited 0. Lint exited 1 solely for seventeen unrelated umbrella
omissions; there are no C72 lint findings. Superseded C72 scratch sources
and caches were removed. No full or umbrella build. Audit logs:
`/tmp/tt_c72_final_*.log`, `/tmp/tt_c72_global_production_axioms.log`,
`/tmp/tt_c72_global_index.log`, `/tmp/tt_c72_global_lint.log`.

## Next hard problem

C73 (`tt-third-slope-nonlinear-cone.md`) attacks global third-slope positivity
using t−h²t²>r*b(h). The nonlinear boundary cancels the known adverse second
jet; its next sign must be derived from the full source field. No global
third-slope or RH conclusion is inferred from this barrier alone.
