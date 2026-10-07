# Logarithmic inverse disks for every real Xi tilt

- **ID:** RH-XILID-20261007
- **Stage:** 3-formalized
- **Parent:** `../1-in-progress/xi-logarithmic-islands-monodromy.md`
- **Verdict:** BRIDGE; no certified scientific novelty or RH conclusion

## Exact unconditional endpoint

`RHTower.exists_xi_tilt_exp_lift_ball (a M R : Real) (hM : 0<M)`:
there exists h:Complex->Complex, holomorphic on ball(0,M), such that
Re(h(w))>R and xi(h(w))*exp(-a*h(w))=exp(w) for every w in that disk.
The radius and real tilt are arbitrary; the real boundary R may have either
sign. There is no zero, critical-value, RH, or univalence hypothesis.

## Dependency-closed proof

The von Mangoldt Dirichlet series is bounded by its absolute sum C at2 on
Re(s)>=2. Vertical minimality and the real lower bound for digamma give
Re(xi'/xi)(s)>=(log(Re(s)/2)-1-log(pi))/2-C. Hence this real logarithmic
derivative eventually exceeds a+1 uniformly in the imaginary part.

For the tilted Xi function f, choose a half-plane Re(s)>T beyond that
boundary and beyond R. The earlier Schottky value-occurrence theorem gives
a point b with f(b)=1 and Re(b)>T+r, where r=2M+2. Integrate f'/f on that
half-plane, normalized to P(b)=0. The scalar differential equation shows
exp(P)=f, and Re(P')>=1 throughout the half-plane.

Noshiro-Warschawski applied to P(s)-c*s for each |c|<1 excludes any difference
quotient of P with modulus<1. Thus P expands all distances. On the circle
of radius r around b, |P(s)-P(b)|>=r. Mathlib's holomorphic open-map estimate
gives ball(P(b),r/2) in the image of the closed source disk. P is injective,
so Function.invFunOn on the half-plane is a left inverse. The strict complex
inverse-function theorem proves it holomorphic. Restrict it to ball(0,M).

This proof reuses actual corpus value occurrence, not a value-distribution
premise. It needs neither vertical decay nor an implicit level curve nor a
new Rouche formalization. Source assumptions are confined to the reusable
generic analytic lemmas and discharged in the actual Xi endpoint.

## Formal leaves and checks

- HTGeometry/HalfPlaneLogarithm: one public theorem.
- HTGeometry/HolomorphicExpandingInverse: two public theorems.
- RHTower/XiLogDerivFarRight: three public theorems.
- RHTower/XiLogarithmicIslands: one public theorem.

All four targeted builds pass. All four actual-source `lake env lean` checks
pass. Seven of seven public axiom closures contain only propext,
Classical.choice, Quot.sound. Each leaf has exactly one umbrella import.
No new heartbeat option or admission. Four matching obsolete proof scratches
were removed after exact comparison and final audits.

Evidence: `/tmp/rh-xi-island-verification.json`,
`/tmp/rh-xi-island-axioms.log`, `/tmp/rh-xi-island-final.sh`,
`/tmp/rh-final-{HalfPlaneLogarithm,HolomorphicExpandingInverse,XiLogDerivFarRight,XiLogarithmicIslands}.log`,
`/tmp/rh-XiLogDerivFarRight-build.log`, `/tmp/rh-island-generic-build.log`,
`/tmp/rh-XiLogarithmicIslands-build.log`.

Global lint exits1 on six unrelated unreachable HTGeometry leaves:
AlgebraicInfinityBranch, ApertureConeCalculus, ApertureConeWinding,
ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra.
No clean global lint claim. Index refresh is tracked in the parent log.

## Scientific audit and next claim

The parent records corpus and primary-literature audits. The uniform
far-right logarithmic derivative and univalence principle are classical.
The inspected Alvarez-Parrilla--Mucino-Raymundo inverse-singularity paper
studies integral dz/xi in its Xi application and leaves the inverse of xi
for further work; that does not establish novelty of this disk theorem.

This closes the exact analytic premise of the parent's finite loop-packet
construction. Joint finite-monodromy equality remains paper-only. Next:
separate arbitrary finite real slopes on each disk, construct actual source
loops, and prove the finite normal-subgroup argument. Do not promote finite
quotient equality to discrete fundamental-group equality.
