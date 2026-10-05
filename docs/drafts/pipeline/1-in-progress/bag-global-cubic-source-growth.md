# BAG full Schwartz critical boundary after actual source growth

- **ID:** BAG-C28.56ae, closed in Lean; retained proof-development history.
- **Route:** BAG actual rational cubic to physical test profiles.
- **Predecessors:** C28.56aa compact arithmetic boundary; C28.56ab full
  rational source; C28.56ac weighted rational/tested identification;
  C28.56ad actual all-order global source control.

## Current status

The complete fixed-Schwartz theorem, actual-source finite-seminorm bounds,
full-plane domination, signed intersection, reflection identities and rational
assembly are formalized. See [audited result](../3-formalized/bag-schwartz-cubic-critical-boundary.md).
Four production leaves and all 33 public axiom audits passed. The active hard
continuation is [physical contraction matching](bag-physical-contraction-moving-poles.md),
C28.56af. The conjecture language below records the proof's development.

## Closed obstacle

C28.56ad proves polynomial bounds for EVERY joint real and complex derivative
of the ACTUAL A_sigma(u,v) and T_sigma(u), uniformly on sigma in [1,2].
It also proves genuine polynomial-radius analytic neighborhoods and actual
H/K tube bounds. See P3 bag-global-cubic-source-growth and its three leaves.
Do not reintroduce source growth as an assumption or repeat this work.

## Hard conjecture

For every fixed Schwartz frequency test Phi, prove the complete critical
boundary of the actual tested rational cubic, with both finite parts,
product PV, intersection mass and ordinary test integral retained. Prove
uniform control in explicit finite Schwartz seminorms. This must concern
realCubicSource, realAxisSource and the literal cubicConnectedKernel, not
an abstract source with unproved growth hypotheses.

Growing physical tests require a further uniform approximation/coupled-limit
argument. A fixed-test limit alone does not close that obligation.

## Corpus-grounded proof mechanism

The new all-order bounds include parameter derivatives and therefore control
source variation as sigma approaches one. Multiply by Schwartz decay, using
Leibniz and the isometric/linear frequency embeddings, to prove uniform rapid
decay of cubicTestedSource and cubicTestedAxisNumerator and their derivatives
through order two. Keep the uniform constants in finite test seminorms.

The literal axis numerator is (A_sigma(u,v)-T_sigma(u))*Phi(u,v).
It vanishes identically at u=0 for EVERY sigma and v by the existing exact
axis identity. Thus near u=0, even reflection gives quadratic cancellation
using second derivatives on the short segment [-|u|,|u|]. At |u|>=1 use
rapid decay directly and the inverse-square denominator. This should yield
an integrable product-decay bound for cubicAxisQuotient, uniform in sigma.
The other axis follows by the already-proved source symmetry and swapped test.

For cubicMixedQuotient split into four regions according to |u|<=1 and
|v|<=1. Both small: the existing two-mean-value mechanism gives mixed
cancellation. One small: reflect only in that coordinate and use first
partial derivative decay in the large coordinate. Both large: use direct
rapid decay of the four source values. Retain every reflected signed
quadrant and prove an integrable full-plane dominator before DCT.

For intersection concentration, the new zeroth-order growth and Schwartz
decay give a uniform bound on A_sigma*Phi over the whole plane. The existing
scaled Cauchy-product density is integrable and has mass pi^2. Reuse the
actual scaling identity and continuity at (sigma,u,v)=(1,0,0), with this
proved noncompact bound replacing compact-support domination.

Finally prove full-plane reflection identities and assemble the literal
connected kernel. Use C28.56ac's rationalCubicTest_hasSum for the exact
rational-series identification. Do not assert convergence of the finite-prime
integral net without a separate uniform-prime argument.

## Search and current status

Search79976 (deep300, "Schwartz reflection finite part product principal value
dominated convergence") finished nonpartial65519/65519. All candidate,
source, proof-idea and ingredient sections inspected. Compiler metadata
mostly pending/source-only; refresh incomplete. It returned general DCT,
Schwartz reflection sources and unrelated finite-part constructions, not
an actual-source noncompact critical theorem. Existing actual reflected
quotients and cancellation identities were read in the aa leaves.

Mathlib Function.HasTemperateGrowth records smoothness and all-order
polynomial bounds; fixed-sigma use alone does not establish the required
uniform-in-sigma seminorm control. Build the missing uniform estimate.
No failure of the Schwartz conjecture has been established.

Physical contraction matching, finite-height near-resonances, coupled
limits, growing moments, moving cofactors and positive common-height
self-return remain open. RH unproved. This is an active proof problem,
not a reason to pivot away from BAG.

## Active proof refinement

Search9492 for Schwartz polynomial multiplier uniform derivative decay finished
nonpartial65524/65524; all ranked sections inspected, compiler metadata mostly
pending/source-only, background refresh incomplete. It gives the standard
Schwartz decay/seminorm machinery, not the desired uniform actual-source result.

A concrete strengthened intermediate conjecture is under Lean audit: for every
weight k and derivative order n, a constant C(k,n), independent of Phi and sigma,
controls BOTH tested-source derivatives by the finite standard seminorm supremum

    S_(k+54+9*n,n)(Phi) = sup_(a<=k+54+9*n,b<=n) seminorm(a,b)(Phi).

The left side is (1+|u|+|v|)^k times the norm of the full joint nth derivative
of cubicTestedSource or cubicTestedAxisNumerator. Local Leibniz and linear
projection of derivatives apply the actual ad producer; the fixed finite
Schwartz seminorm family supplies the decay. No assumed multiplier estimate.

For the quotient domination use weight4 and derivative orders0,1,2. Axis
reflection on a short segment at fixed v preserves transverse decay, unlike
an expanding centered box. Product PV needs short-segment first derivatives
in exactly one small coordinate, the rectangular second derivative for two
small coordinates, and direct source decay for two large coordinates.
The candidate common envelope is a constant times
1/((1+u^2)*(1+v^2)), already integrable as cubicIntersectionDensity.

## Full-plane assembly proof

Use exact reflection averages on the whole plane. Axis quotient is even in
the first coordinate; mixed quotient is even in both. Thus the positive-region
envelopes extend everywhere without changing the product Cauchy density.
Axis average is one half of its two-reflection sum; mixed average is one
quarter of the four-reflection sum. Prove original kernel integrability
before splitting these averages: |u|/(epsilon^2+u^2)<=1/epsilon and
1/(epsilon^2+u^2)<=epsilon^-2 reduce both kernels to actual tested-source
integrable decay. These estimates are only integrability tools, not new
numerical optimization targets.

Full-plane DCT retains the actual moving source and yields both reflected
limits. Together with the already checked Schwartz intersection limit this
gives the candidate complete action

    (1/2) integral Q_axis(Phi) + (1/2) integral Q_axis(Phi swap)
    - pi^2 Phi(0,0) - (1/2) integral Q_mixed(Phi) + integral Phi.

The rational-series identity is the existing unconditional termwise-integral
producer rationalCubicTest_hasSum applied to Schwartz integrability. No claim
about interchanging the finite-prime integral net is part of this argument.
Quotient, DCT, reflection and final-assembly proofs subsequently passed all
production and axiom audits; see the current-status paragraph above.
