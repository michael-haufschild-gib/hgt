# Uniform Gamma stability of actual generator heads

## Target

Find and formalize one constant K, independent of cutoff A, source coefficients,
source cardinality and horizon, such that the constructed finite real cell head
h=P_A f and tail t=f-h satisfy

Gamma(h)+Gamma(t) <= K Gamma(f).

The functions are the actual finite compact BV profiles from
ActualGeneratorHeadsPreserveTheSourceMean. No stability hypothesis may be added.
After this estimate, pay the remaining projected-Gamma term in the complete
even-power head error using the original Gamma reserve.

## Corpus inputs

- Exact stopping-block averages, finite BV realization and ordinary mean preservation.
- GammaMeanVarianceCapacity: simultaneous far-end mean graph and exterior mean
  charges bounded by the original Gamma energy for arbitrary disjoint intervals.
- GammaPairRemainder and GammaExteriorSubsets: actual interval kernels, exact
  averaging defects and a uniform first-moment bound for boundary rows.
- CompleteCellAveragesAreBoundedInGammaEnergy: homogeneous control at one paired
  level. Its constant is not iterated as a substitute for a depth-uniform proof.

## Direct comparison programme

The stopping partition has interval widths at most log 2. Consecutive widths
have uniformly bounded ratios: the initial logarithmic cells decrease slowly,
and the repeated band A<=a<2A resets by a bounded ratio.

For nonadjacent cells, an intervening neighbor makes the nearest separation
at least a fixed fraction of each endpoint width. A scalar density comparison
then bounds the actual kernel by a fixed multiple of the far-end kernel.
For adjacent cells, retain the integrated boundary defect; comparable widths
allow the far-end rectangle to pay that defect. A pointwise kernel comparison
at a touching endpoint is false and will not be used.

Use a finite contiguous partition containing the full source, padded by zero
cells on both ends. This makes nonzero exterior rows separated, avoiding a
false pointwise claim at an exposed nonzero boundary. Compare the complete
energy of the actual block averages with the existing original-source mean
graph and exterior charges. The quadratic triangle bound then pays the tail.

## Proof status

Kernel comparison is verified with C=32 exp(2). The generic finite interval
average estimate Gamma(g)<=C Gamma(f) is verified under explicit geometric,
local-mean and exterior-support conditions. The exact stopping-grid endpoints,
widths<=1 and adjacent width ratios<=3 are verified.

The finite padded-grid specialization is verified, including its exterior
and zero-boundary-mean conditions. The actual local-mean identification and finite support facts are verified.
The final head-plus-tail specialization and even-power consequence await Lean audits. The proposed
universal constant is K=2+96 exp(2). No actual-head Gamma bound is certified
until those source and boundary obligations pass.

The drafted consequence substitutes this constant into the complete even-power
head estimate. For every delta>0 it chooses one cutoff A0 before all finite
sources and horizons; every A>=A0 should give error<=delta Gamma(original).

## Mathematical argument

Write k(s)=exp(-s/2)/(1-exp(-2s)). For 0<s<=t<=7s and
t-s<=2, the geometric-series inequality 1-r^7<=7(1-r) gives
k(s)<=7 exp(1) k(t). The bound 1<=2 exp(1) t k(t), for 0<t<=2,
pays integrated touching-boundary defects with far-end rectangle charges.
Together these give the uniform rectangle constant C=32 exp(2).

The padded grid starts at -log(2), reaches zero after one cell, follows the
original log cells up to log(A), and then repeats the widths log(a+1)-log(a)
for A<=a<2A at every dyadic translate. Reciprocal bounds for log-cell widths
give adjacent ratios<=3. An intervening neighbor pays both endpoint widths
for every nonadjacent pair. A nonzero row separated from a padded exterior
has the same width-scale gap.

Each translated block indicator is the square-root block-length multiple of
a normalized retained cell. The generator projection fixes this indicator.
Self-adjointness equates its pairing with the original source and the head,
so the two profiles have the same integral on each block. The explicit
physical-height formula makes the head constant there. Therefore the head
is the original interval mean, including on every translated stopping cell.

Both profiles are finite compact BV sources, vanish below zero and vanish
above finite explicit endpoints. Choose the right grid boundary above both
support endpoints plus one. Since every width is at most one, the last cell
has zero original mean; the initial negative cell does too. All geometric,
mean and support conditions of the averaged-kernel theorem are then actual
properties of these sources.

The exact averaged-energy decomposition consists of mean-pair rectangles
and twice the exterior rows. Each is at most C times its far-end charge.
The simultaneous original-source mean-variance capacity inequality pays their
sum once, giving Gamma(h)<=C Gamma(f). The quadratic triangle inequality
gives Gamma(t)<=2 Gamma(f)+2 Gamma(h). Consequently
Gamma(h)+Gamma(t)<=(2+3C)Gamma(f)=(2+96 exp(2))Gamma(f).

For the complete even-power source, choose its signed compensation parameter
as epsilon/K. This gives error<=(epsilon+C_epsilon/(1+log A))Gamma(f).
Choosing A0 above exp(2 C_epsilon/delta), with epsilon=delta/2, pays the full
error by delta Gamma(f), uniformly for every A>=A0 and every finite source.

## Scope

Ordinary mean and square-mass identities do not settle the exponential Weil
moments. First-prime payment and retained-orbit positivity are separate from
this Gamma operator bound. Working findings and continuation state are kept in
logs/signed-arithmetic-hodge-research.log.
