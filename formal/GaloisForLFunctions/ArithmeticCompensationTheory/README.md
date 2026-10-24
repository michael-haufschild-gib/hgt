# Arithmetic Compensation Theory

Arithmetic Compensation Theory studies **cancellation between exact descriptions
of the same source**. Two large pieces may cancel to leading order while their
sum still grows beyond the required norm. The programme asks which joint
arithmetic constraints control the absolute remainder, with constants that
survive increasing cutoff or aperture.

Its working rule is to identify and subtract the coherent contribution before
taking absolute values. Mixed terms, poles and boundary corrections carry the
cancellation; they are part of the object being estimated.

## Objects and language

The main arithmetic receiver is

$$
A_\varepsilon(n)=\sum_{d\le n}\mu(d)d^{-\varepsilon}\lfloor n/d\rfloor
 -\frac n{\zeta(1+\varepsilon)},\qquad
E_T(\varepsilon)=\sum_{n\le T}\frac{A_\varepsilon(n)^2}{n(n+1)}.
$$

**Admission** means a bound uniform in $T$ at fixed positive damping.
Admission at dampings accumulating at zero is an RH criterion.

A **compensated decomposition** writes the same receiver as a coherent part
plus a residual, retaining their mixed Gram term. **Relative compensation**
means the residual is small compared with a growing reference energy.
**Absolute compensation** bounds it in the receiver norm itself. These are
different conclusions.

A **corrector** is a source-defined adjustment of the energy intended to make
transport manageable. It must be quantitatively comparable with the original
receiver. A **defect profile** records where normalized energy goes if no
uniform bound exists, including mass moving towards the horizon.

## The prime comb: a guiding example

A prime comb sums weighted translates of a test over primes up to the aperture
horizon. Bounding its pairing by its full norm seems natural, but loses its
geometry. On slowly varying tests, the normalized comb is approximately a
translation towards the horizon. On fixed compact tests, its limit is an
exponential resolvent with horizon energy $J(F)$.

The consequences are sharp: comb energy is asymptotic to $4J(F)e^{2r}$ on
fixed tests, and smooth odd unit families attain the universal exponential
scale. Their first-power pairing with the original test can nevertheless be
much smaller. The large norm is largely located where the original source
has little overlap. This is why a polynomial bound for the raw half-power
cross-prime aggregate is the wrong target. The translation/resolvent law gives
the useful replacement object. See
[ThePrimeCombIsATranslation](ThePrimeCombIsATranslation.lean).

## Other foundational mechanisms

**Exact compensation coordinates.** Large-prime sectors and their literal
complements can be asymptotically antiparallel. Pythagorean and Gram identities
separate the coherent amplitude from the transverse remainder. They show
exactly why nearly perfect relative cancellation can coexist with unbounded
complete energy.

**Signed work versus positive loss.** Continuation uses the integral of signed
damping work. Its positive-part budget is stronger, and a tangent-norm bound
stronger still. Corrector criteria preserve this distinction and require an
independent source estimate, not an energy defined to contain the desired bound.

**Origin and tail costs.** Moving the origin, projecting onto a growing carrier
or changing cutoffs alters the norm and introduces boundary terms. The theory
prices those changes explicitly. A small error after normalization is useful
only when the same normalization preserves the receiver one wants to bound.

**A paid power subtraction.**
[Arithmetic Defect Rigidity](../ArithmeticDefectRigidity/README.md) identifies
the inversion forcing as $c_\varepsilon n^{1-\varepsilon}$ plus a remainder
bounded in the pronic norm. Subtracting that power from the proper cofactor
leaves $A_\varepsilon+\widetilde D_\varepsilon=R_\varepsilon$ with bounded
$R_\varepsilon$. This gives an absolute error budget and a signed constraint
on escape, while still allowing the two large terms to cancel.

**Rates and aperture floors.** Existing single-scale estimates save arbitrary
fixed logarithmic powers but retain the elementary power of the horizon.
Two-scale comparisons improve particular residual rates. On the aperture
side, every positive floor must respect the doubly exponential ground-energy
ceiling; a fixed positive margin cannot be transported indefinitely. Graded
negative floors and sufficiently decaying positive floors remain valid targets.

## Research questions

- Can compatibility between the source's prime- and Möbius-dilation
  decompositions bound the full residual at one fixed damping below $1/2$?
- Which corrector, built from independently controlled source terms, gives a
  horizon-uniform continuation budget?
- Can the translated comb or its resolvent produce a signed first-power
  prime–polar estimate with an improved exponential rate?
- Which moving-horizon defect profiles survive the paid subtraction and all
  source constraints, and what arithmetic estimate excludes them?

A statement of the form $O(T^\alpha/\log^mT)$ is an upper bound, not evidence
of divergence. Conversely, a relative error tending to zero is not evidence
of admission. The absolute remainder and its norm decide both questions.

## Place in the wider research

[Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md)
supplies the prime-comb and shared-cost problems.
[Arithmetic Continuation and Critical Energy](../ArithmeticContinuationAndCriticalEnergy/README.md)
supplies the transport identity whose work must be paid.
[Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) supplies
actual-row bilinear estimates; matching their ranges and remainders gives
usable transfers rather than new representations of the same unknown bound.

Begin with the comb example, then the compensation coordinates appropriate
to the source. The [programme umbrella](../ArithmeticCompensationTheory.lean)
maps the corrector, remainder and horizon laws.
