# Exceptional-layer theory of ζ

- **ID:** ELT
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** ../../reports/review-0911/obstacles-summary.md, §§2.5 and 2.10
- **Statement:** Couple an isolated top layer of ζ to its infinite remainder; prove graded repulsion, finite-stratum reduction, or AAL.

## Exact targets

1. Graded law relating Θ∞−½ to the isolation gap and layer ordinates.
2. Failure of AAL implies finitely many off-line zeros; consequently AAL ⇔ B13.
3. Exclude one isolated quartet, then all isolated top layers.
4. Develop exceptional subtraction, isolated-term power sums, positive kernels,
   Gaussian-current passage and sampling tools that resolve these interactions.

The phrase “every other zero lies on the line” is stronger than target 2;
the reflected bottom and possible finite intermediate layers must be distinguished.
No target above is assumed or claimed proved.

## Observation-scale question

Existing passage handles damping y=1/T at heights [T,2T]. For an exceptional
mode at ρ, the exact contribution is ½Γ((ρ−s)/2)y^((s−ρ)/2).
Its Gamma factor decays exponentially in height separation, while its damping
factor amplifies real-part excess. Determine the joint-scale boundary with
the infinite complementary divisor retained. This decides which observations
can compare top-layer persistence against the continued current.

For y=exp(−aT), the exponential mode rate is a(Re ρ−σ)/2−π/4.
Upper and reciprocal bounds prove both strict sides of this boundary.
The complete pole-plus-finite-layer raw expansion converges uniformly
at every positive exponential speed. Some speeds make the current
asymptotic to a divergent pole mode while every exceptional mode decays.
These results are Lean checked in `TheGaussianObservationBoundary` and
`ThePrimeCurrentAtExponentialScales`; no repulsion or replication follows.

The normalized top-layer profile is now Lean proved in
`TheExceptionalLayerAtEscapingHeights`: its phase is `(at+log(t/2))/2`,
with ordinate weights `exp(π Im ρ/4)`. See
`../3-formalized/elt-moving-layer-phase.md`. The sharp recurrent envelope
is the next refinement (`elt-recurrent-layer-envelope.md`).

## Foundations and gaps

`OnlyExceptionalGaussianModesRemain` bounds the complete complementary field
by C(y+y^((σ−θ)/2))(1+log t). `ThePrimeCurrentPassesAcrossDyadicWindows`
removes finite modes and continuum at inverse-height damping.
The new exponential expansion resolves this family of joint limits.
None of these results changes a zero's height.

Foundational programme document:
`formal/GaloisForLFunctions/ExceptionalLayerTheory/README.md`.
