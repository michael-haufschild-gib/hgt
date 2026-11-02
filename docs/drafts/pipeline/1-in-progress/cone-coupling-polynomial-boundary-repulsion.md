# Cone coupling and polynomial boundary repulsion

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** SC2; `TheConeCouplingHasNoDeepestZero.lean`,
  `TwoPrimeTowersSeeEveryOrdinateDifference.lean`, and the exact-coefficient
  cone construction.
- **Statement:** For distinct primes, bounded natural-cone coupling implies
  RH or constants `c,A>0` such that every zeta zero satisfies
  `D-|Re ρ-1/2| ≥ c(1+|Im ρ|)^(-A)`, where `D` is maximal zero width.

## Mechanism under audit

Write `z=ρ-1/2`, `F(z)=(sinh z/z)^8`, and
`g(z)=F(z)(exp(a z)-1)(exp(b z)-1)`, with `a=log p`, `b=log q`.
Bounded coupling bounds all moments of the actual residues
`dρ=multρ·g(z)`. For a zero `z₀=δ₀+iγ₀`, put

`φ_s(z)=(exp(a(z-D-s-iγ₀))+exp(b(z-D-s-iγ₀)))/2`.

Mixed-moment recurrence should bound the first-order sum
`Σ dρ/(1-φ_s(z))` uniformly as `s↓0` when `D>0`.
The reciprocal has positive real part. Rotating by the phase of `g(z₀)`
makes the constant-residue part of every nearby term nonnegative.
The error is controlled by a uniform relative Lipschitz estimate for `g`.

The denominator `f(w)=1-(exp(a w)+exp(b w))/2` satisfies
`|f(w)|≥(a+b)|w|/4` for `|w|≤1/(2(a+b))`, by the quadratic exponential
remainder. If `D-δ₀≤s`, then
`|z-z₀|≤|z-(D+s+iγ₀)|` for every zero. Thus the local Lipschitz error
times the reciprocal stays bounded, even in an arbitrarily close cluster.

On any strip `0<d≤Re z≤1/2`, the explicit logarithmic derivative

`g'/g = 8(coth z-1/z) + a exp(a z)/(exp(a z)-1)
        + b exp(b z)/(exp(b z)-1)`

is uniformly bounded. Grönwall along segments then supplies the relative
Lipschitz estimate; no zero-spacing assumption is required.

Away from a fixed neighborhood, Baker separation should bound the resolvent
by a power of ordinate height. The precise auxiliary target is: for every
`r>0`, there are `c>0` and `N∈ℕ` such that
`c/(2+|Im w|)^N ≤ |1-(p^w+q^w)/2|` whenever `Re w≤0` and `|w|≥r`.
If `-Re w≥r/2`, radial contraction gives a fixed gap. Otherwise
`|Im w|≥r/2`; Baker separation and the squared chord defect give the bound.
Exact eighth-power spline decay and tempered
zero energy should give `Σ (1+|γ|)^6|dρ|<∞`, hence tail error
`O(s⁻¹(1+T)⁻⁶)`. The own-atom contribution is
`≫(1+|γ₀|)⁻⁸/s` if `D-δ₀≤s`.
Choosing `T=L(1+|γ₀|)²` and then polynomially small `s` should contradict
the uniform Cayley bound.

## Gaps

The actual-coupling specialization, local phase/error estimate, quantitative
far-resolvent bound, and final choice of constants need Lean formalization.
No boundary-repulsion theorem is claimed yet.

## Formalized input

`ConeBoundary/SplineResidueDecay.lean` proves
`summable_sixth_height_wt`, `summable_sixth_height_mixedResidue`, and
`mixedResidue_tail_le` for actual zeta zeros. The tail above height `T≥0`
is at most the total sixth height moment divided by `(1+T)^6`.
Direct module audit passes with only `propext`, `Classical.choice`, and
`Quot.sound`; the umbrella import is wired.

`ConeBoundary/TwoClockResolvent.lean` proves
`norm_tsum_clock_resolvent_le`: absolutely summable residues with mixed
moments bounded by `M` have resolvent norm at most
`M/(1-|x|-|y|)` whenever both the scalar parameter sum and the pointwise
clock combination are strict contractions. It also proves
`clockDefect_lower_near_zero`, the explicit simple-zero bound above.
Its direct audit has the same standard axiom set; the umbrella is wired.

`ConeBoundary/SplineResiduePhase.lean` proves the explicit logarithmic
derivative, its uniform strip bound, `splineResidue_lower`, and
`exists_splineResidue_relative_lipschitz`. Thus the exact complex residue
has an eighth-power height lower bound and uniform relative variation on
each positive strip. Direct audit passes with the same standard axioms;
the umbrella is wired.

## Failed shortcut and retained insight

Direct double-pole isolation cannot use Baker separation as a lower bound
for arbitrarily close ordinates: its bound contains `min(|Δ|,(2+|Δ|)^(-C))`.
The proposed replacement treats close zeros as one phase-coherent cluster.
Even polynomial repulsion would not prove RH: the exact-coefficient abstract
cone model approaches its boundary more slowly and is compatible with it.
