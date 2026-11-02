# Polynomial repulsion from maximal zero width

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** SC2; bounded natural two-prime cone coupling.

## Exact theorem

Let `p != q` be primes. If the actual zeta coupling is bounded on
`(p^m,q^n)`, `m,n∈ℕ`, then either RH holds or there are `c>0` and an integer
`A>0` such that every nontrivial zeta zero satisfies

`c/(1+|Im ρ|)^A ≤ D-|Re ρ-1/2|`,

where `D` is maximal zero width. Constants are uniform over zeros and
multiplicities. No spacing, simplicity, or attained-width assumption enters.
This strengthens exclusion of a deepest zero; it does not prove RH.

## Proof

Put `a=log p`, `b=log q`, `zρ=ρ-1/2`, and
`g(z)=(sinh z/z)^8(exp(a z)-1)(exp(b z)-1)`.
The actual residues are `dρ=multρ·g(zρ)`. Bounded coupling bounds all their
mixed moments. When `D>0`, the geometric resolvent identity therefore bounds

`|Σρ dρ/(1-φ_s(zρ))| ≤ U`,
`φ_s(z)=(exp(a(z-D-s-iγ₀))+exp(b(z-D-s-iγ₀)))/2`,

uniformly in `γ₀` and `s>0`.

Write `f(w)=1-(exp(a w)+exp(b w))/2`. On the left half-plane its reciprocal
has nonnegative real part. Near zero,
`|f(w)|≥(a+b)|w|/4`. For a center `z₀=δ₀+iγ₀` with `D-δ₀≤s`,
`|z-z₀|≤|z-(D+s+iγ₀)|` for every zero. On each positive strip the explicit
logarithmic derivative

`g'/g=8(coth z-1/z)+a exp(a z)/(exp(a z)-1)+b exp(b z)/(exp(b z)-1)`

is bounded. Its relative Lipschitz estimate and the simple-zero denominator
bound show that nearby terms, rotated to align `g(z₀)`, contribute at least
`-C|dρ|`. This treats arbitrarily close clusters without isolating their atoms.

Outside a fixed radius, radial contraction and two-prime Baker separation give
`|f(w)|≥c₁/(2+|Im w|)^N`. Thus the resolvent is at most `F T^N` when both
ordinate heights are at most `T≥1`. Globally it is at most `K/s` for `s≤1`.
Exact eighth-power spline decay and tempered zero energy give
`S=Σρ(1+|γρ|)^6|dρ|<∞`, so the tail above `T` has mass at most
`S/(1+T)^6`.

The aligned center contributes at least `A₀/(s H^8)`, where
`H=1+|γ₀|`, provided `D-δ₀≤s≤s₀=min(D/2,1)`. Summing the negative-error
bounds, with `M=Σρ|dρ|`, gives

`A₀/(s H^8) ≤ U+(C+F T^N)M+(K/s)S/(1+T)^6`.

For `B=1+U+(C+F)M+KS`, this implies
`A₀/H^8≤B(s T^N+T^(-6))` whenever `T≥H`.
Take `L=1+8B/A₀`, `T=L H²`, and
`c=min(s₀,A₀/(8B L^N))`. At `s=c/H^(2N+8)`, each error term is at most
`A₀/(8H^8)`, a contradiction. Hence the right-width gap exceeds this `s`.
Reflection `ρ↦1-conj ρ` preserves ordinate height and gives the absolute-width
bound. If `D=0`, the existing width criterion gives RH.

## Formalization

Namespace `GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary`:

- `PolynomialBoundaryRepulsion.lean`:
  `riemannHypothesis_or_polynomial_boundary_repulsion`.
- `ActualBoundaryEnergy.lean`: `exists_actual_boundary_energy_bound`.
- `PolynomialGapScale.lean`: `exists_polynomial_gap_scale`.
- `ActualResidueGeometry.lean`: actual own-atom and cluster bounds.
- `SplineClusterBounds.lean`: aligned cluster and summable-error inequalities.
- `ActualConeResolvent.lean`: uniform actual boundary resolvent bound.
- `TwoPrimeResolventSeparation.lean`: polynomial denominator separation.
- `SplineResiduePhase.lean`: exact residue lower bound and relative variation.
- `TwoClockResolvent.lean`: mixed-moment resolvent and simple-zero estimates.
- `SplineResidueDecay.lean`: actual sixth height moment and tail estimate.

All direct `lake --old env lean` audits pass. The final theorem's transitive
axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
Umbrella imports are wired.

## Boundary and comparison

Direct double-pole isolation fails at close ordinate differences: Baker's
bound contains `min(|Δ|,(2+|Δ|)^(-C))`. The positive survivor is the uniform
cluster estimate above, which converts cancellation control into a height-gap
law. The exact-spline abstract cone model approaches its boundary more slowly
and is compatible with this conclusion.

The prior no-deepest theorem only excludes attainment.
`zeta_near_top_cluster_collapse` instead assumes positivity of modulated Weil
difference tests over a real lag interval and bounds companion distances.
No matching polynomial repulsion theorem was found in the local corpus;
external priority was not checked.
