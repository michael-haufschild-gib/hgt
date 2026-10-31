# Elliptic closed places have finite degree cutoffs

- **Stage:** 3-formalized
- **Statement:** The actual affine primes of `y²=x³−x` over `F₃` have
  finite bounded-degree sets `S_N`. For every `n>0`, the projective count is
  `N_n=1+Σ_{v∈S_n,d(v)|n}d(v)`.

## Proof

Each residue degree `d(v)` is positive. If `d(v)≤N`, then `d(v)|N!`.
The proved residue-embedding criterion identifies degree-dividing places
with kernels of point maps over the finite extension of degree `N!`.
These maps form a finite set, so their image contains every such place.
Thus `S_N` is finite, including the empty cutoff `N=0`.

For `n>0`, a positive degree dividing `n` is at most `n`. Hence the places
occurring over the degree-`n` extension are precisely the divisor filter of
`S_n`. The proved kernel-fibre count gives `d(v)` points at each such affine
place and one at infinity, yielding the asserted literal finite sum.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticClosedPointDegrees.lean`:
`finite_affinePlaces_degree_le`, `extensionPointCount_eq_closed_degree_sum`.
Direct Lean check passed; transitive axioms are exactly `propext`,
`Classical.choice`, `Quot.sound`.
