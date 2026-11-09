# A height finite part of the critical adelic Green product

- **Stage:** 3-formalized
- **Obstacle:** B133; the multiplicative local-profile candidate.

For reduced `q=a/b∈(0,1)`, the critical archimedean profile at distance
`2log(b/a)`, multiplied by the normalized finite Green factors, equals
`b⁻²/(1−(a/b)⁴)`. The sum of `b⁻ˢ/(1−(a/b)⁴)` over primitive pairs
converges exactly when `s>2`. Consecutive pairs force divergence at `s=2`.

Write

`1/(1−r⁴)=1/(4(1−r))+h(r)`,
`h(r)=1/(4(1+r))+1/(2(1+r²))`,
`c₀=∫₀¹h(r)dr=log 2/4+π/8`.

At height `n≥2`, subtract the exact collision row and density row

`C_n=n⁻² Σ_{1≤a<n,(a,n)=1} 1/(4(1−a/n))`,
`D_n=c₀φ(n)/n²`.

The resulting rows

`R_n=n⁻²(Σ_{1≤a<n,(a,n)=1} h(a/n)−c₀φ(n))`

satisfy `Σ_n |R_n|<∞`. Hence the primitive height cutoff has a finite
limit after subtracting `Σ C_n+Σ D_n`.

## Proof

The closed ordinary row error
`E(n)=Σ_{1≤a≤n}h(a/n)−nc₀` satisfies `|E(n)|≤3/4` by monotone
quadrature. Möbius inversion gives the primitive error exactly as
`Σ_{d|n}μ(d)E(n/d)`, bounded by `3τ(n)/4`. The divisor majorant
`Σ τ(n)/n²` converges. Height one is excluded from the geometric orbit.

## Lean

- `HyperbolicArakelovTheory/TheCriticalAdelicOrbitRequiresGlobalRenormalization.lean`:
  `CoupledOrbit.term_two_eq_local_product`, `term_split`, `summable_term_iff`.
- `HyperbolicArakelovTheory/TheFinitePartOfTheCoupledAdelicOrbit.lean`:
  `CoupledOrbit.regularMean_eq`, `primitiveSmoothRow_moebius`,
  `geometricRow_eq_localGreenSum`, `summable_renormalizedRow`,
  `tendsto_orbit_finitePart`.

Audited capstones use only `propext`, `Classical.choice`, `Quot.sound`.

## Boundary

Absolute convergence is across height rows. It does not permit arbitrary
reindexing of individual rational terms or establish torus automorphy.
This is a prescribed finite part for a product of local Green profiles.
Its identification with the additive adelic Green operator or Weil's
diagonal is unproved. No positivity or RH conclusion follows.
