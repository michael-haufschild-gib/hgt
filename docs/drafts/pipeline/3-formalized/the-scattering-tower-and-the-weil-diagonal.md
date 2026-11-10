# An intrinsic scattering realization of Weil's diagonal

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** B133: geometric normalization of Weil's diagonal.
- **Statement:** A scalar-renormalized tower of actual primitive-pair
  Poincaré pairings converges to the full Weil functional on compact C²
  autocorrelations, without inserting ζ values into its definition.

## Geometric construction

For `Re w>1`, let

`E_w(x+iy)=½ Σ_{gcd(a,b)=1} [y/((ay)²+(ax+b)²)]^w`.

Extract `φ(w)=∫₀¹ E_w(x+i)dx−1`, truncate
`T_w=E_w−1_{y>1}(y^w+φ(w)y^(1−w))`, and put
`P(w)=∫_fd T_w² dμ`. Define

`D(w)=(φ(w)^(-1)−φ(w))/(4(w−½))−P(w)/(2φ(w))`.

These definitions contain neither ζ values, its zero divisor, nor Weil's form.
For `s=c+it`, `c>1`, set

`R_N(s)=Σ_{n<N}D((s+n+1)/2)+r(c+N)+1/s+1/(s−1)`,

where `r(x)=½log(x/2)−½log π`. For `t≠0` and `c+N≥4`,

`|R_N(s)−ξ'(s)/ξ(s)| ≤ 2^(−N)M_c+(3+|t|/2)/(c+N)`,

with `M_c=Σ_{m≥1}Λ(m)m^(−c)`. Hence `R_N(s)→ξ'(s)/ξ(s)`.

For compactly supported C² `f`, put `k=f⋆f̃` and
`F_f(t)=Hfn k(3/2+it)+Hfn k(−1/2−it)`. Then

`lim_N (2π)^(-1)∫ F_f(t)R_N(3/2+it)dt = W_Λ(k)`.

The scalar term contributes exactly
`2r(N+3/2)‖f‖₂²=log((N+3/2)/(2π))‖f‖₂²`.
No separation or mass-balance condition is needed.

## Proof

Write `A=Λ(2w)`, `B=Λ(2w−1)` for the completed function.
Actual zero-Fourier extraction gives `Aφ=B`; actual Fourier uniqueness
gives `P_completed=A²P`. Thus completion cancels from the diagonal.
Maass–Selberg identifies it with
`Λ'/Λ(2w−1)−Λ'/Λ(2w)`. Conjugation of the truncated field supplies
both nonreal chambers, and the finite tower telescopes.

The Euler remainder is at most `2^(−N)M_c`. The half-plane digamma
bound and `|log z−log(Re z)|≤|Im z|/Re z` give the stated scalar
Gamma error. Since `F_f(t)=O((1+t²)^(-2))`, dominated convergence
and the full vertical-line formula give the packet identity. Fourier
inversion gives `∫F_f/(2π)=2k(0)=2‖f‖₂²`, fixing the local mass.

## Lean

Folder `GaloisForLFunctions/HyperbolicArakelovTheory`, namespace
`GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower`:

- `TheWeilSymbolFromTheGeometricScatteringTower.lean`:
  `norm_renormalizedTower_sub_symbol`, `tendsto_renormalizedTower`.
- `TheWeilPacketsFromRenormalizedGeometricDiagonals.lean`:
  `tendsto_geometricWeilEnergy`, `robinCounterterm_packet`.
- `TheIntrinsicGeometricWeilDiagonal.lean`:
  `RawGeometry.diagonal_eq`, `RawGeometry.tendsto_energy`.

All three direct source checks pass. Capstone transitive audits use only
`propext`, `Classical.choice`, `Quot.sound`. The programme umbrella imports
all three modules.

## Separation from operator-only adelic gluing

This identifies a renormalized modular scattering diagonal. The
[structural refutation](../2-fully-proven/hat-weils-diagonal-is-not-one-glued-carrier-object.md)
rules out obtaining it from the proposed torus finite part determined
by the hyperbolic Laplacian and prime adjacency operators alone.
No global Green-operator or positivity claim follows from this packet
identity; a geometric comparison requires additional arithmetic data.
