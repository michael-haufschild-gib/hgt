# Automorphic dyadic return of resonant states

- **Stage:** 3-formalized.
- **Type:** THEOREM / OBSTRUCTION.
- **Parent:** [Arithmetic measure rigidity](../1-in-progress/resonant-state-arithmetic-measure-rigidity.md).

## Exact source identity

Throughout, `−1/2<Re u` and `Im u>0`; norm bounds also assume `A(u)=0` and `Re u<0`.

For `z=x+iy∈fd`, put `h_k(z)=2y/((x+k)²+y²)` and let `C_u(y)` denote the full Eisenstein constant term. Define the global truncation by

`Λ^Y_aut E_u(z)=E_u(z)−½ Σ_(c,d primitive) 1_(Im γ_(c,d)z>Y) C_u(Im γ_(c,d)z)`.

For `Y≥1` it agrees with coordinate truncation on `fd` and is modular invariant. The dyadic correspondence satisfies

`T₂ Λ¹_aut E_u(z) = T₂_coordinate τ_(u,1)(z) − 2^(-1/2) Σ_(k=-1,0,1) 1_(h_k(z)>1) C_u(h_k(z))`.

At a resonance `A(u)=0`, replace `C_u(h)` by `B(u)h^(1/2-u)`. The three return regions are exactly `(x+k)²+(y−1)²<1`.

## Paper argument

On `fd`, `|x|≤1/2` and `x²+y²≥1`, hence `y>1/2`. At the downward branch `(z+b)/2`, a primitive row `(c,d)` has height

`2y/((cy)²+(cx+cb+2d)²)`.

If this exceeds one and `c≠0`, then `|c|≥2` is impossible: `4y²>2y`. Thus `c=±1`. Writing `k=cb+2d`, the return inequality and `(y−1)²≥0` imply `|cx+k|<1`, hence `|k|<3/2`; integrality gives `k∈{-1,0,1}`. For `b=0`, the rows are `±(1,0)`. For `b=1`, they are `±(1,0)` and `±(1,−1)`. Rows with `c=0` are `±(0,1)` and give the original coordinate subtraction. On `2z`, every nonzero first entry has height at most one. Each signed pair contributes twice, canceled by the factor `½`.

Right multiplication by a modular matrix permutes primitive rows and preserves their lifted heights after reindexing. This proves invariance of the global subtraction. Its finite support on every orbit follows from the fundamental-domain horoball bound.

## Boundary

Cutoff-one normalized truncations do not become `L²` Hecke quasimodes when the real parameter stays uniformly below zero. The obstruction persists at `Re u=-1/4`; it does not select that rate or rule out recurrence of other limiting objects. The positive survivor is the exact localized source and its quantitative mass, not merely failure of an eigenstate approximation.

## Quantitative survivor

On `R={|x|≤1/4, 7/4≤y≤15/8}`, precisely `h_0>1` survives; `h_±1≤1`. Thus the coordinate-to-automorphic correction `D_u` satisfies
`|D_u(z)|²=|B(u)|² h_0(z)^(1−2 Re u)/2≥|B(u)|²/2` for `Re u<0`.
Since `y≤2` and the Euclidean area is `1/16`,
`∫_R |D_u|² dμ ≥ |B(u)|²/128`.
Compared with the exact cutoff-one norm, this gives
`∫_R |D_u|² dμ ≥ (−2 Re u)/128 · ||τ_(u,1)||²`.
The bound is uniform in `Im u`. The full residual `(T₂−λ₂)τ` requires the separate comparison below.

## Full residual: noncancellation

No oscillatory estimate is needed on this rectangle. Put `r=x²+y²`, `s=1/2−u`. Here `3≤r≤4` and `1<y<2`. The coordinate residual is `B(u)2^u y^s`, while the return correction is `B(u)h_0^s/√2`. The coordinate term equals the return term multiplied by

`2^(2u) r^(1/2−u) = (r/2)(4/r)^(u+1/2)`.

For `−1/2<Re u<0`, its modulus is at least `r/2≥3/2`. The reverse triangle inequality therefore gives
`|(T₂−λ₂)Λ¹_aut E_u|² ≥ |D_u|²/4 ≥ |B(u)|²/8` on `R`.
Hence the full residual satisfies the uniform core bound
`∫_R |(T₂−λ₂)Λ¹_aut E_u|² dμ ≥ (−2 Re u)/512 · ||τ_(u,1)||²`.
All statements hold at every frequency, without a semiclassical limit or an assumed analytic estimate.

## Lean certificates

Modules under `RenormalizedIntersectionTheory/ResonantStates/`:

- `AutomorphicHeckeReturn.lean`: modular invariance, agreement on `fd`, `resonant_automorphic_dyadic_correction`.
- `CoreReturnMass.lean`: pointwise and integral correction bounds, `dyadicReturnDefect_relative_mass_lower`.
- `CoreHeckeResidual.lean`: `dyadicEigenResidual_factor`, `dyadicEigenResidual_norm_sq_lower`, `dyadicEigenResidual_core_mass_lower`, `dyadicEigenResidual_relative_mass_lower`.

Lean checks passed. Transitive axioms are only `propext`, `Classical.choice`, `Quot.sound`.
