# Automorphic dyadic return of resonant states

- **Stage:** 1-in-progress; source identity checked in Lean, mass bound pending.
- **Parent:** [Arithmetic measure rigidity](resonant-state-arithmetic-measure-rigidity.md).

## Exact candidate

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

This identifies spatial data missing from the cusp Gram model. It neither selects `Re u=-1/4` nor proves Hecke recurrence or entropy. The next question concerns correlations of these explicitly localized returns under repeated correspondences.

## Quantitative survivor

On `R={|x|≤1/4, 7/4≤y≤15/8}`, precisely `h_0>1` survives; `h_±1≤1`. Thus the coordinate-to-automorphic correction `D_u` satisfies
`|D_u(z)|²=|B(u)|² h_0(z)^(1−2 Re u)/2≥|B(u)|²/2` for `Re u<0`.
Since `y≤2` and the Euclidean area is `1/16`,
`∫_R |D_u|² dμ ≥ |B(u)|²/128`.
Compared with the exact cutoff-one norm, this gives
`∫_R |D_u|² dμ ≥ (−2 Re u)/128 · ||τ_(u,1)||²`.
The bound is uniform in `Im u`. It concerns the coordinate-to-automorphic correction, not the entire residual `(T₂−λ₂)τ`; those two quantities must not be conflated. A subsequent phase-correlation estimate is needed to control cancellation with the coordinate residual.
