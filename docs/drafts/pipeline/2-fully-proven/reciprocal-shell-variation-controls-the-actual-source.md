# Reciprocal-shell variation controls the actual source

- **ID:** reciprocal-shell-variation
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean pending)
- **Statement:** The affine shell error has a bound `C_q c/(log Y)^k` whenever `X≥2cY`, with the existing fixed-conductor source threshold. Consequently its unnormalized harmonic square budget is `O_q(c²(1+log c))`.

## Paper proof

For `0<a≤1`, put `W_a(u)=G(a/u)` with its smooth zero extension. Its derivative vanishes on `[0,a/2]`. If `L` is a Lipschitz constant of `G`, then on `[a/2,1]`, `|W_a′(u)|≤La/u²`. Integration gives `∫_0^1|W_a′(u)|du≤L(2-a)≤2L`, independently of `a`. Also `|W_a(1)|≤M=∫φ²`.

The exact Abel identity is `W_a(1)e_F(X)-∫_0^1 W_a′(u)e_F(Xu)du`. The existing residue-Mertens estimate bounds `|e_F(Z)|` by `2Σ_r|F(r)|/(log Y)^k` for `Z≥Y`. With `a=h/c`, the condition `X≥2cY` ensures this bound throughout the derivative support. Therefore each shell error is at most `2(M+2L)qφ(q)/(log Y)^k`. There are at most `2c` shells; exact normalization `2/M` gives the claimed linear source rate.

Combine this rate at `k=2` with the linear global source bound from active-shell counting. For `X=N/n≥T=2cY₀ exp(1)`, let `t=log(X/T)≥0`. Then `log(X/(2c))≥1+t`, so the row error is at most `C_q c/((1+t)√n)`. The established harmonic envelope lemma sums its square with constant cost. The remaining quotient region has harmonic mass at most `1+log(2T)=O_q(1+log c)` and global row bound `D_q c/√n`. This proves the stated square budget.

## Remaining scope

The conductor-dependent residue-Mertens threshold remains. This improvement concerns the actual source, including all shifts and prime powers; it supplies no negative-eigenvector confinement by itself.
