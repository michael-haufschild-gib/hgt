# The cofinal Möbius slope is the limiting period variance

- **ID:** BVI-SLOPE-PERIOD-2026-10-24
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) → Lean
- **Source:** BVI README §7.7 (open: does `κ` equal the limit of the period variance?);
  THIM `MoebiusResponseWhiteNoiseLaw` (only `liminf Var_N(μ) ≥ 1/288` known)
- **Statement:** `C(N) = Σ_{d,e≤N} μ(d)μ(e)/[d,e] → κ = ρ Σ_{j≥1} S(j) log(1+1/j)`, the slope of
  the cofinal profile (`cofinalMobiusSlope`); hence `Var_N(μ) → κ` and `κ ≥ 1/288`.

## Goal
The cofinal profile measures the Möbius energy density on linear horizons `M = O(N)`; the period
variance measures it on complete periods `M ≫ N²`. The generic window laws transfer only beyond
`N²`. The theorem says the two densities coincide in the limit: for the literal Möbius source the
energy density is already the period variance at linear scale, and the white-noise variance has an
exact limit.

## Paper proof
1. Gcd reindex (`sum_gcd_reindex`): `d = gb`, `e = ga`, `(a,b) = 1`, `μ(ga)μ(gb) = μ(g)²μ(a)μ(b)[(g,ab)=1]`:
   `C(N) = Σ_{g≤N} μ(g)²/g · S'_g(⌊N/g⌋)`, `S'_g(X) = Σ_{a,b≤X, (a,b)=1, (ab,g)=1} μ(a)μ(b)/(ab)`.
2. Fibres `j = ⌊N/g⌋`: the fibre sum is `Σ_{a,b≤j} μ(a)μ(b)/(ab) · W_{ab}(N,j)` with
   `W_m(N,j) = Σ_{g ∈ fibre} μ(g)²[(g,m)=1]/g`. By `μ²[(·,m)=1] = Σ_{d²e | ·} μ(d)μ(e)` (`e | m`),
   `W_m(N,j) = Σ_{d, e|m} μ(d)μ(e)/L · A_j(⌊N/L⌋)`, `L = [d², e]`, `A_j` the harmonic fibre mass.
3. `|A_j(n) − log(1+1/j)| ≪ (j+1)/n` (Euler–Mascheroni monotone bounds) gives
   `|W_m(N,j) − D(m) A_j(N)| ≪ τ(m)(j+1)/√N`, `D(m)` the coprime-squarefree density.
4. Main term: `Σ_{a,b} μμ D(ab)/(ab) = ρ S(j)`, so the head `j ≤ N^{1/6}` tends to
   `ρ Σ_j S(j) log(1+1/j) = κ` (dominated by `3ρ|S(j)|/j`), with error `≪ N^{1/3} log⁴N/√N`.
5. Tail `g < N^{5/6}`: `|S'_g(X)| ≪ Π(g)²/(1+log X)⁴` with `Π(g) = ∏_{p|g}(1−p^{-3/4})^{-1}`
   (kernel `1_{g-smooth}/k`, Rankin mass `Π(g)`), and `Σ_{g≤N} μ(g)²Π(g)²/g ≪ log N`; so the tail is
   `≪ log N / log⁴ N`.

Numerics (exploratory): `C(10^5) = 0.44074`, `κ ≈ 0.4407`.

## Gates
- [x] 0 → 1  well-posed, attack
- [ ] 1 → 2  paper proof closed
- [ ] 2 → 3  Lean, audit

## Log
- 2026-10-24 — created in 1-in-progress
