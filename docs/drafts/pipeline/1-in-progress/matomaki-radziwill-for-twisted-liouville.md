# Matomäki–Radziwiłł for `λχ`

**Goal.** For a Dirichlet character `χ` (fixed modulus `q`) and `f = λχ`: for every `ε > 0` there is
`h₀` such that for `h ≥ h₀` and all large `X`,

`(1/X) Σ_{X<n≤2X} |Σ_{n<m≤n+h} f(m)|² ≤ ε h²`.

Consumer: A21 (`logarithmic-two-point-chowla.md` §7): `V(b/s, T) → 0` as `T → ∞`.

Folder: `formal/GaloisForLFunctions/MatomakiRadziwill/` (top level, umbrella `MatomakiRadziwill.lean`).

## Architecture

| Phase | Content | Status |
|---|---|---|
| V | Vinogradov–Korobov zero-free region for `L(s,χ)` | **Lean** (`LFunction_ne_zero_vinogradovKorobov`) |
| RT | Route T for `χ`: `Σ_{p∈B} χ(p)p^{-it}` small for high blocks `B`, `\|t\| ≤ X` | open |
| D | low frequencies: `sup_{\|t\|≤T₀} \|Σ_{n≤x} λχ(n)n^{-it}\| = o(x)` | open |
| L | the ladder: Ramaré, mean value, large values, Halász–Montgomery, rough class | open |
| P | Parseval: additive short windows from the Dirichlet-polynomial mean square | open |
| A | assembly for `λχ`; transfer to `V(b/s,T)` | open |

### V. Zero-free region for `L(s,χ)`

`L(s,χ) = q^{-s} Σ_{a=1}^{q} χ(a) ζ(s, a/q)`; blocks `Σ_{Y<n≤2Y, n≡a} n^{-s} = q^{-s} Σ_m (m+α)^{-s}`,
`α = a/q`.

1. **Shifted Vinogradov.** The corpus estimate (`Sieve.norm_sum_logPhase_le_vinogradov`) passes
   through the shift average `Q² |Σ n^{it}| ≤ Σ_x |R(t,x,Q)| + 8Q⁴`
   (`Sieve.sq_mul_norm_sum_logPhase_le`) with `R(t,x,Q)` evaluated at the *real* point `x`. For
   `(m+α)^{it}` the same shift gives `R(t, m+α, Q)`; everything downstream is unchanged. Result:
   `|Σ_{A<m≤A+L} (m+α)^{it}| ≤ C L N^{-δ_R/4} + 200 N^{1/2}` on `[N, 2N]`.
2. **Growth.** `|L(σ+iτ,χ)| ≤ C_q log τ` for `σ ≥ 1 − θ(log τ)` (as `Sieve.norm_riemannZeta_le_vinogradovKorobov`):
   truncation of the `L`-series, blocks by 1. (middle) and the derivative test (large).
3. **Zero-free.** `3 + 4cos + cos 2` for `L(σ,χ₀)³ L(σ+iτ,χ)⁴ L(σ+2iτ,χ²)` with the growth bound
   (Landau's lemma, as `Sieve.riemannZeta_ne_zero_vinogradovKorobov`):
   `L(β+iγ, χ) ≠ 0` for `β > 1 − c (log γ)^{-2/3}(log log γ)^{-5/3}`, `γ ≥ γ₀(q)`.

### RT. Route T for `χ`

`χ ≠ 1`, `|τ| ≤ 2X`, `x ∈ [y, 2y]`, `log y ≥ (log X)^{0.9}`. With `c_n = χ(n)Λ(n)n^{-iτ}`, truncated
Perron at `σ₀ = 1 + 1/log x`, height `T₁ = (log X)^{A+3}` (`Sieve.norm_tsum_lt_sub_perron_integral_le`):
`Σ_{n<x} c_n = (1/2π)∫_{−T₁}^{T₁} F(σ₀+it) x^{σ₀+it}/(σ₀+it) dt + O(x log²x / T₁)`,
`F(s) = −L'/L(s+iτ, χ)`. `F` is analytic on `[1 − w/2, σ₀] × [−T₁, T₁]` (`w = ε(2X)`: no zeros there by
`exists_LFunction_ne_zero_vinogradovKorobov_width` at heights `τ ± T₁`, and for low heights the fixed
zero-free neighbourhood of `Re s = 1`); the rectangle theorem moves the segment to `Re s = 1 − w/2`,
where `|F| ≤ B = C(log X)^{5/3}` (Landau's lemma with the growth bound and the zero-free disc). Then
`|Σ_{n<x} c_n| ≤ x^{1−w/2} B log T₁ + x·B/T₁·(1/...) + O(x log² x/T₁)`, and `x^{−w/2} ≤ exp(−(log X)^{0.2})`.
Differences `x = y, y'` give the blocks; partial summation against `1/(n log n)` gives `Σ_{p∈B} χ(p)p^{-1-iτ}`.

### L. Ladder (outline)

Scales `[P_j, Q_j]`, `j ≤ J`; `S` = integers with a prime factor in every scale (rough class by
Turán–Kubilius, harmonic masses growing geometrically). Ramaré at scale `j` writes
`A_S ≈ Σ_v Q_v R_v` (blocks `e^{v/H} ≤ p < e^{(v+1)/H}`). Frequencies where all `Q^{(1)}_v` are
`≤ e^{−α₁v/H}`: mean value theorem. Next scales: moment trick against the previous scale's large
`Q`. The exceptional set (large at every scale) has measure `≤ X^{1/2−ε}`; there
Halász–Montgomery for `R` (diagonal) times RT for the high-range `Q`.

## Lean

| Module | Content | Status |
|---|---|---|
| `ShiftedVinogradov` | `R(t,y,Q)` at real `y`; shift average for `(n+α)^{it}`; Vinogradov on dyadic blocks | compiled |
| `ShiftedPhaseBlocks` | `k`-th derivative test from the start point `N+α`; weighted blocks; saving at the classical scale | compiled |
| `HurwitzGrowth` | middle/large Hurwitz blocks; `‖Σ_{k≤K}(k+α)^{-σ-iτ}‖ ≤ C log τ`, `K ≤ 2τ²` | compiled |
| `LFunctionGrowth` | residues of `[1,qT]`; `‖L(σ+iτ,χ)‖ ≤ (q³+56q+qC) log τ` | compiled |
| `LFunctionThreeFourOne` | 3-4-1 for `−L'/L`; pole via `−ζ'/ζ`; `1/(1+1/δ) ≤ ‖L(1+δ+iy,ψ)‖ ≤ 1+1/δ` | compiled |
| `LFunctionDLVP` | `4/(1+δ−β) ≤ 3/δ + 3A + (80/R)(log Φ + log(1+1/δ))` | compiled |
| `LFunctionZeroFree` | disc growth for every `ψ` mod `q`; zero-free region, width `ε(γ)` | compiled |

## Log
- 2026-11-12 — created; architecture after surveying the corpus μ-ladder (`Sieve.MoebiusHeadWindowAllLengths`, Route T via ζ).
