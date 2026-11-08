# BHR — the mean-square law of the cusp modes

- **ID:** bhr-cusp-mean-square-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** "Not formalized" item of `bhr-the-rankin-selberg-continuation.md` (residue at `s = 1`).
- **Statement:** Let `g ∈ S(λ)` with Whittaker coefficients `ρ(n)` (`ρ(0) = 0`), `t = √(λ − ¼)`, `‖g‖² = ∫_𝒟 |g|² dμ`. Then
  `(1/N) Σ_{0≤m<N} (|ρ(m)|² + |ρ(−m)|²) → (24/π²) cosh(πt) ‖g‖²` as `N → ∞`.

## Paper proof
1. *Regularization.* For `u ∉ {0, ±½}`,
   `(u − ½)E*(u) = A₁(u)Y^{½+u} + A₂(u)Y^{½−u} + A₃(u)T(u)` with `A₁ = (u−½)ξ(1+2u)/((1+2u)2u)`,
   `A₂ = ξ(2u)/(4u)`, `A₃ = u − ½` (since `(u−½)/(2u−1) = ½`). The `A_i` are holomorphic on `ℂ∖{0, −½}`, and at
   `u = ½` the function is `ξ(1)/2 = ¼`.
2. *Holomorphy.* For any such Eisenstein-type `Φ` with coefficients holomorphic on an open `V`, `u ↦ ∫_𝒟 |g|²Φ(u)` is
   holomorphic on `V`: on a closed ball the coefficients are bounded, `|Y^w| ≤ Y^a + 2^a`, the tail is bounded
   (C17), so `|Φ| ≤ αY^a + β` for `Y ≥ ½`; `|g|²(αY^a+β)` is bounded on `𝒟` (C17); Cauchy domination.
   Hence `F(s) = ∫_𝒟|g|²(s−1)E*(s−½)` is holomorphic on `ℂ∖{0,½}`, `F = (s−1)Λ_g` off `{0,½,1}`, `F(1) = ¼‖g‖²`.
3. *Normalization.* `φ = F/c` is holomorphic on `Re s > ½` (C17: `c` holomorphic, nonzero). For `Re s > 1`,
   `Im s ≠ 0`: `φ(s)/(s−1) = Λ_g/c = Σ_{n∈ℤ}|ρ(n)|²|n|^{−s} = Σ_m f(m)m^{−s}`, `f(m) = |ρ(m)|²+|ρ(−m)|²` (pair `±m`).
   Both sides are continuous on `Re s > 1` (the L-series converges absolutely there, C14) and `{Im s ≠ 0}` is dense,
   so equality holds on `Re s > 1`.
4. *Tauberian step.* `dslope φ 1` is continuous on `Re s > ½ ⊃ {Re s ≥ 1}` and equals `L_f(s) − φ(1)/(s−1)` on
   `Re s > 1`. `f ≥ 0`. Wiener–Ikehara (vendored `PNTPlus`) gives `(1/N)Σ_{m<N} f(m) → φ(1)`.
5. *Constant.* `ξ(2) = Λ(2) = ζ(2)Γ_ℝ(2) = π/6`; `G(1) = ¼·Γ(½)²·Γ(½+it)Γ(½−it) = ¼·π·π/cosh(πt)`
   (reflection, `sin(π(½+it)) = cosh πt`); `c(1) = (π/6)/2 · (2π)^{−1} · G(1) = π²/(96 cosh πt)`;
   `φ(1) = (¼‖g‖²)/c(1) = (24/π²) cosh(πt)‖g‖²`.

## Lean certificate
`formal/GaloisForLFunctions/BlackHoleRingdown/TheMeanSquareLawOfTheCuspModes.lean`, wired into `BlackHoleRingdown.lean`,
checked with `lake --old env lean`, no messages. Axioms of `tendsto_mean_square`, `differentiableOn_residueRS`:
`propext`, `Classical.choice`, `Quot.sound`.

| Claim | Theorems (namespace `BlackHoleRingdown.CuspMS`) |
|---|---|
| 1 | `shape`, `resA₁`, `resA₂`, `resA₃`, `shape_res_eq`, `shape_res_half` |
| 2 | `exists_shape_bound`, `continuous_shape_max`, `differentiableAt_shape`, `differentiableOn_integral_shape`, `residueRS`, `differentiableOn_residueRS`, `residueRS_eq`, `residueRS_one` |
| 3 | `rsPhi`, `differentiableAt_rsPhi`, `rsCoeff`, `summable_sq_all`, `summable_nterm`, `lSeriesSummable`, `tsum_eq_LSeries`, `rsPhi_div_eq_LSeries` |
| 5 | `xi_two_eq`, `rsFactor_one`, `msConst`, `rsPhi_one` |
| main | `tendsto_mean_square` |

## Scope
The Fourier energy of a cusp ringdown mode is equidistributed over its horocyclic harmonics: the `n`-th harmonic
carries, on average, `(12/π²) cosh(πt)‖g‖²` per sign. The constant is the `L²` energy of the mode times
`cosh(πt) = π/|Γ(½+it)|²`. The rate of convergence is not formalized; it is controlled by the zero-free region of
`ζ(2s)` (poles of `Λ_g/c` at `ρ/2`); a power-saving error term needs growth bounds of `Λ_g` in vertical strips.

## Log
- 2026-11-08 — created and formalized.
