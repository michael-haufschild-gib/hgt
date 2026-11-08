# BHR — the Weyl upper bound for the cusp spectrum

- **ID:** bhr-weyl-upper
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** "open: Weyl law" of the BlackHoleRingdown programme; upper half of A26 in
  `bhr-a-weyl-lower-bound-for-the-cusp-spectrum.md`.
- **Statement:** Let `N(Λ)` count the cusp forms of `PSL₂(ℤ)\ℍ` with eigenvalue `≤ Λ`, with multiplicity.
  1. There is `C` with `N(Λ) ≤ C(Λ + 1)` for all `Λ ≥ 0`.
  2. There are `c, C > 0`, `Λ₀` with `cΛ ≤ N(Λ) ≤ CΛ` for `Λ ≥ Λ₀`.
  3. `Σ_j e^{-tλ_j} < ∞` for every `t > 0`.

## Paper proof
1. *Bessel.* Let `φ ≥ 0` be a profile of radius `R`, mass `∫_ℍ φ(u(i,w))dμ = 1`, `φ ≤ M`. Selberg gives
   `L_φ U_j = κ_j U_j`, and on the one-point deck `(L_φ U)(z) = ∫_𝒟 K_z U` with `K_z(z') = ½Σ_B φ(u(z,Bz'))`.
   Bessel for the orthonormal `(U_j)` gives `Σ_j |κ_j|²|U_j(z)|² ≤ ∫_𝒟 K_z²`. If at most `m` matrices have
   `u(z,Bz') ≤ R` (for each `z'`), Cauchy–Schwarz gives `K_z² ≤ (m/4) Σ_B φ² ≤ (mM/4) Σ_B φ`, and the tiling
   `Σ_B ∫_𝒟 φ(u(z,Bz')) = 2` gives `∫_𝒟 K_z² ≤ mM/2`.
2. *Count.* For `z, z' ∈ 𝒟`: if `c = 0`, `B = ±(1 b; 0 1)` and `|x − x' − ab| ≤ √(4R(4R+2)) y`, so at most
   `2(8√R y + 1)` such `B`. If `c ≠ 0`, `Im Bz' ≤ 1/y' ≤ 2` and `y ≤ (4R+2) Im Bz' ≤ 6`, and the corpus entry bound
   gives `|entries| ≤ 1304`. So `m ≤ 16√R y + 2609⁴ + 2`.
3. *Cusp.* A mode `a_n` (`n ≠ 0`) solves `a'' = (4π²n² − λ/y²)a`, `a → 0`; for `λ ≤ 4π²Y₁²`, `|a|²` is convex and
   nonincreasing on `[Y₁, ∞)`, so `(Y − Y₁)∫_Y^∞ |a|²/y² ≤ Y₁∫_{Y₁}^Y |a|²/y²`, i.e. `Y∫_Y^∞ ≤ Y₁∫_{Y₁}^∞`.
   Parseval on horocycles and dominated convergence sum this over `n`:
   `Y ∫_{𝒟, y>Y} |g|² ≤ Y₁ ∫_{𝒟, y>Y₁} |g|²`.
4. *Assembly.* `R = 1/(512(Λ+1))`, `φ = β(u/R)/mass`, so `M ≤ 8/(πR)` and `|κ_j − 1| ≤ ½` for `λ_j ≤ Λ`.
   `Y₁ = max(1, √Λ/2π)`, `Y = 5Y₁`, `√R Y ≤ 1`. On `A = 𝒟 ∩ {y ≤ Y}`: `Σ_j |U_j|² ≤ 2(16 + 2609⁴ + 2)M`.
   Each `U_j` has `∫_A |U_j|² ≥ 4/5`. Integrate: `(4/5)N(Λ) ≤ 2(18 + 2609⁴)M π/3 = O(Λ+1)`.
5. *Heat trace.* Group `λ_j` by `⌊λ_j⌋ = k`: at most `N(k+1) ≤ C(k+2)` terms, each `≤ e^{-tk}`.

## Lean certificate
`formal/GaloisForLFunctions/BlackHoleRingdown/TheWeylUpperBound.lean`, wired into `BlackHoleRingdown.lean`, checked
with `lake --old env lean`, no messages. Axioms of `cuspCount_le`, `weyl_law_order`, `summable_exp_neg_mul`:
`propext`, `Classical.choice`, `Quot.sound`.

| Claim | Theorems (namespace `BlackHoleRingdown.WeylUpper`) |
|---|---|
| Bessel | `kerFn`, `ppApply_one`, `basis_eq`, `orthonormal_basis`, `sum_sq_le` |
| Count | `im_le_six`, `abs_entry_le`, `translation_data`, `card_near_le` |
| Cusp | `hasSum_slice`, `integrableOn_slice`, `antitone_mode`, `mode_tail_le`, `hasSum_tail`, `tail_le` |
| (1) | `cuspCount_le` |
| (2) | `weyl_law_order` |
| (3) | `summable_exp_neg_mul` |

## Scope
`N(Λ) ≍ Λ`: the undamped tones of the modular horizon have the density of a compact surface, and the heat
semigroup on the cusp channel is trace class. The sharp constant `N(Λ) ~ Λ/12` (Selberg) is not proved; it needs
the trace formula with the scattering determinant. `tail_le` holds for every cusp form, so the cusp above
`5 max(1, √λ/2π)` carries at most a fifth of its mass at every eigenvalue.

## Log
- 2026-11-08 — created and formalized.
