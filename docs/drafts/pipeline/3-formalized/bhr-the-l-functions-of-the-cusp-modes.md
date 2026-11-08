# BHR — the L-functions of the cusp modes

- **ID:** bhr-cusp-l-functions
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Hecke theory of the cusp channel (`bhr-the-hecke-eigenforms-of-the-cusp-channel.md`); the cusp modes
  had no attached L-functions.
- **Statement:** Let `g ∈ S(λ)` (a cusp form of the modular horizon) and `ν = i√(λ − ¼)`.
  1. `a_n(y) = ρ(n) √y K_ν(2π|n|y)` for all `n`, with `ρ(0) = 0`, and `|ρ(n)| ≤ C√|n|`.
  2. `Λ(s) = ∫_0^∞ g(iy) y^{s−1/2} dy/y` is entire and `Λ(1 − s) = Λ(s)`.
  3. For `Re s > 3/2`, `L(s) = Σ_{n≠0} ρ(n)|n|^{−s}` converges absolutely and
     `Λ(s) = ¼ π^{−s} Γ((s+ν)/2) Γ((s−ν)/2) L(s)`.
  4. `L(s) := 4π^s Λ(s) Γ((s+ν)/2)^{−1} Γ((s−ν)/2)^{−1}` is entire and equals the series for `Re s > 3/2`.

## Paper proof
1. *Modes.* Each mode solves the modal equation and is small at the cusp, hence a multiple of `√y K_ν(2π|n|y)`
   (corpus Whittaker uniqueness); `a_0 = 0`. Pick `X` with `Re K_ν(X) > 0`; at `y = X/(2π|n|)`,
   `|ρ(n)| √y |K_ν(X)| = |a_n(y)| ≤ sup|g|`, so `|ρ(n)| ≤ C√|n|`.
2. *Inversion.* The slice `x ↦ g(x+iy)` is `C²` and `1`-periodic with bounded second derivative, so its Fourier
   series converges at `x = 1`: `g(iy) = Σ_n a_n(y)`.
3. *Decay.* `|K_ν(x)| ≤ e^{1−x}M` for `x ≥ 1` and `|n|y ≥ |n| + y − 1` give
   `|g(iy)| ≤ (Σ_n C M e^{1+2π} √|n| e^{−2π|n|}) √y e^{−2πy}` for `y ≥ 1`.
4. *Symmetry.* `S = (0 −1; 1 0)` maps `iy` to `i/y`, so `g(i/y) = g(iy)` and `f(y) = y^{−1/2}g(iy)` has
   `f(1/y) = y f(y)`. By 3, `f = O(y^{−a})` at `∞` for all `a`, and then `f(y) = y^{−1} f(1/y) = O(y^{−b})` at
   `0⁺` for all `b`. Mellin transforms of such `f` are entire; `mellin(f ∘ inv)(s) = mellin f(−s)` and
   `mellin(t·f)(s) = mellin f(s+1)` give `Λ(1−s) = Λ(s)`.
5. *Dirichlet series.* For `Re s > 3/2`, `∫_0^∞ y^{s−1}K_ν(cy)dy = c^{−s}2^{s−2}Γ((s+ν)/2)Γ((s−ν)/2)` and
   `∫ |y^{s−1}K_ν(cy)| = c^{−σ} J(σ)`; with `|ρ(n)| ≤ C√|n|` the norms are summable (`Σ|n|^{−(σ−1/2)} < ∞`), so the
   sum and integral exchange. `(2π|n|)^{−s} 2^{s−2} = ¼ π^{−s}|n|^{−s}`. Divide by the nonvanishing gamma factor.
6. *Entire L.* `π^s`, `1/Γ` and `Λ` are entire.

## Lean certificate
`formal/GaloisForLFunctions/BlackHoleRingdown/TheLFunctionsOfTheCuspModes.lean`, wired into `BlackHoleRingdown.lean`,
checked with `lake --old env lean`, no messages. Axioms of `cusp_L_function`: `propext`, `Classical.choice`,
`Quot.sound`.

| Claim | Theorems (namespace `BlackHoleRingdown.CuspL`) |
|---|---|
| (1) | `exists_whittaker`, `exists_coeff_bound`, `one_quarter_le` |
| (2) | `hasSum_axis`, `norm_axis_le`, `axis_inv`, `profile_inv`, `profile_isBigO_atTop`, `profile_isBigO_zero`, `differentiable_completed`, `completed_one_sub` |
| (3) | `integral_norm_scaled`, `completed_eq` |
| (4) | `lFun`, `differentiable_lFun`, `cusp_L_function` |

## Scope
The statement holds for every `g ∈ S(λ)`; for odd `g` it is trivial (`g(iy) = 0`, and `ρ(−n) = −ρ(n)`). The
odd functional equation (via `∂_x g` on the axis) and the Euler product for Hecke eigenforms are not formalized.
Zeros of `L` on `Re s = ½` (GRH for the cusp modes) are open.

## Log
- 2026-11-08 — created and formalized.
