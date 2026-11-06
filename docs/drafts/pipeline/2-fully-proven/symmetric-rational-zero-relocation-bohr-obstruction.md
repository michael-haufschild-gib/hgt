# Symmetric Rational Zero-Relocation Preserves the Functional Equation but Destroys Vertical Bohr Almost Periodicity

- **ID:** symmetric-rational-zero-relocation-bohr-obstruction
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** docs/drafts/pipeline/1-in-progress/pnt-error-single-finite-oscillation.md
- **Statement:** Multiplying a continuous Bohr almost-periodic function `F` by a continuous asymptotically unitary factor `m` (`m(t) → 1` as `t → +∞`) preserves Bohr almost periodicity if and only if `F(t)(m(t) - 1) = 0` identically; consequently, multiplying `ζ(s)` by the `s ↔ 1 - s` symmetric rational zero-relocation factor `R(s)` preserves the exact Riemann functional equation while strictly destroying vertical Bohr almost periodicity (and every absolutely convergent ordinary Dirichlet series representation) on every vertical line `Re s = σ > 1`.

## Goal
Establish a sharp firewall theorem separating the exact Riemann functional equation plus asymptotic `1 + O(|t|^{-1})` vertical regularity from the Euler/Dirichlet almost-periodic structure of `ζ(s)` on `Re s > 1`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven: complete paper proof below, no open dependency
- [ ] 2 → 3  formalized: `GaloisForLFunctions.ArithmeticPositiveDuality.SymmetricRationalZeroRelocationBohrObstruction`

## Proof
1. **Asymptotically unitary multiplier rigidity for Bohr almost-periodic functions.** Let `F, m : ℝ → ℂ` be continuous with `F` Bohr almost periodic and `m(t) → 1` as `t → +∞`. By `exists_bound_of_isBohrAlmostPeriodic`, `‖F(t)‖ ≤ C` globally, so `H(t) := F(t) m(t) - F(t) = F(t)(m(t) - 1) → 0` as `t → +∞`. If `F · m` is Bohr almost periodic, `H` is Bohr almost periodic (`isBohrAlmostPeriodic_sub`), so Bohr's vanishing lemma (`eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero`) forces `H(t) = 0` for all `t ∈ ℝ`. The converse is immediate since `F · m = F`.
2. **Vertical Bohr almost periodicity of `ζ` on `Re s > 1` and ordinary Dirichlet-series obstruction.** For every `σ > 1`, `ζ(σ + it) = LSeries 1 (σ + it)` (`LSeries_one_eq_riemannZeta`) with `LSeriesSummable 1 σ`, so `t ↦ ζ(σ + it)` is continuous, nowhere zero (`riemannZeta_ne_zero_of_one_lt_re`), and Bohr almost periodic (`isBohrAlmostPeriodic_LSeries_vertical`). By Step 1, for any continuous multiplier `M(σ + it) → 1` not identically `1` on `Re s = σ`, `t ↦ ζ(σ + it) M(σ + it)` is not Bohr almost periodic, hence cannot equal `LSeries a (σ + it)` for any `a : ℕ → ℂ` with `LSeriesSummable a σ`.
3. **Symmetric rational zero-relocation factor `R(s)`.** For `ρ₀ ∈ ℂ` (`1/2 < Re ρ₀ < 1`, `Im ρ₀ ≠ 0`) and `γ₁, γ₂ ∈ ℝ`, set
   `R(s) = ((s - ρ₀)(s - conj ρ₀)(s - (1 - ρ₀))(s - (1 - conj ρ₀))) / ((s - (1/2 + iγ₁))(s - (1/2 - iγ₁))(s - (1/2 + iγ₂))(s - (1/2 - iγ₂)))`.
   Direct algebraic verification gives `R(1 - s) = R(s)` (preserving `Ξ_model(1 - s) = Ξ_model(s)` for `Ξ_model = completedRiemannZeta · R`), `R(conj s) = conj(R(s))`, `(R(1/2 + it)).im = 0`, nonvanishing denominator and exact zero set `{ρ₀, conj ρ₀}` on `Re s > 1/2`, vanishing at `2 s_* - 1` for `s_* = (1 + ρ₀)/2 ∈ {3/4 < Re s < 1}`, and `R(σ + it) → 1` as `t → +∞` (dividing numerator and denominator by `(σ + it)^4`). If `R(σ + it) = 1` for all `t ∈ ℝ` (`σ > 1`), the entire polynomial `Num(z) - Den(z)` vanishes along `(σ + i/(n+1)) → σ`, hence identically on `ℂ` by analytic continuation, contradicting `Num(ρ₀) = 0 ≠ Den(ρ₀)`. Applying Step 2 refutes vertical Bohr almost periodicity and summable `LSeries` representations on every line `Re s = σ > 1`.
