import GaloisForLFunctions.BezoutValuationIncidence.BlockEquidistributionSufficesForCrossScaleDispersion

/-!
# The short-window mean square carries the cross-scale loss

For a weighted large-scale row `x(n) = c'(n)/n²` with generating polynomial `X(z) = Σ_n x(n) zⁿ`, let
`x̄ = x ⋆ 𝟙_{[0,H)}/H` be its average over windows of length `H`. Then exactly

`X̄(z) = B_H(z) X(z)`,  `B_H(z) = (1/H) Σ_{i<H} zⁱ`,

with `B_H(1) = 1`, `|B_H| ≤ 1` and `|1 - B_H(ζ)| ≤ H |ζ - 1|` on the unit circle. In the Fourier form
`Σ_n x(n) Φ_p(kn) = Σ_{η ∈ T_p} |η - 1|^{-2} X(η^k)` the averaged part `x̄` takes the full weight
`Σ_η |η - 1|^{-4} ≤ p⁴/64`, while the difference `x - x̄` has multiplier `1 - B_H(η^k)`, so its weight is
`Σ_η |η - 1|^{-4} min(2, Hk|η - 1|)² ≤ 2Hk Σ_η |η - 1|^{-3} ≤ Hk p³/8`; the classes `p ∣ k` cancel
because `x̄` and `x` have the same mass. Powering by `k` permutes the nontrivial `p`-th roots for
`p ∤ k`, so for every prime `p`

`|Σ_n x(n) 𝔅(p, n)| ≤ (π²/48) p² ‖X̄‖_p + |Σ_n x(n)|/6 + √(2Hp³) ‖X‖_p`,

`‖X‖_p² = Σ_{ζ ∈ T_p} |X(ζ)|²`. The log-free large sieve over the primes of the small scale gives, for
`c` on primes `≤ Q₀` and `c'` on `[A+1, A+L]`,

`|B + m R' + β H'| ≤ (π²/48) √(Σ c(p)² p²) √(L + H + 2Q₀²) ‖x̄‖₂
  + √(2H) √(Σ c(p)² p) √(L + 2Q₀²) ‖x‖₂ + |Σ_n x(n)| Σ_p |c(p)|/(6p) + ¾ Σ |c| p² Σ |c'|/n³`.

Against the large-sieve bound `½ √(Σ c(p)² p²) √(L + 2Q₀²) ‖x‖₂`, which coherent large-scale rows
attain, the loss splits into the normalized short-window mean square `‖x̄‖₂/‖x‖₂` and the factor
`√(H/P)` for `c` on `(P, 2P]`. A large-scale row that cancels in almost all windows of a length
`H = o(P)` therefore beats the Type-II barrier at every cross-scale exponent.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The short-window average and its multiplier -/

/-- The average of a row over the window of length `H` ending at `n`. -/
def shortWindowAverage (H : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ i ∈ range H, x (n - i)) / H

/-- The generating polynomial `X(z) = Σ_{1 ≤ n ≤ N} x(n) zⁿ` of a row. -/
def rowPoly (N : ℕ) (x : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, (x n : ℂ) * z ^ n

/-- The box multiplier `B_H(z) = (1/H) Σ_{i < H} zⁱ`. -/
def boxMultiplier (H : ℕ) (z : ℂ) : ℂ :=
  (∑ i ∈ range H, z ^ i) / H

theorem rowPoly_sub (N : ℕ) (x y : ℕ → ℝ) (z : ℂ) :
    rowPoly N (fun n => x n - y n) z = rowPoly N x z - rowPoly N y z := by
  simp only [rowPoly, ← sum_sub_distrib]
  refine sum_congr rfl fun n _ => ?_
  push_cast
  ring

/-- A shift of the row by `i` multiplies its polynomial by `zⁱ`. -/
theorem sum_Icc_sub_mul_pow {N i : ℕ} {x : ℕ → ℝ} (hx0 : x 0 = 0)
    (hsupp : ∀ n, x n ≠ 0 → n + i ≤ N) (z : ℂ) :
    ∑ n ∈ Icc 1 N, (x (n - i) : ℂ) * z ^ n = z ^ i * rowPoly N x z := by
  rw [rowPoly, mul_sum]
  symm
  refine sum_bij_ne_zero (fun m _ _ => m + i) (fun m hm h => ?_) (fun _ _ _ _ _ _ h => by omega)
    (fun n hn h => ?_) (fun m _ _ => ?_)
  · have hx : x m ≠ 0 := fun h0 => h (by rw [h0]; simp)
    have := hsupp m hx
    exact mem_Icc.mpr ⟨by have := (mem_Icc.mp hm).1; omega, this⟩
  · have hx : x (n - i) ≠ 0 := fun h0 => h (by rw [h0]; simp)
    have hni : n - i ≠ 0 := fun h0 => hx (by rw [h0, hx0])
    have hn' := mem_Icc.mp hn
    refine ⟨n - i, mem_Icc.mpr ⟨by omega, by omega⟩, ?_, by omega⟩
    rw [show n - i + i = n by omega] at *
    intro h0
    apply h
    rw [← h0, show n - i + i = n by omega]
    ring
  · rw [Nat.add_sub_cancel]
    ring

/-- The averaged row has polynomial `B_H(z) X(z)`. -/
theorem rowPoly_shortWindowAverage {N H : ℕ} {x : ℕ → ℝ} (hx0 : x 0 = 0)
    (hsupp : ∀ n, x n ≠ 0 → n + H ≤ N + 1) (z : ℂ) :
    rowPoly N (shortWindowAverage H x) z = boxMultiplier H z * rowPoly N x z := by
  have hi : ∀ i ∈ range H, ∑ n ∈ Icc 1 N, (x (n - i) : ℂ) * z ^ n = z ^ i * rowPoly N x z :=
    fun i hi => sum_Icc_sub_mul_pow hx0 (fun n hn => by
      have := hsupp n hn; have := mem_range.mp hi; omega) z
  simp only [rowPoly, shortWindowAverage, boxMultiplier]
  push_cast
  rw [div_mul_eq_mul_div, sum_mul, sum_div]
  rw [← sum_congr rfl fun i hi' => by rw [rowPoly] at hi; exact hi i hi']
  rw [sum_comm]
  refine sum_congr rfl fun n _ => ?_
  rw [div_mul_eq_mul_div, sum_mul, sum_div]

theorem boxMultiplier_one {H : ℕ} (hH : 1 ≤ H) : boxMultiplier H 1 = 1 := by
  have : (H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp [boxMultiplier, this]

theorem norm_boxMultiplier_le {H : ℕ} (hH : 1 ≤ H) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖boxMultiplier H ζ‖ ≤ 1 := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  rw [boxMultiplier, norm_div, Complex.norm_natCast, div_le_one hHR]
  calc ‖∑ i ∈ range H, ζ ^ i‖ ≤ ∑ i ∈ range H, ‖ζ ^ i‖ := norm_sum_le _ _
    _ = H := by simp [norm_pow, hζ]

/-- `|1 - B_H(ζ)| ≤ H |ζ - 1|` on the unit circle. -/
theorem norm_one_sub_boxMultiplier_le {H : ℕ} (hH : 1 ≤ H) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖1 - boxMultiplier H ζ‖ ≤ H * ‖ζ - 1‖ := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hHC : (H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have he : 1 - boxMultiplier H ζ = (∑ i ∈ range H, (1 - ζ ^ i)) / H := by
    rw [boxMultiplier, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
    field_simp
  rw [he, norm_div, Complex.norm_natCast, div_le_iff₀ hHR]
  calc ‖∑ i ∈ range H, (1 - ζ ^ i)‖ ≤ ∑ i ∈ range H, ‖1 - ζ ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ range H, (H : ℝ) * ‖ζ - 1‖ := by
        refine sum_le_sum fun i hi => ?_
        rw [norm_sub_rev]
        refine (norm_pow_sub_one_le hζ i).trans ?_
        have : (i : ℝ) ≤ H := by exact_mod_cast (mem_range.mp hi).le
        exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = H * ‖ζ - 1‖ * H := by rw [sum_const, card_range, nsmul_eq_mul]; ring

end

end GaloisForLFunctions.BezoutValuationIncidence
