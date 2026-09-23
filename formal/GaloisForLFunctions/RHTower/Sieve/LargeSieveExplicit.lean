import GaloisForLFunctions.RHTower.Sieve.LargeSieveSeparated
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# The large sieve constant in closed form

`LargeSieveSeparated.lean` computes the admissible `Δ` from a separation hypothesis, but leaves it
as a partial harmonic sum with a free cut `M ≥ (2δ)^{-1}`.  Bounding that sum logarithmically and
choosing `M = ⌈(2δ)^{-1}⌉` removes both:

`∑_r |⟪e(λ_r), a⟫|² ≤ (N + δ^{-1}(1 + log((2δ)^{-1} + 1))) ‖a‖²`

for any family `δ`-separated in `ℝ/ℤ`, with no free parameter and no hypothesis beyond the
separation.  This is the weak large sieve in closed form: `Δ = N + O(δ^{-1} log δ^{-1})`.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- **Large sieve with a logarithmic constant.** -/
theorem largeSieve_separated_log {ι : Type*} [DecidableEq ι] (N : ℕ) (s : Finset ι) (lam : ι → ℝ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → δ ≤ toIntDist (lam b - lam a))
    {M : ℕ} (hM : 1 / (2 * δ) ≤ (M : ℝ))
    (a : EuclideanSpace ℂ (Fin N)) :
    ∑ r ∈ s, ‖⟪expRow N (circleFreq (lam r)), a⟫_ℂ‖ ^ (2 : ℕ)
      ≤ ((N : ℝ) + (1 / δ) * (1 + Real.log M)) * ‖a‖ ^ (2 : ℕ) := by
  have hbase := largeSieve_separated N s lam hδ0 hδ hsep hM a
  have hlog := sum_Icc_one_div_le_one_add_log M
  have hδinv : (0 : ℝ) ≤ 1 / δ := by positivity
  have hstep : (N : ℝ) + (1 / δ) * ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ)
      ≤ (N : ℝ) + (1 / δ) * (1 + Real.log M) := by
    have := mul_le_mul_of_nonneg_left hlog hδinv
    linarith
  exact le_trans hbase (mul_le_mul_of_nonneg_right hstep (sq_nonneg _))

/-- **Large sieve in closed form.**  The constant is explicit in the separation alone. -/
theorem largeSieve_separated_explicit {ι : Type*} [DecidableEq ι] (N : ℕ) (s : Finset ι)
    (lam : ι → ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → δ ≤ toIntDist (lam b - lam a))
    (a : EuclideanSpace ℂ (Fin N)) :
    ∑ r ∈ s, ‖⟪expRow N (circleFreq (lam r)), a⟫_ℂ‖ ^ (2 : ℕ)
      ≤ ((N : ℝ) + (1 / δ) * (1 + Real.log (1 / (2 * δ) + 1))) * ‖a‖ ^ (2 : ℕ) := by
  have hx : (0 : ℝ) < 1 / (2 * δ) := by positivity
  set M : ℕ := ⌈1 / (2 * δ)⌉₊ with hMdef
  have hM : 1 / (2 * δ) ≤ (M : ℝ) := Nat.le_ceil _
  have hMpos : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le hx hM
  have hMlt : (M : ℝ) < 1 / (2 * δ) + 1 := Nat.ceil_lt_add_one (le_of_lt hx)
  have hlog : Real.log M ≤ Real.log (1 / (2 * δ) + 1) :=
    Real.log_le_log hMpos (le_of_lt hMlt)
  have hbase := largeSieve_separated_log N s lam hδ0 hδ hsep hM a
  have hδinv : (0 : ℝ) ≤ 1 / δ := by positivity
  have hstep : (N : ℝ) + (1 / δ) * (1 + Real.log M)
      ≤ (N : ℝ) + (1 / δ) * (1 + Real.log (1 / (2 * δ) + 1)) := by
    have := mul_le_mul_of_nonneg_left (add_le_add_left hlog (1 : ℝ)) hδinv
    linarith
  exact le_trans hbase (mul_le_mul_of_nonneg_right hstep (sq_nonneg _))

end RHTower.Sieve
