import Mathlib
import GaloisForLFunctions.HTGeometry.ArcsineSeries
import GaloisForLFunctions.RHTower.ZetaDerivDirichlet
import GaloisForLFunctions.RHTower.Sieve.MertensFirst

/-!
# The arcsine dilation charge is a central-binomial spectrum of even log-Dirichlet sums

`∑_{k} (log k / k)·arcsin(1/k) = ∑_j c_j · ∑_k log k / k^{2j+2}`, obtained by expanding
`arcsin(1/k)` in its Maclaurin series and interchanging the two nonnegative sums (Tonelli).
-/

namespace GaloisForLFunctions

open scoped Nat

theorem log_natCast_nonneg (k : ℕ) : 0 ≤ Real.log k := by
  rcases Nat.eq_zero_or_pos k with h | h
  · simp [h]
  · exact Real.log_nonneg (by exact_mod_cast h)

/-- `∑ log k / k^(2 : ℕ)` converges, from the absolute convergence of `ζ'` at `s = 2`. -/
theorem summable_log_div_sq : Summable (fun k : ℕ => Real.log k / (k : ℝ) ^ (2 : ℕ)) :=
  _root_.RHTower.Sieve.summable_log_div_sq

/-- Per-`k` slice: `∑_j c_j·log k / k^{2j+2} = (log k / k)·arcsin(1/k)`. -/
theorem arcsine_transform_slice (k : ℕ) :
    ∑' j : ℕ, arcsinCoeff j * Real.log k / (k : ℝ) ^ (2 * j + 2)
      = Real.log k / k * Real.arcsin (1 / (k : ℝ)) := by
  rcases lt_or_ge k 2 with hk | hk
  · have hlog : Real.log k = 0 := by interval_cases k <;> simp
    simp [hlog]
  · have hkpos : (0 : ℝ) < k := by positivity
    have h1k : |1 / (k : ℝ)| < 1 := by
      rw [abs_of_nonneg (by positivity), div_lt_one hkpos]; exact_mod_cast hk
    have hhs := (arcsin_hasSum h1k).mul_left (Real.log k / k)
    rw [← hhs.tsum_eq]
    apply tsum_congr; intro j
    rw [div_pow, one_pow, pow_add, pow_mul]
    field_simp
    ring

theorem arcsine_col_summable (k : ℕ) :
    Summable (fun j : ℕ => arcsinCoeff j * Real.log k / (k : ℝ) ^ (2 * j + 2)) := by
  rcases lt_or_ge k 2 with hk | hk
  · have hlog : Real.log k = 0 := by interval_cases k <;> simp
    simp only [hlog, mul_zero, zero_div]
    exact summable_zero
  · have hkpos : (0 : ℝ) < k := by positivity
    have h1k : |1 / (k : ℝ)| < 1 := by
      rw [abs_of_nonneg (by positivity), div_lt_one hkpos]; exact_mod_cast hk
    have hsm := ((arcsin_hasSum h1k).summable).mul_left (Real.log k / k)
    apply hsm.congr; intro j
    rw [div_pow, one_pow, pow_add, pow_mul]; field_simp; ring

theorem arcsine_slice_nonneg (k : ℕ) : 0 ≤ Real.log k / k * Real.arcsin (1 / (k : ℝ)) :=
  mul_nonneg (div_nonneg (log_natCast_nonneg k) (Nat.cast_nonneg k))
    (Real.arcsin_nonneg.mpr (by positivity))

theorem arcsine_row_summable :
    Summable (fun k : ℕ => Real.log k / k * Real.arcsin (1 / (k : ℝ))) := by
  refine Summable.of_nonneg_of_le arcsine_slice_nonneg (fun k => ?_)
    (summable_log_div_sq.mul_left (Real.pi / 2))
  have h1k1 : 1 / (k : ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h]
    · rw [div_le_one (by positivity)]; exact_mod_cast h
  have harc := arcsin_le_pi_half_mul (1 / (k : ℝ)) (by positivity) h1k1
  have hlk : 0 ≤ Real.log k / k := div_nonneg (log_natCast_nonneg k) (Nat.cast_nonneg k)
  calc Real.log k / k * Real.arcsin (1 / (k : ℝ))
      ≤ Real.log k / k * (Real.pi / 2 * (1 / (k : ℝ))) := mul_le_mul_of_nonneg_left harc hlk
    _ = Real.pi / 2 * (Real.log k / (k : ℝ) ^ (2 : ℕ)) := by ring

/-- **Arcsine–Dirichlet transform.**  The arcsine dilation charge equals the central-binomial
superposition of the even log-Dirichlet sums. -/
theorem arcsine_dirichlet_transform :
    ∑' k : ℕ, Real.log k / k * Real.arcsin (1 / (k : ℝ))
      = ∑' j : ℕ, arcsinCoeff j * ∑' k : ℕ, Real.log k / (k : ℝ) ^ (2 * j + 2) := by
  set F : ℕ → ℕ → ℝ := fun k j => arcsinCoeff j * Real.log k / (k : ℝ) ^ (2 * j + 2) with hF
  have hnonneg : ∀ p : ℕ × ℕ, 0 ≤ Function.uncurry F p := by
    rintro ⟨k, j⟩
    exact div_nonneg (mul_nonneg (arcsinCoeff_nonneg j) (log_natCast_nonneg k)) (by positivity)
  have hsum : Summable (Function.uncurry F) := by
    rw [summable_prod_of_nonneg hnonneg]
    refine ⟨arcsine_col_summable, ?_⟩
    exact arcsine_row_summable.congr fun k => (arcsine_transform_slice k).symm
  calc ∑' k : ℕ, Real.log k / k * Real.arcsin (1 / (k : ℝ))
      = ∑' k : ℕ, ∑' j : ℕ, F k j := by
        apply tsum_congr; intro k; exact (arcsine_transform_slice k).symm
    _ = ∑' j : ℕ, ∑' k : ℕ, F k j := (hsum.tsum_comm).symm
    _ = ∑' j : ℕ, arcsinCoeff j * ∑' k : ℕ, Real.log k / (k : ℝ) ^ (2 * j + 2) := by
        apply tsum_congr; intro j
        rw [← tsum_mul_left]
        apply tsum_congr; intro k
        rw [hF]; ring

end GaloisForLFunctions
