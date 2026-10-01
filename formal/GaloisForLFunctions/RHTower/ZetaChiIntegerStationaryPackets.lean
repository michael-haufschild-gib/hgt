import GaloisForLFunctions.RHTower.ZetaChiCoherentPhaseModel

open Complex
noncomputable section
namespace RHTower

private theorem stationary_entropy_bounds {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    0 ≤ t * Real.log (t / a) - t + a ∧
      t * Real.log (t / a) - t + a ≤ (t - a) ^ 2 / a := by
  have hl := mul_le_mul_of_nonneg_left
    (Real.one_sub_inv_le_log_of_pos (div_pos ht ha)) ht.le
  have hu := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos ht ha)) ht.le
  have he : t * (1 - (t / a)⁻¹) = t - a := by field_simp
  have he' : t * (t / a - 1) - t + a = (t - a) ^ 2 / a := by field_simp; ring
  rw [he] at hl
  constructor
  · linarith
  · linarith

/-- Integer stationary frequencies share one actual chi orientation, with a
quadratic distance error valid at every positive integer and height at least four. -/
theorem exists_zetaChi_integer_stationary_alignment :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ n : ℕ, 0 < n → ∀ t : ℝ, 4 ≤ t →
      ‖zetaChi (linePt t) * Complex.exp (((t * Real.log n : ℝ) : ℂ) * I) - κ‖ ≤
        26 / t + (t - 2 * Real.pi * n) ^ 2 / (2 * Real.pi * n) := by
  obtain ⟨κ, hκ, hm⟩ := exists_zetaChi_coherent_integerGrade_model
  refine ⟨κ, hκ, ?_⟩
  intro n hn t ht
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht0 : 0 < t := by linarith
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  let a : ℝ := 2 * Real.pi * n
  have ha : 0 < a := mul_pos hp hnR
  let D : ℝ := t * Real.log (t / a) - t + a
  obtain ⟨hD0, hD⟩ := stationary_entropy_bounds ht0 ha
  change 0 ≤ D at hD0
  change D ≤ (t - a) ^ 2 / a at hD
  have hphase : t - t * Real.log (t / (2 * Real.pi)) + t * Real.log n = a - D := by
    dsimp only [D, a]
    rw [Real.log_div ht0.ne' hp.ne', Real.log_div ht0.ne' ha.ne',
      Real.log_mul hp.ne' hnR.ne']
    ring
  have hint : Complex.exp ((a : ℂ) * I) = 1 := by
    have he : (a : ℂ) * I = (n : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      dsimp only [a]
      push_cast
      ring
    rw [he, Complex.exp_nat_mul_two_pi_mul_I]
  have hv : ‖Complex.exp (((t * Real.log n : ℝ) : ℂ) * I)‖ = 1 := by
    have he : Complex.exp (((t * Real.log n : ℝ) : ℂ) * I) =
        bourgainOscillation (t * Real.log n) := by
      unfold bourgainOscillation
      congr 1
      ring
    rw [he, norm_bourgainOscillation]
  have hb := hm 1 t ht
  simp only [Int.cast_one, zpow_one, one_mul, abs_one, mul_one] at hb
  have hosc : ‖Complex.exp (((t - t * Real.log (t / (2 * Real.pi)) : ℝ) : ℂ) * I) *
      Complex.exp (((t * Real.log n : ℝ) : ℂ) * I) - 1‖ ≤ (t - a) ^ 2 / a := by
    have he : Complex.exp (((t - t * Real.log (t / (2 * Real.pi)) : ℝ) : ℂ) * I) *
        Complex.exp (((t * Real.log n : ℝ) : ℂ) * I) = bourgainOscillation (-D) := by
      rw [← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, hphase,
        Complex.ofReal_sub, sub_mul, Complex.exp_sub, hint]
      dsimp only [bourgainOscillation]
      rw [one_div, ← Complex.exp_neg]
      congr 1
      push_cast
      ring
    rw [he]
    have hz : bourgainOscillation 0 = 1 := by simp [bourgainOscillation]
    rw [← hz]
    exact (norm_bourgainOscillation_sub_le (-D) 0).trans
      (by simpa only [sub_zero, abs_neg, abs_of_nonneg hD0] using hD)
  calc
    _ ≤ ‖(zetaChi (linePt t) - κ * Complex.exp
          (((t - t * Real.log (t / (2 * Real.pi)) : ℝ) : ℂ) * I)) *
          Complex.exp (((t * Real.log n : ℝ) : ℂ) * I)‖ +
        ‖κ * (Complex.exp (((t - t * Real.log (t / (2 * Real.pi)) : ℝ) : ℂ) * I) *
          Complex.exp (((t * Real.log n : ℝ) : ℂ) * I) - 1)‖ := by
      convert norm_add_le
        ((zetaChi (linePt t) - κ * Complex.exp
          (((t - t * Real.log (t / (2 * Real.pi)) : ℝ) : ℂ) * I)) *
          Complex.exp (((t * Real.log n : ℝ) : ℂ) * I))
        (κ * (Complex.exp (((t - t * Real.log (t / (2 * Real.pi)) : ℝ) : ℂ) * I) *
          Complex.exp (((t * Real.log n : ℝ) : ℂ) * I) - 1)) using 1
      congr 1
      ring
    _ = ‖zetaChi (linePt t) - κ * Complex.exp
          (((t - t * Real.log (t / (2 * Real.pi)) : ℝ) : ℂ) * I)‖ +
        ‖Complex.exp (((t - t * Real.log (t / (2 * Real.pi)) : ℝ) : ℂ) * I) *
          Complex.exp (((t * Real.log n : ℝ) : ℂ) * I) - 1‖ := by
      rw [norm_mul, norm_mul, hv, hκ, mul_one, one_mul]
    _ ≤ _ := add_le_add hb hosc

end RHTower
