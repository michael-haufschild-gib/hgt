import GaloisForLFunctions.RHTower.ZetaChiPositiveGradeStationary

open Complex MeasureTheory
noncomputable section
namespace RHTower

/-- Every negative grade is exactly the conjugate positive physical grade
with reversed Dirichlet frequency. -/
theorem zetaChi_negative_natGrade_integrand_eq_conj (k : ℕ) (ω t : ℝ) :
    zetaChi (linePt t) ^ (-(k : ℤ)) * bourgainOscillation (-(k : ℝ) * t * ω) =
      (starRingEnd ℂ) (zetaChi (linePt t) ^ k * bourgainOscillation ((k : ℝ) * t * ω)) := by
  rw [zetaChi_line_eq_exp_neg_two_theta, ← Complex.exp_int_mul, ← Complex.exp_nat_mul]
  unfold bourgainOscillation
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_add, map_mul, map_neg, map_ofNat, map_natCast,
    Complex.conj_I, Complex.conj_ofReal]
  ring

/-- Negative chi grades have the conjugate stationary orientation and the
same full quantitative remainder as their positive partners. -/
theorem norm_integral_zetaChi_negative_grade_stationary_le (k : ℕ) (hk : 0 < k)
    {a h l u : ℝ} (ha : 8 ≤ a) (hh : 0 < h) (hha : h ≤ a / 2)
    (hl : a / 2 ≤ l) (hlh : l ≤ a - h) (hhu : a + h ≤ u) (hu : u ≤ 2 * a) :
    ‖(∫ t in l..u, zetaChi (linePt t) ^ (-(k : ℤ)) *
        bourgainOscillation (-(k : ℝ) * t * Real.log (a / (2 * Real.pi)))) -
      (((k : ℝ)⁻¹ * Real.sqrt (2 * Real.pi * ((k : ℝ) * a)) : ℝ) : ℂ) *
        bourgainOscillation (-((k : ℝ) * a + ((k : ℝ) - 1) * (Real.pi / 4)))‖ ≤
      78 * (k : ℝ) + 4 * (k : ℝ) * h ^ 4 / a ^ 2 + 40 * a / ((k : ℝ) * h) := by
  have hb := norm_integral_zetaChi_positive_grade_stationary_le k hk ha hh hha hl hlh hhu hu
  have hi : (∫ t in l..u, zetaChi (linePt t) ^ (-(k : ℤ)) *
      bourgainOscillation (-(k : ℝ) * t * Real.log (a / (2 * Real.pi)))) =
      (starRingEnd ℂ) (∫ t in l..u, zetaChi (linePt t) ^ k *
        bourgainOscillation ((k : ℝ) * t * Real.log (a / (2 * Real.pi)))) := by
    simp_rw [zetaChi_negative_natGrade_integrand_eq_conj]
    exact intervalIntegral.intervalIntegral_conj
  let A : ℝ := (k : ℝ)⁻¹ * Real.sqrt (2 * Real.pi * ((k : ℝ) * a))
  let θ : ℝ := (k : ℝ) * a + ((k : ℝ) - 1) * (Real.pi / 4)
  have hp : (starRingEnd ℂ) (bourgainOscillation θ) = bourgainOscillation (-θ) := by
    unfold bourgainOscillation
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
    ring
  have hm : (starRingEnd ℂ) ((A : ℂ) * bourgainOscillation θ) =
      (A : ℂ) * bourgainOscillation (-θ) := by
    rw [map_mul, Complex.conj_ofReal, hp]
  change ‖(∫ t in l..u, zetaChi (linePt t) ^ (-(k : ℤ)) *
    bourgainOscillation (-(k : ℝ) * t * Real.log (a / (2 * Real.pi)))) -
      (A : ℂ) * bourgainOscillation (-θ)‖ ≤ _
  rw [hi, ← hm, ← map_sub, Complex.norm_conj]
  exact hb

end RHTower
