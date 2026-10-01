import GaloisForLFunctions.RHTower.SteinhausAffineCircleMean

open Complex
open scoped ComplexConjugate
noncomputable section
namespace RHTower
open SteinhausModel

/-- Exact identification of an affine phase density from its two spectral coefficients. -/
theorem steinhausAffineCircleWeight_eq_norm_sq_factor
    {a b m : ℂ} (hnorm : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) (hmean : a * conj b = m)
    (x : ℝ) : steinhausAffineCircleWeight m x = ‖a + b * charFactor 1 x‖ ^ 2 := by
  have hcross : (a * conj (b * charFactor 1 x)).re =
      (conj m * charFactor 1 x).re := by
    rw [map_mul, ← mul_assoc, hmean]
    simp [Complex.mul_re]
  have hz : Complex.normSq (charFactor 1 x) = 1 := by
    rw [← Complex.sq_norm, norm_charFactor]
    norm_num
  rw [Complex.sq_norm, Complex.normSq_add, Complex.normSq_mul, hz, mul_one,
    ← Complex.sq_norm, ← Complex.sq_norm, hnorm, hcross]
  rfl

/-- Every allowed affine bias admits an actual normalized degree-one spectral
factor; its nonconstant coefficient pays at least the squared bias. -/
theorem exists_steinhausAffineCircle_spectralFactor {m : ℂ} (hm : ‖m‖ ≤ 1 / 2) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ∃ b : ℂ,
      a ^ 2 + ‖b‖ ^ 2 = 1 ∧ (a : ℂ) * conj b = m ∧
      ‖m‖ ^ 2 ≤ ‖b‖ ^ 2 ∧
      ∀ x : ℝ, steinhausAffineCircleWeight m x = ‖(a : ℂ) + b * charFactor 1 x‖ ^ 2 := by
  let r := ‖m‖
  have hr : 0 ≤ r := norm_nonneg _
  have hrhalf : r ≤ 1 / 2 := hm
  have hdisc : 0 ≤ 1 - 4 * r ^ 2 := by nlinarith
  let x := (1 + Real.sqrt (1 - 4 * r ^ 2)) / 2
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hsqrt := Real.sq_sqrt hdisc
  have hsqrt0 := Real.sqrt_nonneg (1 - 4 * r ^ 2)
  have hx1 : x ≤ 1 := by dsimp [x]; nlinarith [sq_nonneg r]
  have hquad : x ^ 2 - x + r ^ 2 = 0 := by dsimp [x]; nlinarith
  let a := Real.sqrt x
  have ha : 0 < a := Real.sqrt_pos.2 hx0
  have ha2 : a ^ 2 = x := Real.sq_sqrt hx0.le
  have ha1 : a ≤ 1 := by nlinarith
  let b : ℂ := conj m / (a : ℂ)
  have hb : ‖b‖ = r / a := by simp [b, Real.norm_eq_abs, abs_of_pos ha, r]
  have hsum : a ^ 2 + ‖b‖ ^ 2 = 1 := by
    rw [hb, div_pow, ha2]
    field_simp [hx0.ne']
    nlinarith [hquad]
  have hmean : (a : ℂ) * conj b = m := by
    dsimp [b]
    simp only [map_div₀, conj_conj, conj_ofReal]
    field_simp [ha.ne']
  have hlower : ‖m‖ ^ 2 ≤ ‖b‖ ^ 2 := by
    have heq : ‖m‖ = a * ‖b‖ := by
      rw [← hmean, norm_mul, norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    have hnormle : ‖m‖ ≤ ‖b‖ := by rw [heq]; nlinarith [norm_nonneg b]
    nlinarith [norm_nonneg m, norm_nonneg b]
  refine ⟨a, ha, ha1, b, hsum, hmean, hlower, ?_⟩
  intro y
  apply steinhausAffineCircleWeight_eq_norm_sq_factor _ hmean y
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha] using hsum

end RHTower
