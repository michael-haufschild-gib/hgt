import GaloisForLFunctions.RHTower.XiGaussianHeatTraceCriterion

/-!
# The first Gaussian Mellin bridge for the Xi divisor

The Gaussian heat trace has an unconditional first ray Mellin coefficient.  Integrating
`κ exp (-(κ² / 2) μ²)` over `κ > 0` gives `μ⁻²` for every centered Xi-divisor copy.  The
existing squared-coordinate sector bound makes the norm integrals summable, so this pointwise
identity passes through the multiplicity-exact divisor sum.  Thus the Gaussian heat trace
recovers the first central reciprocal moment without RH, numerical zero data, or a choice of
zero enumeration.
-/

open Complex Filter MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The ray-Mellin integrand contributed by one multiplicity-exact Xi-divisor copy. -/
def xiGaussianMellinTerm (q : XiZeroCopy) (κ : ℝ) : ℂ :=
  (κ : ℂ) * xiGaussianHeatTerm (κ ^ 2 / 2) q

/-- One Xi-divisor Mellin term is integrable on the positive ray. -/
theorem xiGaussianMellinTerm_integrable (q : XiZeroCopy) :
    Integrable (xiGaussianMellinTerm q) (volume.restrict (Ioi 0)) := by
  let b : ℂ := xiSpectralPoint q ^ 2 / 2
  have hb : 0 < b.re := by
    simpa [b, Complex.div_re] using half_pos (xiSpectralSq_re_pos q)
  have hbase : IntegrableOn
      (fun κ : ℝ => (κ : ℂ) * Complex.exp (-b * (κ : ℂ) ^ 2)) (Ioi 0) :=
    (integrable_mul_cexp_neg_mul_sq hb).integrableOn
  refine hbase.congr_fun_ae (Filter.Eventually.of_forall fun κ => ?_)
  simp only [xiGaussianMellinTerm, xiGaussianHeatTerm, b]
  push_cast
  ring

/-- Integrating one Xi-divisor Mellin term extracts its reciprocal square. -/
theorem integral_xiGaussianMellinTerm (q : XiZeroCopy) :
    ∫ κ : ℝ in Ioi 0, xiGaussianMellinTerm q κ =
      xiZeroCopyReciprocalSquare q := by
  let b : ℂ := xiSpectralPoint q ^ 2 / 2
  have hb : 0 < b.re := by
    simpa [b, Complex.div_re] using half_pos (xiSpectralSq_re_pos q)
  rw [show (fun κ : ℝ => xiGaussianMellinTerm q κ) =
      fun κ : ℝ => (κ : ℂ) * Complex.exp (-b * (κ : ℂ) ^ 2) by
    funext κ
    simp only [xiGaussianMellinTerm, xiGaussianHeatTerm, b]
    push_cast
    ring]
  rw [integral_mul_cexp_neg_mul_sq hb, xiZeroCopyReciprocalSquare]
  dsimp [b]
  have hne : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  field_simp

/-- The norm of one Mellin term has an exact positive-ray integral. -/
theorem integral_norm_xiGaussianMellinTerm (q : XiZeroCopy) :
    ∫ κ : ℝ in Ioi 0, ‖xiGaussianMellinTerm q κ‖ =
      ((xiSpectralPoint q ^ 2).re)⁻¹ := by
  let A : ℝ := (xiSpectralPoint q ^ 2).re
  have hA : 0 < A := xiSpectralSq_re_pos q
  calc
    ∫ κ : ℝ in Ioi 0, ‖xiGaussianMellinTerm q κ‖ =
        ∫ κ : ℝ in Ioi 0, κ * Real.exp (-(A / 2) * κ ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro κ hκ
      change ‖(κ : ℂ) * xiGaussianHeatTerm (κ ^ 2 / 2) q‖ =
        κ * Real.exp (-(A / 2) * κ ^ 2)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ,
        xiGaussianHeatTerm, Complex.norm_exp]
      simp only [A, Complex.mul_re]
      simp only [pow_two, Complex.mul_re, Complex.mul_im]
      simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    _ = A⁻¹ := by
      have h := integral_mul_cexp_neg_mul_sq (b := (A / 2 : ℂ)) (by
        simpa [Complex.div_re] using half_pos hA)
      have hcongr :
          (fun κ : ℝ => (κ : ℂ) * Complex.exp (-(A / 2 : ℂ) * (κ : ℂ) ^ 2)) =
            fun κ : ℝ => ((κ * Real.exp (-(A / 2) * κ ^ 2) : ℝ) : ℂ) := by
        funext κ
        rw [Complex.ofReal_mul, Complex.ofReal_exp]
        congr 1
        push_cast
        ring
      rw [hcongr] at h
      have hreal :
          ∫ κ : ℝ in Ioi 0, κ * Real.exp (-(A / 2) * κ ^ 2) =
            (2 * (A / 2))⁻¹ := by
        exact_mod_cast h
      rw [hreal]
      field_simp [hA.ne']

/-- The positive-ray norm integrals are summable over the full Xi divisor. -/
theorem summable_integral_norm_xiGaussianMellinTerm :
    Summable (fun q : XiZeroCopy =>
      ∫ κ : ℝ in Ioi 0, ‖xiGaussianMellinTerm q κ‖) := by
  apply Summable.of_norm_bounded (xiSpectralPoint_inv_sq_summable.mul_left 2)
  intro q
  rw [integral_norm_xiGaussianMellinTerm]
  let A : ℝ := (xiSpectralPoint q ^ 2).re
  let N : ℝ := Complex.normSq (xiSpectralPoint q)
  have hgap : N < 2 * A := by
    simpa only [A, N] using xiSpectralPoint_normSq_lt_two_mul_sq_re q
  have hN : 0 < N := Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)
  have hA : 0 < A := xiSpectralSq_re_pos q
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hA.le)]
  calc
    A⁻¹ = 1 / A := by ring
    _ ≤ 2 / N := by
      rw [div_le_div_iff₀ hA hN]
      nlinarith
    _ = 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
      rw [Complex.sq_norm]
      change 2 / N = 2 * (1 / N)
      ring

/-- **First Gaussian Mellin bridge.** The positive-ray Mellin coefficient of the complete
Xi Gaussian heat trace is exactly the first central reciprocal moment. -/
theorem integral_xiGaussianHeatTrace_eq_xiCentralReciprocalMoment_zero :
    ∫ κ : ℝ in Ioi 0,
      (κ : ℂ) * xiGaussianHeatTrace (κ ^ 2 / 2) = xiCentralReciprocalMoment 0 := by
  calc
    ∫ κ : ℝ in Ioi 0, (κ : ℂ) * xiGaussianHeatTrace (κ ^ 2 / 2) =
        ∫ κ : ℝ in Ioi 0, ∑' q : XiZeroCopy, xiGaussianMellinTerm q κ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro κ _
      change (κ : ℂ) * xiGaussianHeatTrace (κ ^ 2 / 2) =
        ∑' q : XiZeroCopy, (κ : ℂ) * xiGaussianHeatTerm (κ ^ 2 / 2) q
      rw [xiGaussianHeatTrace, ← tsum_mul_left]
    _ = ∑' q : XiZeroCopy, ∫ κ : ℝ in Ioi 0, xiGaussianMellinTerm q κ :=
      (MeasureTheory.integral_tsum_of_summable_integral_norm
        xiGaussianMellinTerm_integrable
        summable_integral_norm_xiGaussianMellinTerm).symm
    _ = ∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q := by
      apply tsum_congr
      intro q
      exact integral_xiGaussianMellinTerm q
    _ = xiCentralReciprocalMoment 0 := by
      simpa only [zero_add, pow_one] using tsum_xiZeroCopyReciprocalSquare_pow 0

end

end RHTower
