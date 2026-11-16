import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheUntwistedSquarefreeThetaSeriesHasASimplePole
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinTwoKBesselMellinProduct
import GaloisForLFunctions.RHTower.ThetaPrimeDeletionMellin

/-!
# The untwisted continuation has no Mellin poles

The substitution `t=(x/2)e^u` identifies the positive-ray cubic Bessel kernel
with the hyperbolic-cosh kernel. The two-Bessel Mellin formula then gives an
explicit Gamma quotient, nonzero throughout `Re s>2/3`. Dividing the completed
squarefree series therefore introduces no poles in its upper strip.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover
open MetaplecticMobiusDescent.CubicEisenstein

private theorem integral_exp_scale (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), f t) =
      ∫ u : ℝ, ((a * Real.exp u : ℝ) : ℂ) * f (a * Real.exp u) := by
  have h := _root_.RHTower.integral_Ioi_comp_exp_complex (fun t => (a : ℂ) * f (a * t))
  rw [integral_const_mul, integral_comp_mul_left_Ioi f 0 ha, mul_zero,
    Complex.real_smul, Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀
      (Complex.ofReal_ne_zero.mpr ha.ne'), one_mul] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards with u
  push_cast
  ring

private theorem cpow_exp_real (u : ℝ) (ν : ℂ) :
    (Real.exp u : ℂ) ^ ν = Complex.exp (ν * (u : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero u)),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
  congr 1
  ring

/-- The positive-ray and hyperbolic-cosh normalizations of the Bessel kernel agree. -/
theorem schlafliBesselK_eq_modifiedBesselKOrder (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    schlafliBesselK ν x = HTGeometry.modifiedBesselKOrder x ν := by
  set a : ℝ := x / 2 with ha_def
  have ha : 0 < a := half_pos hx
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hint : schlafliIntegral ν x =
      (a : ℂ) ^ ν * ∫ u : ℝ, RHTower.besselOrderExpKernel x ν u := by
    rw [schlafliIntegral, integral_exp_scale _ ha, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    have he : (Real.exp u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero u)
    have ht : ((a * Real.exp u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_pos ha (Real.exp_pos u)).ne'
    have hpow : ((a * Real.exp u : ℝ) : ℂ) * ((a * Real.exp u : ℝ) : ℂ) ^ (ν - 1) =
        (a : ℂ) ^ ν * Complex.exp (ν * (u : ℂ)) := by
      calc
        _ = ((a * Real.exp u : ℝ) : ℂ) ^ (1 : ℂ) *
            ((a * Real.exp u : ℝ) : ℂ) ^ (ν - 1) := by rw [Complex.cpow_one]
        _ = ((a * Real.exp u : ℝ) : ℂ) ^ ν := by
          rw [← Complex.cpow_add _ _ ht, show (1 : ℂ) + (ν - 1) = ν by ring]
        _ = _ := by
          rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha.le
            (Real.exp_pos u).le, cpow_exp_real]
    have hexponent : -((a * Real.exp u : ℝ) : ℂ) - (x : ℂ) ^ 2 /
        (4 * ((a * Real.exp u : ℝ) : ℂ)) = -(x : ℂ) * Complex.cosh (u : ℂ) := by
      rw [Complex.cosh, Complex.exp_neg, ← Complex.ofReal_exp]
      rw [ha_def]
      push_cast
      field_simp
      ring
    rw [← mul_assoc, hpow, hexponent, RHTower.besselOrderExpKernel,
      Complex.exp_add]
    ring
  rw [schlafliBesselK, hint, ← mul_assoc]
  have ha_cast : (x / 2 : ℂ) = (a : ℂ) := by rw [ha_def]; push_cast; rfl
  rw [ha_cast]
  have hcancel : (a : ℂ) ^ (-ν) * (a : ℂ) ^ ν = 1 := by
    rw [← Complex.cpow_add _ _ haC, neg_add_cancel, Complex.cpow_zero]
  rw [mul_assoc (1 / 2 : ℂ) _ _, hcancel, mul_one,
    RHTower.integral_besselOrderExpKernel_eq_two_mul hx ν]
  ring

/-- The Mellin factor is an explicit quotient of four Gamma values. -/
theorem besselSqMellin_eq_gamma (s : ℂ) (hs : 2 / 3 < s.re) :
    besselSqMellin s = (2 : ℂ) ^ (s - 3) / Complex.Gamma s *
      (Complex.Gamma (s / 2 + 1 / 3) * Complex.Gamma (s / 2) ^ 2 *
        Complex.Gamma (s / 2 - 1 / 3)) := by
  have hchamber : |(1 / 3 : ℂ).re| + |(1 / 3 : ℂ).re| < s.re := by
    norm_num
    linarith
  have h := RHTower.integral_cpow_mul_modifiedBesselKOrder_mul_modifiedBesselKOrder hchamber
  have hleft : besselSqMellin s = ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) *
      HTGeometry.modifiedBesselKOrder x (1 / 3) * HTGeometry.modifiedBesselKOrder x (1 / 3) := by
    unfold besselSqMellin mellin besselSq
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [schlafliBesselK_eq_modifiedBesselKOrder _ hx, smul_eq_mul]
    ring
  rw [hleft, h]
  congr 1
  rw [show (s + 1 / 3 + 1 / 3) / 2 = s / 2 + 1 / 3 by ring,
    show (s + 1 / 3 - 1 / 3) / 2 = s / 2 by ring,
    show (s - 1 / 3 + 1 / 3) / 2 = s / 2 by ring,
    show (s - 1 / 3 - 1 / 3) / 2 = s / 2 - 1 / 3 by ring]
  ring

/-- No Mellin zeros occur in the full half-plane of absolute convergence. -/
theorem besselSqMellin_ne_zero (s : ℂ) (hs : 2 / 3 < s.re) :
    besselSqMellin s ≠ 0 := by
  rw [besselSqMellin_eq_gamma s hs]
  have h0 : 0 < s.re := by linarith
  have hp : 0 < (s / 2 + 1 / 3).re := by simp; linarith
  have hm : 0 < (s / 2 - 1 / 3).re := by simp; linarith
  have hh : 0 < (s / 2).re := by simp; linarith
  exact mul_ne_zero
    (div_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))
      (Complex.Gamma_ne_zero_of_re_pos h0))
    (mul_ne_zero (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos hp)
      (pow_ne_zero 2 (Complex.Gamma_ne_zero_of_re_pos hh)))
      (Complex.Gamma_ne_zero_of_re_pos hm))

/-- Removing the Mellin factor preserves holomorphy throughout the upper strip. -/
theorem continuedUntwistedTheta_differentiableOn :
    DifferentiableOn ℂ continuedUntwistedTheta untwistedContinuationDomain := by
  intro w hw
  have hr : (2 * w).re = 2 * w.re := by simp
  have hi : (2 * w).im = 2 * w.im := by simp
  have hs : 2 / 3 < (2 * w).re := by rw [hr]; linarith only [hw.1]
  have hlin : DifferentiableAt ℂ (fun w : ℂ => 2 * w) w := differentiableAt_id.const_mul 2
  exact (((completedUntwistedS_differentiableAt (2 * w)
    (by rw [hr]; linarith only [hw.1]) (by rw [hr]; linarith only [hw.2.1])
    (by rw [hi]; linarith only [hw.2.2])).comp w hlin).div
      ((besselSqMellin_differentiableAt _ hs).comp w hlin)
      (besselSqMellin_ne_zero _ hs)).differentiableWithinAt

/-- The continuation agrees pointwise with the convergent untwisted series. -/
theorem continuedUntwistedTheta_eq_series (w : ℂ) (hw : 2 < w.re)
    (hu : w.re < 13 / 6) (hi : 0 < w.im) :
    continuedUntwistedTheta w = twistedSquarefreeSeries 1 w := by
  apply continuedUntwistedTheta_eq w hw hu hi
  apply besselSqMellin_ne_zero
  have hr : (2 * w).re = 2 * w.re := by simp
  rw [hr]
  linarith

/-- The untwisted squarefree series has a holomorphic continuation through the
upper strip, joined to its explicit nonzero simple pole at `2/3`. -/
theorem untwistedSquarefreeSeries_holomorphic_simple_pole :
    ∃ L : ℂ → ℂ,
      DifferentiableOn ℂ L untwistedContinuationDomain ∧
      (∀ w : ℂ, 2 < w.re → w.re < 13 / 6 → 0 < w.im →
        L w = twistedSquarefreeSeries 1 w) ∧
      (∀ᶠ w in 𝓝[≠] (2 / 3 : ℂ), DifferentiableAt ℂ L w) ∧
      Tendsto (fun w => (w - 2 / 3) * L w) (𝓝[≠] (2 / 3 : ℂ))
        (𝓝 untwistedThetaResidue) ∧
      untwistedThetaResidue ≠ 0 :=
  ⟨continuedUntwistedTheta, continuedUntwistedTheta_differentiableOn,
    continuedUntwistedTheta_eq_series, continuedUntwistedTheta_differentiableAt_near,
    continuedUntwistedTheta_simple_pole, untwistedThetaResidue_ne_zero⟩

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
