import GaloisForLFunctions.goldbach.LiLiu.Arithmetic.DensityDirichlet
import GaloisForLFunctions.goldbach.LiLiu.Mellin.DirichletInversion
import GaloisForLFunctions.goldbach.LiLiu.Mellin.ProfileContour

/-! # Evaluation of the single density contour by its integer samples -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory Set
noncomputable section

private theorem profile_inversion (φ : TestWeight) {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    (signedProfile φ x : ℂ) = (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
      (x : ℂ)^(-((σ:ℂ)+t*I)) * profileMellin φ ((σ:ℂ)+t*I) := by
  have hc := (sumProfile_smooth φ).continuous
  have hcont : Continuous (fun u => (signedProfile φ u : ℂ)) :=
    continuous_ofReal.comp ((continuous_const.mul (hc.comp (continuous_const.sub continuous_id))).sub hc)
  have H := mellinInv_mellin_eq σ _ hx (signedProfile_mellinConvergent φ hσ)
    (profileMellin_vertical_integrable φ hσ) hcont.continuousAt
  simpa only [profileMellin, mellinInv, smul_eq_mul, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat] using H.symm

/-- The density coefficients sample the signed profile only at one. The zero
of its Mellin transform at one allows the starting line to be left of the pole. -/
theorem singleModel_integral {N : ℕ} (hN : N ≠ 0) (φ : TestWeight)
    {a : ℝ} (ha : 0 < a) (hb : a ≤ 3/2) :
    (1/(2*Real.pi) : ℂ) * (∫ t : ℝ, continuedProfileDensity N φ ((a:ℂ)+t*I)) =
      -(singularSeries N * φ.mass : ℝ) := by
  let c : ℝ := 3/2
  let A (k : ℕ) : ℂ := singularSeries (k*N)
  let w (t : ℝ) : ℂ := (c:ℂ)+t*I
  have hw (t : ℝ) : 1 < (w t).re := by norm_num [w,c]
  have hc : 0 < c := by norm_num [c]
  have he (t : ℝ) : continuedProfileDensity N φ (w t) = LSeries A (w t) * profileMellin φ (w t) := by
    have hn : w t ≠ 1 := fun h => by simpa [h] using hw t
    rw [continuedProfileDensity_eq hn, show LSeries A (w t) = _ from (densitySeries_kernel hN (hw t)).tsum_eq]
  rw [model_contour_shift N φ ha hb]
  change _ * (∫ t : ℝ, continuedProfileDensity N φ (w t)) = _
  simp_rw [he]
  rw [integral_LSeries_mul A (densitySeries_kernel hN (w := (c:ℂ)) (by norm_num [c])).summable
    (profileMellin_vertical_integrable φ hc), ← tsum_mul_left]
  have hs (k : ℕ) (hk : k ≠ 0) :
      (1/(2*Real.pi) : ℂ) * (∫ t : ℝ, LSeries.term A (w t) k * profileMellin φ (w t)) =
        A k * (signedProfile φ k : ℂ) := by
    rw [profile_inversion φ hc (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk))]
    simp only [LSeries.term_of_ne_zero hk, div_eq_mul_inv, ← Complex.cpow_neg, Complex.ofReal_natCast,
      mul_assoc, integral_const_mul, w]
    ring
  rw [tsum_eq_single 1]
  · rw [hs 1 one_ne_zero, signedProfile_nat φ Nat.one_pos, if_pos rfl]
    simp [A]
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp
    · rw [hs k hpos.ne', signedProfile_nat φ hpos, if_neg hk, Complex.ofReal_zero, mul_zero]

#print axioms singleModel_integral
end
end GaloisForLFunctions.Goldbach.LiLiu
