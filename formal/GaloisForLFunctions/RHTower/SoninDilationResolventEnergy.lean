import GaloisForLFunctions.RHTower.SoninDilationAverage
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact energy of the physical dilation resolvent

The translated strong-integral tail yields the resolvent energy identity on
every full Sonin vector, without a generator-domain premise. Its affine
transforms have an exact positive loss, and commute with physical dilations.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace RHTower

private def logDilation (t : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  dilationCLM (Real.exp t) (Real.exp_pos t)

private theorem logDilation_eq (t : ℝ) (f : SoninL2) :
    logDilation t f = rayDilate (Real.exp t) f := by
  rw [rayDilate_of_pos (Real.exp_pos _)]
  rfl

private theorem logDilation_zero (f : SoninL2) : logDilation 0 f = f := by
  apply Lp.ext
  have h := dilation_ae (Real.exp 0) (Real.exp_pos 0) f
  filter_upwards [h] with x hx
  simpa [logDilation, dilationCLM_apply] using hx

private theorem logDilation_add (s t : ℝ) (f : SoninL2) :
    logDilation (s+t) f = logDilation s (logDilation t f) := by
  dsimp only [logDilation, dilationCLM_apply]
  rw [dilation_dilation]
  simp only [Real.exp_add]

private theorem logDilation_norm (t : ℝ) (f : SoninL2) : ‖logDilation t f‖ = ‖f‖ :=
  (dilation (Real.exp t) (Real.exp_pos t)).norm_map f

private theorem logDilation_continuous (f : SoninL2) : Continuous fun t => logDilation t f := by
  simpa only [logDilation_eq] using continuous_dilationOrbit f

private def dampedOrbit (lam : ℝ) (f : SoninL2) (t : ℝ) : SoninL2 :=
  Real.exp (-lam*t) • logDilation t f

private theorem dampedOrbit_continuous (lam : ℝ) (f : SoninL2) : Continuous (dampedOrbit lam f) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul (logDilation_continuous f)

private theorem dampedOrbit_norm (lam : ℝ) (f : SoninL2) (t : ℝ) :
    ‖dampedOrbit lam f t‖ = Real.exp (-lam*t) * ‖f‖ := by
  rw [dampedOrbit, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), logDilation_norm]

private theorem dampedOrbit_integrable (lam : ℝ) (hlam : 0 < lam) (f : SoninL2) (b : ℝ) :
    IntegrableOn (dampedOrbit lam f) (Ioi b) volume := by
  apply Integrable.mono' ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hlam) b).mul_const ‖f‖)
    (dampedOrbit_continuous lam f).aestronglyMeasurable.restrict
  exact Eventually.of_forall fun t => (dampedOrbit_norm lam f t).le

private theorem dampedIntegral_bound (lam : ℝ) (hlam : 0 < lam) (f : SoninL2) :
    ‖∫ t in Ioi (0 : ℝ), dampedOrbit lam f t‖ ≤ lam⁻¹ * ‖f‖ := by
  have h := norm_integral_le_of_norm_le
    ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hlam) 0).mul_const ‖f‖)
    (Eventually.of_forall fun t => (dampedOrbit_norm lam f t).le)
  have he : (∫ t in Ioi (0 : ℝ), Real.exp (-lam*t)) = lam⁻¹ := by
    simpa using integral_exp_mul_Ioi (neg_neg_of_pos hlam) 0
  rwa [integral_mul_const, he] at h

/-- The literal whole-ray strong Laplace integral of normalized dilations. -/
def soninDilationResolvent (lam : ℝ) (hlam : 0 < lam) : SoninL2 →L[ℂ] SoninL2 :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ t in Ioi (0 : ℝ), dampedOrbit lam f t
      map_add' := by
        intro f g
        rw [← integral_add (dampedOrbit_integrable lam hlam f 0)
          (dampedOrbit_integrable lam hlam g 0)]
        apply integral_congr_ae
        filter_upwards [] with t
        simp only [dampedOrbit, map_add, smul_add]
      map_smul' := by
        intro c f
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards [] with t
        simp only [dampedOrbit, map_smul, RingHom.id_apply]
        exact smul_comm _ _ _ }
    lam⁻¹ (dampedIntegral_bound lam hlam)

/-- Source provenance of the bounded resolvent on every full physical vector. -/
theorem soninDilationResolvent_apply (lam : ℝ) (hlam : 0 < lam) (f : SoninL2) :
    soninDilationResolvent lam hlam f =
      ∫ t in Ioi (0 : ℝ), Real.exp (-lam*t) • rayDilate (Real.exp t) f := by
  change (∫ t in Ioi (0 : ℝ), dampedOrbit lam f t) = _
  simp only [dampedOrbit, logDilation_eq]

private theorem translate_tail (F : ℝ → SoninL2) (h : ℝ) :
    (∫ t in Ioi (0 : ℝ), F (h+t)) = ∫ t in Ioi h, F t := by
  calc
    _ = ∫ t : ℝ, (Ioi h).indicator F (h+t) := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards [] with t
      by_cases ht : 0 < t
      · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht), indicator_of_mem (show h+t ∈ Ioi h by simpa using ht)]
      · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht),
          indicator_of_notMem (show h+t ∉ Ioi h by simpa using ht)]
    _ = ∫ t : ℝ, (Ioi h).indicator F t := integral_add_left_eq_self _ _
    _ = _ := integral_indicator measurableSet_Ioi

private theorem resolvent_tail (lam : ℝ) (hlam : 0 < lam) (f : SoninL2) (h : ℝ) :
    Real.exp (-lam*h) • logDilation h (soninDilationResolvent lam hlam f) =
      ∫ t in Ioi h, dampedOrbit lam f t := by
  change Real.exp (-lam*h) • logDilation h (∫ t in Ioi (0 : ℝ), dampedOrbit lam f t) = _
  rw [← (logDilation h).integral_comp_comm (dampedOrbit_integrable lam hlam f 0),
    ← integral_smul, ← translate_tail (dampedOrbit lam f) h]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [dampedOrbit, ContinuousLinearMap.map_smul_of_tower, smul_smul, logDilation_add]
  rw [← Real.exp_add]
  congr 2
  ring

private theorem resolvent_tail_primitive (lam : ℝ) (hlam : 0 < lam) (f : SoninL2) (h : ℝ) :
    Real.exp (-lam*h) • logDilation h (soninDilationResolvent lam hlam f) =
      soninDilationResolvent lam hlam f - ∫ t in (0 : ℝ)..h, dampedOrbit lam f t := by
  rw [resolvent_tail]
  have ht := intervalIntegral.integral_Ioi_sub_Ioi'
    (dampedOrbit_integrable lam hlam f 0) (dampedOrbit_integrable lam hlam f h)
  change _ = (∫ t in Ioi (0 : ℝ), dampedOrbit lam f t) - _
  rw [← ht, sub_sub_cancel]

/-- Exact real energy of the literal dilation resolvent, for every physical
vector, obtained from its translated strong-integral tail. -/
theorem soninDilationResolvent_real_energy (lam : ℝ) (hlam : 0 < lam) (f : SoninL2) :
    (inner ℂ (soninDilationResolvent lam hlam f) f).re =
      lam * ‖soninDilationResolvent lam hlam f‖ ^ 2 := by
  letI : InnerProductSpace ℝ SoninL2 := InnerProductSpace.rclikeToReal ℂ SoninL2
  let y := soninDilationResolvent lam hlam f
  let H : ℝ → SoninL2 := fun h => y - ∫ t in (0 : ℝ)..h, dampedOrbit lam f t
  have hc := dampedOrbit_continuous lam f
  have hp := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 0)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hd : HasDerivAt H (-f) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).sub hp using 1
    simp only [dampedOrbit, mul_zero, Real.exp_zero, logDilation_zero, one_smul, zero_sub]
  have hnorm (h : ℝ) : ‖H h‖ ^ 2 = (Real.exp (-lam*h) * ‖y‖) ^ 2 := by
    rw [show H h = Real.exp (-lam*h) • logDilation h y from
      (resolvent_tail_primitive lam hlam f h).symm,
      norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), logDilation_norm]
  have he : HasDerivAt (fun h : ℝ => Real.exp (-lam*h)) (-lam) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (-lam)).exp
  have hs : HasDerivAt (fun h : ℝ => (Real.exp (-lam*h) * ‖y‖)^2)
      (-2 * lam * ‖y‖^2) 0 := by
    convert! (he.mul_const ‖y‖).pow 2 using 1
    simp
    ring
  have h := hd.norm_sq.unique (hs.congr_of_eventuallyEq (Eventually.of_forall hnorm))
  have hzero : H 0 = y := by simp [H]
  rw [hzero, inner_neg_right, real_inner_eq_re_inner ℂ] at h
  change 2 * (-(inner ℂ y f).re) = -2 * lam * ‖y‖^2 at h
  change (inner ℂ y f).re = lam * ‖y‖^2
  linarith

/-- Exact loss identity for a real affine transform of the actual resolvent.
The lost energy is explicit; no operator-norm or arithmetic premise is supplied. -/
theorem soninDilationResolvent_loss_identity (lam : ℝ) (hlam : 0 < lam)
    (c : ℝ) (f : SoninL2) :
    ‖f - c • soninDilationResolvent lam hlam f‖ ^ 2 +
      c * (2*lam-c) * ‖soninDilationResolvent lam hlam f‖ ^ 2 = ‖f‖ ^ 2 := by
  have he := soninDilationResolvent_real_energy lam hlam f
  rw [norm_sub_sq (𝕜 := ℂ)]
  have hi : (inner ℂ f (c • soninDilationResolvent lam hlam f)).re =
      c * (inner ℂ (soninDilationResolvent lam hlam f) f).re := by
    change (inner ℂ f ((c : ℂ) • soninDilationResolvent lam hlam f)).re = _
    rw [inner_smul_right, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact congrArg (fun x : ℝ => c*x) (inner_re_symm (𝕜 := ℂ) f
      (soninDilationResolvent lam hlam f))
  change ‖f‖ ^ 2 - 2 * (inner ℂ f (c • soninDilationResolvent lam hlam f)).re +
    ‖c • soninDilationResolvent lam hlam f‖ ^ 2 + _ = _
  rw [hi, he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- The canonical contraction intended to transfer the ground cutoff source
to every homogeneous time-band Taylor output. -/
def soninMonomialTransfer (n : ℕ) : SoninL2 →L[ℂ] SoninL2 :=
  1 - (n : ℝ) • soninDilationResolvent ((n : ℝ)+1/2) (by positivity)

/-- The proposed degree-transfer operator has an exact positive energy defect. -/
theorem soninMonomialTransfer_energy (n : ℕ) (f : SoninL2) :
    ‖soninMonomialTransfer n f‖ ^ 2 +
      (n : ℝ) * ((n : ℝ)+1) *
        ‖soninDilationResolvent ((n : ℝ)+1/2) (by positivity) f‖ ^ 2 = ‖f‖ ^ 2 := by
  have h := soninDilationResolvent_loss_identity ((n : ℝ)+1/2) (by positivity) (n : ℝ) f
  have hc : (n : ℝ) * (2*((n : ℝ)+1/2)-(n : ℝ)) = (n : ℝ) * ((n : ℝ)+1) := by ring
  rw [hc] at h
  exact h

/-- The resolvent commutes with every original logarithmic dilation. -/
theorem soninDilationResolvent_commutes (lam : ℝ) (hlam : 0 < lam) (h : ℝ) (f : SoninL2) :
    soninDilationResolvent lam hlam (rayDilate (Real.exp h) f) =
      rayDilate (Real.exp h) (soninDilationResolvent lam hlam f) := by
  simp only [← logDilation_eq]
  change (∫ t in Ioi (0 : ℝ), dampedOrbit lam (logDilation h f) t) =
    logDilation h (∫ t in Ioi (0 : ℝ), dampedOrbit lam f t)
  rw [← (logDilation h).integral_comp_comm (dampedOrbit_integrable lam hlam f 0)]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [dampedOrbit, ContinuousLinearMap.map_smul_of_tower, ← logDilation_add]
  rw [add_comm t h]

end RHTower
