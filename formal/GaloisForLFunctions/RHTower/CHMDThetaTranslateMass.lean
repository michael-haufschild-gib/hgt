import GaloisForLFunctions.RHTower.CHMDFullJumpCoreDensity
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKernelEnergy
import GaloisForLFunctions.RHTower.CHMDTranslatedPrimitiveSource

/-!
# Actual source admission for small theta translations

The translated theta kernel divided by the original kernel lies in the original
theta--cosh L2 space on an open interval of shifts. This is the source-coordinate
admission needed to construct exact critical modes of the complete jump form.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDThetaTranslate
open CHMDDoobGraph HedenmalmThetaSource

def ratio (a x : ℝ) : ℝ := riemannKernelReal (x - a) / riemannKernelReal x

theorem continuous_ratio (a : ℝ) : Continuous (ratio a) :=
  ((CHMDTranslation.continuous_translate continuous_riemannKernelReal a).div
    continuous_riemannKernelReal (fun x => (riemannKernelReal_pos x).ne'))

theorem theta_upper (x : ℝ) :
    riemannKernelReal x ≤ thetaEnvelopeUpper * thetaEnvelope |x| := by
  have h := thetaCuspFullSource_le_envelope (abs_nonneg x)
  rw [thetaCuspFullSource_eq_riemannKernelReal] at h
  simpa only [riemannKernelReal, abs_abs] using h

theorem theta_lower {x : ℝ} (hx : x ≠ 0) :
    thetaEnvelopeLower * thetaEnvelope |x| ≤ riemannKernelReal x := by
  have h := thetaCuspFullSource_ge_envelope (abs_pos.mpr hx)
  rw [thetaCuspFullSource_eq_riemannKernelReal] at h
  simpa only [riemannKernelReal, abs_abs] using h

/-- An analytic domination lemma, retaining a strictly positive cusp exponent. -/
theorem cusp_integrable (b c : ℝ) (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (b * |x| - c * Real.exp (2 * |x|))) := by
  let K := (b + 1) ^ 2 / (8 * c)
  apply (integrable_exp_neg_abs.const_mul (Real.exp K)).mono' (by fun_prop)
  refine Eventually.of_forall fun x => ?_
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hp := Real.pow_div_factorial_le_exp (x := 2 * |x|) (by positivity) 2
  norm_num [Nat.factorial] at hp
  have hk : (b + 1) * |x| - 2 * c * |x| ^ 2 ≤ K := by
    dsimp [K]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (4 * c * |x| - (b + 1))]
  nlinarith [mul_le_mul_of_nonneg_left hp hc.le]

theorem ratio_mass_bound (a x : ℝ) (hx : x ≠ 0) :
    massDensity x * ratio a x ^ 2 ≤
      (thetaEnvelopeUpper ^ 2 / thetaEnvelopeLower * Real.exp (9 * |a|)) *
        Real.exp (5 * |x| - (Real.pi * (2 * Real.exp (-2 * |a|) - 1)) *
          Real.exp (2 * |x|)) := by
  have hU := thetaEnvelopeUpper_pos
  have hL := thetaEnvelopeLower_pos
  have ht := riemannKernelReal_pos x
  have hta := riemannKernelReal_pos (x - a)
  have he := thetaEnvelope_pos |x|
  have he' := thetaEnvelope_pos |x - a|
  have hc : Real.cosh (x / 2) ≤ Real.exp (|x| / 2) := by
    rw [Real.cosh_eq]
    have hp := Real.exp_le_exp.mpr (show x / 2 ≤ |x| / 2 by linarith [le_abs_self x])
    have hm := Real.exp_le_exp.mpr (show -(x / 2) ≤ |x| / 2 by linarith [neg_le_abs x])
    linarith
  have hnum : riemannKernelReal (x-a) ^ 2 * Real.cosh (x/2) ≤
      (thetaEnvelopeUpper * thetaEnvelope |x-a|) ^ 2 * Real.exp (|x|/2) :=
    mul_le_mul (sq_le_sq₀ hta.le (by positivity) |>.mpr (theta_upper (x-a))) hc
      (Real.cosh_pos _).le (sq_nonneg _)
  calc
    _ = riemannKernelReal (x-a) ^ 2 * Real.cosh (x/2) / riemannKernelReal x := by
      unfold massDensity ratio
      field_simp
    _ ≤ ((thetaEnvelopeUpper * thetaEnvelope |x-a|) ^ 2 * Real.exp (|x|/2)) /
        (thetaEnvelopeLower * thetaEnvelope |x|) := by
      exact div_le_div₀ (by positivity) hnum (by positivity) (theta_lower hx)
    _ = (thetaEnvelopeUpper ^ 2 / thetaEnvelopeLower) *
        Real.exp (9 * |x-a| - 4 * |x| -
          Real.pi * (2 * Real.exp (2 * |x-a|) - Real.exp (2 * |x|))) := by
      simp only [thetaEnvelope, mul_pow, ← Real.exp_nat_mul, Real.exp_sub]
      field_simp
      ring_nf
      simp only [← Real.exp_add]
      congr 1
      ring
    _ ≤ (thetaEnvelopeUpper ^ 2 / thetaEnvelopeLower) *
        Real.exp (9 * |a| + (5 * |x| -
          (Real.pi * (2 * Real.exp (-2 * |a|) - 1)) * Real.exp (2 * |x|))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hp : |x-a| ≤ |x| + |a| := abs_sub x a
      have hm : |x| - |a| ≤ |x-a| := by
        have hh := abs_add_le (x-a) a
        simp only [sub_add_cancel] at hh
        linarith
      have he : Real.exp (2 * |x|) * Real.exp (-2 * |a|) ≤ Real.exp (2 * |x-a|) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      nlinarith [Real.pi_pos]
    _ = _ := by rw [Real.exp_add]; ring

/-- Source L2 admission for the actual inverse Doob translate. -/
theorem memLp_ratio {a : ℝ} (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    MemLp (ratio a) 2 massMeasure := by
  rw [memLp_two_iff_integrable_sq (continuous_ratio a).aestronglyMeasurable,
    massMeasure, integrable_weighted_iff volume continuous_massDensity.measurable
      (Eventually.of_forall fun x => (massDensity_pos x).le)]
  apply ((cusp_integrable 5 (Real.pi * (2 * Real.exp (-2 * |a|) - 1))
    (mul_pos Real.pi_pos (by linarith))).const_mul
      (thetaEnvelopeUpper ^ 2 / thetaEnvelopeLower * Real.exp (9 * |a|))).mono'
        (continuous_massDensity.mul ((continuous_ratio a).pow 2)).aestronglyMeasurable
  have hz : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff]
  filter_upwards [hz] with x hx
  change ‖massDensity x * ratio a x ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (massDensity_pos x).le (sq_nonneg _))]
  exact ratio_mass_bound a x hx

def radius : ℝ := Real.log (4 / 3) / 2

theorem radius_pos : 0 < radius := by
  unfold radius
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

theorem small_shift {a : ℝ} (ha : |a| ≤ radius) : 1 < 2 * Real.exp (-2 * |a|) := by
  have he : Real.exp (-2 * radius) = 3 / 4 := by
    unfold radius
    rw [show -2 * (Real.log (4 / 3) / 2) = -Real.log (4 / 3) by ring,
      Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
    norm_num
  have hh := Real.exp_le_exp.mpr (show -2 * radius ≤ -2 * |a| by linarith)
  rw [he] at hh
  linarith

theorem memLp_ratio_small {a : ℝ} (ha : |a| ≤ radius) : MemLp (ratio a) 2 massMeasure :=
  memLp_ratio (small_shift ha)

end RHTower.CHMDThetaTranslate
