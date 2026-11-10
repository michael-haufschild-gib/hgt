import GaloisForLFunctions.HyperbolicArakelovTheory.TheGreenDampingOnSmoothProbes
import GaloisForLFunctions.BiScaleUncertainty.CompactCorrelationDerivativeBounds

/-!
# Ordered Sobolev control of hyperbolic Green damping

Removing the Green self-energy leaves an increasing jump energy. Its deficit
from the critical Lévy energy is nonnegative and at most
`(1-r²) ∫ |f'|² / 2`. The constant is independent of the packet and its support.
The estimate follows from `sinh t ≥ t` and the translation derivative bound.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped CompactlySupported

namespace GaloisForLFunctions.HyperbolicArakelovTheory
open SurfaceOfSpecZ _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.ArchimedeanExactForm

private theorem positive_kernel_error {r d : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hd : 0 < d) :
    d ^ 2 * (Real.exp (-d / 2) / (1 - Real.exp (-2 * d)) -
      Real.exp (-d / 2) / (1 - r ^ 2 * Real.exp (-2 * d))) ≤
      (1 - r ^ 2) / 4 * Real.exp (-d / 2) := by
  let a := Real.exp (-d)
  have ha : 0 < a := Real.exp_pos _
  have ha2 : a ^ 2 = Real.exp (-2 * d) := by
    dsimp only [a]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have ha1 : a ^ 2 < 1 := by
    rw [ha2, Real.exp_lt_one_iff]
    linarith only [hd]
  have hD : 0 < 1 - a ^ 2 := sub_pos.mpr ha1
  have hr2 : r ^ 2 < 1 := by
    nlinarith only [hr1, mul_nonneg hr0 (sub_pos.mpr hr1).le]
  have hDD : 1 - a ^ 2 ≤ 1 - r ^ 2 * a ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hr2.le) (sq_nonneg a)]
  have hDr := hD.trans_le hDD
  have hc : a * Real.exp d = 1 := by
    dsimp only [a]
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hden : 2 * a * Real.sinh d = 1 - a ^ 2 := by
    rw [Real.sinh_eq]
    change 2 * a * ((Real.exp d - a) / 2) = _
    nlinarith only [hc]
  have hlin : 2 * a * d ≤ 1 - a ^ 2 := by
    rw [← hden]
    exact mul_le_mul_of_nonneg_left (Real.self_le_sinh_iff.mpr hd.le) (by positivity)
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * a * d) hlin 2
  have hprod : 4 * d ^ 2 * a ^ 2 ≤ (1 - a ^ 2) * (1 - r ^ 2 * a ^ 2) := by
    have hsq : 4 * d ^ 2 * a ^ 2 ≤ (1 - a ^ 2) ^ 2 := by nlinarith only [hs]
    exact hsq.trans (by simpa only [pow_two] using mul_le_mul_of_nonneg_left hDD hD.le)
  have hquot : d ^ 2 * a ^ 2 / ((1 - a ^ 2) * (1 - r ^ 2 * a ^ 2)) ≤ 1 / 4 := by
    apply (div_le_iff₀ (mul_pos hD hDr)).mpr
    nlinarith only [hprod]
  rw [← ha2]
  calc
    _ = (1 - r ^ 2) * Real.exp (-d / 2) *
        (d ^ 2 * a ^ 2 / ((1 - a ^ 2) * (1 - r ^ 2 * a ^ 2))) := by
      rw [div_sub_div _ _ hD.ne' hDr.ne']
      ring
    _ ≤ (1 - r ^ 2) * Real.exp (-d / 2) * (1 / 4) :=
      mul_le_mul_of_nonneg_left hquot (mul_nonneg (sub_nonneg.mpr hr2.le) (Real.exp_pos _).le)
    _ = _ := by ring

/-- Multiplication by squared distance removes the critical singularity uniformly in damping. -/
theorem sq_mul_archProfile_sub_archDamped_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (x : ℝ) :
    x ^ 2 * (archProfile |x| - archDamped r x) ≤
      (1 - r ^ 2) / 4 * Real.exp (-|x| / 2) := by
  by_cases hx : x = 0
  · subst x
    simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, abs_zero, neg_zero, zero_div,
      Real.exp_zero, mul_one]
    have hr2 : r ^ 2 < 1 := by
      nlinarith only [hr1, mul_nonneg hr0 (sub_pos.mpr hr1).le]
    positivity
  · simpa only [sq_abs, archProfile, archDamped] using
      positive_kernel_error hr0 hr1 (abs_pos.mpr hx)

/-- The renormalized Green energy written as a convergent jump integral. -/
def dampedJumpEnergy (r : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ x, archDamped r x * (autocorr f 0 - autocorr f x)

private theorem deficit_nonneg {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (x : ℝ) : 0 ≤ autocorr f 0 - autocorr f x := by
  have h : (0 : ℝ) ≤ ∫ u, (f u - f (u + x)) ^ 2 :=
    integral_nonneg (fun u : ℝ => sq_nonneg (f u - f (u + x)))
  rw [integral_sub_shift_sq hfc hf] at h
  linarith only [h]

theorem integrable_dampedJump {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Integrable (fun x => archDamped r x * (autocorr f 0 - autocorr f x)) := by
  have hg : Integrable (autocorr f) := (continuous_autocorr hf hfc).integrable_of_hasCompactSupport
    (hasCompactSupport_autocorr hfc)
  have hKg : Integrable (fun x => archDamped r x * autocorr f x) :=
    hg.bdd_mul (c := (1 - r ^ 2)⁻¹) (continuous_archDamped hr0 hr1).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (archDamped_nonneg hr0 hr1 x)]
        exact archDamped_le_inv hr0 hr1 x)
  convert ((integrable_archDamped hr0 hr1).const_mul (autocorr f 0)).sub hKg using 1
  ext x
  simp only [Pi.sub_apply]
  ring

theorem dampedJumpEnergy_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    dampedJumpEnergy r f = selfEnergy r * (∫ u, f u ^ 2) - smoothGreenEnergy r f := by
  have hg : Integrable (autocorr f) := (continuous_autocorr hf hfc).integrable_of_hasCompactSupport
    (hasCompactSupport_autocorr hfc)
  have h := integral_archDamped_mul_eq hr0 hr1 hg
  have hz : autocorr f 0 = ∫ u, f u ^ 2 := by simp only [autocorr, add_zero, pow_two]
  change smoothGreenEnergy r f = autocorr f 0 * selfEnergy r - dampedJumpEnergy r f at h
  rw [hz] at h
  linarith only [h]

/-- The critical energy is approached from below with an explicit derivative-energy error. -/
theorem levyEnergy_sub_dampedJump_bounds (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 ≤ levyEnergy f - dampedJumpEnergy r f ∧
      levyEnergy f - dampedJumpEnergy r f ≤
        (1 - r ^ 2) / 2 * ∫ u, (deriv (f : ℝ → ℝ) u) ^ 2 := by
  let H := ∫ u, (deriv (f : ℝ → ℝ) u) ^ 2
  have hH : 0 ≤ H := integral_nonneg fun _ => sq_nonneg _
  have hr2 : r ^ 2 < 1 := by
    nlinarith only [hr1, mul_nonneg hr0 (sub_pos.mpr hr1).le]
  let E := fun x => (archProfile |x| - archDamped r x) * (autocorr f 0 - autocorr f x)
  have hE : Integrable E := by
    convert (smoothGreen_deficit f hf f.hasCompactSupport).1.sub
      (integrable_dampedJump hf f.hasCompactSupport hr0 hr1) using 1
    ext x
    exact sub_mul _ _ _
  have heq : (∫ x, E x) = levyEnergy f - dampedJumpEnergy r f := by
    simp only [E, sub_mul]
    rw [integral_sub (smoothGreen_deficit f hf f.hasCompactSupport).1
      (integrable_dampedJump hf f.hasCompactSupport hr0 hr1),
      (smoothGreen_deficit f hf f.hasCompactSupport).2]
    rfl
  have hnn (x : ℝ) : 0 ≤ E x := by
    by_cases hx : x = 0
    · subst x; simp only [E, sub_self, mul_zero, le_refl]
    · exact mul_nonneg (sub_nonneg.mpr (archDamped_le_archProfile hr0 hr1.le hx))
        (deficit_nonneg f.continuous f.hasCompactSupport x)
  have hbound (x : ℝ) : E x ≤ (1 - r ^ 2) * H / 8 * Real.exp (-(1 / 2 * |x|)) := by
    by_cases hx : x = 0
    · subst x
      simp only [E, sub_self, mul_zero]
      positivity
    have hker : 0 ≤ archProfile |x| - archDamped r x :=
      sub_nonneg.mpr (archDamped_le_archProfile hr0 hr1.le hx)
    have hd := BiScaleUncertainty.autocorr_origin_deficit_le_derivative_energy f hf x
    have hmul := mul_le_mul_of_nonneg_left hd hker
    have hk := mul_le_mul_of_nonneg_right (sq_mul_archProfile_sub_archDamped_le hr0 hr1 x) hH
    have hex : -(1 / 2 * |x|) = -|x| / 2 := by ring
    rw [hex]
    dsimp only [E]
    change _ ≤ x ^ 2 * H at hd
    nlinarith only [hmul, hk]
  have hmajor := (integrable_exp_neg_mul_abs (a := 1 / 2) (by norm_num)).const_mul
    ((1 - r ^ 2) * H / 8)
  constructor
  · rw [← heq]; exact integral_nonneg hnn
  · have h := integral_mono hE hmajor hbound
    rw [heq, integral_const_mul,
      SurfaceOfSpecZ.integral_exp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 2)] at h
    change _ ≤ (1 - r ^ 2) / 2 * H
    nlinarith only [h]

theorem archDamped_mono {r s : ℝ} (hr0 : 0 ≤ r) (hrs : r ≤ s) (hs1 : s < 1)
    (x : ℝ) : archDamped r x ≤ archDamped s x := by
  have hs0 := hr0.trans hrs
  have hs2 : s ^ 2 < 1 := by
    nlinarith only [hs1, mul_nonneg hs0 (sub_pos.mpr hs1).le]
  have hrs2 := pow_le_pow_left₀ hr0 hrs 2
  have he0 := (Real.exp_pos (-2 * |x|)).le
  have he1 : Real.exp (-2 * |x|) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith only [abs_nonneg x])
  have hden : 0 < 1 - s ^ 2 * Real.exp (-2 * |x|) := by
    nlinarith only [hs2, mul_le_mul_of_nonneg_left he1 (sq_nonneg s)]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hden
    (by nlinarith only [mul_le_mul_of_nonneg_right hrs2 he0])

/-- Damping orders the renormalized energies, despite the divergence of the separate masses. -/
theorem dampedJumpEnergy_mono {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {r s : ℝ} (hr0 : 0 ≤ r) (hrs : r ≤ s) (hs1 : s < 1) :
    dampedJumpEnergy r f ≤ dampedJumpEnergy s f := by
  exact integral_mono (integrable_dampedJump hf hfc hr0 (hrs.trans_lt hs1))
    (integrable_dampedJump hf hfc (hr0.trans hrs) hs1) fun x =>
      mul_le_mul_of_nonneg_right (archDamped_mono hr0 hrs hs1 x)
        (deficit_nonneg hf.continuous hfc x)

#print axioms sq_mul_archProfile_sub_archDamped_le
#print axioms levyEnergy_sub_dampedJump_bounds
#print axioms dampedJumpEnergy_mono

end GaloisForLFunctions.HyperbolicArakelovTheory
