import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# Compact sine-squared peeling pulse

This module formalizes the compact scalar calibration in Okten--Turan,
arXiv:2608.19244v1, equations `(26)`--`(32)` and `(77)`--`(84)`: exact derivative, endpoint
restoration, total variation, vanishing signed response, and conformal normalization.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Sine-squared pulse on its active interval, equation `(27)` or `(77)`. -/
def sineSquaredPulse (a0 u0 tau u : ℝ) : ℝ :=
  a0 * Real.sin (Real.pi * (u - u0) / tau) ^ 2

/-- Analytic velocity of the sine-squared pulse, equation `(28)`. -/
def sineSquaredPulseVelocity (a0 u0 tau u : ℝ) : ℝ :=
  a0 * Real.pi / tau * Real.sin (2 * Real.pi * (u - u0) / tau)

/-- Globally compact version of equation `(27)` or `(77)`, extended by zero off the active
interval. -/
def compactSineSquaredPulse (a0 u0 tau u : ℝ) : ℝ :=
  if u ∈ Icc u0 (u0 + tau) then sineSquaredPulse a0 u0 tau u else 0

/-- Piecewise velocity displayed in equation `(28)`. -/
def compactSineSquaredPulseVelocity (a0 u0 tau u : ℝ) : ℝ :=
  if u ∈ Icc u0 (u0 + tau) then sineSquaredPulseVelocity a0 u0 tau u else 0

@[simp] theorem compactSineSquaredPulse_of_mem {a0 u0 tau u : ℝ}
    (hu : u ∈ Icc u0 (u0 + tau)) :
    compactSineSquaredPulse a0 u0 tau u = sineSquaredPulse a0 u0 tau u := by
  simp [compactSineSquaredPulse, hu]

@[simp] theorem compactSineSquaredPulse_of_not_mem {a0 u0 tau u : ℝ}
    (hu : u ∉ Icc u0 (u0 + tau)) :
    compactSineSquaredPulse a0 u0 tau u = 0 := by
  simp [compactSineSquaredPulse, hu]

/-- The global pulse is supported inside its prescribed compact interval. -/
theorem support_compactSineSquaredPulse_subset (a0 u0 tau : ℝ) :
    Function.support (compactSineSquaredPulse a0 u0 tau) ⊆ Icc u0 (u0 + tau) := by
  intro u hu
  by_contra hmem
  exact hu (compactSineSquaredPulse_of_not_mem hmem)

/-- Equation `(28)`: the displayed velocity is exactly the derivative of the pulse. -/
theorem deriv_sineSquaredPulse (a0 u0 : ℝ) {tau : ℝ} (htau : tau ≠ 0) :
    deriv (sineSquaredPulse a0 u0 tau) = sineSquaredPulseVelocity a0 u0 tau := by
  funext u
  have hinner := by
    have hnum := (hasDerivAt_const u Real.pi).mul ((hasDerivAt_id u).sub_const u0)
    exact hnum.div (hasDerivAt_const u tau) htau
  have hsin := (Real.hasDerivAt_sin (Real.pi * (u - u0) / tau)).comp u hinner
  have h := (hasDerivAt_const u a0).mul (hsin.pow 2)
  rw [sineSquaredPulseVelocity]
  have hd := h.deriv
  have hfun : sineSquaredPulse a0 u0 tau =
      ((fun _ : ℝ => a0) * (Real.sin ∘ fun x => Real.pi * (x - u0) / tau) ^ 2) := by
    funext x
    rfl
  let rawInner : ℝ → ℝ :=
    ((fun _ : ℝ => Real.pi) * (fun x => id x - u0)) / (fun _ : ℝ => tau)
  let rawPulse : ℝ → ℝ := (fun _ : ℝ => a0) * (Real.sin ∘ rawInner) ^ 2
  have hraw : ((fun _ : ℝ => a0) * (Real.sin ∘ fun x => Real.pi * (x - u0) / tau) ^ 2) =
      rawPulse := by
    funext x
    rfl
  rw [hfun, hraw]
  change deriv rawPulse u = _
  rw [show deriv rawPulse u = _ from hd]
  simp only [Function.comp_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply,
    id_eq, zero_mul, zero_add, mul_one, Nat.cast_ofNat]
  have hangle : 2 * Real.pi * (u - u0) / tau =
        2 * (Real.pi * (u - u0) / tau) := by ring
  rw [hangle, Real.sin_two_mul]
  field_simp
  ring

/-- The compact pulse has the displayed derivative away from the two gluing endpoints. -/
theorem deriv_compactSineSquaredPulse_of_ne_endpoints {tau : ℝ} (htau : 0 < tau)
    (a0 u0 u : ℝ) (hstart : u ≠ u0) (hend : u ≠ u0 + tau) :
    deriv (compactSineSquaredPulse a0 u0 tau) u =
      compactSineSquaredPulseVelocity a0 u0 tau u := by
  rcases lt_or_gt_of_ne hstart with hlt | hgt
  · have heq : compactSineSquaredPulse a0 u0 tau =ᶠ[nhds u] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hlt] with x hx
      have hx' : x < u0 := hx
      simp [compactSineSquaredPulse, not_le_of_gt hx']
    rw [heq.deriv_eq]
    simp [compactSineSquaredPulseVelocity, not_le_of_gt hlt]
  · rcases lt_or_gt_of_ne hend with hltEnd | hgtEnd
    · have heq : compactSineSquaredPulse a0 u0 tau =ᶠ[nhds u]
          sineSquaredPulse a0 u0 tau := by
        filter_upwards [Ioo_mem_nhds hgt hltEnd] with x hx
        simp [compactSineSquaredPulse, hx.1.le, hx.2.le]
      rw [heq.deriv_eq, congrFun (deriv_sineSquaredPulse a0 u0 htau.ne') u]
      simp [compactSineSquaredPulseVelocity, hgt.le, hltEnd.le]
    · have heq : compactSineSquaredPulse a0 u0 tau =ᶠ[nhds u] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds hgtEnd] with x hx
        have hx' : u0 + tau < x := hx
        simp [compactSineSquaredPulse, not_le_of_gt hx']
      rw [heq.deriv_eq]
      simp [compactSineSquaredPulseVelocity, not_le_of_gt hgtEnd]

/-- Equation `(28)` holds almost everywhere globally; the only omitted points are the two
measure-zero gluing endpoints. -/
theorem deriv_compactSineSquaredPulse_ae {tau : ℝ} (htau : 0 < tau) (a0 u0 : ℝ) :
    ∀ᵐ u ∂volume, deriv (compactSineSquaredPulse a0 u0 tau) u =
      compactSineSquaredPulseVelocity a0 u0 tau u := by
  have hstart : ∀ᵐ u ∂volume, u ≠ u0 := by simp [ae_iff, measure_singleton]
  have hend : ∀ᵐ u ∂volume, u ≠ u0 + tau := by simp [ae_iff, measure_singleton]
  filter_upwards [hstart, hend] with u hu0 hu1
  exact deriv_compactSineSquaredPulse_of_ne_endpoints htau a0 u0 u hu0 hu1

/-- The compact pulse is differentiable with derivative zero at the initial gluing endpoint. -/
theorem deriv_compactSineSquaredPulse_start {tau : ℝ} (htau : 0 < tau) (a0 u0 : ℝ) :
    deriv (compactSineSquaredPulse a0 u0 tau) u0 = 0 := by
  have hsineDiff : DifferentiableAt ℝ (sineSquaredPulse a0 u0 tau) u0 := by
    unfold sineSquaredPulse
    fun_prop
  have hsine := hsineDiff.hasDerivAt
  rw [congrFun (deriv_sineSquaredPulse a0 u0 htau.ne') u0] at hsine
  have hvel : sineSquaredPulseVelocity a0 u0 tau u0 = 0 := by
    simp [sineSquaredPulseVelocity]
  rw [hvel] at hsine
  have hleft : HasDerivWithinAt (compactSineSquaredPulse a0 u0 tau) 0 (Iic u0) u0 := by
    apply (hasDerivAt_const u0 0).hasDerivWithinAt.congr
    · intro x hx
      by_cases hxu : x = u0
      · subst x
        rw [compactSineSquaredPulse_of_mem ⟨le_rfl, by linarith⟩]
        simp [sineSquaredPulse]
      · have hlt : x < u0 := lt_of_le_of_ne hx hxu
        simp [compactSineSquaredPulse, not_le_of_gt hlt]
    · rw [compactSineSquaredPulse_of_mem ⟨le_rfl, by linarith⟩]
      simp [sineSquaredPulse]
  have hright : HasDerivWithinAt (compactSineSquaredPulse a0 u0 tau) 0
      (Icc u0 (u0 + tau)) u0 := by
    apply hsine.hasDerivWithinAt.congr
    · intro x hx
      simp [compactSineSquaredPulse, hx]
    · exact compactSineSquaredPulse_of_mem ⟨le_rfl, by linarith⟩
  have hunion := hleft.union hright
  have hsets : Iic u0 ∪ Icc u0 (u0 + tau) = Iic (u0 + tau) := by
    ext x
    simp only [mem_union, mem_Iic, mem_Icc]
    constructor
    · rintro (hx | hx)
      · linarith
      · exact hx.2
    · intro hx
      by_cases hxu : x ≤ u0
      · exact Or.inl hxu
      · exact Or.inr ⟨le_of_not_ge hxu, hx⟩
  rw [hsets] at hunion
  have hnhds : Iic (u0 + tau) ∈ nhds u0 :=
    Filter.mem_of_superset (Iio_mem_nhds (by linarith)) Iio_subset_Iic_self
  exact (hunion.hasDerivAt hnhds).deriv

/-- The compact pulse is differentiable with derivative zero at the final gluing endpoint. -/
theorem deriv_compactSineSquaredPulse_end {tau : ℝ} (htau : 0 < tau) (a0 u0 : ℝ) :
    deriv (compactSineSquaredPulse a0 u0 tau) (u0 + tau) = 0 := by
  have hsineDiff : DifferentiableAt ℝ (sineSquaredPulse a0 u0 tau) (u0 + tau) := by
    unfold sineSquaredPulse
    fun_prop
  have hsine := hsineDiff.hasDerivAt
  rw [congrFun (deriv_sineSquaredPulse a0 u0 htau.ne') (u0 + tau)] at hsine
  have hvel : sineSquaredPulseVelocity a0 u0 tau (u0 + tau) = 0 := by
    have harg : 2 * Real.pi * (u0 + tau - u0) / tau = 2 * Real.pi := by
      field_simp
      ring
    rw [sineSquaredPulseVelocity, harg, Real.sin_two_pi]
    ring
  have hpulseEnd : sineSquaredPulse a0 u0 tau (u0 + tau) = 0 := by
    have harg : Real.pi * (u0 + tau - u0) / tau = Real.pi := by
      field_simp
      ring
    rw [sineSquaredPulse, harg, Real.sin_pi]
    ring
  rw [hvel] at hsine
  have hleft : HasDerivWithinAt (compactSineSquaredPulse a0 u0 tau) 0
      (Icc u0 (u0 + tau)) (u0 + tau) := by
    apply hsine.hasDerivWithinAt.congr
    · intro x hx
      simp [compactSineSquaredPulse, hx]
    · exact compactSineSquaredPulse_of_mem ⟨by linarith, le_rfl⟩
  have hright : HasDerivWithinAt (compactSineSquaredPulse a0 u0 tau) 0
      (Ici (u0 + tau)) (u0 + tau) := by
    apply (hasDerivAt_const (u0 + tau) 0).hasDerivWithinAt.congr
    · intro x hx
      by_cases hxe : x = u0 + tau
      · subst x
        rw [compactSineSquaredPulse_of_mem (by constructor <;> linarith), hpulseEnd]
      · have hgt : u0 + tau < x := lt_of_le_of_ne hx (Ne.symm hxe)
        simp [compactSineSquaredPulse, not_le_of_gt hgt]
    · rw [compactSineSquaredPulse_of_mem (by constructor <;> linarith), hpulseEnd]
  have hunion := hleft.union hright
  have hsets : Icc u0 (u0 + tau) ∪ Ici (u0 + tau) = Ici u0 := by
    ext x
    simp only [mem_union, mem_Ici, mem_Icc]
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · linarith
    · intro hx
      by_cases hxe : x ≤ u0 + tau
      · exact Or.inl ⟨hx, hxe⟩
      · exact Or.inr (le_of_not_ge hxe)
  rw [hsets] at hunion
  have hnhds : Ici u0 ∈ nhds (u0 + tau) :=
    Filter.mem_of_superset (Ioi_mem_nhds (by linarith)) Ioi_subset_Ici_self
  exact (hunion.hasDerivAt hnhds).deriv

/-- Equation `(28)` globally, including both gluing endpoints. -/
theorem deriv_compactSineSquaredPulse {tau : ℝ} (htau : 0 < tau) (a0 u0 : ℝ) :
    deriv (compactSineSquaredPulse a0 u0 tau) =
      compactSineSquaredPulseVelocity a0 u0 tau := by
  funext u
  by_cases hstart : u = u0
  · subst u
    rw [deriv_compactSineSquaredPulse_start htau]
    simp [compactSineSquaredPulseVelocity, sineSquaredPulseVelocity]
  · by_cases hend : u = u0 + tau
    · subst u
      rw [deriv_compactSineSquaredPulse_end htau]
      have harg : 2 * Real.pi * (u0 + tau - u0) / tau = 2 * Real.pi := by
        field_simp
        ring
      have hmem : u0 + tau ∈ Icc u0 (u0 + tau) := ⟨by linarith, le_rfl⟩
      rw [compactSineSquaredPulseVelocity, if_pos hmem, sineSquaredPulseVelocity,
        harg, Real.sin_two_pi]
      ring
    · exact deriv_compactSineSquaredPulse_of_ne_endpoints htau a0 u0 u hstart hend

@[simp] theorem sineSquaredPulse_start (a0 u0 tau : ℝ) :
    sineSquaredPulse a0 u0 tau u0 = 0 := by simp [sineSquaredPulse]

@[simp] theorem sineSquaredPulse_mid (a0 u0 : ℝ) {tau : ℝ} (htau : tau ≠ 0) :
    sineSquaredPulse a0 u0 tau (u0 + tau / 2) = a0 := by
  have harg : Real.pi * (u0 + tau / 2 - u0) / tau = Real.pi / 2 := by
    field_simp
    ring
  rw [sineSquaredPulse, harg, Real.sin_pi_div_two]
  ring

@[simp] theorem sineSquaredPulse_end (a0 u0 : ℝ) {tau : ℝ} (htau : tau ≠ 0) :
    sineSquaredPulse a0 u0 tau (u0 + tau) = 0 := by
  have harg : Real.pi * (u0 + tau - u0) / tau = Real.pi := by
    field_simp
    ring
  rw [sineSquaredPulse, harg, Real.sin_pi]
  ring

/-- Pulse amplitude remains between zero and `a0`. -/
theorem sineSquaredPulse_mem_Icc {a0 : ℝ} (ha0 : 0 ≤ a0) (u0 tau u : ℝ) :
    sineSquaredPulse a0 u0 tau u ∈ Icc 0 a0 := by
  have hsinSq : Real.sin (Real.pi * (u - u0) / tau) ^ 2 ≤ 1 := by
    nlinarith [Real.neg_one_le_sin (Real.pi * (u - u0) / tau),
      Real.sin_le_one (Real.pi * (u - u0) / tau)]
  constructor
  · exact mul_nonneg ha0 (sq_nonneg _)
  · simpa [sineSquaredPulse] using mul_le_mul_of_nonneg_left hsinSq ha0

/-- Equation `(78)`: a dipole perturbation smaller than its positive background leaves the full
peeling field positive.  Apply with `z = cos theta`. -/
theorem dipolePeeling_pos {kappaBar a0 a z : ℝ}
    (hbackground : a0 < kappaBar)
    (ha : |a| ≤ a0) (hz : |z| ≤ 1) :
    0 < kappaBar + a * z := by
  have habsMul : |a * z| ≤ a0 := by
    rw [abs_mul]
    calc
      |a| * |z| ≤ |a| * 1 := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      _ = |a| := mul_one _
      _ ≤ a0 := ha
  have hlower : -a0 ≤ a * z := le_trans (neg_le_neg habsMul) (neg_abs_le (a * z))
  linarith

theorem continuous_sineSquaredPulseVelocity (a0 u0 tau : ℝ) :
    Continuous (sineSquaredPulseVelocity a0 u0 tau) := by
  unfold sineSquaredPulseVelocity
  fun_prop

/-- Fundamental-theorem identity for every subinterval of the pulse. -/
theorem integral_sineSquaredPulseVelocity (a0 u0 : ℝ) {tau : ℝ} (htau : tau ≠ 0)
    (a b : ℝ) :
    ∫ u in a..b, sineSquaredPulseVelocity a0 u0 tau u =
      sineSquaredPulse a0 u0 tau b - sineSquaredPulse a0 u0 tau a := by
  apply intervalIntegral.integral_deriv_eq_sub' (sineSquaredPulse a0 u0 tau)
    (deriv_sineSquaredPulse a0 u0 htau)
  · intro x _
    unfold sineSquaredPulse
    fun_prop
  · exact (continuous_sineSquaredPulseVelocity a0 u0 tau).continuousOn

/-- Velocity is nonnegative while the pulse rises. -/
theorem sineSquaredPulseVelocity_nonneg_first_half {a0 tau : ℝ}
    (ha0 : 0 ≤ a0) (htau : 0 < tau) (u0 : ℝ)
    {u : ℝ} (hu : u ∈ Icc u0 (u0 + tau / 2)) :
    0 ≤ sineSquaredPulseVelocity a0 u0 tau u := by
  unfold sineSquaredPulseVelocity
  have hdiff0 : 0 ≤ u - u0 := sub_nonneg.mpr hu.1
  have harg0 : 0 ≤ 2 * Real.pi * (u - u0) / tau := by positivity
  have hargpi : 2 * Real.pi * (u - u0) / tau ≤ Real.pi := by
    apply (div_le_iff₀ htau).2
    calc
      2 * Real.pi * (u - u0) ≤ 2 * Real.pi * (tau / 2) :=
        mul_le_mul_of_nonneg_left (by linarith [hu.2]) (by positivity)
      _ = Real.pi * tau := by ring
  exact mul_nonneg (div_nonneg (mul_nonneg ha0 Real.pi_pos.le) htau.le)
    (Real.sin_nonneg_of_nonneg_of_le_pi harg0 hargpi)

/-- Velocity is nonpositive while the pulse falls. -/
theorem sineSquaredPulseVelocity_nonpos_second_half {a0 tau : ℝ}
    (ha0 : 0 ≤ a0) (htau : 0 < tau) (u0 : ℝ)
    {u : ℝ} (hu : u ∈ Icc (u0 + tau / 2) (u0 + tau)) :
    sineSquaredPulseVelocity a0 u0 tau u ≤ 0 := by
  unfold sineSquaredPulseVelocity
  have hargpi : Real.pi ≤ 2 * Real.pi * (u - u0) / tau := by
    apply (le_div_iff₀ htau).2
    calc
      Real.pi * tau = 2 * Real.pi * (tau / 2) := by ring
      _ ≤ 2 * Real.pi * (u - u0) :=
        mul_le_mul_of_nonneg_left (by linarith [hu.1]) (by positivity)
  have harg2pi : 2 * Real.pi * (u - u0) / tau ≤ 2 * Real.pi := by
    have hdiff : u - u0 ≤ tau := by linarith [hu.2]
    have hmul : 2 * Real.pi * (u - u0) ≤ 2 * Real.pi * tau :=
      mul_le_mul_of_nonneg_left hdiff (by positivity)
    exact (div_le_iff₀ htau).2 hmul
  have hsin : Real.sin (2 * Real.pi * (u - u0) / tau) ≤ 0 := by
    have hz : 0 ≤ 2 * Real.pi - 2 * Real.pi * (u - u0) / tau := sub_nonneg.mpr harg2pi
    have hp : 2 * Real.pi - 2 * Real.pi * (u - u0) / tau ≤ Real.pi := by linarith
    have hnonneg : 0 ≤ Real.sin (2 * Real.pi - 2 * Real.pi * (u - u0) / tau) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hz hp
    rw [Real.sin_two_pi_sub] at hnonneg
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg (mul_nonneg ha0 Real.pi_pos.le) htau.le) hsin

/-- Equations `(31)` and `(83)`: total variation of the pulse is exactly `2 * a0`. -/
theorem integral_abs_sineSquaredPulseVelocity {a0 tau : ℝ}
    (ha0 : 0 ≤ a0) (htau : 0 < tau) (u0 : ℝ) :
    ∫ u in u0..u0 + tau, |sineSquaredPulseVelocity a0 u0 tau u| = 2 * a0 := by
  have hleftOrder : u0 ≤ u0 + tau / 2 := by linarith
  have hrightOrder : u0 + tau / 2 ≤ u0 + tau := by linarith
  have hcontAbs : Continuous (fun u => |sineSquaredPulseVelocity a0 u0 tau u|) :=
    (continuous_sineSquaredPulseVelocity a0 u0 tau).abs
  have hleft : (∫ u in u0..u0 + tau / 2, |sineSquaredPulseVelocity a0 u0 tau u|) =
      ∫ u in u0..u0 + tau / 2, sineSquaredPulseVelocity a0 u0 tau u := by
    apply intervalIntegral.integral_congr
    intro u hu
    change |sineSquaredPulseVelocity a0 u0 tau u| = _
    exact abs_of_nonneg (sineSquaredPulseVelocity_nonneg_first_half ha0 htau u0 (by
      simpa [uIcc_of_le hleftOrder] using hu))
  have hright : (∫ u in u0 + tau / 2..u0 + tau,
      |sineSquaredPulseVelocity a0 u0 tau u|) =
      ∫ u in u0 + tau / 2..u0 + tau, -sineSquaredPulseVelocity a0 u0 tau u := by
    apply intervalIntegral.integral_congr
    intro u hu
    change |sineSquaredPulseVelocity a0 u0 tau u| = _
    exact abs_of_nonpos (sineSquaredPulseVelocity_nonpos_second_half ha0 htau u0 (by
      simpa [uIcc_of_le hrightOrder] using hu))
  calc
    (∫ u in u0..u0 + tau, |sineSquaredPulseVelocity a0 u0 tau u|) =
        (∫ u in u0..u0 + tau / 2, |sineSquaredPulseVelocity a0 u0 tau u|) +
          ∫ u in u0 + tau / 2..u0 + tau,
            |sineSquaredPulseVelocity a0 u0 tau u| :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hcontAbs.intervalIntegrable u0 (u0 + tau / 2))
        (hcontAbs.intervalIntegrable (u0 + tau / 2) (u0 + tau))).symm
    _ = (∫ u in u0..u0 + tau / 2, sineSquaredPulseVelocity a0 u0 tau u) +
          ∫ u in u0 + tau / 2..u0 + tau,
            -sineSquaredPulseVelocity a0 u0 tau u := by rw [hleft, hright]
    _ = (sineSquaredPulse a0 u0 tau (u0 + tau / 2) -
          sineSquaredPulse a0 u0 tau u0) -
          (sineSquaredPulse a0 u0 tau (u0 + tau) -
            sineSquaredPulse a0 u0 tau (u0 + tau / 2)) := by
      rw [intervalIntegral.integral_neg,
        integral_sineSquaredPulseVelocity a0 u0 htau.ne' u0 (u0 + tau / 2),
        integral_sineSquaredPulseVelocity a0 u0 htau.ne' (u0 + tau / 2) (u0 + tau)]
      ring
    _ = 2 * a0 := by
      simp [sineSquaredPulse_mid a0 u0 htau.ne', sineSquaredPulse_end a0 u0 htau.ne']
      ring

/-- Equation `(32)`: equal endpoint values make the signed velocity integral vanish. -/
theorem integral_sineSquaredPulseVelocity_eq_zero {tau : ℝ} (htau : 0 < tau)
    (a0 u0 : ℝ) :
    ∫ u in u0..u0 + tau, sineSquaredPulseVelocity a0 u0 tau u = 0 := by
  rw [integral_sineSquaredPulseVelocity a0 u0 htau.ne' u0 (u0 + tau),
    sineSquaredPulse_start, sineSquaredPulse_end a0 u0 htau.ne', sub_zero]

/-- Conformal defect `C * kappa'`, with `C = cCFT / (24 * pi)` in the paper. -/
def scalarConformalPulseDefect (C a0 u0 tau u : ℝ) : ℝ :=
  C * sineSquaredPulseVelocity a0 u0 tau u

/-- Absolute response of a conformally scaled pulse. -/
theorem integral_abs_scalarConformalPulseDefect {C a0 tau : ℝ}
    (hC : 0 ≤ C) (ha0 : 0 ≤ a0) (htau : 0 < tau) (u0 : ℝ) :
    ∫ u in u0..u0 + tau, |scalarConformalPulseDefect C a0 u0 tau u| =
      2 * C * a0 := by
  have hfun : (fun u => |scalarConformalPulseDefect C a0 u0 tau u|) =
      fun u => C * |sineSquaredPulseVelocity a0 u0 tau u| := by
    funext u
    simp [scalarConformalPulseDefect, abs_mul, abs_of_nonneg hC]
  rw [hfun, intervalIntegral.integral_const_mul,
    integral_abs_sineSquaredPulseVelocity ha0 htau u0]
  ring

/-- Signed conformal response of the restored pulse vanishes. -/
theorem integral_scalarConformalPulseDefect_eq_zero {tau : ℝ} (htau : 0 < tau)
    (C a0 u0 : ℝ) :
    ∫ u in u0..u0 + tau, scalarConformalPulseDefect C a0 u0 tau u = 0 := by
  change ∫ u in u0..u0 + tau, C * sineSquaredPulseVelocity a0 u0 tau u = 0
  rw [intervalIntegral.integral_const_mul,
    integral_sineSquaredPulseVelocity_eq_zero htau a0 u0, mul_zero]

/-- Equation `(31)`: paper normalization of the absolute conformal response. -/
theorem integral_abs_paperConformalPulseDefect {cCFT a0 tau : ℝ}
    (hc : 0 ≤ cCFT) (ha0 : 0 ≤ a0) (htau : 0 < tau) (u0 : ℝ) :
    ∫ u in u0..u0 + tau,
      |scalarConformalPulseDefect (cCFT / (24 * Real.pi)) a0 u0 tau u| =
        cCFT / (12 * Real.pi) * a0 := by
  rw [integral_abs_scalarConformalPulseDefect
    (div_nonneg hc (mul_nonneg (by norm_num) Real.pi_pos.le)) ha0 htau u0]
  field_simp [Real.pi_ne_zero]
  ring

end

end GaloisForLFunctions.HTGeometry
