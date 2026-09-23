import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Jensen sandwich for a shifted resolvent and the recession bound

For a nonnegative spectral law, the resolvent mean at a positive shift is trapped between the
reciprocal of the shift and the reciprocal of the shift plus the spectral mean.  The upper bound is
pointwise; the lower bound is the supporting line of the convex reciprocal at the mean, whose
defect is the exact square `(x - m)²/[(x+r)(m+r)²]`.

Applying the upper bound to the even response and the lower bound to the odd one turns target
identification into an explicit bound on the negative part of the shift.  The rearrangement is
algebra, and when the negative part diverges both sides of the sandwich become asymptotically equal,
so the parity Cayley scalar collapses to zero.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## `(295)`: the sandwich -/

/-- The supporting line of the convex reciprocal, with its exact square defect. -/
theorem tangentLine_inv_le {x m r : ℝ} (hx : 0 < x + r) (hm : 0 < m + r) :
    1 / (m + r) - (x - m) / (m + r) ^ (2 : ℕ) ≤ 1 / (x + r) := by
  have hkey : 1 / (x + r) - (1 / (m + r) - (x - m) / (m + r) ^ (2 : ℕ))
      = (x - m) ^ (2 : ℕ) / ((x + r) * (m + r) ^ (2 : ℕ)) := by
    field_simp
    ring
  nlinarith [hkey, div_nonneg (sq_nonneg (x - m))
    (le_of_lt (by positivity : (0 : ℝ) < (x + r) * (m + r) ^ (2 : ℕ)))]

/-- **`(295)`, upper half: the resolvent mean is at most the reciprocal of the shift.** -/
theorem integral_inv_shift_le {ν : Measure ℝ} [IsProbabilityMeasure ν] {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ᵐ x ∂ν, 0 ≤ x) (hint : Integrable (fun x => 1 / (x + r)) ν) :
    (∫ x, 1 / (x + r) ∂ν) ≤ 1 / r := by
  have hmono : ∫ x, 1 / (x + r) ∂ν ≤ ∫ _x : ℝ, 1 / r ∂ν := by
    refine integral_mono_ae hint (integrable_const _) ?_
    filter_upwards [hsupp] with x hx
    have h1 : (0 : ℝ) < x + r := by linarith
    rw [div_le_div_iff₀ h1 hr]
    linarith
  rw [integral_const] at hmono
  simpa using hmono

/-- **`(295)`, lower half: the resolvent mean is at least the reciprocal of the shifted spectral
mean.** -/
theorem inv_shift_mean_le_integral {ν : Measure ℝ} [IsProbabilityMeasure ν] {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ᵐ x ∂ν, 0 ≤ x) (hid : Integrable (fun x : ℝ => x) ν)
    (hint : Integrable (fun x => 1 / (x + r)) ν) :
    1 / (r + ∫ x, x ∂ν) ≤ ∫ x, 1 / (x + r) ∂ν := by
  set m : ℝ := ∫ x, x ∂ν with hm
  have hm0 : 0 ≤ m := by
    rw [hm]
    exact integral_nonneg_of_ae hsupp
  have hmr : (0 : ℝ) < m + r := by linarith
  have hlow : ∫ x, (1 / (m + r) - (x - m) / (m + r) ^ (2 : ℕ)) ∂ν ≤ ∫ x, 1 / (x + r) ∂ν := by
    refine integral_mono_ae ?_ hint ?_
    · exact (integrable_const _).sub (((hid.sub (integrable_const m))).div_const _)
    · filter_upwards [hsupp] with x hx
      have h1 : (0 : ℝ) < x + r := by linarith
      exact tangentLine_inv_le h1 hmr
  have hval : ∫ x, (1 / (m + r) - (x - m) / (m + r) ^ (2 : ℕ)) ∂ν = 1 / (m + r) := by
    have hf : Integrable (fun x : ℝ => (x - m) / (m + r) ^ (2 : ℕ)) ν :=
      (hid.sub (integrable_const m)).div_const _
    have hz : ∫ x : ℝ, (x - m) / (m + r) ^ (2 : ℕ) ∂ν = 0 := by
      rw [integral_div, integral_sub hid (integrable_const m), integral_const]
      simp [hm]
    rw [integral_sub (integrable_const _) hf, hz, integral_const]
    simp
  rw [hval] at hlow
  rw [add_comm r m]
  exact hlow

/-! ## `(297)`: the recession bound -/

/-- **`(297)`: the negative part of the shift is bounded by the rearranged sandwich.** -/
theorem recession_le {R Ne No M r : ℝ} (hr : 0 < r) (hNe : 0 < Ne) (hNo : 0 < No)
    (h : R ≤ Ne / No * (1 + M / r)) (hgt : 1 < R * No / Ne) :
    r ≤ M / (R * No / Ne - 1) := by
  have hstep : R * No / Ne ≤ 1 + M / r := by
    have hmul : R * (No / Ne) ≤ (Ne / No * (1 + M / r)) * (No / Ne) :=
      mul_le_mul_of_nonneg_right h (by positivity)
    have hcancel : (Ne / No * (1 + M / r)) * (No / Ne) = 1 + M / r := by
      field_simp
    rw [hcancel] at hmul
    calc R * No / Ne = R * (No / Ne) := by ring
      _ ≤ 1 + M / r := hmul
  have hD : 0 < R * No / Ne - 1 := by linarith
  have hMr : R * No / Ne - 1 ≤ M / r := by linarith
  rw [le_div_iff₀ hD]
  have hmul2 : (R * No / Ne - 1) * r ≤ M / r * r := mul_le_mul_of_nonneg_right hMr hr.le
  rw [div_mul_cancel₀ _ (ne_of_gt hr)] at hmul2
  linarith

/-! ## `(298)`: the parity Cayley scalar collapses -/

/-- **`(298)`: when the two parity responses have ratio tending to one, the parity Cayley scalar
tends to zero.** -/
theorem tendsto_cayley_zero_of_ratio_one {E O : ℕ → ℝ} (hO : ∀ j, O j ≠ 0)
    (h : Tendsto (fun j => E j / O j) atTop (𝓝 1)) :
    Tendsto (fun j => (E j - O j) / (E j + O j)) atTop (𝓝 0) := by
  have hrw : ∀ j, (E j - O j) / (E j + O j) = (E j / O j - 1) / (E j / O j + 1) := by
    intro j
    have hOj := hO j
    rcases eq_or_ne (E j + O j) 0 with hz | hz
    · have h1 : E j / O j + 1 = 0 := by
        rw [div_add_one hOj, hz, zero_div]
      rw [hz, h1, div_zero, div_zero]
    · field_simp
  have hlim : Tendsto (fun j => (E j / O j - 1) / (E j / O j + 1)) atTop (𝓝 ((1 - 1) / (1 + 1))) :=
    (h.sub tendsto_const_nhds).div (h.add tendsto_const_nhds) (by norm_num)
  have hzero : ((1 : ℝ) - 1) / (1 + 1) = 0 := by norm_num
  rw [hzero] at hlim
  exact hlim.congr fun j => (hrw j).symm

end GaloisForLFunctions.RHTower
