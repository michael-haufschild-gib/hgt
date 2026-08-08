import GaloisForLFunctions.RHTower.BesselJOneEnvelope

/-!
# The weighted Bessel primitive on a bounded radius

The recurrence `(r J₁(c r))' = c r J₀(c r)` turns a weighted Bessel integral into boundary terms
plus the integral against the derivative of the weight.  Both are controlled by the order-one
envelope, which gives `|r J₁(c r)| ≤ C √r / √c` at every radius: the amplitude bound near the
origin and the decay bound away from it combine into a single estimate with no case split at the
end user's level.

The result is uniform in the endpoint: on a bounded radius range, a `C¹` weight produces a weighted
Bessel integral of size `c^{-3/2}`.  This is the mechanism of the pole-uniform primitive on the
compact parameter interval.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral

theorem continuous_besselJ0 : Continuous besselJ0 :=
  continuous_iff_continuousAt.mpr fun u => (hasDerivAt_besselJ0 u).continuousAt

theorem continuous_besselJ1 : Continuous besselJ1 :=
  continuous_iff_continuousAt.mpr fun u => (hasDerivAt_besselJ1 u).continuousAt

/-- A single square-root envelope for the order-one function, valid at every positive argument:
the amplitude bound covers the origin and the decay bound covers infinity. -/
theorem abs_besselJ1_le_sqrt {u : ℝ} (hu : 0 < u) :
    |besselJ1 u| ≤ 108 * Real.sqrt 2 / Real.sqrt u := by
  rcases le_or_gt 1 u with h | h
  · exact abs_besselJ1_le_envelope h
  · have hsu : Real.sqrt u ≤ 1 := Real.sqrt_le_one.mpr h.le
    have hsupos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
    have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hle : |besselJ1 u| ≤ |u| / 2 := abs_besselJ1_le u
    have habs : |u| = u := abs_of_pos hu
    have hstep : u / 2 ≤ 108 * Real.sqrt 2 / Real.sqrt u := by
      rw [le_div_iff₀ hsupos]
      nlinarith [hsu, hsupos, hs2, h.le, hu.le]
    rw [habs] at hle
    linarith

/-- The weighted order-one function obeys `|r J₁(c r)| ≤ C √r / √c` at every nonnegative radius. -/
theorem abs_mul_besselJ1_scaled_le {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    |r * besselJ1 (c * r)| ≤ 108 * Real.sqrt 2 * Real.sqrt r / Real.sqrt c := by
  rcases eq_or_lt_of_le hr with rfl | hrpos
  · simp [besselJ1_zero]
  · have hcr : 0 < c * r := mul_pos hc hrpos
    have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
    have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hrpos
    have hsplit : Real.sqrt (c * r) = Real.sqrt c * Real.sqrt r := Real.sqrt_mul hc.le r
    have hbase := abs_besselJ1_le_sqrt hcr
    rw [abs_mul, abs_of_nonneg hr]
    calc r * |besselJ1 (c * r)| ≤ r * (108 * Real.sqrt 2 / Real.sqrt (c * r)) := by
          exact mul_le_mul_of_nonneg_left hbase hr
      _ = 108 * Real.sqrt 2 * Real.sqrt r / Real.sqrt c := by
          rw [hsplit]
          have hrs : r = Real.sqrt r * Real.sqrt r := (Real.mul_self_sqrt hr).symm
          field_simp
          nlinarith [hrs, hsr, hsc]

/-- **The weighted Bessel primitive.**  On radii bounded by `2`, a `C¹` weight of size `M` produces
a weighted Bessel integral of size `M c^{-3/2}`, uniformly in the endpoint. -/
theorem abs_integral_mul_besselJ0_le {c R M : ℝ} {B B' : ℝ → ℝ}
    (hc : 0 < c) (hR0 : 0 ≤ R) (hR : R ≤ 2)
    (hB : ∀ r ∈ Set.uIcc (0 : ℝ) R, HasDerivAt B (B' r) r)
    (hB'c : ContinuousOn B' (Set.uIcc (0 : ℝ) R))
    (hMB : ∀ r ∈ Set.uIcc (0 : ℝ) R, |B r| ≤ M)
    (hMB' : ∀ r ∈ Set.uIcc (0 : ℝ) R, |B' r| ≤ M) :
    |∫ r in (0 : ℝ)..R, r * B r * besselJ0 (c * r)| ≤ 648 * M / (c * Real.sqrt c) := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (B 0)) (hMB 0 Set.left_mem_uIcc)
  have huIcc : Set.uIcc (0 : ℝ) R = Set.Icc 0 R := Set.uIcc_of_le hR0
  have hmem : ∀ r ∈ Set.uIcc (0 : ℝ) R, 0 ≤ r ∧ r ≤ R := by
    intro r hr
    rw [huIcc] at hr
    exact ⟨hr.1, hr.2⟩
  -- the pointwise envelope of the antiderivative, uniform on the radius range
  have henv : ∀ r ∈ Set.uIcc (0 : ℝ) R, |r * besselJ1 (c * r)| ≤ 216 / Real.sqrt c := by
    intro r hr
    obtain ⟨hr0, hrR⟩ := hmem r hr
    have h := abs_mul_besselJ1_scaled_le hc hr0
    have hsr : Real.sqrt r ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (le_trans hrR hR)
    have hprod : Real.sqrt 2 * Real.sqrt r ≤ 2 := by
      calc Real.sqrt 2 * Real.sqrt r ≤ Real.sqrt 2 * Real.sqrt 2 :=
            mul_le_mul_of_nonneg_left hsr hs2.le
        _ = 2 := hs2sq
    have hstep : 108 * Real.sqrt 2 * Real.sqrt r / Real.sqrt c ≤ 216 / Real.sqrt c := by
      gcongr
      nlinarith [hprod]
    linarith
  -- integration by parts against the exact antiderivative
  have hv : ∀ r ∈ Set.uIcc (0 : ℝ) R,
      HasDerivAt (fun s : ℝ => s * besselJ1 (c * s)) (c * r * besselJ0 (c * r)) r :=
    fun r _ => hasDerivAt_mul_besselJ1_scaled c r
  have hiB' : IntervalIntegrable B' volume 0 R := hB'c.intervalIntegrable
  have hiv : IntervalIntegrable (fun r : ℝ => c * r * besselJ0 (c * r)) volume 0 R :=
    ((continuous_const.mul continuous_id).mul
      (continuous_besselJ0.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul hB hv hiB' hiv
  have hzero : B 0 * (0 * besselJ1 (c * 0)) = 0 := by ring
  rw [hzero] at hIBP
  -- the left side is `c` times the integral of interest
  have hleft : (∫ r in (0 : ℝ)..R, B r * (c * r * besselJ0 (c * r)))
      = c * ∫ r in (0 : ℝ)..R, r * B r * besselJ0 (c * r) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun r _ => ?_
    ring
  rw [hleft] at hIBP
  -- bound the boundary term and the remaining integral
  have hbdy : |B R * (R * besselJ1 (c * R))| ≤ M * (216 / Real.sqrt c) := by
    rw [abs_mul]
    exact mul_le_mul (hMB R Set.right_mem_uIcc) (henv R Set.right_mem_uIcc) (abs_nonneg _) hM0
  have hrest : |∫ r in (0 : ℝ)..R, B' r * (r * besselJ1 (c * r))|
      ≤ M * (216 / Real.sqrt c) * 2 := by
    have hpt : ∀ r ∈ Set.uIoc (0 : ℝ) R, ‖B' r * (r * besselJ1 (c * r))‖
        ≤ M * (216 / Real.sqrt c) := by
      intro r hr
      have hr' : r ∈ Set.uIcc (0 : ℝ) R := Set.uIoc_subset_uIcc hr
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hMB' r hr') (henv r hr') (abs_nonneg _) hM0
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [Real.norm_eq_abs] at h
    have habs : |R - 0| ≤ 2 := by
      rw [sub_zero, abs_of_nonneg hR0]
      exact hR
    have hnn : 0 ≤ M * (216 / Real.sqrt c) := by positivity
    calc |∫ r in (0 : ℝ)..R, B' r * (r * besselJ1 (c * r))|
        ≤ M * (216 / Real.sqrt c) * |R - 0| := h
      _ ≤ M * (216 / Real.sqrt c) * 2 := by exact mul_le_mul_of_nonneg_left habs hnn
  have hcbound : |c * ∫ r in (0 : ℝ)..R, r * B r * besselJ0 (c * r)| ≤ 648 * M / Real.sqrt c := by
    rw [hIBP]
    have hz : B R * (R * besselJ1 (c * R)) - 0 = B R * (R * besselJ1 (c * R)) := by ring
    calc |B R * (R * besselJ1 (c * R)) - 0
            - ∫ r in (0 : ℝ)..R, B' r * (r * besselJ1 (c * r))|
        ≤ |B R * (R * besselJ1 (c * R)) - 0|
            + |∫ r in (0 : ℝ)..R, B' r * (r * besselJ1 (c * r))| := abs_sub _ _
      _ ≤ M * (216 / Real.sqrt c) + M * (216 / Real.sqrt c) * 2 := by
          rw [hz]; linarith [hbdy, hrest]
      _ = 648 * M / Real.sqrt c := by field_simp; ring
  rw [abs_mul, abs_of_pos hc] at hcbound
  have hfinal : |∫ r in (0 : ℝ)..R, r * B r * besselJ0 (c * r)| * (c * Real.sqrt c)
      ≤ 648 * M := by
    have h1 := mul_le_mul_of_nonneg_right hcbound hsc.le
    rw [div_mul_cancel₀ _ hsc.ne'] at h1
    calc |∫ r in (0 : ℝ)..R, r * B r * besselJ0 (c * r)| * (c * Real.sqrt c)
        = c * |∫ r in (0 : ℝ)..R, r * B r * besselJ0 (c * r)| * Real.sqrt c := by ring
      _ ≤ 648 * M := h1
  exact (le_div_iff₀ (by positivity)).mpr hfinal

/-- A single square-root envelope for the order-zero function, valid at every positive argument:
the bound `|J_0| ≤ 1` covers the origin and the decay bound covers infinity. -/
theorem abs_besselJ0_le_sqrt {u : ℝ} (hu : 0 < u) :
    |besselJ0 u| ≤ 72 * Real.sqrt 2 / Real.sqrt u := by
  rcases le_or_gt 1 u with h | h
  · exact abs_besselJ0_le_envelope h
  · have hsu : Real.sqrt u ≤ 1 := Real.sqrt_le_one.mpr h.le
    have hsupos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
    have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hstep : (1 : ℝ) ≤ 72 * Real.sqrt 2 / Real.sqrt u := by
      rw [le_div_iff₀ hsupos]
      nlinarith [hsu, hsupos, hs2]
    exact le_trans (abs_besselJ0_le_one u) hstep

/-- **The Bessel envelope integral.**  On radii bounded by `2`, the absolute weighted Bessel
integrand has integral of size `c^{-1/2}`.  This is the majorant that the exterior channels are
summed against. -/
theorem integral_abs_mul_besselJ0_le {c R M : ℝ} {B : ℝ → ℝ}
    (hc : 0 < c) (hR0 : 0 ≤ R) (hR : R ≤ 2)
    (hBc : ContinuousOn B (Set.uIcc (0 : ℝ) R))
    (hMB : ∀ r ∈ Set.uIcc (0 : ℝ) R, |B r| ≤ M) :
    (∫ r in (0 : ℝ)..R, |r * B r * besselJ0 (c * r)|) ≤ 288 * M / Real.sqrt c := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (B 0)) (hMB 0 Set.left_mem_uIcc)
  have huIcc : Set.uIcc (0 : ℝ) R = Set.Icc 0 R := Set.uIcc_of_le hR0
  have hint : IntervalIntegrable (fun r : ℝ => |r * B r * besselJ0 (c * r)|) volume 0 R := by
    refine (ContinuousOn.abs ?_).intervalIntegrable
    exact (continuousOn_id.mul hBc).mul
      (continuous_besselJ0.comp_continuousOn (continuousOn_const.mul continuousOn_id))
  have hpt : ∀ r ∈ Set.Icc (0 : ℝ) R, |r * B r * besselJ0 (c * r)| ≤ 144 * M / Real.sqrt c := by
    intro r hr
    have hrmem : r ∈ Set.uIcc (0 : ℝ) R := huIcc ▸ hr
    rcases eq_or_lt_of_le hr.1 with rfl | hrpos
    · simpa using by positivity
    · have hcr : 0 < c * r := mul_pos hc hrpos
      have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hrpos
      have hsrle : Real.sqrt r ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (le_trans hr.2 hR)
      have hsplit : Real.sqrt (c * r) = Real.sqrt c * Real.sqrt r := Real.sqrt_mul hc.le r
      have hJ := abs_besselJ0_le_sqrt hcr
      have hB := hMB r hrmem
      have hchain : r * |B r| * |besselJ0 (c * r)|
          ≤ r * M * (72 * Real.sqrt 2 / (Real.sqrt c * Real.sqrt r)) := by
        rw [← hsplit]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hB hr.1) hJ (abs_nonneg _)
          (by positivity)
      have hval : r * M * (72 * Real.sqrt 2 / (Real.sqrt c * Real.sqrt r))
          = 72 * Real.sqrt 2 * Real.sqrt r * M / Real.sqrt c := by
        have hrs : r = Real.sqrt r * Real.sqrt r := (Real.mul_self_sqrt hr.1).symm
        field_simp
        nlinarith [hrs, hsr, hsc]
      have hfin : 72 * Real.sqrt 2 * Real.sqrt r * M / Real.sqrt c ≤ 144 * M / Real.sqrt c := by
        gcongr
        nlinarith [hsrle, hs2sq, hs2, hM0]
      rw [abs_mul, abs_mul, abs_of_nonneg hr.1]
      rw [hval] at hchain
      linarith [hchain, hfin]
  have hmono : (∫ r in (0 : ℝ)..R, |r * B r * besselJ0 (c * r)|)
      ≤ ∫ _r in (0 : ℝ)..R, 144 * M / Real.sqrt c :=
    intervalIntegral.integral_mono_on hR0 hint intervalIntegrable_const hpt
  have hconst : (∫ _r in (0 : ℝ)..R, 144 * M / Real.sqrt c) = R * (144 * M / Real.sqrt c) := by
    simp
    ring
  rw [hconst] at hmono
  have hstep : R * (144 * M / Real.sqrt c) ≤ 288 * M / Real.sqrt c := by
    have hnn : 0 ≤ 144 * M / Real.sqrt c := by positivity
    calc R * (144 * M / Real.sqrt c) ≤ 2 * (144 * M / Real.sqrt c) :=
          mul_le_mul_of_nonneg_right hR hnn
      _ = 288 * M / Real.sqrt c := by ring
  linarith


end GaloisForLFunctions.RHTower
