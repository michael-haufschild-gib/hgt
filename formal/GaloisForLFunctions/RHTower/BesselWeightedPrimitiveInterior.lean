import GaloisForLFunctions.RHTower.BesselWeightedPrimitive
import GaloisForLFunctions.HTGeometry.InteriorIntegrationByParts

/-!
# The weighted Bessel primitive for a weight degenerate at the origin

The bounded-radius primitive was proved for a weight differentiable on the closed radius interval.
Dunster's weight is not: at the origin the inverse coordinate is undefined, so the weight has no
value there, let alone a derivative.

Nothing is lost.  The product being differentiated is the weight against `r J_1(c r)`, and that
second factor vanishes at the origin, so the product is continuous there whatever the weight does.
Integration by parts with interior derivatives then gives the same bound, with the same constant,
and the boundary term at the origin is identically zero.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.RHTower

/-- **The weighted Bessel primitive, for a weight controlled only on the open radius interval.** -/
theorem abs_integral_mul_besselJ0_le_interior {c R M : ℝ} {B B' : ℝ → ℝ}
    (hc : 0 < c) (hR0 : 0 < R) (hR : R ≤ 2)
    (hB : ∀ r ∈ Ioo (0 : ℝ) R, HasDerivAt B (B' r) r)
    (hBc : ContinuousOn B (Ioc (0 : ℝ) R))
    (hB'c : ContinuousOn B' (Ioo (0 : ℝ) R))
    (hMB : ∀ r ∈ Ioc (0 : ℝ) R, |B r| ≤ M)
    (hMB' : ∀ r ∈ Ioc (0 : ℝ) R, |B' r| ≤ M) :
    |∫ r in (0 : ℝ)..R, r * B r * besselJ0 (c * r)| ≤ 648 * M / (c * Real.sqrt c) := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (B R)) (hMB R ⟨hR0, le_rfl⟩)
  -- the antiderivative and its envelope
  have hvc : Continuous fun r : ℝ => r * besselJ1 (c * r) :=
    continuous_id.mul (continuous_besselJ1.comp (continuous_const.mul continuous_id))
  have henv : ∀ r ∈ Icc (0 : ℝ) R, |r * besselJ1 (c * r)| ≤ 216 / Real.sqrt c := by
    intro r hr
    have h := abs_mul_besselJ1_scaled_le hc hr.1
    have hsr : Real.sqrt r ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (le_trans hr.2 hR)
    have hprod : Real.sqrt 2 * Real.sqrt r ≤ 2 := by
      calc Real.sqrt 2 * Real.sqrt r ≤ Real.sqrt 2 * Real.sqrt 2 :=
            mul_le_mul_of_nonneg_left hsr hs2.le
        _ = 2 := hs2sq
    have hstep : 108 * Real.sqrt 2 * Real.sqrt r / Real.sqrt c ≤ 216 / Real.sqrt c := by
      gcongr
      nlinarith [hprod]
    linarith
  have hv : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt (fun s : ℝ => s * besselJ1 (c * s)) (c * r * besselJ0 (c * r)) r :=
    fun r _ => hasDerivAt_mul_besselJ1_scaled c r
  -- continuity of the product up to the origin
  have hcont : ContinuousOn (fun r : ℝ => B r * (r * besselJ1 (c * r))) (Icc 0 R) := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with h | h
    · rw [← h]
      exact GaloisForLFunctions.HTGeometry.continuousWithinAt_mul_of_bounded_of_tendsto_zero
        hR0 hMB hvc (by simp)
    · have hmem : Ioc (0 : ℝ) R ∈ nhdsWithin r (Icc 0 R) := by
        have : Ioc (0 : ℝ) R = Icc 0 R ∩ Ioi 0 := by
          ext y
          simp only [mem_Ioc, mem_inter_iff, mem_Icc, mem_Ioi]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨⟨le_of_lt h1, h2⟩, h1⟩
          · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
        rw [this]
        exact inter_mem_nhdsWithin _ (isOpen_Ioi.mem_nhds h)
      exact ((hBc.mul hvc.continuousOn) r ⟨h, hr.2⟩).mono_of_mem_nhdsWithin hmem
  -- integrability of the two products
  have hi1 : IntervalIntegrable (fun r : ℝ => B' r * (r * besselJ1 (c * r))) volume 0 R := by
    refine GaloisForLFunctions.HTGeometry.intervalIntegrable_of_continuousOn_Ioo_of_bounded
      hR0.le (hB'c.mul hvc.continuousOn) (M := M * (216 / Real.sqrt c)) ?_
    intro r hr
    rw [abs_mul]
    exact mul_le_mul (hMB' r (Ioo_subset_Ioc_self hr)) (henv r (Ioo_subset_Icc_self hr))
      (abs_nonneg _) hM0
  have hi2 : IntervalIntegrable
      (fun r : ℝ => B r * (c * r * besselJ0 (c * r))) volume 0 R := by
    refine GaloisForLFunctions.HTGeometry.intervalIntegrable_of_continuousOn_Ioo_of_bounded
      hR0.le ?_ (M := M * (c * 2)) ?_
    · exact (hBc.mono Ioo_subset_Ioc_self).mul
        (((continuous_const.mul continuous_id).mul
          (continuous_besselJ0'.comp (continuous_const.mul continuous_id))).continuousOn)
    · intro r hr
      rw [abs_mul]
      have hJ : |c * r * besselJ0 (c * r)| ≤ c * 2 := by
        have hcr : (0 : ℝ) ≤ c * r := mul_nonneg hc.le (le_of_lt hr.1)
        have hr2 : r ≤ 2 := le_trans (le_of_lt hr.2) hR
        rw [abs_mul, abs_of_nonneg hcr]
        have h1 := abs_besselJ0_le_one (c * r)
        nlinarith [h1, hcr, hc.le, hr2, abs_nonneg (besselJ0 (c * r)), hr.1]
      exact mul_le_mul (hMB r (Ioo_subset_Ioc_self hr)) hJ (abs_nonneg _) hM0
  -- integration by parts on the interior
  have hIBP := GaloisForLFunctions.HTGeometry.integral_mul_deriv_eq_deriv_mul_interior
    hR0.le hcont hB hv hi1 hi2
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
    exact mul_le_mul (hMB R ⟨hR0, le_rfl⟩) (henv R ⟨hR0.le, le_rfl⟩) (abs_nonneg _) hM0
  have hrest : |∫ r in (0 : ℝ)..R, B' r * (r * besselJ1 (c * r))|
      ≤ M * (216 / Real.sqrt c) * 2 := by
    have hpt : ∀ r ∈ Set.uIoc (0 : ℝ) R, ‖B' r * (r * besselJ1 (c * r))‖
        ≤ M * (216 / Real.sqrt c) := by
      intro r hr
      rw [Set.uIoc_of_le hR0.le] at hr
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hMB' r hr) (henv r ⟨le_of_lt hr.1, hr.2⟩) (abs_nonneg _) hM0
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [Real.norm_eq_abs] at h
    have habs : |R - 0| ≤ 2 := by
      rw [sub_zero, abs_of_nonneg hR0.le]
      exact hR
    have hnn : 0 ≤ M * (216 / Real.sqrt c) := by positivity
    calc |∫ r in (0 : ℝ)..R, B' r * (r * besselJ1 (c * r))|
        ≤ M * (216 / Real.sqrt c) * |R - 0| := h
      _ ≤ M * (216 / Real.sqrt c) * 2 := mul_le_mul_of_nonneg_left habs hnn
  have hcbound : |c * ∫ r in (0 : ℝ)..R, r * B r * besselJ0 (c * r)| ≤ 648 * M / Real.sqrt c := by
    rw [hIBP]
    calc |B R * (R * besselJ1 (c * R)) - 0
            - ∫ r in (0 : ℝ)..R, B' r * (r * besselJ1 (c * r))|
        ≤ |B R * (R * besselJ1 (c * R)) - 0|
            + |∫ r in (0 : ℝ)..R, B' r * (r * besselJ1 (c * r))| := abs_sub _ _
      _ ≤ M * (216 / Real.sqrt c) + M * (216 / Real.sqrt c) * 2 := by
          rw [sub_zero]; linarith [hbdy, hrest]
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

end GaloisForLFunctions.RHTower
