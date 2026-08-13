import GaloisForLFunctions.RHTower.Sieve.MaynardLocalPrimePowerLeakage
import GaloisForLFunctions.RHTower.Sieve.CutoffMass

/-!
# Pole-preserving Mellin calibration for Route T

Reference and target windows of different widths cannot have identical Mellin kernels.  The exact
surviving structure is their pole mode: after normalization by width, every adjacent smooth window
has Mellin value one at `s = 1`.  Consequently any target--reference difference annihilates the
zeta pole without erasing the arithmetic contrast between their normalized von Mangoldt masses.

This is the correct common-mode principle behind two-scale calibration.  Away from the pole the
kernel defect remains a quantitative analytic obligation; no false exact-kernel identity is used.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set GaloisForLFunctions.HTGeometry

private theorem integralOn_Ioi_smoothWeight_eq_interval
    {N H : ℝ} (hN : 0 ≤ N) (hH : 0 < H) :
    (∫ x in Ioi (0 : ℝ), smoothWeight N H x) =
      ∫ x in (0 : ℝ)..(N + H), smoothWeight N H x := by
  have hNH : 0 ≤ N + H := by linarith
  have hhead : IntegrableOn (fun x : ℝ => smoothWeight N H x) (Ioc 0 (N + H)) :=
    ((smoothWeight_contDiff N H (n := 0)).continuous).integrableOn_Ioc
  have htail : IntegrableOn (fun x : ℝ => smoothWeight N H x) (Ioi (N + H)) := by
    refine IntegrableOn.congr_fun
      (integrableOn_zero (μ := (volume : Measure ℝ)) (s := Ioi (N + H))) ?_
      measurableSet_Ioi
    intro x hx
    exact (smoothWeight_eq_zero hH (le_of_lt hx)).symm
  have hsplit : Ioc (0 : ℝ) (N + H) ∪ Ioi (N + H) = Ioi 0 :=
    Ioc_union_Ioi_eq_Ioi hNH
  rw [← hsplit, setIntegral_union (by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd hx.2 (not_le.mpr hx')) measurableSet_Ioi hhead htail]
  have hzero : ∫ x in Ioi (N + H), smoothWeight N H x = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    exact smoothWeight_eq_zero hH (le_of_lt hx)
  rw [hzero, add_zero, intervalIntegral.integral_of_le hNH]

private theorem smoothWeight_shift (N H x : ℝ) :
    smoothWeight (N + H) H x = smoothWeight N H (x - H) := by
  unfold smoothWeight
  congr 2
  ring

/-- Adjacent smooth windows have exact physical mass equal to their width. -/
theorem integral_routeTSmoothWindowWeight_eq_width
    {N H : ℝ} (hN : 0 ≤ N) (hH : 0 < H) :
    (∫ x in Ioi (0 : ℝ), routeTSmoothWindowWeight N H x) = H := by
  have hNH : 0 ≤ N + H := by linarith
  have hplus := integrableOn_smoothWeight_Ioi hNH hH
  have hbase := integrableOn_smoothWeight_Ioi hN hH
  change (∫ x in Ioi (0 : ℝ),
    smoothWeight (N + H) H x - smoothWeight N H x) = H
  rw [integral_sub hplus hbase,
    integralOn_Ioi_smoothWeight_eq_interval hNH hH,
    integralOn_Ioi_smoothWeight_eq_interval hN hH]
  have hshift :
      (∫ x in (0 : ℝ)..(N + H + H), smoothWeight (N + H) H x) =
        ∫ x in (-H : ℝ)..(N + H), smoothWeight N H x := by
    calc
      (∫ x in (0 : ℝ)..(N + H + H), smoothWeight (N + H) H x) =
          ∫ x in (0 : ℝ)..(N + H + H), smoothWeight N H (x + (-H)) := by
            apply intervalIntegral.integral_congr
            intro x _hx
            simpa only [sub_eq_add_neg] using smoothWeight_shift N H x
      _ = ∫ x in (-H : ℝ)..(N + H), smoothWeight N H x := by
        simpa only [zero_add, add_assoc, add_neg_cancel, add_zero] using
          (intervalIntegral.integral_comp_add_right
            (f := fun x : ℝ => smoothWeight N H x)
            (a := (0 : ℝ)) (b := N + H + H) (-H))
  rw [hshift]
  have hcont : Continuous fun x : ℝ => smoothWeight N H x :=
    (smoothWeight_contDiff N H (n := 0)).continuous
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hcont.intervalIntegrable (-H) 0) (hcont.intervalIntegrable 0 (N + H))
  rw [← hadd]
  have hone : (∫ x in (-H : ℝ)..0, smoothWeight N H x) = H := by
    calc
      (∫ x in (-H : ℝ)..0, smoothWeight N H x) =
          ∫ _x in (-H : ℝ)..0, (1 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [uIcc_of_le (by linarith : -H ≤ (0 : ℝ))] at hx
            exact smoothWeight_eq_one hH (by linarith [hx.2])
      _ = H := by simp
  rw [hone]
  ring

/-- Mellin transform of an adjacent smooth window at the zeta pole is exactly its width. -/
theorem mellin_routeTSmoothWindowWeight_one
    {N H : ℝ} (hN : 0 ≤ N) (hH : 0 < H) :
    mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ)) 1 = H := by
  rw [mellin]
  simp only [sub_self, Complex.cpow_zero]
  calc
    (∫ t in Ioi (0 : ℝ), (1 : ℂ) • (routeTSmoothWindowWeight N H t : ℂ)) =
        ((∫ t in Ioi (0 : ℝ), routeTSmoothWindowWeight N H t : ℝ) : ℂ) := by
          simp only [one_smul]
          exact integral_ofReal (𝕜 := ℂ)
    _ = (H : ℂ) := by rw [integral_routeTSmoothWindowWeight_eq_width hN hH]

/-- Width-normalized adjacent Mellin kernel. -/
def routeTNormalizedSmoothWindowMellin (N H : ℝ) (s : ℂ) : ℂ :=
  (H : ℂ)⁻¹ *
    mellin (fun x : ℝ => ((routeTSmoothWindowWeight N H x : ℝ) : ℂ)) s

/-- Every normalized adjacent kernel carries the same unit pole mode. -/
theorem routeTNormalizedSmoothWindowMellin_one
    {N H : ℝ} (hN : 0 ≤ N) (hH : 0 < H) :
    routeTNormalizedSmoothWindowMellin N H 1 = 1 := by
  rw [routeTNormalizedSmoothWindowMellin,
    mellin_routeTSmoothWindowWeight_one hN hH]
  exact inv_mul_cancel₀ (by exact_mod_cast hH.ne')

/-- Target--reference subtraction annihilates the pole mode exactly for arbitrary positive widths. -/
theorem routeT_normalized_reference_target_pole_cancel
    {N H R : ℝ} (hN : 0 ≤ N) (hH : 0 < H) (hR : 0 < R) :
    routeTNormalizedSmoothWindowMellin N R 1 -
        routeTNormalizedSmoothWindowMellin N H 1 = 0 := by
  rw [routeTNormalizedSmoothWindowMellin_one hN hR,
    routeTNormalizedSmoothWindowMellin_one hN hH, sub_self]

end RHTower.Sieve
