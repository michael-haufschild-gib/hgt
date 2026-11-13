import GaloisForLFunctions.HTGeometry.HardyBoundary.DiskMultiplierInnerDelay
import GaloisForLFunctions.HTGeometry.HardyBoundary.NegativeHalfLineLaplaceHardy
import GaloisForLFunctions.HTGeometry.HardyBoundary.BoundedHardyDelayDivision
import GaloisForLFunctions.HTGeometry.HardyBoundary.HardyDelaySupportGap
import GaloisForLFunctions.HTGeometry.DiskMultiplierAlgebra

/-!
# Endpoint support and boundary nonvanishing force Laplace outerness

The only possible inner factor is a pure delay. Its removal is a bounded Hardy
quotient, so Plancherel forces an endpoint support gap unless the delay vanishes.
-/

noncomputable section
open Complex MeasureTheory Metric Set Filter Topology
open _root_.RHTower

namespace GaloisForLFunctions.HTGeometry

/-- A constant nonzero canonical inner factor leaves an outer multiplier. -/
theorem isOuterDiskMultiplier_of_innerFactor_constant (φ : DiskMultiplier)
    (hφ : ∃ z ∈ ball (0 : ℂ) 1, φ.fn z ≠ 0)
    {c : ℂ} (hc : c ≠ 0)
    (he : ∀ z ∈ ball (0 : ℂ) 1, (diskMultiplierInnerFactor φ hφ).fn z = c) :
    IsOuterDiskMultiplier φ := by
  have hI : IsOuterDiskMultiplier (diskMultiplierInnerFactor φ hφ) := by
    apply cyclicSubspace_hardyOf_eq_top (ψ := DiskMultiplier.const c⁻¹)
    intro z hz
    rw [he z hz, DiskMultiplier.const_fn, mul_inv_cancel₀ hc]
  have hprod := hI.mul (isOuterDiskMultiplier_diskMultiplierOuterFactor φ hφ)
  have hvec : hardyOf ((diskMultiplierInnerFactor φ hφ).mul
      (diskMultiplierOuterFactor φ hφ)) = hardyOf φ :=
    hardyOf_innerFactor_mul_outerFactor φ hφ
  change cyclicSubspace (hardyOf _) = ⊤ at hprod
  change cyclicSubspace (hardyOf φ) = ⊤
  rwa [hvec] at hprod

/-- A boundary-nonvanishing half-line Laplace transform with mass arbitrarily near
the endpoint is outer after Cayley transport. -/
theorem isOuter_negativeHalfLineLaplaceDiskMultiplier
    {f : ℝ → ℂ} (h1 : Integrable f) (h2 : MemLp f 2 (volume : Measure ℝ))
    (hs : ∀ u, 0 ≤ u → f u = 0)
    (hne : ∀ z : ℂ, 0 ≤ z.re → negativeHalfLineLaplace f z ≠ 0)
    (hend : ∀ a : ℝ, 0 < a → 0 < ∫ u in Ioo (-a) 0, ‖f u‖ ^ (2 : ℕ)) :
    IsOuterDiskMultiplier (negativeHalfLineLaplaceDiskMultiplier f h1 h2 hs) := by
  let φ := negativeHalfLineLaplaceDiskMultiplier f h1 h2 hs
  have hz0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  have hφ : ∃ z ∈ ball (0 : ℂ) 1, φ.fn z ≠ 0 := by
    refine ⟨0, hz0, ?_⟩
    exact negativeHalfLineLaplace_comp_diskToRight_ne_zero hne (by simp) (by norm_num)
  have hc : ContinuousOn φ.fn {z : ℂ | ‖z‖ ≤ 1 ∧ z ≠ 1} :=
    continuousOn_negativeHalfLineLaplace_comp_diskToRight h1 hs
  have hn : ∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 → φ.fn z ≠ 0 :=
    fun _ hz hne1 => negativeHalfLineLaplace_comp_diskToRight_ne_zero hne hz hne1
  obtain ⟨d, hd, c, hcunit, hinner⟩ := exists_innerFactor_eq_unit_mul_delay φ hφ hc hn
  have hquot : ∀ w : ℂ, 0 < w.re →
      ‖Complex.exp ((d : ℂ) * w) * negativeHalfLineLaplace f w‖ ≤
        (diskMultiplierOuterFactor φ hφ).bd := by
    intro w hw
    have hz : cayleyRight w ∈ ball (0 : ℂ) 1 :=
      mem_ball_zero_iff.mpr (norm_cayleyRight_lt_one hw)
    have hmap : diskToRight (cayleyRight w) = w := cayleyRight_inv hw.le
    have hfactor := diskMultiplierInnerFactor_mul_outerFactor_fn φ hφ (cayleyRight w) hz
    rw [hinner _ hz, hmap] at hfactor
    change (c * Complex.exp (-((d : ℂ) * w))) *
      (diskMultiplierOuterFactor φ hφ).fn (cayleyRight w) =
      negativeHalfLineLaplace f (diskToRight (cayleyRight w)) at hfactor
    rw [hmap] at hfactor
    have he : Complex.exp ((d : ℂ) * w) * negativeHalfLineLaplace f w =
        c * (diskMultiplierOuterFactor φ hφ).fn (cayleyRight w) := by
      rw [← hfactor]
      calc
        _ = c * (Complex.exp ((d : ℂ) * w) * Complex.exp (-((d : ℂ) * w))) *
            (diskMultiplierOuterFactor φ hφ).fn (cayleyRight w) := by ring
        _ = _ := by rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    rw [he, norm_mul, hcunit, one_mul]
    exact (diskMultiplierOuterFactor φ hφ).bd_le _ hz
  have hQ := isHalfPlaneHardy_exp_mul_of_bounded
    (isHalfPlaneHardy_negativeHalfLineLaplace h2 hs) hquot
  have hQray : IsHalfPlaneHardy
      (fun w => Complex.exp ((d : ℂ) * w) * laplaceRay (fun u => f (-u)) w)
      (∫ u in Ioi (0 : ℝ), ‖f (-u)‖ ^ (2 : ℕ)) :=
    hQ.congr (fun w _ => by
      rw [negativeHalfLineLaplace_eq_laplaceRay_reflect f hs])
  have hd0 : d = 0 := by
    by_contra hd0
    have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    have hzero := integral_initial_sq_eq_zero_of_hardy_delay
      (memLp_reflected_negativeProfile h2) hQray (a := d / 2) (by linarith only [hdpos])
    have he := integral_reflect_initial_interval (fun u => ‖f u‖ ^ (2 : ℕ)) (d / 2)
    exact (ne_of_gt (hend (d / 2) (half_pos hdpos))) (he.symm.trans hzero)
  apply isOuterDiskMultiplier_of_innerFactor_constant φ hφ
    (c := c) (norm_ne_zero_iff.mp (by rw [hcunit]; exact one_ne_zero))
  intro z hz
  simpa only [hd0, ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] using hinner z hz

#print axioms isOuter_negativeHalfLineLaplaceDiskMultiplier

end GaloisForLFunctions.HTGeometry
