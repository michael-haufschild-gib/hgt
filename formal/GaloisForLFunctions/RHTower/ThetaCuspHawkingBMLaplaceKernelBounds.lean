import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceSumBounds
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceSolutions
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceSourceProfile

/-! Bounds on both full-endpoint Green integrands of the retained source. -/
open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section

private theorem paired_power_norm (w : ℂ) {z : ℝ} (hz : 0 < z) :
    ‖power (w/2) z‖*‖power (w/2) z‖=z^w.re := by
  rw [power,Complex.norm_cpow_eq_rpow_re_of_pos hz]
  rw [← Real.rpow_add hz]
  congr 1
  simp

/-- The true horizon Green integrand decays by z^Re(w), uniformly up to AdS. -/
theorem horizon_source_bound {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, z ∈ Ioo 0 1 →
      ‖horizon w chi z*sourceProfile s w a J K T z‖ ≤ C*z^w.re := by
  obtain ⟨D,hD,hF⟩ := horizonFactor_bound h
  obtain ⟨C,hC,hR⟩ := sourceRemainder_bound s w a J K T
  refine ⟨D*C,mul_nonneg hD hC,fun z hz => ?_⟩
  have hprod := mul_le_mul (hF z ⟨hz.1.le,hz.2.le⟩) (hR z ⟨hz.1.le,hz.2.le⟩) (norm_nonneg _) hD
  calc
    ‖horizon w chi z*sourceProfile s w a J K T z‖ =
        (‖power (w/2) z‖*‖power (w/2) z‖)*
          (‖gaussFactor w chi false z‖*‖sourceRemainder s w a J K T z‖) := by
      simp only [horizon,dress,sourceProfile,norm_mul]
      ring
    _ ≤ (D*C)*z^w.re := by
      rw [paired_power_norm w hz.1,mul_comm (D*C)]
      exact mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hz.1.le _)

/-- The true outer Green integrand has an integrable power bound whenever
Re(w) ≤ k+1 < Re(w)+1; no resonance is discarded. -/
theorem normalizable_source_bound {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ)
    (k : ℕ) (hk : w.re-1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, z ∈ Ioo 0 1 →
      ‖normalizable w chi z*sourceProfile s w a J K T z‖ ≤ C*z^(w.re-(k+1:ℕ)) := by
  obtain ⟨D,hD,hF⟩ := outerFactor_bound h k hk
  obtain ⟨C,hC,hR⟩ := sourceRemainder_bound s w a J K T
  refine ⟨D*C,mul_nonneg hD hC,fun z hz => ?_⟩
  have hs : ‖power (1/2) (1-z)‖ ≤ 1 := by
    rw [power_half_eq_sqrt (sub_nonneg.mpr hz.2.le),Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_le_one).mpr (by linarith [hz.1])
  have hFR := mul_le_mul (hF z hz) (hR z ⟨hz.1.le,hz.2.le⟩) (norm_nonneg _)
    (div_nonneg hD (pow_nonneg hz.1.le _))
  have hSFR : ‖power (1/2) (1-z)‖*(‖gaussFactor w chi true (1-z)‖*
      ‖sourceRemainder s w a J K T z‖) ≤ D/z^(k+1)*C := by
    simpa only [one_mul] using mul_le_mul hs hFR (by positivity) (by norm_num : (0:ℝ)≤1)
  calc
    ‖normalizable w chi z*sourceProfile s w a J K T z‖ =
        (‖power (w/2) z‖*‖power (w/2) z‖)*
          (‖power (1/2) (1-z)‖*(‖gaussFactor w chi true (1-z)‖*
            ‖sourceRemainder s w a J K T z‖)) := by
      simp only [normalizable,dress,outerFactor,sourceProfile,norm_mul]
      ring
    _ ≤ z^w.re*(D/z^(k+1)*C) := by
      rw [paired_power_norm w hz.1]
      exact mul_le_mul_of_nonneg_left hSFR (Real.rpow_nonneg hz.1.le _)
    _ = (D*C)*z^(w.re-(k+1:ℕ)) := by
      rw [Real.rpow_sub hz.1,Real.rpow_natCast]
      ring

end
end RHTower.D4BMLaplaceRadial
