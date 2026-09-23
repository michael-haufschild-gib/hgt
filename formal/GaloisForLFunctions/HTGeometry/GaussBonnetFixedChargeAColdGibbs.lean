import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAColdLatent

/-!
# Finite common Gibbs energy at the cold coexistence endpoint

The small phase approaches the extremal mass and a finite entropy for
any fixed reference length. Its thermal entropy contribution vanishes.
Equality of the two actual phase Gibbs energies therefore gives a finite
common cold limit, even though the large-phase enthalpy diverges.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAColdEntropy (w φ l : ℝ) : ℝ :=
  Real.pi * exp w ^ (2 : ℕ) + 4 * Real.pi * (exp w * sin φ) ^ (2 : ℕ) * (w - l)

theorem egbFixedChargeA_extremal_mass (w φ : ℝ) :
    egbMass 0 (exp w * cos φ) (exp w * sin φ) (exp w) = exp w := by
  unfold egbMass
  rw [egbFixedChargeA_conserved_scale]
  field_simp <;> ring

theorem egbFixedChargeA_extremal_entropy (w φ l : ℝ) :
    egbEntropyA (exp w * sin φ) l (exp w) = egbFixedChargeAColdEntropy w φ l := by
  unfold egbEntropyA egbFixedChargeAColdEntropy
  rw [log_div (exp_ne_zero w) (exp_ne_zero l), log_exp, log_exp]

theorem egbFixedChargeA_small_log_radius_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => log (egbFixedChargeASmallRadius w φ τ)) atTop (𝓝 w) := by
  simpa only [log_exp] using (egbFixedChargeASmallRadius_cold_limit w φ).log (exp_ne_zero w)

theorem egbFixedChargeA_small_entropy_log_formula (w φ τ l : ℝ) :
    egbEntropyA (exp w * sin φ) l (egbFixedChargeASmallRadius w φ τ) =
      Real.pi * egbFixedChargeASmallRadius w φ τ ^ (2 : ℕ) +
        4 * Real.pi * (exp w * sin φ) ^ (2 : ℕ) * (log (egbFixedChargeASmallRadius w φ τ) - l) := by
  unfold egbEntropyA
  rw [log_div (egbFixedChargeA_radii_order w φ τ).1.ne' (exp_ne_zero l), log_exp]

theorem egbFixedChargeA_small_entropy_cold_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbEntropyA (exp w * sin φ) l (egbFixedChargeASmallRadius w φ τ)) atTop
      (𝓝 (egbFixedChargeAColdEntropy w φ l)) := by
  simp only [egbFixedChargeA_small_entropy_log_formula]
  exact (tendsto_const_nhds.mul ((egbFixedChargeASmallRadius_cold_limit w φ).pow 2)).add
    (tendsto_const_nhds.mul ((egbFixedChargeA_small_log_radius_cold_limit w φ).sub tendsto_const_nhds))

theorem egbFixedChargeA_small_mass_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)
      (egbFixedChargeASmallRadius w φ τ)) atTop (𝓝 (exp w)) := by
  have hR := egbFixedChargeASmallRadius_cold_limit w φ
  have hP := egbFixedChargeAPressure_cold_limit w φ
  have h : Tendsto (fun τ => egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)
      (egbFixedChargeASmallRadius w φ τ)) atTop (𝓝 (egbMass 0 (exp w * cos φ) (exp w * sin φ) (exp w))) :=
    ((hR.div tendsto_const_nhds (by norm_num)).add
      (tendsto_const_nhds.div (tendsto_const_nhds.mul hR) (by positivity))).add
        (((tendsto_const_nhds.mul hP).mul (hR.pow 3)).div tendsto_const_nhds (by norm_num))
  rwa [egbFixedChargeA_extremal_mass] at h

theorem egbFixedChargeA_small_thermal_entropy_cold_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeATemperature w φ τ *
      egbEntropyA (exp w * sin φ) l (egbFixedChargeASmallRadius w φ τ)) atTop (𝓝 0) := by
  simpa only [zero_mul] using (egbFixedChargeATemperature_cold_limit w φ).mul (egbFixedChargeA_small_entropy_cold_limit w φ l)

theorem egbFixedChargeASmallGibbs_cold_limit (w φ l : ℝ) :
    Tendsto (egbFixedChargeASmallGibbs w φ l) atTop (𝓝 (exp w)) := by
  change Tendsto (fun τ => egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)
    (egbFixedChargeASmallRadius w φ τ) - egbFixedChargeATemperature w φ τ *
      egbEntropyA (exp w * sin φ) l (egbFixedChargeASmallRadius w φ τ)) atTop (𝓝 (exp w))
  simpa only [sub_zero] using (egbFixedChargeA_small_mass_cold_limit w φ).sub (egbFixedChargeA_small_thermal_entropy_cold_limit w φ l)

/-- The unbounded large phase has the same finite Gibbs limit as the extremal small phase. -/
theorem egbFixedChargeALargeGibbs_cold_limit (w φ l : ℝ) :
    Tendsto (egbFixedChargeALargeGibbs w φ l) atTop (𝓝 (exp w)) := by
  have he : egbFixedChargeALargeGibbs w φ l = egbFixedChargeASmallGibbs w φ l := by
    funext τ
    exact (egbFixedChargeA_equal_gibbs w φ τ l).symm
  rw [he]
  exact egbFixedChargeASmallGibbs_cold_limit w φ l

end GaloisForLFunctions.HTGeometry
