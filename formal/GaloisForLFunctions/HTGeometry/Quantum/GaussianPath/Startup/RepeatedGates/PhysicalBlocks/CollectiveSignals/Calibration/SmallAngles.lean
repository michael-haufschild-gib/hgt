import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.BoxPrice
import GaloisForLFunctions.QuantumAlg.Util.Complex

/-! # Box mass and signal strength at small calibration angles -/

open Real Set
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
noncomputable section

/-- Shrinking all 48 Gaussian coordinates costs the forty-eighth power of time. -/
theorem calibrated_small_time_mass : ∃ c>0, ∀ t∈Ioc (0:ℝ) 1,
    c*t^48≤boxProbability (1/sqrt 2) (t/10000) := by
  let A := 2/(10000*sqrt (2*π))
  have hA : 0<A := by dsimp only [A]; positivity
  refine ⟨A^48*exp (-96),mul_pos (pow_pos hA _) (exp_pos _),?_⟩
  intro t ht
  let δ := t/10000
  have hδ : 0≤δ := div_nonneg ht.1.le (by norm_num)
  have hq : |1/sqrt 2|≤1 := by
    rw [abs_of_nonneg (by positivity : (0:ℝ)≤1/sqrt 2)]
    exact (div_le_one (sqrt_pos.mpr (by norm_num))).mpr (one_le_sqrt.mpr (by norm_num))
  have hsq := mul_self_le_mul_self (add_nonneg (abs_nonneg _) hδ)
    (show |1/sqrt 2|+δ≤2 by dsimp only [δ]; linarith only [hq,ht.2])
  have hexp : exp (-96) ≤ exp (-24*(|1/sqrt 2|+δ)^2) := exp_le_exp.mpr (by linarith only [hsq])
  refine le_trans ?_ (calibrated_box_mass (1/sqrt 2) hδ)
  rw [packet_probability_formula,show 2*δ/sqrt (2*π)=A*t by dsimp only [δ,A]; ring,mul_pow]
  exact (show A^48*exp (-96)*t^48=(A^48*t^48)*exp (-96) by ring).trans_le
    (mul_le_mul_of_nonneg_left hexp (mul_nonneg (pow_nonneg hA.le _) (pow_nonneg ht.1.le _)))

/-- Lower chord bound for the calibrated signal through one time unit. -/
theorem short_sine {t : ℝ} (ht : t∈Ioc (0:ℝ) 1) : t/2 ≤ sin t := by
  have hπ : 1≤π/2 := by linarith only [pi_gt_three]
  have hs := QuantumAlg.sin_ge_slope_mul_of_nonneg_of_le (half_pos pi_pos) (half_le_self pi_pos.le)
    ht.1.le (ht.2.trans hπ)
  rw [sin_pi_div_two] at hs
  have hhalf : (1:ℝ)/2≤1/(π/2) := (div_le_div_iff₀ two_pos (half_pos pi_pos)).mpr
    (by linarith only [pi_lt_four])
  exact (show t/2=1/2*t by ring).trans_le ((mul_le_mul_of_nonneg_right hhalf ht.1.le).trans hs)

#print axioms calibrated_small_time_mass
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
