import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Reading
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.Window.Calibration.ThermodynamicMatch
import GaloisForLFunctions.RHTower.ExponentialIntegralE1Quantile

/-! # The limiting joint Laplace reading for a bounded largest prime -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime

open Filter Topology Set _root_.RHTower

/-- Multiply the excess inverse temperature by the positive Laplace scale. -/
def scaled (r h : Ioi (0:ℝ)) : Ioi (0:ℝ) :=
  ⟨r.val*h.val,by change (0:ℝ) < r.val*h.val; exact mul_pos r.property h.property⟩

private theorem scaled_approach (r : Ioi (0:ℝ)) :
    Tendsto (scaled r) criticalApproach criticalApproach := by
  apply tendsto_comap_iff.mpr
  have H : Tendsto (Subtype.val : Ioi (0:ℝ) → ℝ) criticalApproach (𝓝[>] 0) := tendsto_comap
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,Eventually.of_forall fun h => (scaled r h).property⟩
  change Tendsto (fun h : Ioi (0:ℝ) => r.val*h.val) criticalApproach (𝓝 0)
  simpa only [mul_zero] using (H.mono_right nhdsWithin_le_nhds).const_mul r.val

private theorem half_approach :
    Tendsto (fun h : Ioi (0:ℝ) => h.val/2) criticalApproach (𝓝[>] (0:ℝ)) := by
  have H : Tendsto (Subtype.val : Ioi (0:ℝ) → ℝ) criticalApproach (𝓝[>] 0) := tendsto_comap
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [zero_div] using (H.mono_right nhdsWithin_le_nhds).div_const 2
  · exact Eventually.of_forall fun h => (show 0 < h.val/2 from div_pos h.property zero_lt_two)

private theorem retained_eq (c : ℝ) (r h : Ioi (0:ℝ)) :
    criticalRetainedMass (r.val*c) ((scaled r h).val/2) =
      (∏ p ∈ (primeCut c h+1).primesBelow, (1+(p:ℝ)^(-(1+r.val*h.val))))/binaryPartition (scaled r h) := by
  rw [criticalRetainedMass_eq (div_pos (scaled r h).property zero_lt_two)]
  have h2 : 2*((scaled r h).val/2) = r.val*h.val := by change 2*(r.val*h.val/2) = _; ring
  have hcut : criticalCutoff (r.val*c) ((scaled r h).val/2) = Real.exp (c/h.val) := by
    rw [criticalCutoff,h2,mul_div_mul_left _ _ r.property.ne']
  rw [hcut,h2,Window.binaryPartition_squarefreeTotal]
  rfl

/-- The tilted joint reading is exactly one largest-prime probability at rescaled temperature
times the change in the unrestricted partition. -/
theorem joint_exact (c t : ℝ) (ht : 0 < 1+t) (h : Ioi (0:ℝ)) :
    jointReading c t h = criticalRetainedMass ((1+t)*c) ((1+t)*h.val/2)*
      (binaryPartition (scaled ⟨1+t,ht⟩ h)/binaryPartition h) := by
  let r : Ioi (0:ℝ) := ⟨1+t,ht⟩
  rw [joint_product _ _ ht]
  change _ = criticalRetainedMass (r.val*c) ((scaled r h).val/2)*_
  rw [retained_eq,← mul_div_assoc,div_mul_cancel₀ _ (binaryPartition_pos (scaled r h)).ne']

private theorem vacuum_eq (h : Ioi (0:ℝ)) : binaryMass h vacuum = (binaryPartition h)⁻¹ := by
  change thermalWeight (labelTemperature h) 1/binaryPartition h = _
  simp [thermalWeight,energy,one_div]

private theorem partition_ratio (r : Ioi (0:ℝ)) :
    Tendsto (fun h : Ioi (0:ℝ) => binaryPartition (scaled r h)/binaryPartition h)
      criticalApproach (𝓝 (1/r.val)) := by
  have hp := InverseSpectrum.ShellMixing.gasPartition_pos (⟨2,one_lt_two⟩ : TraceTemperature)
  have hz : (riemannZeta 2).re ≠ 0 := hp.ne'
  have H := (Window.binary_vacuum_pole.div (Window.binary_vacuum_pole.comp (scaled_approach r)) hz).div_const r.val
  rw [div_self hz] at H
  apply H.congr
  intro h
  change ((binaryMass h vacuum/h.val)/(binaryMass (scaled r h) vacuum/(r.val*h.val)))/r.val = _
  rw [vacuum_eq,vacuum_eq]
  have hh : h.val ≠ 0 := (show 0 < h.val from h.property).ne'
  have hr : r.val ≠ 0 := (show 0 < r.val from r.property).ne'
  field_simp [hh,hr,(binaryPartition_pos h).ne',(binaryPartition_pos (scaled r h)).ne']

/-- Joint transform of scaled energy and the event that the largest marked prime is at most exp(c/h). -/
theorem joint_limit {c t : ℝ} (hc : 0 < c) (ht : 0 < 1+t) :
    Tendsto (jointReading c t) criticalApproach (𝓝 (Real.exp (-expIntegralOne ((1+t)*c))/(1+t))) := by
  let r : Ioi (0:ℝ) := ⟨1+t,ht⟩
  have H := ((tendsto_criticalRetainedMass (mul_pos r.property hc)).comp
    (half_approach.comp (scaled_approach r))).mul (partition_ratio r)
  rw [mul_one_div] at H
  exact H.congr (fun h => (joint_exact c t ht h).symm)

/-- The conditioning event has positive probability at each cutoff. -/
theorem cutoff_probability_pos (c : ℝ) (h : Ioi (0:ℝ)) : 0 < jointReading c 0 h := by
  rw [joint_product c 0 (by simp)]
  exact div_pos (Finset.prod_pos fun _ _ => add_pos_of_pos_of_nonneg zero_lt_one
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (binaryPartition_pos h)

/-- Conditional energy transform under the observed largest-prime bound. -/
theorem conditional_limit {c t : ℝ} (hc : 0 < c) (ht : 0 < 1+t) :
    Tendsto (fun h => jointReading c t h/jointReading c 0 h) criticalApproach
      (𝓝 (Real.exp (expIntegralOne c-expIntegralOne ((1+t)*c))/(1+t))) := by
  have h0 := joint_limit (t := 0) hc (by simp)
  simp only [add_zero,one_mul,div_one] at h0
  have H := (joint_limit hc ht).div h0 (Real.exp_pos _).ne'
  have he : (Real.exp (-expIntegralOne ((1+t)*c))/(1+t))/Real.exp (-expIntegralOne c) =
      Real.exp (expIntegralOne c-expIntegralOne ((1+t)*c))/(1+t) := by
    rw [div_right_comm,← Real.exp_sub]
    congr 2
    ring
  rwa [he] at H


/-- Unrestricted Laplace weight in the same two-copy orientation ensemble. -/
def totalReading (t : ℝ) (h : Ioi (0:ℝ)) : ℝ :=
  ∑' j : SquarefreeLabel, binaryMass h j*Real.exp (-t*scaledEnergy h j)

theorem total_limit {t : ℝ} (ht : 0 < 1+t) :
    Tendsto (totalReading t) criticalApproach (𝓝 (1/(1+t))) := by
  let r : Ioi (0:ℝ) := ⟨1+t,ht⟩
  apply (partition_ratio r).congr
  intro h
  change (∑' j : SquarefreeLabel, thermalWeight (labelTemperature (scaled r h)) j.val)/binaryPartition h =
    ∑' j : SquarefreeLabel, binaryMass h j*Real.exp (-t*scaledEnergy h j)
  rw [← tsum_div_const]
  apply tsum_congr
  intro j
  rw [binaryMass,div_mul_eq_mul_div]
  apply congrArg (·/binaryPartition h)
  rw [thermalWeight,thermalWeight,← Real.exp_add]
  apply congrArg Real.exp
  change -(1+(1+t)*h.val)*energy j.val = -(1+h.val)*energy j.val+ -t*(h.val*energy j.val)
  ring

/-- For positive Laplace probes the cutoff increases the reading by a strictly positive limiting amount. -/
theorem limiting_dependence {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    ∃ d : ℝ, 0 < d ∧ Tendsto (fun h => jointReading c t h/jointReading c 0 h-totalReading t h)
      criticalApproach (𝓝 d) := by
  have hr : 0 < 1+t := add_pos zero_lt_one ht
  have hrc : c < (1+t)*c := by rw [add_mul,one_mul]; exact lt_add_of_pos_right c (mul_pos ht hc)
  have hd := expIntegralOne_strictAntiOn hc (mul_pos hr hc) hrc
  refine ⟨_,sub_pos.mpr ((div_lt_div_iff_of_pos_right hr).mpr (Real.one_lt_exp_iff.mpr (sub_pos.mpr hd))),?_⟩
  exact (conditional_limit hc hr).sub (total_limit hr)

#print axioms cutoff_probability_pos
#print axioms total_limit
#print axioms limiting_dependence
#print axioms joint_exact
#print axioms joint_limit
#print axioms conditional_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime
