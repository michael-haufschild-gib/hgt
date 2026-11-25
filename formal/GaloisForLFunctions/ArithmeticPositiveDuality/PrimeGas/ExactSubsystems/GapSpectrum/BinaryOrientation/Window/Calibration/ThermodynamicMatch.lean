import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.Window.Calibration.Response
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.Gibbs
import GaloisForLFunctions.RHTower.MobiusCoMovingDiffuseCodiagonal

/-! # Matching the critical-window slope to the unrestricted two-copy gas -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.Window

open Filter Topology Set _root_.RHTower

theorem binaryPartition_squarefreeTotal (h : Ioi (0:ℝ)) :
    binaryPartition h = squarefreeMobiusTotal (labelTemperature h).val := by
  have z (v : Ioi (0:ℝ)) : (labelPartition v:ℂ) = riemannZeta ((labelTemperature v).val:ℂ) :=
    thermalWeight_partition (labelTemperature v)
  have hd : 2*((labelTemperature h).val:ℂ) = ((labelTemperature (pairedExcess h)).val:ℂ) := by
    change 2*((1+h.val:ℝ):ℂ) = ((1+(1+2*h.val):ℝ):ℂ)
    push_cast
    ring
  rw [squarefreeMobiusTotal_eq_zetaRatio_re (labelTemperature h).property,hd,← z h,← z (pairedExcess h),
    ← Complex.ofReal_div,Complex.ofReal_re]
  exact (eq_div_iff (labelPartition_pos (pairedExcess h)).ne').mpr (binaryPartition_times_paired h)

/-- The full, unrestricted squarefree orientation has vacuum probability asymptotic to h ζ(2). -/
theorem binary_vacuum_pole :
    Tendsto (fun h : Ioi (0:ℝ) => binaryMass h vacuum/h.val) criticalApproach (𝓝 (riemannZeta 2).re) := by
  have hv : Tendsto (Subtype.val : Ioi (0:ℝ) → ℝ) criticalApproach (𝓝[>] 0) := tendsto_comap
  have ht : Tendsto (fun h : Ioi (0:ℝ) => (labelTemperature h).val) criticalApproach (𝓝[>] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall fun h => (labelTemperature h).property⟩
    change Tendsto (fun h : Ioi (0:ℝ) => 1+h.val) criticalApproach (𝓝 1)
    simpa only [add_zero] using (tendsto_const_nhds (x := (1:ℝ))).add (hv.mono_right nhdsWithin_le_nhds)
  apply (tendsto_inv_squarefreeMobiusTotal_div_sub_one.comp ht).congr
  intro h
  have hδ : (labelTemperature h).val-1 = h.val := by change 1+h.val-1 = h.val; ring
  change (squarefreeMobiusTotal (labelTemperature h).val)⁻¹/((labelTemperature h).val-1) = _
  rw [← binaryPartition_squarefreeTotal,hδ]
  change (binaryPartition h)⁻¹/h.val = (thermalWeight (labelTemperature h) 1/binaryPartition h)/h.val
  simp [thermalWeight,energy,one_div]

/-- The two independent calibrations have the same coefficient at their common boundary. -/
theorem matching_vacuum_ratio :
    Tendsto (fun p : ℝ × Ioi (0:ℝ) => (response p.1/(2*p.1))/(binaryMass p.2 vacuum/p.2.val))
      (atTop ×ˢ criticalApproach) (𝓝 1) := by
  have hp := InverseSpectrum.ShellMixing.gasPartition_pos (⟨2,one_lt_two⟩ : TraceTemperature)
  have H := (response_slope_atTop.comp tendsto_fst).div (binary_vacuum_pole.comp tendsto_snd)
    (show (riemannZeta 2).re ≠ 0 from hp.ne')
  rwa [div_self (show (riemannZeta 2).re ≠ 0 from hp.ne')] at H

#print axioms binaryPartition_squarefreeTotal
#print axioms binary_vacuum_pole
#print axioms matching_vacuum_ratio

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.Window
