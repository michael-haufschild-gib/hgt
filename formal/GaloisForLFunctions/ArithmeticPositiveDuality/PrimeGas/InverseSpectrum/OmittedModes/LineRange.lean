import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.LineMoments
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.LineArc
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.RankReadings

/-! # The full interval of trace deficits for a one-dimensional omission -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set ContinuousLinearMap

/-- A reciprocal packet supplies an exterior direction for all arcs between physical shells. -/
def reciprocalTail : Gas := packet ⟨1,by norm_num⟩

theorem reciprocalTail_outside : reciprocalTail ∉ LinearMap.range criticalOperator.toLinearMap := by
  change packet ⟨1,by norm_num⟩ ∉ Set.range criticalOperator
  rw [packet_in_range_iff]
  norm_num

theorem lineLoss_surjective : Set.range (fun v : MissingWave => lineLoss v.val) = Ioo (0:ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨v,rfl⟩
    exact line_loss_bounds v
  · intro hy
    obtain ⟨n,hn⟩ := modeWave_straddle ⟨y,hy⟩
    have ne (k : ℕ+) : modeWave k ≠ 0 := norm_ne_zero_iff.mp ((modeWave_norm k).trans_ne one_ne_zero)
    obtain ⟨t,ht,he⟩ := omissionArc_intermediate (LinearMap.range criticalOperator.toLinearMap)
      (modeWave_mem_range n) (modeWave_mem_range 1) reciprocalTail_outside (ne n) (ne 1)
      lineLoss (fun _ hv => continuousAt_lineLoss hv) hn
    exact ⟨⟨_,omissionArc_notMem _ (modeWave_mem_range n) (modeWave_mem_range 1) reciprocalTail_outside ht⟩,he⟩

/-- At missing dimension one, exactly the open unit interval of fourth-trace losses occurs. -/
theorem lossesAtRank_one : lossesAtRank 1 = Ioo (0:ℝ) 1 := by
  rw [← lineLoss_surjective]
  ext y
  constructor
  · rintro ⟨P,hd,hc,he⟩
    obtain ⟨v,hv,rfl⟩ := (missingDimension_one_iff P).mp hd
    exact ⟨⟨v,(nonzero_line_conserves_iff v).mp ⟨hv,hc⟩⟩,(traceLoss_omitLine v).symm.trans he⟩
  · rintro ⟨v,rfl⟩
    have hc := (nonzero_line_conserves_iff v.val).mpr v.property
    exact ⟨omitLine v.val,(missingDimension_one_iff _).mpr ⟨v.val,hc.1,rfl⟩,hc.2,traceLoss_omitLine _⟩

#print axioms lineLoss_surjective
#print axioms lossesAtRank_one

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
