import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OccupationProbabilities.Tomography
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.LineRange

/-! # Exactly which native levels can be blind to a coherent one-mode reference -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology ContinuousLinearMap

private theorem moment_mode (n : ℕ+) : firstMoment (modeWave n) = attenuation n^2 := by
  rw [firstMoment,heat_modeWave,norm_smul,Complex.norm_real,Real.norm_of_nonneg (attenuation_pos _).le,modeWave_norm,mul_one,one_pow,div_one]

private theorem continuous_firstMoment {v : Gas} (hv : v ≠ 0) : ContinuousAt firstMoment v :=
  ((criticalOperator.continuous.norm.pow 2).continuousAt).div (continuous_norm.pow 2).continuousAt
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv))

/-- Every mean inverse occupation strictly between zero and one occurs for an exterior omission. -/
theorem poleReading_range : Set.range poleReading = Ioo (0:ℝ) 1 := by
  have hr (v : MissingWave) : poleReading v = firstMoment v.val := by rw [poleReading,omissionPartition_pole,Complex.ofReal_re]
  ext y
  constructor
  · rintro ⟨v,rfl⟩
    rw [hr]
    exact ⟨(missing_moments v).1,(missing_moments v).2.1⟩
  · intro hy
    obtain ⟨k,hk⟩ := (occupationWeight_tendsto.eventually_lt_const hy.1).exists
    have hlow : firstMoment (modeWave (number k)) < y := (moment_mode _).trans_lt hk
    have hhi : y < firstMoment (modeWave 1) := by simpa [moment_mode,attenuation,gain] using hy.2
    have hne (n : ℕ+) : modeWave n ≠ 0 := norm_ne_zero_iff.mp ((modeWave_norm n).trans_ne one_ne_zero)
    obtain ⟨t,ht,he⟩ := omissionArc_intermediate (LinearMap.range criticalOperator.toLinearMap)
      (modeWave_mem_range (number k)) (modeWave_mem_range 1) reciprocalTail_outside
      (hne _) (hne _) firstMoment (fun _ hu => continuous_firstMoment hu) ⟨hlow,hhi⟩
    let v : MissingWave := ⟨_,omissionArc_notMem _ (modeWave_mem_range (number k)) (modeWave_mem_range 1) reciprocalTail_outside ht⟩
    exact ⟨v,(hr v).trans he⟩

/-- Every nonvacuum label and only those labels can conceal a wave from all coherent references in that same mode. -/
theorem possible_blind_labels (k : ℕ) :
    (∃ v : MissingWave, ∀ c, poleReading (addNative v k c) = poleReading v) ↔ k ≠ 0 := by
  have h0 : occupationWeight 0 = 1 := by rw [occupationWeight_eq]; norm_num
  constructor
  · rintro ⟨v,h⟩ rfl
    have hh := (all_references_silent_iff v 0).mp h
    have hmem := poleReading_range ▸ (Set.mem_range_self v : poleReading v ∈ Set.range poleReading)
    exact hmem.2.ne (hh.trans h0)
  · intro hk
    have hlt := occupationWeight_strictAnti (Nat.pos_of_ne_zero hk)
    rw [h0] at hlt
    have hm : occupationWeight k ∈ Set.range poleReading := poleReading_range.symm ▸
      (show occupationWeight k ∈ Ioo (0:ℝ) 1 from ⟨occupationWeight_pos k,hlt⟩)
    obtain ⟨v,h⟩ := hm
    exact ⟨v,(all_references_silent_iff v k).mpr h⟩

#print axioms poleReading_range
#print axioms possible_blind_labels

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
