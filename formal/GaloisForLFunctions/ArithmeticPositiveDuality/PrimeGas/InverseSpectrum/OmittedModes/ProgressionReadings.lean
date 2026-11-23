import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.LineRange
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.OccupationProgressions

/-! # Realization of one omitted trace reading in a prescribed arithmetic progression -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

private theorem extended_mode (f : ℕ+ ↪ ℕ+) (n : ℕ+) :
    extendModes f (modeWave n) = modeWave (f n) :=
  _root_.RHTower.lpScalarInjection_single _ _ _ _

/-- Lane j realizes every strict reading between zero and its lowest shell loss. The
preimage of the missing direction is itself outside the heat range. -/
theorem progression_realizes {r : ℕ} (j : Fin r) {y : ℝ}
    (hy : y ∈ Ioo 0 (occupationWeight j.val ^ 2)) :
    ∃ v : MissingWave, lineLoss (extendModes (progression j) v.val) = y := by
  let f := progression j
  let F (u : Gas) := lineLoss (extendModes f u)
  have hc (u : Gas) (hu : u ≠ 0) : ContinuousAt F u := by
    have he : extendModes f u ≠ 0 := fun h => hu ((extendModes f).injective (h.trans (map_zero _).symm))
    exact (continuousAt_lineLoss he).comp (extendModes f).continuous.continuousAt
  have hup : F (modeWave 1) = occupationWeight j.val ^ 2 := by
    change lineLoss (extendModes (progression j) (modeWave 1)) = _
    rw [extended_mode,progression_one,lineLoss_modeWave]
    rfl
  have hyn : y < 1 := by
    have hw := occupationWeight_antitone (Nat.zero_le j.val)
    rw [occupationWeight_zero] at hw
    exact hy.2.trans_le (by simpa only [one_pow] using (pow_le_pow_left₀ (occupationWeight_pos _).le hw 2))
  obtain ⟨n,hn⟩ := modeWave_straddle ⟨y,hy.1,hyn⟩
  have hlo : F (modeWave n) < y := by
    have ha := attenuation_antitone (progression_increases j n)
    change lineLoss (extendModes (progression j) (modeWave n)) < y
    rw [extended_mode,lineLoss_modeWave]
    have hh := hn.1
    rw [lineLoss_modeWave] at hh
    exact (pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ (attenuation_pos _).le ha 2) 2).trans_lt hh
  have ne (k : ℕ+) : modeWave k ≠ 0 := norm_ne_zero_iff.mp ((modeWave_norm k).trans_ne one_ne_zero)
  obtain ⟨t,ht,he⟩ := omissionArc_intermediate (LinearMap.range criticalOperator.toLinearMap)
    (modeWave_mem_range n) (modeWave_mem_range 1) reciprocalTail_outside (ne n) (ne 1) F hc
    ⟨hlo,hy.2.trans_eq hup.symm⟩
  exact ⟨⟨_,omissionArc_notMem _ (modeWave_mem_range n) (modeWave_mem_range 1) reciprocalTail_outside ht⟩,he⟩

#print axioms progression_realizes

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
