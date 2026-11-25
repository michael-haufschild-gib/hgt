import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrefixDeadlines.DifferenceWindows
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # A finite observation along an arbitrary spectral phase path -/

open Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines.HaarWindows
noncomputable section

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

/-- Average over the starting phase. On each translate, subtract the first
visit in the window. The resulting physical lags all belong to `B`. -/
theorem translated_window_floor {ι : Type*} [Fintype ι] (φ : ℝ → ι → UnitAddCircle) (hφ : Continuous φ)
    (A : Set (ι → UnitAddCircle)) (hA : IsClosed A) (B : Set ℝ) (hB : MeasurableSet B)
    (hpair : ∀ x t u, φ t + x ∈ A → φ u + x ∈ A → t-u ∈ B)
    (T : ℝ) (hT : 0 ≤ T) :
    volume.real A * T ≤ volume.real (B ∩ Icc 0 T) := by
  classical
  let G := ι → UnitAddCircle
  let μ : Measure G := volume
  let ν := volume.restrict (Icc 0 T)
  let S := (fun p : G × ℝ => φ p.2 + p.1) ⁻¹' A
  have hS : MeasurableSet S := hA.measurableSet.preimage ((hφ.comp continuous_snd).add continuous_fst).measurable
  have htrans (t : ℝ) : μ ((fun x : G => (x,t)) ⁻¹' S) = μ A :=
    (measurePreserving_add_left μ (φ t)).measure_preimage hA.measurableSet.nullMeasurableSet
  let W := B ∩ Icc 0 T
  have hfin (K : Set ℝ) : volume (K ∩ Icc 0 T) ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  have hslice (x : G) : ν (Prod.mk x ⁻¹' S) ≤ volume W := by
    let K := (fun t => φ t + x) ⁻¹' A
    have hK : IsClosed K := hA.preimage (hφ.add continuous_const)
    have h := translate_from_first K B hK hB (fun t ht u hu => hpair x t u ht hu) 0 T
    rw [zero_add] at h
    change volume.restrict (Icc 0 T) K ≤ _
    rw [Measure.restrict_apply hK.measurableSet]
    exact (ENNReal.toReal_le_toReal (hfin K) (hfin B)).mp h
  have hmass : μ A * ν univ ≤ volume W := calc
    μ A * ν univ = (μ.prod ν) S := by
      rw [Measure.prod_apply_symm hS]
      simp only [htrans,lintegral_const]
    _ ≤ ∫⁻ _ : G, volume W ∂μ := by
      rw [Measure.prod_apply hS]
      exact lintegral_mono hslice
    _ = volume W := by simp only [lintegral_const,μ,measure_univ,mul_one]
  have h := ENNReal.toReal_mono (hfin B) hmass
  rwa [ENNReal.toReal_mul,show ν univ = volume (Icc 0 T) from Measure.restrict_apply_univ _,
    Real.volume_Icc,sub_zero,ENNReal.toReal_ofReal hT] at h

#print axioms translated_window_floor
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines.HaarWindows
