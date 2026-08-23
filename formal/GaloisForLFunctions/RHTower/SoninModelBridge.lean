import GaloisForLFunctions.RHTower.SoninExtendedDilation
import GaloisForLFunctions.RHTower.BurnolSoninEvenCosineAperture
import GaloisForLFunctions.RHTower.BurnolSoninDividedShift

/-!
# The two models of the extended Sonine space agree

`soninExtendedSpace a` lives inside `evenSubspace` and is described by constant *heads* on `(0,a)`
for the vector and its cosine transform; `centralSoninExtendedCarrier a` lives inside `SoninL2` and
is described by constancy on the central band `[-a,a]` for the vector and its Fourier transform.
For even vectors the two descriptions are the same, because an even function constant on `(0,a)` is
constant a.e. on `[-a,a]` and the cosine unitary is the Fourier unitary there.

## Main results

* `ae_centralInterval_of_soninHeadConstant`
* `mem_centralSoninExtendedCarrier_of_mem_soninExtendedSpace`
-/

open Complex Set Topology Filter MeasureTheory

namespace RHTower

noncomputable section

theorem ae_centralInterval_of_soninHeadConstant {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hev : f ∈ evenSubspace) (h : SoninHeadConstant a ((f : SoninL2) : ℝ → ℂ)) :
    ∃ d : ℂ, ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo (0 : ℝ) a → (f : ℝ → ℂ) t = c :=
    (ae_restrict_iff' measurableSet_Ioo).1 hc
  have hrefl : ∀ᵐ t ∂(volume : Measure ℝ), (f : ℝ → ℂ) (-t) = (f : ℝ → ℂ) t := by
    have hfix : l2Reflection f = f := (mem_evenSubspace_iff f).1 hev
    have hae := l2Reflection_ae f
    rw [hfix] at hae
    exact hae.symm
  have h3 : ∀ᵐ t ∂(volume : Measure ℝ), (-t) ∈ Ioo (0 : ℝ) a → (f : ℝ → ℂ) (-t) = c :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h1
  have hnull : (volume : Measure ℝ) ({(0 : ℝ), a, -a}) = 0 := by
    refine measure_union_null (measure_singleton _) ?_
    exact measure_union_null (measure_singleton _) (measure_singleton _)
  filter_upwards [h1, hrefl, h3, MeasureTheory.compl_mem_ae_iff.2 hnull] with t ht1 ht2 ht3 ht4
  intro hmem
  rw [centralInterval, Set.mem_Icc] at hmem
  rw [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at ht4
  push Not at ht4
  obtain ⟨ht0, hta, htna⟩ := ht4
  rcases lt_trichotomy t 0 with hlt | heq | hgt
  · rw [← ht2]
    refine ht3 ?_
    rw [Set.mem_Ioo]
    constructor
    · linarith
    · have : -a < t := lt_of_le_of_ne hmem.1 (fun h => htna h.symm)
      linarith
  · exact absurd heq ht0
  · refine ht1 ?_
    rw [Set.mem_Ioo]
    exact ⟨hgt, lt_of_le_of_ne hmem.2 hta⟩

theorem mem_centralSoninExtendedCarrier_of_mem_soninExtendedSpace {a : ℝ} (ha : 0 < a)
    {f : evenSubspace} (hf : f ∈ soninExtendedSpace a) :
    ((f : SoninL2)) ∈ centralSoninExtendedCarrier a := by
  obtain ⟨hhead, hcos⟩ := mem_soninExtendedSpace.1 hf
  refine (mem_centralSoninExtendedCarrier_iff _).2 ⟨?_, ?_⟩
  · exact ae_centralInterval_of_soninHeadConstant ha f.property hhead
  · have hfour : ((fourierUnitary (f : SoninL2) : SoninL2) : ℝ → ℂ)
        = (((soninCosineUnitary f : evenSubspace) : SoninL2) : ℝ → ℂ) := by
      have h := evenFourierTransform_eq_soninCosineUnitary f
      have hcoe : ((evenFourierTransform f : evenSubspace) : SoninL2)
          = fourierUnitary (f : SoninL2) := rfl
      rw [← hcoe, h]
    have hev' : ((soninCosineUnitary f : evenSubspace) : SoninL2) ∈ evenSubspace :=
      (soninCosineUnitary f).property
    obtain ⟨c, hc⟩ := ae_centralInterval_of_soninHeadConstant ha hev' hcos
    refine ⟨c, ?_⟩
    filter_upwards [hc] with u hu hmem
    rw [hfour]
    exact hu hmem

end

end RHTower
