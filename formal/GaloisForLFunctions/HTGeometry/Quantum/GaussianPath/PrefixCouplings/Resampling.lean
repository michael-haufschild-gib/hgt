import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass

/-! # Resampling a single coupling of an infinite product -/
open MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry.PrefixCouplings
noncomputable section

/-- Replacing one coordinate by a fresh copy leaves the whole joint law
unchanged. On a finite cylinder only that coordinate's factor is removed
from the old sample and supplied by the fresh sample. -/
theorem resample_preserving {I X : Type*} [DecidableEq I] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (i : I) :
    let P := Measure.infinitePi (fun _ : I => μ)
    MeasurePreserving (fun p : (I→X)×X => Function.update p.1 i p.2) (P.prod μ) P := by
  intro P
  let R (p : (I→X)×X) := Function.update p.1 i p.2
  have hm : Measurable R := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j=i
    · subst j; simpa only [R,Function.update_self] using (measurable_snd : Measurable (Prod.snd : (I→X)×X→X))
    · simpa only [R,Function.update_of_ne hj,Function.comp_def] using
        (measurable_pi_apply j).comp (measurable_fst : Measurable (Prod.fst : (I→X)×X→(I→X)))
  refine ⟨hm,Measure.eq_infinitePi _ ?_⟩
  intro s T hT
  rw [Measure.map_apply hm (.pi s.countable_toSet fun j _ => hT j)]
  by_cases hi : i∈s
  · have he : R ⁻¹' (Set.pi (s:Set I) T)=Set.pi (s.erase i:Set I) T ×ˢ T i := by
      ext p
      constructor
      · intro h
        refine ⟨fun j hj => ?_,?_⟩
        · have hh := Finset.mem_erase.mp hj
          simpa only [R,Function.update_of_ne hh.1] using h j hh.2
        · simpa only [R,Function.update_self] using h i hi
      · rintro ⟨hp,hq⟩ j hj
        by_cases h : j=i
        · subst j; simpa only [R,Function.update_self] using hq
        · simpa only [R,Function.update_of_ne h] using hp j (Finset.mem_erase.mpr ⟨h,hj⟩)
    rw [he,Measure.prod_prod]
    change Measure.infinitePi _ (Set.pi (s.erase i:Set I) T)*μ (T i)=_
    rw [Measure.infinitePi_pi _ (fun j _ => hT j),Finset.prod_erase_mul _ _ hi]
  · have he : R ⁻¹' (Set.pi (s:Set I) T)=Set.pi (s:Set I) T ×ˢ (univ:Set X) := by
      ext p
      constructor
      · intro h
        refine ⟨fun j hj => ?_,mem_univ _⟩
        simpa only [R,Function.update_of_ne (show j≠i from fun he => hi (he ▸ hj))] using h j hj
      · rintro ⟨h,_⟩ j hj
        simpa only [R,Function.update_of_ne (show j≠i from fun he => hi (he ▸ hj))] using h j hj
    rw [he,Measure.prod_prod,measure_univ,mul_one]
    exact Measure.infinitePi_pi _ (fun j _ => hT j)

/-- An almost-sure conclusion after conditioning on all the other
couplings transfers to the original, unmodified product draw. -/
theorem ae_of_resampled_coordinate {I X : Type*} [DecidableEq I] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (i : I) (S : Set (I→X)) (hS : MeasurableSet S)
    (h : ∀ᵐ x ∂(Measure.infinitePi (fun _ : I => μ)), ∀ᵐ y ∂μ, Function.update x i y∈S) :
    ∀ᵐ x ∂(Measure.infinitePi (fun _ : I => μ)), x∈S := by
  let P := Measure.infinitePi (fun _ : I => μ)
  let R (p : (I→X)×X) := Function.update p.1 i p.2
  have hp := resample_preserving μ i
  have hh : ∀ᵐ p ∂(P.prod μ), R p∈S := (Measure.ae_prod_iff_ae_ae (hS.preimage hp.measurable)).mpr h
  rw [←hp.map_eq]
  exact (ae_map_iff hp.measurable.aemeasurable hS).mpr hh

#print axioms ae_of_resampled_coordinate
end
end GaloisForLFunctions.HTGeometry.PrefixCouplings
