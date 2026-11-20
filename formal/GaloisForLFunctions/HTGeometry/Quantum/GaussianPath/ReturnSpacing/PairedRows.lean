import Mathlib.Probability.Independence.InfinitePi

/-! # Disjoint pairs of independent coefficient rows -/
open MeasureTheory
namespace GaloisForLFunctions.HTGeometry

/-- Pair consecutive iid rows. All pairs have the same product law and are independent. -/
theorem measurePreserving_paired_rows {I : Type*} (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun (ω : (ℕ × I) → ℝ) (k : ℕ) (i : Fin 2 × I) => ω (2*k+i.1.val,i.2))
      (Measure.infinitePi fun _ => μ)
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : Fin 2 × I => μ) := by
  let F (p : ℕ × (Fin 2 × I)) : ℕ × I := (2*p.1+p.2.1.val,p.2.2)
  have hf : Function.Injective F := by
    rintro ⟨k,i,d⟩ ⟨j,l,e⟩ h
    obtain ⟨he,hd⟩ := Prod.mk.inj h
    change 2*k+i.val = 2*j+l.val at he
    change d = e at hd
    have hk : k=j := by have := i.isLt; have := l.isLt; omega
    have hpos : i=l := Fin.ext (by omega)
    exact Prod.ext hk (Prod.ext hpos hd)
  let R (ω : ((ℕ × I) → ℝ)) (p : ℕ × (Fin 2 × I)) := ω (F p)
  let ν : Measure ((ℕ × (Fin 2 × I)) → ℝ) := Measure.infinitePi fun _ => μ
  have hR : MeasurePreserving R (Measure.infinitePi fun _ => μ) ν :=
    ⟨measurable_pi_lambda _ (fun _ => measurable_pi_apply _),Measure.map_infinitePi_infinitePi_of_inj hf⟩
  have hC : MeasurePreserving (MeasurableEquiv.curry ℕ (Fin 2 × I) ℝ) ν (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : Fin 2 × I => μ) :=
    ⟨(MeasurableEquiv.curry ..).measurable,Measure.infinitePi_map_curry (fun _ _ => μ)⟩
  exact hC.comp hR

end GaloisForLFunctions.HTGeometry
