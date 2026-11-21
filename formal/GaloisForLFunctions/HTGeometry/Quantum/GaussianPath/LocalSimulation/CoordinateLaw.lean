import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi

/-! # A strong law along each coordinate direction of an independent array -/
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.LocalPatches
noncomputable section

/-- An integrable observable has its scalar mean as each direction's
limiting empirical average in an infinite independent array. -/
theorem coordinate_strong_law {ι : Type*} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (d : ι) (f : ℝ → ℝ) (hf : Measurable f) (hi : Integrable f μ) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ × ι => μ), Tendsto
      (fun N : ℕ => (∑ i ∈ Finset.range N, f (ω (i,d))) / N)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  let law := Measure.infinitePi (fun _ : ℕ × ι => μ)
  let X (i : ℕ) (ω : ((ℕ × ι) → ℝ)) := f (ω (i,d))
  have hident (i : ℕ) : IdentDistrib (X i) f law μ := by
    have h := measurePreserving_eval_infinitePi (fun _ : ℕ × ι => μ) (i,d)
    have h' : IdentDistrib (Function.eval (i,d)) id law μ :=
      ⟨h.measurable.aemeasurable,measurable_id.aemeasurable,by rw [Measure.map_id]; exact h.map_eq⟩
    exact h'.comp hf
  have hindep : iIndepFun X law := by
    have h := iIndepFun_infinitePi (P := fun _ : ℕ × ι => μ)
      (X := fun _ x => f x) (fun _ => hf)
    exact h.precomp (g := fun i : ℕ => (i,d)) (fun _ _ e => congrArg Prod.fst e)
  have h := strong_law_ae_real X ((hident 0).integrable_iff.mpr hi)
    (fun _ _ hij => hindep.indepFun hij) (fun i => (hident i).trans (hident 0).symm)
  rwa [(hident 0).integral_eq] at h

end
end GaloisForLFunctions.HTGeometry.LocalPatches
