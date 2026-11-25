import GaloisForLFunctions.HTGeometry.RealAnalyticImplicit
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Compactness.Lindelof

/-! # Null forecast dates on regular field branches of an analytic test -/

open Filter Topology Set MeasureTheory ContinuousLinearMap
open scoped ContDiff
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.CircuitContacts
noncomputable section

/-- A regular zero, with date as first coordinate and field as second,
locally assigns just one differentiable field value to each forecast date. -/
private theorem field_chart {f : ℝ×ℝ→ℝ} {z : ℝ×ℝ} (hf : AnalyticAt ℝ f z)
    (hz : f z=0) (hd : (fderiv ℝ f z) (0,1)≠0) :
    ∃ g : ℝ→ℝ, ∀ᶠ p in 𝓝 z, DifferentiableAt ℝ g p.1 ∧ (f p=0 → g p.1=p.2) := by
  have cdf : ContDiffAt ℝ ω f z := hf.contDiffAt
  have hinv : (fderiv ℝ f z ∘L (.inr ℝ ℝ ℝ)).IsInvertible :=
    clm_invertible_of_apply_one_ne_real (by simpa using hd)
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by decide
  let g := cdf.implicitFunction hω hinv
  have ha : AnalyticAt ℝ g z.1 := (cdf.contDiffAt_implicitFunction hω hinv).analyticAt
  refine ⟨g,?_⟩
  filter_upwards [continuousAt_fst.tendsto ha.eventually_analyticAt,
    cdf.eventually_apply_eq_iff_implicitFunction hω hinv] with p hp he
  exact ⟨hp.differentiableAt, fun h => he.mp (h.trans hz.symm)⟩

/-- All transverse incidence points above a null set of dates project to
a null set of fields. The date set need not be measurable. -/
theorem transverse_field_null (f : ℝ×ℝ→ℝ) (A : Set ℝ) (hA : volume A=0) :
    volume (Prod.snd '' {p : ℝ×ℝ | p.1∈A ∧ AnalyticAt ℝ f p ∧ f p=0 ∧
      (fderiv ℝ f p) (0,1)≠0})=0 := by
  classical
  let S := {p : ℝ×ℝ | p.1∈A ∧ AnalyticAt ℝ f p ∧ f p=0 ∧ (fderiv ℝ f p) (0,1)≠0}
  choose g hg using fun p : S => field_chart p.property.2.1 p.property.2.2.1 p.property.2.2.2
  let U (p : S) := {q : ℝ×ℝ | DifferentiableAt ℝ (g p) q.1 ∧ (f q=0 → g p q.1=q.2)}
  obtain ⟨J,hJ,hcov⟩ := (IsLindelof.of_coe (s:=S)).elim_nhds_subcover'
    (fun p hp => U ⟨p,hp⟩) (fun p hp => hg ⟨p,hp⟩)
  letI : Countable J := hJ.to_subtype
  let E (p : J) := A∩{t | DifferentiableAt ℝ (g p.val) t}
  have hnull (p : J) : volume ((g p.val) '' E p)=0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (μ:=volume)
      (fun _ ht => ht.2.differentiableWithinAt) (measure_mono_null inter_subset_left hA)
  apply measure_mono_null (t:=(⋃ p : J, (g p.val) '' E p)) _ (measure_iUnion_null hnull)
  rintro _ ⟨q,hq,rfl⟩
  obtain ⟨p,hp⟩ := mem_iUnion.mp (hcov hq)
  obtain ⟨hj,hu⟩ := mem_iUnion.mp hp
  exact mem_iUnion.mpr ⟨⟨p,hj⟩,q.1,⟨hq.1,hu.1⟩,hu.2 hq.2.2.1⟩

#print axioms transverse_field_null
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.CircuitContacts
