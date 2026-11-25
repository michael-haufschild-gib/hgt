import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.CircuitContacts.TransverseCharts
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Projecting analytic contact points above a null set of dates -/

open Filter Topology Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.CircuitContacts
noncomputable section

/-- Derivatives in the unrevealed field, with the forecast date fixed. -/
def fieldPartial (n : ℕ) (f : ℝ×ℝ→ℝ) (p : ℝ×ℝ) :=
  iteratedDeriv n (fun y => f (p.1,y)) p.2

private theorem next_partial {f : ℝ×ℝ→ℝ} {n : ℕ} {p : ℝ×ℝ}
    (h : DifferentiableAt ℝ (fieldPartial n f) p) :
    (fderiv ℝ (fieldPartial n f) p) (0,1) = fieldPartial (n+1) f p := by
  have he : HasDerivAt (fun y : ℝ => (p.1,y)) (0,1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id _)
  have hh := h.hasFDerivAt.comp_hasDerivAt p.2 he
  change _ = iteratedDeriv (n+1) (fun y => f (p.1,y)) p.2
  rw [iteratedDeriv_succ]
  exact hh.deriv.symm

private theorem analytic_partial {f : ℝ×ℝ→ℝ} (n : ℕ) {p : ℝ×ℝ}
    (h : AnalyticAt ℝ f p) : AnalyticAt ℝ (fieldPartial n f) p := by
  induction n generalizing p with
  | zero =>
    have he : fieldPartial 0 f=f := funext fun z => by simp only [fieldPartial,iteratedDeriv_zero]
    rwa [he]
  | succ n ih =>
    have hn := ih h
    have ha : AnalyticAt ℝ (fun z => (fderiv ℝ (fieldPartial n f) z) (0,1)) p :=
      ((ContinuousLinearMap.apply ℝ ℝ ((0,1) : ℝ×ℝ)).analyticAt _).comp hn.fderiv
    apply ha.congr
    filter_upwards [hn.eventually_analyticAt] with q hq
    exact next_partial hq.differentiableAt

/-- For any real analytic test, its zeros over a null set of dates project
to a null set of field values wherever its fixed-date germ is nonzero.
Multiple roots are included by applying the regular chart to the preceding
field derivative. -/
theorem horizontal_zero_projection (f : ℝ×ℝ→ℝ) (A : Set ℝ) (hA : volume A=0) :
    volume (Prod.snd '' {p : ℝ×ℝ | p.1∈A ∧ AnalyticAt ℝ f p ∧ f p=0 ∧
      ∃ᶠ y in 𝓝 p.2, f (p.1,y)≠0})=0 := by
  let B (n : ℕ) := {p : ℝ×ℝ | p.1∈A ∧ AnalyticAt ℝ (fieldPartial n f) p ∧
    fieldPartial n f p=0 ∧ (fderiv ℝ (fieldPartial n f) p) (0,1)≠0}
  have hn (n : ℕ) : volume (Prod.snd '' B n)=0 := transverse_field_null _ A hA
  apply measure_mono_null (t:=⋃ n, Prod.snd '' B n) _ (measure_iUnion_null hn)
  rintro _ ⟨p,⟨hp,hf,hz,hpos⟩,rfl⟩
  let g (y : ℝ) := f (p.1,y)
  have hg : AnalyticAt ℝ g p.2 := hf.comp (analyticAt_const.prod analyticAt_id)
  have hm : analyticOrderAt g p.2≠⊤ := fun h => hpos ((analyticOrderAt_eq_top.mp h).mono
    fun y hy => not_not.mpr hy)
  obtain ⟨m,he⟩ := ENat.ne_top_iff_exists.mp hm
  have hj := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hg).mp he.symm
  cases m with
  | zero => exact False.elim (hj.2 (by simpa only [iteratedDeriv_zero,g] using hz))
  | succ n =>
    refine mem_iUnion.mpr ⟨n,p,⟨hp,analytic_partial n hf,hj.1 n (Nat.lt_succ_self n),?_⟩,rfl⟩
    rw [next_partial (analytic_partial n hf).differentiableAt]
    exact hj.2

#print axioms horizontal_zero_projection
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.CircuitContacts
