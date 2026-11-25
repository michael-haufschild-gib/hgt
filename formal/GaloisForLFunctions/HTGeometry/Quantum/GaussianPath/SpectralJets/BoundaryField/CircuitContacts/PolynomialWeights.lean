import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.CircuitContacts.WeightedSlice

/-! # Polynomial weights in the single unrevealed coupling -/

open Polynomial Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.CircuitContacts
open SelectedDates.AlgebraicCurves
noncomputable section

/-- A nonzero polynomial coefficient already prevents a local fixed-date
relation, even at a zero of that coefficient. The exponents are algebraic
energy actions with pairwise nonconstant differences. -/
theorem polynomial_weight_escape {J : Type*} [Fintype J] (f : J→ℂ→ℂ) (p : J→ℂ[X])
    (hf : ∀ j, AnalyticAt ℂ (f j) 0)
    (ha : ∀ j, IsAlgebraic (RatFunc ℂ) (ofMero (f j) (hf j).meromorphicAt))
    (hd : ∀ i j, i≠j → ∀ c : ℂ, ¬((fun z => f i z-f j z) =ᶠ[𝓝[≠] 0] fun _ => c))
    (hp : ∃ j, p j≠0) :
    ∃ᶠ v : ℝ in 𝓝 0, ∑ j, (p j).eval (v:ℂ)*Complex.exp (f j v)≠0 := by
  by_contra h
  have hz : ∀ᶠ v : ℝ in 𝓝 0, ∑ j, (p j).eval (v:ℂ)*Complex.exp (f j v)=0 := by
    simpa only [not_frequently,not_not] using h
  let a (j : J) (z : ℂ) := (p j).eval z
  have han (j : J) : AnalyticAt ℂ (a j) 0 :=
    Differentiable.analyticAt (fun _ => (p j).differentiableAt) 0
  have halg (j : J) : IsAlgebraic (RatFunc ℂ) (ofMero (a j) (han j).meromorphicAt) := by
    let r := algebraMap ℂ[X] (RatFunc ℂ) (p j)
    have he : algebraMap (RatFunc ℂ) MeroGerm r=ofMero (a j) (han j).meromorphicAt := by
      change ratGerm (algebraMap ℂ[X] (RatFunc ℂ) (p j))=_
      rw [ratGerm,RatFunc.liftRingHom_algebraMap]
      exact aeval_zGerm (p j)
    rw [←he]
    exact isAlgebraic_algebraMap _
  obtain ⟨j,hj⟩ := hp
  have hzero := weighted_exp_sum_real_slice f a hf han ha halg hd hz j
  exact aeval_zGerm_ne_zero hj ((aeval_zGerm (p j)).trans hzero)

#print axioms polynomial_weight_escape
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.CircuitContacts
