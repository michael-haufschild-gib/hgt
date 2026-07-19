import GaloisForLFunctions.HTGeometry.MultiplicativeGaugeFullRankResidual

/-!
# Full expanded rank along an affine density chart

A chart that perturbs the density additively, `u ↦ base + ι u`, satisfies the affine reachability
requirement with no analytic input whatsoever: the displacement identity is the linearity of `ι`,
and the perturbed parameter is `u₀ + h` itself, at distance exactly `‖h‖`.

This is the chart of the Nevanlinna carrier family, whose densities are `baseDensity + w` for `w` in
a closed subspace.  The multiplicative gauge is needed only where positivity of the density has to
be preserved; where the family is already a linear slice, reachability costs nothing and the whole
genericity conclusion rests on surjectivity of the jet map alone.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Affine reachability from an additive chart.**  For a density chart `u ↦ base + ι u` the
reachability hypothesis holds with `L = J ∘ ι`, exactly and with no smallness condition. -/
theorem affine_reachability_of_affine_chart
    {X D σ : Type*} [Fintype σ]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (base : D) (i : X →L[ℝ] D) (J : D →L[ℝ] (σ → ℂ))
    (hsurj : Function.Surjective (J.comp i)) :
    ∀ u₀ : X, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∃ L : X →L[ℝ] (σ → ℂ), Function.Surjective L ∧
        ∀ h : X, ‖h‖ < δ → ∃ u : X, dist u u₀ < ε ∧
          (fun x => J (base + i x)) u = (fun x => J (base + i x)) u₀ + L h := by
  intro u₀ ε hε
  refine ⟨ε, hε, J.comp i, hsurj, ?_⟩
  intro h hh
  refine ⟨u₀ + h, ?_, ?_⟩
  · simpa [dist_eq_norm] using hh
  · show J (base + i (u₀ + h)) = J (base + i u₀) + J (i h)
    simp only [map_add, add_assoc]

/-- **Full expanded rank is generic along an affine density chart.**  With the jet map surjective on
the chart directions, the parameters carrying full expanded column rank are open, dense and
residual.  No reachability, transversality or differentiability hypothesis remains. -/
theorem exists_nodes_residual_expandedMatrix_of_affine_chart
    {κ X D : Type} [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (q n : ℕ) (exponent : κ → (Fin n →₀ ℕ)) (hexp : Function.Injective exponent)
    (base : D) (i : X →L[ℝ] D)
    (J : D →L[ℝ] ((κ × Fin (q + 1)) × Fin n → ℂ))
    (hsurj : Function.Surjective (J.comp i)) :
    ∃ z : κ × Fin (q + 1) → ℂ,
      Function.Injective z ∧
      IsOpen {u : X | Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent (J (base + i u))).mulVec} ∧
      Dense {u : X | Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent (J (base + i u))).mulVec} ∧
      {u : X | Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent
          (J (base + i u))).mulVec} ∈ residual X :=
  exists_nodes_residual_expandedMatrix_mulVec_injective q n exponent hexp
    (fun u => J (base + i u))
    (J.continuous.comp (continuous_const.add i.continuous))
    (affine_reachability_of_affine_chart base i J hsurj)

end

end GaloisForLFunctions.HTGeometry
