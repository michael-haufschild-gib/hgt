import GaloisForLFunctions.HTGeometry.ExpandedJetDeterminantGenericity

/-!
# Residual full expanded rank, and reachability from a multiplicative chart

Two complements to the density statement.

First, full expanded rank is an *open* condition on the parameter when the jet map is continuous,
because it is the nonvanishing of a determinant depending continuously on the jets.  Open and dense
gives residual, which is the form the countable pattern intersection consumes.

Second, the affine reachability hypothesis is supplied by any chart that perturbs multiplicatively.
If the jets are a continuous linear image `J` of a density, and the chart moves the density from
`G u₀` to `G u₀ + M u₀ h` for small `h`, then the jets move by exactly `J ∘ M u₀`, with no
linearization error.  Surjectivity of that composite is surjectivity of the two factors.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Openness and residuality of full expanded rank.**  For a continuous jet map, the parameters
carrying full expanded column rank form an open set; combined with density it is residual. -/
theorem exists_nodes_residual_expandedMatrix_mulVec_injective
    {κ X : Type} [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (q n : ℕ) (exponent : κ → (Fin n →₀ ℕ)) (hexp : Function.Injective exponent)
    (F : X → ((κ × Fin (q + 1)) × Fin n → ℂ)) (hF : Continuous F)
    (hreach : ∀ u₀ : X, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∃ L : X →L[ℝ] ((κ × Fin (q + 1)) × Fin n → ℂ), Function.Surjective L ∧
          ∀ h : X, ‖h‖ < δ → ∃ u : X, dist u u₀ < ε ∧ F u = F u₀ + L h) :
    ∃ z : κ × Fin (q + 1) → ℂ,
      Function.Injective z ∧
      IsOpen {u : X | Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent (F u)).mulVec} ∧
      Dense {u : X | Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent (F u)).mulVec} ∧
      {u : X | Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent (F u)).mulVec} ∈ residual X := by
  classical
  obtain ⟨z, hz, hdense⟩ :=
    exists_nodes_dense_expandedMatrix_mulVec_injective q n exponent hexp F hreach
  have hset : {u : X | Function.Injective
      (expandedDifferentialEvaluationMatrix q n z exponent (F u)).mulVec} =
      (fun u => (expandedDifferentialEvaluationMatrix q n z exponent (F u)).det) ⁻¹'
        ({0}ᶜ : Set ℂ) := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have hcont : Continuous fun u =>
      (expandedDifferentialEvaluationMatrix q n z exponent (F u)).det :=
    ((continuous_expandedDifferentialEvaluationMatrix q n z exponent).comp hF).matrix_det
  have hopen : IsOpen {u : X | Function.Injective
      (expandedDifferentialEvaluationMatrix q n z exponent (F u)).mulVec} := by
    rw [hset]
    exact isOpen_compl_singleton.preimage hcont
  exact ⟨z, hz, hopen, hdense, residual_of_dense_open hopen hdense⟩

/-- **Affine reachability from a multiplicative chart.**  If the jets are a continuous linear image
of a density and the chart perturbs the density by a surjective linear map, the jets are reachable
affinely.  No derivative of the chart appears: the identity `G u = G u₀ + M u₀ h` is exact. -/
theorem affine_reachability_of_multiplicative_chart
    {X D σ : Type*} [Fintype σ]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (G : X → D) (J : D →L[ℝ] (σ → ℂ)) (hJ : Function.Surjective J)
    (M : X → (X →L[ℝ] D)) (hM : ∀ u₀, Function.Surjective (M u₀))
    (hchart : ∀ (u₀ : X) (ε : ℝ), 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ h : X, ‖h‖ < δ → ∃ u : X, dist u u₀ < ε ∧ G u = G u₀ + M u₀ h) :
    ∀ u₀ : X, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∃ L : X →L[ℝ] (σ → ℂ), Function.Surjective L ∧
        ∀ h : X, ‖h‖ < δ → ∃ u : X, dist u u₀ < ε ∧
          (fun x => J (G x)) u = (fun x => J (G x)) u₀ + L h := by
  intro u₀ ε hε
  obtain ⟨δ, hδ, hch⟩ := hchart u₀ ε hε
  refine ⟨δ, hδ, J.comp (M u₀), hJ.comp (hM u₀), ?_⟩
  intro h hh
  obtain ⟨u, hdist, hGu⟩ := hch h hh
  refine ⟨u, hdist, ?_⟩
  show J (G u) = J (G u₀) + J (M u₀ h)
  rw [hGu, map_add]

/-- **Full expanded rank is generic along a multiplicative chart.**  Combining the two: for a
continuous multiplicatively-perturbed chart into the densities, the parameters carrying full
expanded column rank are open, dense and residual. -/
theorem exists_nodes_residual_expandedMatrix_of_multiplicative_chart
    {κ X D : Type} [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (q n : ℕ) (exponent : κ → (Fin n →₀ ℕ)) (hexp : Function.Injective exponent)
    (G : X → D) (hG : Continuous G)
    (J : D →L[ℝ] ((κ × Fin (q + 1)) × Fin n → ℂ)) (hJ : Function.Surjective J)
    (M : X → (X →L[ℝ] D)) (hM : ∀ u₀, Function.Surjective (M u₀))
    (hchart : ∀ (u₀ : X) (ε : ℝ), 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ h : X, ‖h‖ < δ → ∃ u : X, dist u u₀ < ε ∧ G u = G u₀ + M u₀ h) :
    ∃ z : κ × Fin (q + 1) → ℂ,
      Function.Injective z ∧
      IsOpen {u : X | Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent (J (G u))).mulVec} ∧
      Dense {u : X | Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent (J (G u))).mulVec} ∧
      {u : X | Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent (J (G u))).mulVec} ∈ residual X :=
  exists_nodes_residual_expandedMatrix_mulVec_injective q n exponent hexp
    (fun u => J (G u)) (J.continuous.comp hG)
    (affine_reachability_of_multiplicative_chart G J hJ M hM hchart)

end

end GaloisForLFunctions.HTGeometry
