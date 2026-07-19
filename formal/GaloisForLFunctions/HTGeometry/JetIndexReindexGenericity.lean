import GaloisForLFunctions.HTGeometry.AffineChartFullRankGenericity
import GaloisForLFunctions.HTGeometry.FlattenedCauchyJetRigidity

/-!
# Reindexing the jet coordinates

The jet map of a reweighting lands in `jetIndex n → ℂ`, indexed by a sigma type over the shift
family, while the expanded evaluation matrix indexes its jets by row and flattened coordinate.  The
two index types differ only by a bijection, and precomposition with a bijection is a continuous
linear isomorphism, so surjectivity transports across it.

With the identity chart on the density space the genericity conclusion then needs nothing beyond
surjectivity of the jet map itself.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Precomposition of a finite tuple by a reindexing map, as a continuous linear map. -/
def funLeftCLM {α β : Type*} (e : β → α) : (α → ℂ) →L[ℝ] (β → ℂ) where
  toLinearMap := LinearMap.funLeft ℝ ℂ e
  cont := continuous_pi fun b => continuous_apply (e b)

@[simp]
theorem funLeftCLM_apply {α β : Type*} (e : β → α) (f : α → ℂ) (b : β) :
    funLeftCLM e f b = f (e b) := rfl

/-- Reindexing by a bijection preserves surjectivity of a map into tuples. -/
theorem surjective_funLeftCLM_comp {α β γ : Type*} (e : β ≃ α)
    (F : γ → (α → ℂ)) (hF : Function.Surjective F) :
    Function.Surjective fun x => funLeftCLM (e : β → α) (F x) := by
  intro g
  obtain ⟨x, hx⟩ := hF fun a => g (e.symm a)
  refine ⟨x, ?_⟩
  funext b
  show funLeftCLM (e : β → α) (F x) b = g b
  rw [funLeftCLM_apply, hx]
  simp

/-- The jet index of a shift family repeated over rows splits as rows times the single-row jet
index. -/
def jetIndexProdEquiv {ι row : Type*} (n : ι → ℕ) :
    (Σ p : row × ι, Fin (n p.2)) ≃ row × (Σ i : ι, Fin (n i)) where
  toFun s := (s.1.1, ⟨s.1.2, s.2⟩)
  invFun p := ⟨(p.1, p.2.1), p.2.2⟩
  left_inv s := by
    obtain ⟨⟨r, i⟩, k⟩ := s
    rfl
  right_inv p := by
    obtain ⟨r, ⟨i, k⟩⟩ := p
    rfl

/-- **Full expanded rank is generic for a surjective jet map.**  Along the identity chart on the
density space, with the jet coordinates matched to the matrix coordinates by any bijection, the
densities carrying full expanded column rank are open, dense and residual.

The only hypothesis is surjectivity of the jet map. -/
theorem exists_nodes_residual_expandedMatrix_of_surjective_jetMap
    {κ D J' : Type} [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
    (q n : ℕ) (exponent : κ → (Fin n →₀ ℕ)) (hexp : Function.Injective exponent)
    (J : D →L[ℝ] (J' → ℂ)) (hJ : Function.Surjective J)
    (e : ((κ × Fin (q + 1)) × Fin n) ≃ J') :
    ∃ z : κ × Fin (q + 1) → ℂ,
      Function.Injective z ∧
      IsOpen {u : D | Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent
          (funLeftCLM (e : ((κ × Fin (q + 1)) × Fin n) → J') (J u))).mulVec} ∧
      Dense {u : D | Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent
          (funLeftCLM (e : ((κ × Fin (q + 1)) × Fin n) → J') (J u))).mulVec} ∧
      {u : D | Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent
          (funLeftCLM (e : ((κ × Fin (q + 1)) × Fin n) → J') (J u))).mulVec} ∈ residual D := by
  classical
  set K : D →L[ℝ] (((κ × Fin (q + 1)) × Fin n) → ℂ) :=
    (funLeftCLM (e : ((κ × Fin (q + 1)) × Fin n) → J')).comp J with hK
  have hKsurj : Function.Surjective K := surjective_funLeftCLM_comp e J hJ
  refine exists_nodes_residual_expandedMatrix_mulVec_injective q n exponent hexp
    (fun u => K u) K.continuous ?_
  -- The identity chart: the perturbed parameter is the displacement itself.
  intro u₀ ε hε
  refine ⟨ε, hε, K, hKsurj, ?_⟩
  intro h hh
  refine ⟨u₀ + h, ?_, ?_⟩
  · simpa [dist_eq_norm] using hh
  · show K (u₀ + h) = K u₀ + K h
    rw [map_add]

end

end GaloisForLFunctions.HTGeometry
