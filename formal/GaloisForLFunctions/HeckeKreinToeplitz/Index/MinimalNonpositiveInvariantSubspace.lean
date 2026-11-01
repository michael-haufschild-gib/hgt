import GaloisForLFunctions.HeckeKreinToeplitz.Index.WeaklyCompactNonpositiveDirections

/-!
# Minimal invariant subspaces containing a nonpositive direction

Weak compactness preserves a normalized nonpositive vector under decreasing
intersections. Zorn's lemma therefore produces a minimal closed subspace
invariant under every operator and its inverse.
-/

noncomputable section
set_option autoImplicit false
open Set

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {ι H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]

/-- Invariance under a family of invertible maps in both directions. -/
def IsBiInvariant (T : ι → (H × E) ≃L[ℂ] (H × E))
    (W : Submodule ℂ (H × E)) : Prop :=
  ∀ i v, v ∈ W → T i v ∈ W ∧ (T i).symm v ∈ W

/-- The subspace contains a nonzero vector with nonpositive square. -/
def HasNonpositiveDirection (W : Submodule ℂ (H × E)) : Prop :=
  ∃ v ∈ W, v ≠ 0 ∧ (pairing v v).re ≤ 0

/-- A closed invariant subspace with a nonpositive direction contains a minimal one. -/
theorem exists_minimal_nonpositive_invariant_subspace
    (T : ι → (H × E) ≃L[ℂ] (H × E)) (W₀ : Submodule ℂ (H × E))
    (hc₀ : IsClosed (W₀ : Set (H × E))) (hi₀ : IsBiInvariant T W₀)
    (hn₀ : HasNonpositiveDirection W₀) :
    ∃ W ≤ W₀, Minimal (fun V : Submodule ℂ (H × E) =>
      IsClosed (V : Set (H × E)) ∧ IsBiInvariant T V ∧ HasNonpositiveDirection V) W := by
  let P : Submodule ℂ (H × E) → Prop := fun W =>
    IsClosed (W : Set (H × E)) ∧ IsBiInvariant T W ∧ HasNonpositiveDirection W
  let S : Set (OrderDual (Submodule ℂ (H × E))) := {W | P W}
  have hchains : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hc hchain y hy
    let d : Set (Submodule ℂ (H × E)) := c
    have hdchain : IsChain (· ≤ ·) d := by
      intro a ha b hb hab
      exact (hchain ha hb hab).symm
    have hdclosed : ∀ W ∈ d, IsClosed (W : Set (H × E)) := fun W hW => (hc hW).1
    have hdnonpos : ∀ W ∈ d, HasNonpositiveDirection W := fun W hW => (hc hW).2.2
    let Z : Submodule ℂ (H × E) := sInf d
    have hZ : P Z := by
      refine ⟨?_, ?_, exists_nonpositive_mem_sInf d ⟨y, hy⟩ hdchain hdclosed hdnonpos⟩
      · change IsClosed ((sInf d : Submodule ℂ (H × E)) : Set (H × E))
        rw [Submodule.coe_sInf]
        exact isClosed_iInter fun W => isClosed_iInter fun hW => hdclosed W hW
      · intro i v hv
        have hall := Submodule.mem_sInf.mp hv
        exact ⟨Submodule.mem_sInf.mpr fun W hW => ((hc hW).2.1 i v (hall W hW)).1,
          Submodule.mem_sInf.mpr fun W hW => ((hc hW).2.1 i v (hall W hW)).2⟩
    refine ⟨Z, hZ, ?_⟩
    intro z hz
    change Z ≤ OrderDual.ofDual z
    exact sInf_le hz
  obtain ⟨W, hW₀, hW⟩ := zorn_le_nonempty₀ S hchains W₀ ⟨hc₀, hi₀, hn₀⟩
  exact ⟨W, hW₀, hW⟩

#print axioms exists_minimal_nonpositive_invariant_subspace

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
