import GaloisForLFunctions.RHTower.FiniteReverseResidualEndpointDeletion

/-!
# Sixth-moment IVT for a continuous reverse residual head

The finite selector produces a continuous cubic power sum whenever residual
mass and energy remain positive on a closed interval. Opposite endpoint
brackets then give an exact cubic trace. Source-specific admission and
brackets are separate obligations.
-/

namespace RHTower
noncomputable section

/-- Cubic trace after choosing one atom and selecting a padded residual head. -/
def oneHeadReverseCubic (E F : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  x^3 + ∑ i : Fin (N-1),
    (reverseResidualSelectorAux (E-x) (F-x^2) (N-1) (N-3) i)^3

theorem continuousOn_oneHeadReverseCubic
    {E F l u : ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Set.Icc l u, 0 < E-x ∧ 0 < F-x^2) :
    ContinuousOn (oneHeadReverseCubic E F N) (Set.Icc l u) := by
  rw [continuousOn_iff_continuous_restrict]
  have hA : Continuous (fun x : Set.Icc l u => E-(x:ℝ)) := by fun_prop
  have hB : Continuous (fun x : Set.Icc l u => F-(x:ℝ)^2) := by fun_prop
  have hSel : Continuous (fun x : Set.Icc l u =>
      reverseResidualSelectorAux (E-(x:ℝ)) (F-(x:ℝ)^2) (N-1) (N-3)) :=
    continuous_reverseResidualSelectorAux hA hB
      (fun x => (hpos x.val x.property).1)
      (fun x => (hpos x.val x.property).2) _ _
  have hSum : Continuous (fun x : Set.Icc l u =>
      ∑ i : Fin (N-1),
        (reverseResidualSelectorAux (E-(x:ℝ)) (F-(x:ℝ)^2)
          (N-1) (N-3) i)^3) := by
    apply continuous_finsetSum
    intro i hi
    exact ((continuous_apply i).comp hSel).pow 3
  exact (continuous_subtype_val.pow 3).add hSum

theorem exists_oneHeadReverseCubic_match
    {E F G l u : ℝ} {N : ℕ} (hlu : l ≤ u)
    (hpos : ∀ x ∈ Set.Icc l u, 0 < E-x ∧ 0 < F-x^2)
    (hlow : oneHeadReverseCubic E F N l ≤ G)
    (hhigh : G ≤ oneHeadReverseCubic E F N u) :
    ∃ x ∈ Set.Icc l u, oneHeadReverseCubic E F N x = G := by
  have hcont := continuousOn_oneHeadReverseCubic (N:=N) hpos
  have hmem : G ∈ Set.Icc (oneHeadReverseCubic E F N l)
      (oneHeadReverseCubic E F N u) := ⟨hlow,hhigh⟩
  obtain ⟨x,hx,heq⟩ := (intermediate_value_Icc hlu hcont) hmem
  exact ⟨x,hx,heq⟩

end
end RHTower
