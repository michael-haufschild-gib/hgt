import GaloisForLFunctions.RHTower.PaperHeatHankelCompletion

/-! # Exact off-line negative index of the compact heat-Hankel completion -/

namespace RHTower.PaperHeatHankel
noncomputable section
open Polynomial GaloisForLFunctions.HTGeometry KernelClosedSpanInertia

/-- The original polynomial subspace embeds with its dimension and form unchanged. -/
theorem map_negative_subspace (a : Time) (V : Submodule ℂ ℂ[X]) :
    Module.finrank ℂ (V.map (polynomialEmbedding a)) = Module.finrank ℂ V ∧
      ((∀ P ∈ V, P ≠ 0 → (heatHankel a.val P P).re < 0) →
        ∀ x ∈ V.map (polynomialEmbedding a), x ≠ 0 →
          (inner ℂ x (operator a x)).re < 0) := by
  refine ⟨(Submodule.equivMapOfInjective _ (polynomialEmbedding_injective a) V).symm.finrank_eq, ?_⟩
  intro hV x hx hx0
  obtain ⟨P, hP, rfl⟩ := hx
  have hP0 : P ≠ 0 := by intro hz; apply hx0; simp [hz]
  change (inner ℂ (vector a P) (operator a (vector a P))).re < 0
  rw [inner_vector_operator]
  exact hV P hP hP0

theorem negativeTuple_dimension_le (a : Time) (hU : xiUpperFrequencies.Finite)
    {r : ℕ} (hv : ∃ v : Fin r → Space, IsNegativeTuple (operator a) v) :
    r ≤ hU.toFinset.card := by
  obtain ⟨P, hP⟩ := (exists_negativeTuple_iff_polynomials a r).mp hv
  let L : (Fin r → ℂ) →ₗ[ℂ] ℂ[X] := Fintype.linearCombination ℂ P
  have hL (c : Fin r → ℂ) : L c = ∑ i, c i • P i :=
    Fintype.linearCombination_apply ℂ P c
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra hn
    have h := hP c hn
    rw [← hL, hc] at h
    simp [heatHankel, heatHankelTermAt] at h
  have hneg : ∀ Q ∈ LinearMap.range L, Q ≠ 0 → (heatHankel a.val Q Q).re < 0 := by
    rintro _ ⟨c, rfl⟩ hc
    rw [hL]
    exact hP c (fun hz => hc (by rw [hz, map_zero]))
  have h := finrank_le_of_heatHankel_neg a.property hU (LinearMap.range L) hneg
  simpa only [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] using h

theorem negative_subspace_dimension_le (a : Time) (hU : xiUpperFrequencies.Finite)
    (W : Submodule ℂ Space)
    (hW : ∀ x ∈ W, x ≠ 0 → (inner ℂ x (operator a x)).re < 0) :
    Module.finrank ℂ W ≤ hU.toFinset.card := by
  classical
  rcases Nat.eq_zero_or_pos (Module.finrank ℂ W) with hz | hp
  · rw [hz]; exact Nat.zero_le _
  letI : FiniteDimensional ℂ W := Module.finite_of_finrank_pos hp
  let b := Module.finBasis ℂ W
  apply negativeTuple_dimension_le a hU
  refine ⟨fun i => (b i : Space), fun c hc => ?_⟩
  let y : W := ∑ i, c i • b i
  have hy : y ≠ 0 := by
    intro hz
    have hzero : c = 0 := by
      funext i
      have he := congrArg (fun w : W => b.repr w i) hz
      simpa [y, Finsupp.single_apply] using he
    simp [hzero] at hc
  have he : sectionSynthesis (fun i => (b i : Space)) c = (y : Space) := by
    simp only [sectionSynthesis, y, Submodule.coe_sum, Submodule.coe_smul]
  rw [sectionQuadratic, he]
  exact hW y y.property (fun h => hy (Subtype.ext h))

theorem operator_negativeIndex_eq_card (a : Time) (hU : xiUpperFrequencies.Finite) :
    (∀ W : Submodule ℂ Space,
      (∀ x ∈ W, x ≠ 0 → (inner ℂ x (operator a x)).re < 0) →
        Module.finrank ℂ W ≤ hU.toFinset.card) ∧
    ∃ W : Submodule ℂ Space, Module.finrank ℂ W = hU.toFinset.card ∧
      ∀ x ∈ W, x ≠ 0 → (inner ℂ x (operator a x)).re < 0 := by
  refine ⟨negative_subspace_dimension_le a hU, ?_⟩
  obtain ⟨V, hdim, hV⟩ := (heatHankel_negativeIndex_eq_card a.property hU).2
  have h := map_negative_subspace a V
  exact ⟨V.map (polynomialEmbedding a), h.1.trans hdim, h.2 hV⟩

theorem operator_negative_subspace_of_infinite (a : Time) (hU : xiUpperFrequencies.Infinite)
    (n : ℕ) : ∃ W : Submodule ℂ Space, Module.finrank ℂ W = n ∧
      ∀ x ∈ W, x ≠ 0 → (inner ℂ x (operator a x)).re < 0 := by
  obtain ⟨V, hdim, hV⟩ := heatHankel_negative_subspace_of_infinite a.property hU n
  have h := map_negative_subspace a V
  exact ⟨V.map (polynomialEmbedding a), h.1.trans hdim, h.2 hV⟩

end
end RHTower.PaperHeatHankel
