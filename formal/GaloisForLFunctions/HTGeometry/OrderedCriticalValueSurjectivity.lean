import GaloisForLFunctions.HTGeometry.OrderedCriticalValueDifferential
import GaloisForLFunctions.HTGeometry.ComplexConfigurationSpace

/-!
# Surjectivity of the ordered critical-value map

Properness closes the actual image. Local inverses make its intersection with the
connected distinct-value locus open and nonempty. Density then includes all collisions.
This realizes critical values; identification of prescribed covering monodromy is separate.
-/

open Set Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
noncomputable section

/-- Centering an injective tuple gives a parameter with distinct critical positions. -/
theorem exists_injective_position (n : ℕ) : ∃ v : Parameter n, Function.Injective (position v) := by
  let u : Fin (n + 1) → ℂ := fun j => (j.val : ℂ)
  let μ : ℂ := (∑ j, u j) / (n + 1 : ℂ)
  let v : Parameter n := (fun i => u i.succ - μ, 0)
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
  have hμ : (n + 1 : ℂ) * μ = ∑ j, u j := by
    dsimp [μ]
    field_simp
  have hpos : ∀ j, position v j = u j - μ := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [position, v, Fin.cons_zero, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Fin.sum_univ_succ] at hμ
      linear_combination hμ
    · simp [position, v]
  refine ⟨v, ?_⟩
  intro i j hij
  apply FiniteComplexConfiguration.injective_natTuple (n + 1)
  rw [hpos, hpos] at hij
  exact sub_left_inj.mp hij

/-- The actual critical-value map reaches at least one distinct-value configuration. -/
theorem exists_injective_valuesWithConstant (n : ℕ) :
    ∃ v : Parameter n, Function.Injective (valuesWithConstant v) := by
  obtain ⟨v, hv⟩ := exists_injective_position n
  obtain ⟨e, he, hve⟩ := exists_openPartialHomeomorph_valuesWithConstant v hv
  obtain ⟨b, hbt, hbc⟩ := (FiniteComplexConfiguration.dense_space (n + 1)).inter_open_nonempty
    e.target e.open_target ⟨e v, e.map_source hve⟩
  refine ⟨e.symm b, ?_⟩
  have hb : valuesWithConstant (e.symm b) = b := by
    rw [← he]
    exact e.right_inv hbt
  rw [hb]
  exact hbc

/-- Every ordered critical-value tuple is realized by the constructed monic centered polynomial
family, including tuples with collisions. -/
theorem surjective_valuesWithConstant (n : ℕ) :
    Function.Surjective (valuesWithConstant (n := n)) := by
  let R : Set (Fin (n + 1) → ℂ) := Set.range (valuesWithConstant (n := n))
  have hR : IsClosed R := by
    simpa only [Set.image_univ] using
      (isProperMap_valuesWithConstant n).isClosedMap Set.univ isClosed_univ
  let Cfg := FiniteComplexConfiguration.space (n + 1)
  let I : Set Cfg := Subtype.val ⁻¹' R
  haveI : PreconnectedSpace Cfg := isPreconnected_iff_preconnectedSpace.mp
    (FiniteComplexConfiguration.isPathConnected_space (n + 1)).isConnected.isPreconnected
  have hIc : IsClosed I := hR.preimage continuous_subtype_val
  have hIo : IsOpen I := by
    apply isOpen_iff_mem_nhds.mpr
    intro b hb
    obtain ⟨v, hvb⟩ := hb
    have hv : Function.Injective (valuesWithConstant v) := hvb.symm ▸ b.property
    obtain ⟨e, he, hve⟩ := exists_openPartialHomeomorph_valuesWithConstant v
      (injective_position_of_injective_values v hv)
    have hbt : b.val ∈ e.target := by
      rw [← hvb, ← he]
      exact e.map_source hve
    have hN : Subtype.val ⁻¹' e.target ∈ 𝓝 b :=
      (e.open_target.preimage continuous_subtype_val).mem_nhds hbt
    apply mem_of_superset hN
    intro c hc
    refine ⟨e.symm c.val, ?_⟩
    rw [← he]
    exact e.right_inv hc
  have hIn : I.Nonempty := by
    obtain ⟨v, hv⟩ := exists_injective_valuesWithConstant n
    exact ⟨⟨valuesWithConstant v, hv⟩, v, rfl⟩
  have hIall : I = Set.univ := (show IsClopen I from ⟨hIc, hIo⟩).eq_univ hIn
  have hsub : Cfg ⊆ R := by
    intro b hb
    have hi : (⟨b, hb⟩ : Cfg) ∈ I := by rw [hIall]; trivial
    exact hi
  have hdense : Dense R := (FiniteComplexConfiguration.dense_space (n + 1)).mono hsub
  intro b
  have hb := hdense b
  rw [hR.closure_eq] at hb
  exact hb

end
end GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
