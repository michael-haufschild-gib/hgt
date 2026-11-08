import GaloisForLFunctions.HeightHomotopyArithmeticCounts.SpacingDefiniteFamilies
import GaloisForLFunctions.HeightHomotopyArithmeticCounts.WeightedTorsionCompactness

/-!
# Finite constraints cannot remove either sign of the torsion limit

Orthogonal prime-pair families yield injective definite subspaces of every
finite dimension. A map into a finite-dimensional space has a nonzero kernel
on a sufficiently large such subspace. Thus any finite family of linear
constraints leaves both signs, and every finite-rank bilinear or Hilbert
operator correction retains indefinite quadratic values.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts

private theorem spacing_synthesis_neg {ι : Type*} [Fintype ι] (δ : ℝ) (hδ : 0<δ)
    (u : ι → WeightedProbe δ)
    (hneg : ∀ i, spacingLimitOperator δ hδ (u i) (u i)<0)
    (horth : ∀ i j, i≠j → spacingLimitOperator δ hδ (u i) (u j)=0)
    (a : ι → ℝ) (ha : a≠0) :
    spacingLimitOperator δ hδ (spacingProbeSynthesis δ u a) (spacingProbeSynthesis δ u a)<0 := by
  rw [spacingProbeSynthesis_energy δ hδ u horth]
  have hex : ∃ i, a i≠0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  obtain ⟨i,hi⟩ := hex
  exact sum_neg' (fun j _ => mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hneg j).le)
    ⟨i,mem_univ i,mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hi) (hneg i)⟩

private theorem spacing_synthesis_pos {ι : Type*} [Fintype ι] (δ : ℝ) (hδ : 0<δ)
    (u : ι → WeightedProbe δ)
    (hpos : ∀ i, 0<spacingLimitOperator δ hδ (u i) (u i))
    (horth : ∀ i j, i≠j → spacingLimitOperator δ hδ (u i) (u j)=0)
    (a : ι → ℝ) (ha : a≠0) :
    0<spacingLimitOperator δ hδ (spacingProbeSynthesis δ u a) (spacingProbeSynthesis δ u a) := by
  rw [spacingProbeSynthesis_energy δ hδ u horth]
  have hex : ∃ i, a i≠0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  obtain ⟨i,hi⟩ := hex
  exact sum_pos' (fun j _ => mul_nonneg (sq_nonneg _) (hpos j).le)
    ⟨i,mem_univ i,mul_pos (sq_pos_of_ne_zero hi) (hpos i)⟩

/-- The actual arithmetic limit has negative definite subspaces of every finite dimension. -/
theorem spacingLimitOperator_negative_subspace (δ : ℝ) (hδ : 0<δ) (m : ℕ) :
    ∃ T : (Fin (m+1) → ℝ) →ₗ[ℝ] WeightedProbe δ, Function.Injective T ∧
      ∀ a, a≠0 → spacingLimitOperator δ hδ (T a) (T a)<0 := by
  obtain ⟨u,hneg,horth⟩ := spacing_exists_negative_family δ hδ m
  refine ⟨spacingProbeSynthesis δ u,?_,spacing_synthesis_neg δ hδ u hneg horth⟩
  intro a b hab
  by_contra hne
  have hz : spacingProbeSynthesis δ u (a-b)=0 := by rw [map_sub,hab,sub_self]
  have hn := spacing_synthesis_neg δ hδ u hneg horth (a-b) (sub_ne_zero.mpr hne)
  rw [hz,map_zero] at hn
  exact (lt_irrefl 0) hn

/-- The actual arithmetic limit also has positive definite subspaces of every finite dimension. -/
theorem spacingLimitOperator_positive_subspace (δ : ℝ) (hδ : 0<δ) (m : ℕ) :
    ∃ T : (Fin (m+1) → ℝ) →ₗ[ℝ] WeightedProbe δ, Function.Injective T ∧
      ∀ a, a≠0 → 0<spacingLimitOperator δ hδ (T a) (T a) := by
  obtain ⟨u,hpos,horth⟩ := spacing_exists_positive_family δ hδ m
  refine ⟨spacingProbeSynthesis δ u,?_,spacing_synthesis_pos δ hδ u hpos horth⟩
  intro a b hab
  by_contra hne
  have hz : spacingProbeSynthesis δ u (a-b)=0 := by rw [map_sub,hab,sub_self]
  have hp := spacing_synthesis_pos δ hδ u hpos horth (a-b) (sub_ne_zero.mpr hne)
  rw [hz,map_zero] at hp
  exact (lt_irrefl 0) hp

private theorem spacing_constraint_kernel {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (F : (Fin (Module.finrank ℝ V+1) → ℝ) →ₗ[ℝ] V) :
    ∃ a, a≠0 ∧ F a=0 := by
  have hni : ¬Function.Injective F := by
    intro hi
    have h := LinearMap.finrank_le_finrank_of_injective hi
    rw [Module.finrank_fin_fun] at h
    omega
  simp only [Function.Injective] at hni
  push Not at hni
  obtain ⟨a,b,hab,hne⟩ := hni
  refine ⟨a-b,sub_ne_zero.mpr hne,?_⟩
  rw [map_sub,hab,sub_self]

/-- Any finite-dimensional family of linear constraints leaves an actual negative torsion probe. -/
theorem spacingLimitOperator_negative_of_finite_constraints (δ : ℝ) (hδ : 0<δ)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (ℓ : WeightedProbe δ →ₗ[ℝ] V) :
    ∃ u : WeightedProbe δ, ℓ u=0 ∧ spacingLimitOperator δ hδ u u<0 := by
  obtain ⟨T,_,hneg⟩ := spacingLimitOperator_negative_subspace δ hδ (Module.finrank ℝ V)
  obtain ⟨a,ha,hker⟩ := spacing_constraint_kernel (ℓ.comp T)
  exact ⟨T a,hker,hneg a ha⟩

/-- Any finite-dimensional family of linear constraints also leaves a positive torsion probe. -/
theorem spacingLimitOperator_positive_of_finite_constraints (δ : ℝ) (hδ : 0<δ)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (ℓ : WeightedProbe δ →ₗ[ℝ] V) :
    ∃ u : WeightedProbe δ, ℓ u=0 ∧ 0<spacingLimitOperator δ hδ u u := by
  obtain ⟨T,_,hpos⟩ := spacingLimitOperator_positive_subspace δ hδ (Module.finrank ℝ V)
  obtain ⟨a,ha,hker⟩ := spacing_constraint_kernel (ℓ.comp T)
  exact ⟨T a,hker,hpos a ha⟩

/-- Every finite-rank bilinear correction leaves the arithmetic limit indefinite. -/
theorem spacingLimitOperator_finite_rank_correction_indefinite (δ : ℝ) (hδ : 0<δ)
    (C : WeightedProbe δ →ₗ[ℝ] WeightedProbe δ →ₗ[ℝ] ℝ)
    [FiniteDimensional ℝ (LinearMap.range C)] :
    (∃ u : WeightedProbe δ, spacingLimitOperator δ hδ u u+C u u<0) ∧
      ∃ v : WeightedProbe δ, 0<spacingLimitOperator δ hδ v v+C v v := by
  obtain ⟨u,hu,hn⟩ := spacingLimitOperator_negative_of_finite_constraints δ hδ (V := LinearMap.range C) C.rangeRestrict
  obtain ⟨v,hv,hp⟩ := spacingLimitOperator_positive_of_finite_constraints δ hδ (V := LinearMap.range C) C.rangeRestrict
  have hCu : C u=0 := congrArg Subtype.val hu
  have hCv : C v=0 := congrArg Subtype.val hv
  refine ⟨⟨u,?_⟩,v,?_⟩
  · simpa only [hCu,LinearMap.zero_apply,add_zero] using hn
  · simpa only [hCv,LinearMap.zero_apply,add_zero] using hp

/-- Adding a finite-rank Hilbert operator cannot remove either sign of the actual torsion limit. -/
theorem spacingLimitHilbertOperator_finite_rank_indefinite (δ : ℝ) (hδ : 0<δ)
    (K : WeightedProbe δ →L[ℝ] WeightedProbe δ)
    [FiniteDimensional ℝ (LinearMap.range K.toLinearMap)] :
    (∃ u : WeightedProbe δ, inner ℝ ((spacingLimitHilbertOperator δ hδ+K) u) u<0) ∧
      ∃ v : WeightedProbe δ, 0 < inner ℝ ((spacingLimitHilbertOperator δ hδ+K) v) v := by
  obtain ⟨u,hu,hn⟩ := spacingLimitOperator_negative_of_finite_constraints δ hδ
    (V := LinearMap.range K.toLinearMap) K.toLinearMap.rangeRestrict
  obtain ⟨v,hv,hp⟩ := spacingLimitOperator_positive_of_finite_constraints δ hδ
    (V := LinearMap.range K.toLinearMap) K.toLinearMap.rangeRestrict
  have hKu : K u=0 := congrArg Subtype.val hu
  have hKv : K v=0 := congrArg Subtype.val hv
  refine ⟨⟨u,?_⟩,v,?_⟩
  · rw [add_apply,hKu,add_zero,spacingLimitHilbertOperator_inner]
    exact hn
  · rw [add_apply,hKv,add_zero,spacingLimitHilbertOperator_inner]
    exact hp

#print axioms spacingLimitOperator_negative_subspace
#print axioms spacingLimitOperator_positive_subspace
#print axioms spacingLimitOperator_negative_of_finite_constraints
#print axioms spacingLimitOperator_positive_of_finite_constraints
#print axioms spacingLimitOperator_finite_rank_correction_indefinite
#print axioms spacingLimitHilbertOperator_finite_rank_indefinite
end GaloisForLFunctions.HeightHomotopyArithmeticCounts
