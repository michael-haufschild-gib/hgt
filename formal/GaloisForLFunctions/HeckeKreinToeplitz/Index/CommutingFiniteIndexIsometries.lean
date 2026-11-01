import GaloisForLFunctions.HeckeKreinToeplitz.Index.MinimalNonpositiveInvariantSubspace
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ClosedSubspaceNonpositiveEigenvector
import GaloisForLFunctions.HTGeometry.FiniteCommutingFamiliesHaveCommonEigenvectors

/-!
# Common nonpositive eigenvectors for commuting finite-index isometries

A minimal closed invariant subspace either has a finite radical or admits a
complete signed Hilbert model. In the latter case each nonpositive eigenspace
is invariant under the whole family, so minimality makes every operator scalar.
-/

noncomputable section
set_option autoImplicit false
open Complex
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {ι H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]

omit [CompleteSpace H] [FiniteDimensional ℂ E] in
private theorem commute_inverse (T : ι → (H × E) ≃L[ℂ] (H × E))
    (hcomm : ∀ i j v, T i (T j v) = T j (T i v)) (i j : ι) (v : H × E) :
    T i ((T j).symm v) = (T j).symm (T i v) := by
  apply (T j).injective
  rw [← hcomm, (T j).apply_symm_apply, (T j).apply_symm_apply]

/-- Every closed common invariant subspace containing a nonpositive direction
contains a common nonpositive eigenvector, for an arbitrary commuting family. -/
theorem exists_common_nonpositive_eigenvector_in_subspace
    (T : ι → (H × E) ≃L[ℂ] (H × E))
    (hT : ∀ i v w, pairing (T i v) (T i w) = pairing v w)
    (hcomm : ∀ i j v, T i (T j v) = T j (T i v))
    (W₀ : Submodule ℂ (H × E)) (hc₀ : IsClosed (W₀ : Set (H × E)))
    (hi₀ : IsBiInvariant T W₀) (hn₀ : HasNonpositiveDirection W₀) :
    ∃ (w : H × E) (χ : ι → ℂ), w ∈ W₀ ∧ w ≠ 0 ∧ (pairing w w).re ≤ 0 ∧
      ∀ i, χ i ≠ 0 ∧ T i w = χ i • w := by
  classical
  obtain ⟨W, hWW₀, hmin⟩ := exists_minimal_nonpositive_invariant_subspace T W₀ hc₀ hi₀ hn₀
  have hcW := hmin.1.1
  have hiW := hmin.1.2.1
  have hnW := hmin.1.2.2
  by_cases hr : restrictedRadical W = ⊥
  · have hscalar : ∀ i, ∃ a : ℂ, ∀ v ∈ W, T i v = a • v := by
      intro i
      obtain ⟨w, a, hwW, hw, ha, hwq, hwe⟩ :=
        exists_nonpositive_eigenvector_closed_subspace W hcW hr hnW (T i) (hT i)
          (fun v hv => (hiW i v hv).1) (fun v hv => (hiW i v hv).2)
      let L : Submodule ℂ (H × E) := W ⊓
        ((T i).toLinearEquiv.toLinearMap - a • LinearMap.id).ker
      have hmem (v : H × E) : v ∈ L ↔ v ∈ W ∧ T i v = a • v := by
        simp only [L, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
        rfl
      have hcL : IsClosed (L : Set (H × E)) := by
        have heq : (L : Set (H × E)) = {v | v ∈ W ∧ T i v = a • v} := Set.ext hmem
        rw [heq]
        exact hcW.inter (isClosed_eq (T i).continuous (by fun_prop))
      have hiL : IsBiInvariant T L := by
        intro j v hv
        obtain ⟨hvW, hve⟩ := (hmem v).mp hv
        constructor
        · apply (hmem _).mpr
          refine ⟨(hiW j v hvW).1, ?_⟩
          rw [hcomm, hve, map_smul]
        · apply (hmem _).mpr
          refine ⟨(hiW j v hvW).2, ?_⟩
          rw [commute_inverse T hcomm, hve, map_smul]
      have hnL : HasNonpositiveDirection L := ⟨w, (hmem w).mpr ⟨hwW, hwe⟩, hw, hwq⟩
      have hWL : W ≤ L := hmin.2 ⟨hcL, hiL, hnL⟩ inf_le_left
      exact ⟨a, fun v hv => ((hmem v).mp (hWL hv)).2⟩
    choose χ hχ using hscalar
    obtain ⟨w, hwW, hw, hwq⟩ := hnW
    refine ⟨w, χ, hWW₀ hwW, hw, hwq, ?_⟩
    intro i
    have he := hχ i w hwW
    refine ⟨?_, he⟩
    intro hz
    rw [hz, zero_smul] at he
    exact hw ((T i).injective (he.trans (map_zero (T i)).symm))
  · let R := restrictedRadical W
    have hR : ∃ v : R, v ≠ 0 := by
      by_contra h
      push Not at h
      apply hr
      apply le_antisymm
      · intro v hv
        exact (Submodule.mem_bot ℂ).mpr (congrArg Subtype.val (h ⟨v, hv⟩))
      · exact bot_le
    obtain ⟨v₀, hv₀⟩ := hR
    letI : Nontrivial R := ⟨⟨v₀, 0, hv₀⟩⟩
    let f : ι → Module.End ℂ R := fun i =>
      { toFun v := ⟨T i v, map_mem_restrictedRadical W (T i) (hT i)
          (fun v hv => (hiW i v hv).1) (fun v hv => (hiW i v hv).2) v.property⟩
        map_add' u v := Subtype.ext (map_add (T i) (u : H × E) (v : H × E))
        map_smul' a v := Subtype.ext (map_smul (T i) a (v : H × E)) }
    have hf : ∀ i j, Commute (f i) (f j) := by
      intro i j
      apply LinearMap.ext
      intro v
      exact Subtype.ext (hcomm i j v)
    obtain ⟨v, χ, hv, he⟩ := exists_common_eigenvector_family f hf
    have hvne : (v : H × E) ≠ 0 := fun h => hv (Subtype.ext h)
    have hvW := ((mem_restrictedRadical W (v : H × E)).mp v.property).1
    refine ⟨v, χ, hWW₀ hvW, hvne, ?_, ?_⟩
    · exact le_of_eq (congrArg Complex.re (restrictedRadical_square W v.property))
    · intro i
      have he' : T i (v : H × E) = χ i • (v : H × E) := congrArg Subtype.val (he i)
      refine ⟨?_, he'⟩
      intro hz
      rw [hz, zero_smul] at he'
      exact hvne ((T i).injective (he'.trans (map_zero (T i)).symm))

/-- A nontrivial finite negative factor forces a common nonpositive eigenline. -/
theorem exists_common_nonpositive_eigenvector [Nontrivial E]
    (T : ι → (H × E) ≃L[ℂ] (H × E))
    (hT : ∀ i v w, pairing (T i v) (T i w) = pairing v w)
    (hcomm : ∀ i j v, T i (T j v) = T j (T i v)) :
    ∃ (w : H × E) (χ : ι → ℂ), w ≠ 0 ∧ (pairing w w).re ≤ 0 ∧
      ∀ i, χ i ≠ 0 ∧ T i w = χ i • w := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hn : HasNonpositiveDirection (⊤ : Submodule ℂ (H × E)) := by
    refine ⟨(0, v), by trivial, ?_, ?_⟩
    · intro h
      exact hv (congrArg Prod.snd h)
    · rw [pairing_self_nonpos_iff, norm_zero]
      exact norm_nonneg v
  obtain ⟨w, χ, _, hw, hq, he⟩ := exists_common_nonpositive_eigenvector_in_subspace
    T hT hcomm ⊤ isClosed_univ (fun _ _ _ => ⟨by trivial, by trivial⟩) hn
  exact ⟨w, χ, hw, hq, he⟩

#print axioms exists_common_nonpositive_eigenvector

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
