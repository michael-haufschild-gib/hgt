import GaloisForLFunctions.HTGeometry.PaperNegativePartInertia
import GaloisForLFunctions.HTGeometry.HermitianInertia

/-!
# Finite Grams of a bounded operator

A linear realization of a finite Hermitian form transfers its negative
space injectively into the operator's negative index. This provides the
finite-matrix interface to the canonical negative-part repair.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PaperNegativePart

open Matrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι]

/-- Gram matrix of the operator pairing on a finite family. -/
def finiteGram (Q : E →L[ℂ] E) (v : ι → E) : Matrix ι ι ℂ :=
  fun i j => inner ℂ (Q (v i)) (v j)

/-- The linear realization of coefficient vectors in a finite family. -/
def finiteCombination (v : ι → E) : (ι → ℂ) →ₗ[ℂ] E where
  toFun c := ∑ i, c i • v i
  map_add' c d := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' z c := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.smul_sum, smul_smul]

theorem hermQuad_finiteGram (Q : E →L[ℂ] E) (v : ι → E) (c : ι → ℂ) :
    hermQuad (finiteGram Q v) c =
      (inner ℂ (Q (finiteCombination v c)) (finiteCombination v c)).re := by
  change (∑ i, star (c i) * ∑ j, inner ℂ (Q (v i)) (v j) * c j).re =
    (inner ℂ (Q (∑ i, c i • v i)) (∑ j, c j • v j)).re
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.star_def]
  ring

/-- Every negative matrix subspace is injected by its realization: a zero
image would have zero quadratic value. -/
theorem hermNegIndex_le_negativeRank_of_realization
    (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q) [FiniteDimensional ℂ (negativeSpace Q)]
    (H : Matrix ι ι ℂ) (L : (ι → ℂ) →ₗ[ℂ] E)
    (hL : ∀ c, hermQuad H c = (inner ℂ (Q (L c)) (L c)).re) :
    hermNegIndex H ≤ negativeRank Q := by
  obtain ⟨W, hdim, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-H)
  let T : W →ₗ[ℂ] E := L.comp W.subtype
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra hc0
    have h := hW c c.property (fun hz => hc0 (Subtype.ext hz))
    rw [hermQuad_neg, hL] at h
    change L (c : ι → ℂ) = 0 at hc
    simpa only [hc, map_zero, inner_zero_left, Complex.zero_re, neg_zero,
      lt_self_iff_false] using h
  have hneg : ∀ x ∈ LinearMap.range T, x ≠ 0 → (inner ℂ (Q x) x).re < 0 := by
    rintro _ ⟨c, rfl⟩ hc0
    have hc : (c : ι → ℂ) ≠ 0 := fun hz => hc0 (by
      change L (c : ι → ℂ) = 0
      rw [hz, map_zero])
    have h := hW c c.property hc
    rw [hermQuad_neg, hL] at h
    exact neg_pos.mp h
  have hb := (negative_subspace_finite_dimension Q hQ (LinearMap.range T) hneg).2
  have he := (LinearEquiv.ofInjective T hinj).finrank_eq
  change Module.finrank ℂ W = Module.finrank ℂ (LinearMap.range T) at he
  rw [← he, hdim] at hb
  exact hb

/-- Every finite operator Gram has at most the canonical negative rank. -/
theorem hermNegIndex_finiteGram_le (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q)
    [FiniteDimensional ℂ (negativeSpace Q)] (v : ι → E) :
    hermNegIndex (finiteGram Q v) ≤ negativeRank Q :=
  hermNegIndex_le_negativeRank_of_realization Q hQ _ (finiteCombination v)
    (hermQuad_finiteGram Q v)

/-- A basis of the negative spectral space realizes its entire index in
one finite Gram. -/
theorem exists_finiteGram_index_eq (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q)
    [FiniteDimensional ℂ (negativeSpace Q)] :
    ∃ v : Fin (negativeRank Q) → E, hermNegIndex (finiteGram Q v) = negativeRank Q := by
  change ∃ v : Fin (Module.finrank ℂ (negativeSpace Q)) → E,
    hermNegIndex (finiteGram Q v) = Module.finrank ℂ (negativeSpace Q)
  let b := Module.finBasis ℂ (negativeSpace Q)
  let v : Fin (Module.finrank ℂ (negativeSpace Q)) → E := fun i => (b i : E)
  have hcomb (c : Fin (Module.finrank ℂ (negativeSpace Q)) → ℂ) :
      finiteCombination v c = (b.equivFun.symm c : E) := by
    change (∑ i, c i • (b i : E)) = (b.equivFun.symm c : E)
    rw [Module.Basis.equivFun_symm_apply]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  have hp : IsPosDefOn (-(finiteGram Q v))
      (⊤ : Submodule ℂ (Fin (Module.finrank ℂ (negativeSpace Q)) → ℂ)) := by
    intro c _ hc
    rw [hermQuad_neg, hermQuad_finiteGram, hcomb]
    apply neg_pos.mpr
    apply negativeSpace_strict Q hQ (b.equivFun.symm c).property
    intro hz
    apply hc
    apply b.equivFun.symm.injective
    rw [map_zero]
    exact Subtype.ext hz
  have hlo : Module.finrank ℂ (negativeSpace Q) ≤ hermNegIndex (finiteGram Q v) := by
    have h := finrank_le_posIndex hp
    simpa only [hermNegIndex, finrank_top, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] using h
  exact ⟨v, le_antisymm (hermNegIndex_finiteGram_le Q hQ v) hlo⟩

end GaloisForLFunctions.HTGeometry.PaperNegativePart
