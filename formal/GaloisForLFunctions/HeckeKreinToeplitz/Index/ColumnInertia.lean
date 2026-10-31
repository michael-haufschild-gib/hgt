import GaloisForLFunctions.HeckeKreinToeplitz.Index.IsotropicSubspaces

/-!
# Negative-index bounds inside the kernel column space

Strictly negative linear families inject into finite-dimensional nonpositive subspaces.
Consequently every finite Gram family of column-space vectors retains the kernel's index bound,
and every orthogonal negative family has cardinality at most that bound.
-/

open Complex Finset Module Matrix
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz
variable {G : Type*} [Group G]

/-- A strictly negative linear family has dimension bounded by the kernel's negative index. -/
theorem finite_of_negative_column_map {k : G → ℂ} (hk : IsHermKernel k) {r : ℕ}
    (hi : negIndex k ≤ r) {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (F : V →ₗ[ℂ] kernelColumnSpan k)
    (hF : ∀ v, v ≠ 0 → (kernelColumnPairing k (F v) (F v)).re < 0) :
    Module.Finite ℂ V ∧ finrank ℂ V ≤ r := by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ
  let W := LinearMap.range F
  letI : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ
  have hW : ∀ w ∈ W, (kernelColumnPairing k w w).re ≤ 0 := by
    rintro w ⟨v, rfl⟩
    by_cases hv : v = 0
    · rw [hv, map_zero, map_zero, Complex.zero_re]
    · exact (hF v hv).le
  obtain ⟨hfinite, hdim⟩ := finite_nonpositive_column_subspace hk hi W hW
  letI := hfinite
  have hzero (v : V) (hv : F v = 0) : v = 0 := by
    by_contra h
    have hn := hF v h
    rw [hv, map_zero, Complex.zero_re] at hn
    exact (lt_irrefl 0) hn
  let L : V →ₗ[ℂ] W := F.rangeRestrict
  have hinj : Function.Injective L := by
    intro v w he
    have hf : F v = F w := congrArg Subtype.val he
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hf, sub_self]
  letI : Module.Finite ℂ V := Module.Finite.of_injective L hinj
  exact ⟨inferInstance, (LinearMap.finrank_le_finrank_of_injective hinj).trans hdim⟩

/-- The Gram matrix of an arbitrary finite family of column-space vectors. -/
def kernelColumnGram (k : G → ℂ) {ι : Type*} (v : ι → kernelColumnSpan k) : Matrix ι ι ℂ :=
  fun i j => kernelColumnPairing k (v i) (v j)

theorem kernelColumnGram_isHermitian {k : G → ℂ} (hk : IsHermKernel k)
    {ι : Type*} (v : ι → kernelColumnSpan k) : (kernelColumnGram k v).IsHermitian := by
  ext i j
  change conj (kernelColumnPairing k (v j) (v i)) = kernelColumnPairing k (v i) (v j)
  exact (kernelColumnPairing_conj_symm hk (v i) (v j)).symm

def kernelColumnSynthesis {k : G → ℂ} {ι : Type*} [Fintype ι]
    (v : ι → kernelColumnSpan k) : (ι → ℂ) →ₗ[ℂ] kernelColumnSpan k where
  toFun c := ∑ i, c i • v i
  map_add' c d := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem kernelColumnPairing_synthesis {k : G → ℂ} (hk : IsHermKernel k)
    {ι : Type*} [Fintype ι] (v : ι → kernelColumnSpan k) (c : ι → ℂ)
    (w : kernelColumnSpan k) :
    kernelColumnPairing k (kernelColumnSynthesis v c) w =
      ∑ i, conj (c i) * kernelColumnPairing k (v i) w := by
  change kernelColumnPairing k (∑ i, c i • v i) w = _
  rw [kernelColumnPairing_conj_symm hk, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul, map_mul, ← kernelColumnPairing_conj_symm hk]

theorem hermQuad_kernelColumnGram {k : G → ℂ} (hk : IsHermKernel k)
    {ι : Type*} [Fintype ι] (v : ι → kernelColumnSpan k) (c : ι → ℂ) :
    hermQuad (kernelColumnGram k v) c =
      (kernelColumnPairing k (kernelColumnSynthesis v c) (kernelColumnSynthesis v c)).re := by
  rw [kernelColumnPairing_synthesis hk]
  simp only [kernelColumnSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    map_sum, map_smul, smul_eq_mul, hermQuad, Matrix.mulVec, dotProduct,
    Pi.star_apply, Complex.star_def, kernelColumnGram, mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every finite Gram family in the column space retains the original negative-index bound. -/
theorem hermNegIndex_kernelColumnGram_le {k : G → ℂ} (hk : IsHermKernel k) {r : ℕ}
    (hi : negIndex k ≤ r) {ι : Type*} [Fintype ι] (v : ι → kernelColumnSpan k) :
    hermNegIndex (kernelColumnGram k v) ≤ r := by
  obtain ⟨W, hW, hneg⟩ := exists_isPosDefOn_finrank_eq_posIndex (-kernelColumnGram k v)
  have h := (finite_of_negative_column_map hk hi
    ((kernelColumnSynthesis v).comp W.subtype) (fun c hc => by
      have hc' : (c : ι → ℂ) ≠ 0 := fun he => hc (Subtype.ext he)
      have hn := hneg c c.property hc'
      rw [hermQuad_neg, hermQuad_kernelColumnGram hk] at hn
      change (kernelColumnPairing k (kernelColumnSynthesis v c) (kernelColumnSynthesis v c)).re < 0
      linarith only [hn])).2
  rw [hW] at h
  exact h

#print axioms finite_of_negative_column_map
#print axioms hermNegIndex_kernelColumnGram_le

/-- An orthogonal finite family gives a diagonal formula for every linear combination. -/
theorem kernelColumnPairing_synthesis_orthogonal {k : G → ℂ} (hk : IsHermKernel k)
    {ι : Type*} [Fintype ι] (v : ι → kernelColumnSpan k)
    (ho : ∀ i j, i ≠ j → kernelColumnPairing k (v i) (v j) = 0) (c : ι → ℂ) :
    kernelColumnPairing k (kernelColumnSynthesis v c) (kernelColumnSynthesis v c) =
      ∑ i, (normSq (c i) : ℂ) * kernelColumnPairing k (v i) (v i) := by
  classical
  rw [kernelColumnPairing_synthesis hk]
  apply Finset.sum_congr rfl
  intro i _
  have hrow : kernelColumnPairing k (v i) (kernelColumnSynthesis v c) =
      c i * kernelColumnPairing k (v i) (v i) := by
    change kernelColumnPairing k (v i) (∑ j, c j • v j) = _
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [ho i j hji.symm, mul_zero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hrow, ← mul_assoc, ← Complex.normSq_eq_conj_mul_self]

/-- An orthogonal family of negative vectors cannot exceed the kernel's negative index. -/
theorem card_le_index_of_orthogonal_negative_columns {k : G → ℂ} (hk : IsHermKernel k)
    {r : ℕ} (hi : negIndex k ≤ r) {ι : Type*} [Fintype ι]
    (v : ι → kernelColumnSpan k)
    (hv : ∀ i, (kernelColumnPairing k (v i) (v i)).re < 0)
    (ho : ∀ i j, i ≠ j → kernelColumnPairing k (v i) (v j) = 0) :
    Fintype.card ι ≤ r := by
  classical
  have hdiag (c : ι → ℂ) :
      (kernelColumnPairing k (kernelColumnSynthesis v c) (kernelColumnSynthesis v c)).re =
      ∑ i, normSq (c i) * (kernelColumnPairing k (v i) (v i)).re := by
    rw [kernelColumnPairing_synthesis_orthogonal hk v ho, Complex.re_sum]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have h := (finite_of_negative_column_map hk hi (kernelColumnSynthesis v) (fun c hc => by
    obtain ⟨i, hci⟩ : ∃ i, c i ≠ 0 := by
      by_contra h
      push Not at h
      exact hc (funext h)
    rw [hdiag]
    have hs : (∑ j, normSq (c j) * (kernelColumnPairing k (v j) (v j)).re) <
        ∑ _j : ι, (0 : ℝ) := by
      apply Finset.sum_lt_sum
      · intro j _
        exact mul_nonpos_of_nonneg_of_nonpos (normSq_nonneg _) (hv j).le
      · exact ⟨i, Finset.mem_univ i, mul_neg_of_pos_of_neg (normSq_pos.mpr hci) (hv i)⟩
    simpa only [sum_const_zero] using hs)).2
  simpa only [Module.finrank_fintype_fun_eq_card] using h

#print axioms card_le_index_of_orthogonal_negative_columns
end GaloisForLFunctions.HeckeKreinToeplitz
