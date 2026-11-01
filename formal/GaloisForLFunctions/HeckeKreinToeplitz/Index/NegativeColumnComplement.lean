import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnInertia
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnPositivity

/-!
# The positive complement of a negative kernel column

A nonpositive-definite kernel has a column-space vector of square `-1`.
At negative index at most one, its orthogonal complement is positive
definite: another negative vector would give two negative squares, and a
null vector would annihilate the entire nondegenerate column form.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [Group G] {k : G → ℂ}

/-- The squared column synthesis is exactly the finite kernel Gram form. -/
theorem kernelColumnPoint_sum_self_re (hk : IsHermKernel k)
    {I : Type*} [Fintype I] (x : I → G) (c : I → ℂ) :
    (kernelColumnPairing k (∑ i, c i • kernelColumnPoint k (x i))
      (∑ i, c i • kernelColumnPoint k (x i))).re = hermQuad (gram k x) c := by
  have hgram : kernelColumnGram k (fun i => kernelColumnPoint k (x i)) = gram k x := by
    ext i j
    exact kernelColumnPairing_point_left hk (x i) (kernelColumnPoint k (x j))
  rw [← hgram, hermQuad_kernelColumnGram hk]
  rfl

/-- A Hermitian kernel which is not positive definite has a normalized negative column vector. -/
theorem exists_negative_unit_column (hk : IsHermKernel k) (hp : ¬ IsPosDefKernel k) :
    ∃ e : kernelColumnSpan k, kernelColumnPairing k e e = -1 := by
  have hnot : ¬ ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ), 0 ≤ hermQuad (gram k x) c :=
    fun h => hp ⟨hk, h⟩
  push Not at hnot
  obtain ⟨n, x, c, hc⟩ := hnot
  let v : kernelColumnSpan k := ∑ i, c i • kernelColumnPoint k (x i)
  have hv : (kernelColumnPairing k v v).re < 0 := by
    rw [kernelColumnPoint_sum_self_re hk]
    exact hc
  have him : (kernelColumnPairing k v v).im = 0 := by
    have h := congrArg Complex.im (kernelColumnPairing_conj_symm hk v v)
    simp only [Complex.conj_im] at h
    linarith only [h]
  let r : ℝ := Real.sqrt (-(kernelColumnPairing k v v).re)
  have hr : 0 < r := Real.sqrt_pos.mpr (neg_pos.mpr hv)
  have hr2 : r ^ 2 = -(kernelColumnPairing k v v).re := Real.sq_sqrt (neg_nonneg.mpr hv.le)
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have he : kernelColumnPairing k v v = -((r : ℂ) ^ 2) := by
    apply Complex.ext
    · rw [← Complex.ofReal_pow, Complex.neg_re, Complex.ofReal_re]
      linarith only [hr2]
    · rw [← Complex.ofReal_pow, Complex.neg_im, Complex.ofReal_im, neg_zero, him]
  refine ⟨(r : ℂ)⁻¹ • v, ?_⟩
  rw [kernelColumnPairing_smul_left hk, map_smul, smul_eq_mul, map_inv₀,
    Complex.conj_ofReal, he]
  field_simp

/-- At index one, the orthogonal complement of a negative vector has no negative square. -/
theorem kernelColumnPairing_nonneg_of_orthogonal_negative (hk : IsHermKernel k)
    (hi : negIndex k ≤ 1) {e v : kernelColumnSpan k}
    (he : (kernelColumnPairing k e e).re < 0) (hev : kernelColumnPairing k e v = 0) :
    0 ≤ (kernelColumnPairing k v v).re := by
  by_contra h
  have hv : (kernelColumnPairing k v v).re < 0 := lt_of_not_ge h
  have hve : kernelColumnPairing k v e = 0 := by
    rw [kernelColumnPairing_conj_symm hk, hev, map_zero]
  have hneg (i : Fin 2) : (kernelColumnPairing k (![e, v] i) (![e, v] i)).re < 0 := by
    fin_cases i
    · exact he
    · exact hv
  have horth (i j : Fin 2) (hij : i ≠ j) : kernelColumnPairing k (![e, v] i) (![e, v] j) = 0 := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hev
    · exact hve
    · exact (hij rfl).elim
  have hbound := card_le_index_of_orthogonal_negative_columns hk (r := 1) hi ![e, v] hneg horth
  norm_num at hbound

/-- The positive complement has no radical, by Cauchy–Schwarz and column nondegeneracy. -/
theorem kernelColumnPairing_definite_on_negative_complement (hk : IsHermKernel k)
    (hi : negIndex k ≤ 1) {e v : kernelColumnSpan k}
    (he : kernelColumnPairing k e e = -1) (hev : kernelColumnPairing k e v = 0)
    (hv : kernelColumnPairing k v v = 0) : v = 0 := by
  let W : Submodule ℂ (kernelColumnSpan k) := (kernelColumnPairing k e).ker
  have hneg : (kernelColumnPairing k e e).re < 0 := by rw [he]; norm_num
  have hW : ∀ w ∈ W, 0 ≤ (kernelColumnPairing k w w).re :=
    fun w hw => kernelColumnPairing_nonneg_of_orthogonal_negative hk hi hneg hw
  have hvW : v ∈ W := hev
  have hve : kernelColumnPairing k v e = 0 := by
    rw [kernelColumnPairing_conj_symm hk, hev, map_zero]
  apply kernelColumnPairing_nondegenerate hk
  intro z
  let w : kernelColumnSpan k := z + kernelColumnPairing k e z • e
  have hw : w ∈ W := by
    change kernelColumnPairing k e (z + kernelColumnPairing k e z • e) = 0
    rw [map_add, map_smul, smul_eq_mul, he]
    ring
  have hcs := kernelColumnPairing_normSq_le_on_subspace hk W hW v w hvW hw
  rw [hv, Complex.zero_re, zero_mul] at hcs
  have hzero : kernelColumnPairing k v w = 0 :=
    Complex.normSq_eq_zero.mp (le_antisymm hcs (normSq_nonneg _))
  change kernelColumnPairing k v (z + kernelColumnPairing k e z • e) = 0 at hzero
  rw [map_add, map_smul, smul_eq_mul, hve, mul_zero, add_zero] at hzero
  rw [kernelColumnPairing_conj_symm hk, hzero, map_zero]

end GaloisForLFunctions.HeckeKreinToeplitz
