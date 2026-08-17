import Mathlib
import GaloisForLFunctions.HTGeometry.TwoBlockUnitaryAlgebra

/-!
# Conjugation-equivariant linear maps on matrices have two parameters

A linear map `L` on `n × n` complex matrices satisfying `L (Vᴴ A V) = Vᴴ (L A) V` for every unitary
`V` is determined by two scalars: diagonal phase unitaries force `L (E i j)` to be a multiple of
`E i j` for `i ≠ j` and `L (E i i)` to be diagonal, permutation matrices make those multiples
independent of the indices, and the two-index block unitary — the one non-monomial unitary needed —
ties the diagonal constant to the off-diagonal one by `α = a + b`.  Expanding an arbitrary matrix in
matrix units gives

`L A = a A + b (tr A) I`   for `n ≥ 2`.
-/

namespace GaloisForLFunctions.EquivariantCausalizer

open Matrix

variable {n : ℕ}

section Classification

variable (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
  (hL : ∀ V ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, L (Vᴴ * A * V) = Vᴴ * L A * V)

include hL in
/-- The off-diagonal coefficient does not depend on the pair of distinct indices. -/
theorem offDiag_coeff_eq {i j i' j' : Fin n} (hij : i ≠ j) (hij' : i' ≠ j') :
    (L (Matrix.single i j 1)) i j = (L (Matrix.single i' j' 1)) i' j' := by
  obtain ⟨σ, hσi, hσj⟩ := exists_perm_map_pair hij hij'
  have h := perm_transport L hL σ i j (σ i) (σ j)
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, hσi, hσj] at h
  exact h.symm

include hL in
/-- The off-diagonal diagonal-image coefficient does not depend on the pair of distinct indices. -/
theorem diag_offCoeff_eq {i k i' k' : Fin n} (hik : i ≠ k) (hik' : i' ≠ k') :
    (L (Matrix.single i i 1)) k k = (L (Matrix.single i' i' 1)) k' k' := by
  obtain ⟨σ, hσi, hσk⟩ := exists_perm_map_pair hik hik'
  have h := perm_transport L hL σ i i (σ k) (σ k)
  rw [Equiv.symm_apply_apply, hσi, hσk] at h
  exact h.symm

include hL in
/-- The diagonal-image diagonal coefficient does not depend on the index. -/
theorem diag_sameCoeff_eq (i i' : Fin n) :
    (L (Matrix.single i i 1)) i i = (L (Matrix.single i' i' 1)) i' i' := by
  classical
  set σ := Equiv.swap i i' with hσ
  have hσi : σ i = i' := by simp [hσ]
  have h := perm_transport L hL σ i i (σ i) (σ i)
  rw [Equiv.symm_apply_apply, hσi] at h
  exact h.symm

end Classification


section Constants

variable (hn : 2 ≤ n) (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
  (hL : ∀ V ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, L (Vᴴ * A * V) = Vᴴ * L A * V)

/-- The first normalising index. -/
def idxZero (hn : 2 ≤ n) : Fin n := ⟨0, lt_of_lt_of_le (by norm_num) hn⟩

/-- The second normalising index. -/
def idxOne (hn : 2 ≤ n) : Fin n := ⟨1, lt_of_lt_of_le (by norm_num) hn⟩

theorem idxZero_ne_idxOne : idxZero hn ≠ idxOne hn := by
  intro h
  have h2 := congrArg Fin.val h
  simp only [idxZero, idxOne] at h2
  exact absurd h2 (by norm_num)

include hn in
/-- Every index has a distinct partner. -/
theorem exists_ne_index (i : Fin n) : ∃ j : Fin n, i ≠ j := by
  by_cases h : i = idxZero hn
  · exact ⟨idxOne hn, by rw [h]; exact idxZero_ne_idxOne hn⟩
  · exact ⟨idxZero hn, fun hc => h hc⟩

/-- The off-diagonal (Gram) constant of a conjugation-equivariant linear map. -/
noncomputable def coeffA : ℂ :=
  (L (Matrix.single (idxZero hn) (idxOne hn) 1)) (idxZero hn) (idxOne hn)

/-- The isotropic (trace) constant of a conjugation-equivariant linear map. -/
noncomputable def coeffB : ℂ :=
  (L (Matrix.single (idxZero hn) (idxZero hn) 1)) (idxOne hn) (idxOne hn)

include hL in
theorem offDiag_image {i j : Fin n} (hij : i ≠ j) :
    L (Matrix.single i j 1) = coeffA hn L • Matrix.single i j 1 := by
  obtain ⟨c, hc⟩ := exists_offDiag_coeff L hL hij
  have hcval : c = (L (Matrix.single i j 1)) i j := by
    rw [hc, Matrix.single_apply, if_pos ⟨rfl, rfl⟩]
  rw [hc, hcval, offDiag_coeff_eq L hL hij (idxZero_ne_idxOne hn), Matrix.smul_single, smul_eq_mul,
    mul_one]
  rfl

include hL in
theorem diag_image_entry_off {i k : Fin n} (hik : i ≠ k) :
    (L (Matrix.single i i 1)) k k = coeffB hn L :=
  diag_offCoeff_eq L hL hik (idxZero_ne_idxOne hn)

include hL in
theorem diag_image_aux (i : Fin n) :
    L (Matrix.single i i 1)
      = ((L (Matrix.single i i 1)) i i - coeffB hn L) • Matrix.single i i 1
        + coeffB hn L • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext k l
  by_cases hkl : k = l
  · subst hkl
    by_cases hk : k = i
    · subst hk
      simp
    · rw [diag_image_entry_off hn L hL (Ne.symm hk)]
      simp [Ne.symm hk]
  · rw [diag_image_offDiag_eq_zero L hL i (Ne.symm hkl)]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, Matrix.one_apply,
      smul_eq_mul]
    rw [if_neg (fun h : i = k ∧ i = l => hkl (h.1.symm.trans h.2)), if_neg hkl]
    ring

include hL in
theorem L_blockZ (i j : Fin n) :
    L (blockZ i j) = ((L (Matrix.single i i 1)) i i - coeffB hn L) • blockZ i j := by
  have h1 := diag_image_aux hn L hL i
  have h2 := diag_image_aux hn L hL j
  have hji : (L (Matrix.single j j 1)) j j = (L (Matrix.single i i 1)) i i :=
    (diag_sameCoeff_eq L hL i j).symm
  rw [hji] at h2
  set α := (L (Matrix.single i i 1)) i i with hα
  show L (Matrix.single i i 1 - Matrix.single j j 1)
      = (α - coeffB hn L) • (Matrix.single i i 1 - Matrix.single j j 1)
  rw [map_sub, h1, h2]
  module

include hL in
theorem L_blockR {i j : Fin n} (hij : i ≠ j) :
    L (blockR i j) = coeffA hn L • blockR i j := by
  show L (Matrix.single i j 1 - Matrix.single j i 1)
      = coeffA hn L • (Matrix.single i j 1 - Matrix.single j i 1)
  rw [map_sub, offDiag_image hn L hL hij, offDiag_image hn L hL (Ne.symm hij)]
  module

end Constants


section Crux

variable (hn : 2 ≤ n) (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
  (hL : ∀ V ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, L (Vᴴ * A * V) = Vᴴ * L A * V)

include hL in
/-- **The two constants are related by the block unitary.**  Conjugating the diagonal difference
onto the antisymmetric pair identifies the off-diagonal constant with the gap of the diagonal
constants. -/
theorem coeffA_eq_sub {i j : Fin n} (hij : i ≠ j) :
    coeffA hn L = (L (Matrix.single i i 1)) i i - coeffB hn L := by
  have hV := hL (blockUnitary i j) (blockUnitary_mem_unitaryGroup hij) (blockZ i j)
  rw [blockUnitary_conj_blockZ hij, L_blockZ hn L hL i j, map_smul, L_blockR hn L hL hij,
    Matrix.mul_smul, Matrix.smul_mul, blockUnitary_conj_blockZ hij] at hV
  have hentry := congrFun (congrFun hV i) j
  have hR : (blockR i j) i j = 1 := by
    simp [blockR, Ne.symm hij]
  simp only [Matrix.smul_apply, smul_eq_mul, hR, mul_one] at hentry
  have hI : (-Complex.I) ≠ 0 := by
    simp [Complex.I_ne_zero]
  field_simp at hentry
  exact neg_inj.mp hentry

include hL in
theorem diag_image_entry_same (i : Fin n) :
    (L (Matrix.single i i 1)) i i = coeffA hn L + coeffB hn L := by
  obtain ⟨j, hij⟩ := exists_ne_index hn i
  have h := coeffA_eq_sub hn L hL hij
  rw [h]
  ring

include hL in
theorem diag_image (i : Fin n) :
    L (Matrix.single i i 1)
      = coeffA hn L • Matrix.single i i 1 + coeffB hn L • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have h := diag_image_aux hn L hL i
  rw [diag_image_entry_same hn L hL i] at h
  simpa using h

end Crux


section Assembly

variable (hn : 2 ≤ n) (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
  (hL : ∀ V ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, L (Vᴴ * A * V) = Vᴴ * L A * V)

include hL in
theorem single_image (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    L (Matrix.single i j (A i j))
      = coeffA hn L • Matrix.single i j (A i j)
        + (if i = j then (coeffB hn L * A i j) • (1 : Matrix (Fin n) (Fin n) ℂ) else 0) := by
  have hsingle : Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  by_cases hij : i = j
  · subst hij
    rw [hsingle, map_smul, diag_image hn L hL i, if_pos rfl, ← hsingle]
    rw [show Matrix.single i i (A i i) = A i i • Matrix.single i i (1 : ℂ) from hsingle]
    module
  · rw [hsingle, map_smul, offDiag_image hn L hL hij, if_neg hij, ← hsingle]
    rw [show Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℂ) from hsingle]
    module

include hL in
/-- **Classification of conjugation-equivariant linear maps on matrices.** -/
theorem classification (A : Matrix (Fin n) (Fin n) ℂ) :
    L A = coeffA hn L • A
      + coeffB hn L • (A.trace • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  classical
  conv_lhs => rw [matrix_eq_sum_single A]
  rw [map_sum]
  have hstep : ∀ i : Fin n, L (∑ j, Matrix.single i j (A i j))
      = coeffA hn L • (∑ j, Matrix.single i j (A i j))
        + (coeffB hn L * A i i) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    intro i
    rw [map_sum]
    rw [Finset.sum_congr rfl (fun j _ => single_image hn L hL A i j)]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum]
    congr 1
    rw [Finset.sum_ite_eq Finset.univ i
      (fun j => (coeffB hn L * A i j) • (1 : Matrix (Fin n) (Fin n) ℂ))]
    rw [if_pos (Finset.mem_univ i)]
  rw [Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_add_distrib, ← Finset.smul_sum,
    ← matrix_eq_sum_single A]
  congr 1
  rw [← Finset.sum_smul, Matrix.trace]
  simp only [Matrix.diag_apply, smul_smul]
  congr 1
  rw [Finset.mul_sum]

end Assembly

end GaloisForLFunctions.EquivariantCausalizer
