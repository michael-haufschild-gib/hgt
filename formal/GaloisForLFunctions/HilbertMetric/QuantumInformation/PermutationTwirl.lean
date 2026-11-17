import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.LinearCombination

/-!
# Exact finite permutation averages

Permutation averaging preserves Gram positivity, trace, and total entry
sum. Pair transitivity puts the average in the span of identity and the
all-ones matrix, yielding exact entries and quadratic energy formulas.
-/

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
namespace GaloisForLFunctions.HilbertMetric.PermutationTwirl

/-- Averaging all coordinate relabelings of a finite matrix. -/
def twirl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ •
    ∑ σ : Equiv.Perm (Fin n), A.submatrix σ σ

/-- Relabeling output coordinates leaves the permutation average unchanged. -/
theorem twirl_submatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (τ : Equiv.Perm (Fin n)) : (twirl A).submatrix τ τ = twirl A := by
  ext i j
  simp only [twirl, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  change (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ *
      (∑ σ : Equiv.Perm (Fin n), A (σ (τ i)) (σ (τ j))) =
    (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ *
      (∑ σ : Equiv.Perm (Fin n), A (σ i) (σ j))
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight τ) (fun σ : Equiv.Perm (Fin n) => A (σ i) (σ j))

/-- Every positive Gram stays positive after permutation averaging. -/
theorem twirl_gram_posSemidef {n m : ℕ} (B : Matrix (Fin m) (Fin n) ℂ) :
    (twirl (Bᴴ * B)).PosSemidef := by
  unfold twirl
  apply Matrix.PosSemidef.smul
  · apply Matrix.posSemidef_sum Finset.univ
    intro σ _
    exact (Matrix.posSemidef_conjTranspose_mul_self B).submatrix σ
  · positivity

private theorem permutation_card_ne_zero (n : ℕ) :
    (Fintype.card (Equiv.Perm (Fin n)) : ℂ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

/-- Relabeling preserves trace, hence so does the permutation average. -/
theorem trace_twirl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : trace (twirl A) = trace A := by
  simp only [Matrix.trace, Matrix.diag_apply, twirl, Matrix.smul_apply,
    smul_eq_mul, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have he (σ : Equiv.Perm (Fin n)) : (∑ i, A (σ i) (σ i)) = ∑ i, A i i :=
    Equiv.sum_comp σ (fun i => A i i)
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (permutation_card_ne_zero n), one_mul]

/-- The sum of all coefficients is unchanged by permutation averaging. -/
theorem sum_twirl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, ∑ j, twirl A i j) = ∑ i, ∑ j, A i j := by
  simp only [twirl, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
    Matrix.submatrix_apply]
  simp_rw [← Finset.mul_sum]
  have hswap : (∑ i, ∑ j, ∑ σ : Equiv.Perm (Fin n), A (σ i) (σ j)) =
      ∑ σ : Equiv.Perm (Fin n), ∑ i, ∑ j, A (σ i) (σ j) := by
    calc
      _ = ∑ i, ∑ σ : Equiv.Perm (Fin n), ∑ j, A (σ i) (σ j) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hswap]
  have he (σ : Equiv.Perm (Fin n)) : (∑ i, ∑ j, A (σ i) (σ j)) = ∑ i, ∑ j, A i j := by
    have hr (i : Fin n) : (∑ j, A (σ i) (σ j)) = ∑ j, A (σ i) j :=
      Equiv.sum_comp σ (fun j => A (σ i) j)
    simp_rw [hr]
    exact Equiv.sum_comp σ (fun i => ∑ j, A i j)
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (permutation_card_ne_zero n), one_mul]

private theorem exists_pair_perm {n : ℕ} (i j a b : Fin n) (hij : i ≠ j) (hab : a ≠ b) :
    ∃ σ : Equiv.Perm (Fin n), σ i = a ∧ σ j = b := by
  classical
  let τ : Equiv.Perm (Fin n) := Equiv.swap i a
  have hi : τ i = a := Equiv.swap_apply_left i a
  have hj : τ j ≠ a := fun h => hij (τ.injective (hi.trans h.symm))
  refine ⟨τ.trans (Equiv.swap (τ j) b), ?_, ?_⟩
  · simp only [Equiv.trans_apply, hi, Equiv.swap_apply_def,
      if_neg (Ne.symm hj), if_neg hab]
  · exact Equiv.swap_apply_left _ _

/-- Permutation averaging has one diagonal entry and one off-diagonal entry. -/
theorem twirl_entry_classification {n : ℕ}
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (i j : Fin (n + 2)) :
    twirl A i j = if i = j then twirl A 0 0 else twirl A 0 1 := by
  by_cases h : i = j
  · subst j
    have ht := congrArg (fun M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ => M 0 0)
      (twirl_submatrix A (Equiv.swap 0 i))
    simpa only [Matrix.submatrix_apply, Equiv.swap_apply_left, if_true] using ht
  · have h01 : (0 : Fin (n + 2)) ≠ 1 := by
      intro he
      have hv := congrArg Fin.val he
      change 0 % (n + 2) = 1 % (n + 2) at hv
      rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 1 < n + 2)] at hv
      omega
    obtain ⟨σ, h0, h1⟩ := exists_pair_perm (0 : Fin (n + 2)) 1 i j h01 h
    have ht := congrArg (fun M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ => M 0 1)
      (twirl_submatrix A σ)
    simpa only [Matrix.submatrix_apply, h0, h1, if_neg h] using ht

/-- The average lies in the two-dimensional algebra generated by identity and the all-ones matrix. -/
theorem twirl_two_parameter_decomposition {n : ℕ}
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) :
    twirl A = (twirl A 0 1) • Matrix.of (fun (_ _ : Fin (n + 2)) => (1 : ℂ)) +
      (twirl A 0 0 - twirl A 0 1) • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) := by
  ext i j
  rw [twirl_entry_classification]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
    smul_eq_mul, Matrix.one_apply, mul_one]
  by_cases h : i = j <;> simp only [h, if_true, if_false, mul_one, mul_zero, add_zero]
  ring

/-- The diagonal of a permutation average is the original trace divided by dimension. -/
theorem twirl_diagonal_value {n : ℕ}
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) :
    twirl A 0 0 = Matrix.trace A / (n + 2 : ℂ) := by
  have ht := trace_twirl A
  change (∑ i, twirl A i i) = Matrix.trace A at ht
  have hdiag : (∑ i, twirl A i i) = ∑ _i : Fin (n + 2), twirl A 0 0 := by
    apply Finset.sum_congr rfl
    intro i _
    simpa only [if_true] using twirl_entry_classification A i i
  rw [hdiag] at ht
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_ofNat] at ht
  have hn : (n + 2 : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : n + 2 ≠ 0)
  apply (eq_div_iff hn).mpr
  simpa only [mul_comm] using ht

private theorem twirl_row_sum {n : ℕ}
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (i : Fin (n + 2)) :
    (∑ j, twirl A i j) = twirl A 0 0 + (n + 1 : ℂ) * twirl A 0 1 := by
  have he (j : Fin (n + 2)) : twirl A i j =
      twirl A 0 1 + if i = j then twirl A 0 0 - twirl A 0 1 else 0 := by
    rw [twirl_entry_classification]
    by_cases h : i = j <;> simp only [h, if_true, if_false, add_zero]
    ring
  simp_rw [he, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Nat.cast_add, Nat.cast_ofNat]
  ring

/-- The off-diagonal average is determined by the total coefficient sum and trace. -/
theorem twirl_offDiagonal_value {n : ℕ}
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) :
    twirl A 0 1 = ((∑ i, ∑ j, A i j) - Matrix.trace A) /
      ((n + 2 : ℂ) * (n + 1 : ℂ)) := by
  have hs := sum_twirl A
  simp_rw [twirl_row_sum] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_ofNat] at hs
  have hn : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  have hm : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
  have ht : (n + 2 : ℂ) * twirl A 0 0 = Matrix.trace A := by
    rw [twirl_diagonal_value]
    field_simp [hn]
  apply (eq_div_iff (mul_ne_zero hn hm)).mpr
  linear_combination hs - ht

/-- Averaged quadratic energies depend only on coefficient sum and squared size. -/
theorem twirl_bilinear_energy {n : ℕ}
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (v : Fin (n + 2) → ℂ) :
    (∑ i, ∑ j, v i * twirl A i j * v j) =
      twirl A 0 1 * (∑ i, v i) ^ 2 +
        (twirl A 0 0 - twirl A 0 1) * ∑ i, v i ^ 2 := by
  have he (i j : Fin (n + 2)) : v i * twirl A i j * v j =
      twirl A 0 1 * v i * v j +
        if i = j then (twirl A 0 0 - twirl A 0 1) * v i ^ 2 else 0 := by
    rw [twirl_entry_classification]
    by_cases h : i = j
    · subst j
      simp only [if_true]
      ring
    · simp only [if_neg h, add_zero]
      ring
  have hc : (∑ i, ∑ j, twirl A 0 1 * v i * v j) =
      twirl A 0 1 * (∑ i, v i) ^ 2 := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, ← Finset.mul_sum, pow_two]
    ring
  simp_rw [he, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hc, ← Finset.mul_sum]

/-- The quadratic form of the twirl is the literal average of relabeled quadratic forms. -/
theorem twirl_bilinear_average {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    (∑ i, ∑ j, v i * twirl A i j * v j) =
      (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin n), ∑ i, ∑ j, v i * A (σ i) (σ j) * v j := by
  have he (i j : Fin n) : v i * twirl A i j * v j =
      (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin n), v i * A (σ i) (σ j) * v j := by
    simp only [twirl, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
      Matrix.submatrix_apply]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  simp_rw [he, ← Finset.mul_sum]
  congr 1
  calc
    _ = ∑ i, ∑ σ : Equiv.Perm (Fin n), ∑ j, v i * A (σ i) (σ j) * v j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

#print axioms twirl_submatrix
#print axioms twirl_gram_posSemidef
#print axioms trace_twirl
#print axioms sum_twirl
#print axioms twirl_entry_classification
#print axioms twirl_two_parameter_decomposition
#print axioms twirl_diagonal_value
#print axioms twirl_offDiagonal_value
#print axioms twirl_bilinear_energy
#print axioms twirl_bilinear_average
end GaloisForLFunctions.HilbertMetric.PermutationTwirl
