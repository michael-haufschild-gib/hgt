import GaloisForLFunctions.HTGeometry.GammaShiftCasoratian
import GaloisForLFunctions.HTGeometry.NegSupportedDimension
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Universal alternating-inertia law for reciprocal-factorial Hankel matrices

For every order `n`, this module studies the Hankel matrix
`Hₙ(i,j) = 1 / (i+j+1)!`.  Leading-block inverse columns form an explicit
upper-triangular flag frame `Qₙ`.  The central identity is the unconditional
all-order congruence

`Qₙᵀ Hₙ Qₙ = diagonal(d₀,...,dₙ₋₁)`,

where `dⱼ` is the bottom-right entry of `Hⱼ₊₁⁻¹`.  Consecutive determinant
signs show `dⱼ < 0` for every odd `j`.  Hence the `2m` block contains an
explicit injective `m`-column negative frame.  Negative inertia is therefore
unbounded along the tower.  No computation or unproved hypothesis is used.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry.ReciprocalFactorialHankel

open Matrix Polynomial

noncomputable section

def H (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    ((Nat.descFactorial (n + i) (Fin.rev j) : ℕ) : ℝ) /
      (((n + i).factorial : ℕ) : ℝ)

theorem H_apply (n : ℕ) (i j : Fin n) :
    H n i j = 1 / ((((i : ℕ) + (j : ℕ) + 1).factorial : ℕ) : ℝ) := by
  rw [H]
  have hrev : (Fin.rev j : ℕ) = n - 1 - (j : ℕ) := by
    simp [Fin.val_rev]
    omega
  have hle : (Fin.rev j : ℕ) ≤ n + (i : ℕ) := by omega
  have hsub :
      n + (i : ℕ) - (Fin.rev j : ℕ) =
        (i : ℕ) + (j : ℕ) + 1 := by
    rw [hrev]
    omega
  have hfac := Nat.factorial_mul_descFactorial hle
  rw [hsub] at hfac
  have hden : ((((n + (i : ℕ)).factorial : ℕ) : ℝ)) ≠ 0 := by positivity
  have hsmall : (((((i : ℕ) + (j : ℕ) + 1).factorial : ℕ) : ℝ)) ≠ 0 := by
    positivity
  have hfacR :
      (((((i : ℕ) + (j : ℕ) + 1).factorial : ℕ) : ℝ)) *
          ((Nat.descFactorial (n + (i : ℕ)) (Fin.rev j) : ℕ) : ℝ) =
        (((n + (i : ℕ)).factorial : ℕ) : ℝ) := by
    exact_mod_cast hfac
  field_simp [hden, hsmall]
  nlinarith

def descEval (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i k => (descPochhammer ℝ (k : ℕ)).eval ((n + (i : ℕ) : ℕ) : ℝ)

theorem det_descEval (n : ℕ) :
    (descEval n).det =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
        (((n + (j : ℕ) : ℕ) : ℝ) - ((n + (i : ℕ) : ℕ) : ℝ)) := by
  let p : Fin n → ℝ[X] := fun k => descPochhammer ℝ (k : ℕ)
  have hdeg : ∀ k, (p k).natDegree = k := by
    intro k
    exact descPochhammer_natDegree ℝ (k : ℕ)
  have hmonic : ∀ k, (p k).Monic := by
    intro k
    exact monic_descPochhammer (R := ℝ) (k : ℕ)
  calc
    (descEval n).det =
        (Matrix.of fun (i k : Fin n) =>
          (p k).eval (((n + (i : ℕ) : ℕ) : ℝ))).det := by
      rfl
    _ = (Matrix.vandermonde fun i : Fin n =>
          (((n + (i : ℕ) : ℕ) : ℝ))).det :=
      (Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
        (fun i : Fin n => (((n + (i : ℕ) : ℕ) : ℝ))) p hdeg hmonic).symm
    _ = _ := Matrix.det_vandermonde _

theorem revPerm_sign (n : ℕ) :
    (@Fin.revPerm n).sign = (-1 : ℤˣ) ^ n.choose 2 := by
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  simp only [Fin.revPerm_apply, Fin.rev_lt_rev]
  have hinner : ∀ i : Fin n,
      (∏ j ∈ Finset.Ioi i, if j < i then (1 : ℤˣ) else -1) =
        ∏ _j ∈ Finset.Ioi i, (-1 : ℤˣ) := by
    intro i
    apply Finset.prod_congr rfl
    intro j hj
    rw [if_neg]
    exact not_lt_of_ge (Finset.mem_Ioi.mp hj).le
  simp_rw [hinner]
  simp only [Finset.prod_const, Fin.card_Ioi]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_range_reflect (fun i => i) n, Finset.sum_range_id]
  exact (Nat.choose_two_right n).symm

theorem rowScaled_eq (n : ℕ) :
    (fun (i j : Fin n) => (((n + (i : ℕ)).factorial : ℕ) : ℝ) * H n i j) =
      Matrix.reindex (Equiv.refl (Fin n)) Fin.revPerm (descEval n) := by
  ext i j
  rw [H]
  simp only [Matrix.reindex_apply, Equiv.refl_symm, Fin.revPerm_symm,
    Matrix.submatrix_apply, Equiv.refl_apply, Fin.revPerm_apply,
    descEval, descPochhammer_eval_eq_descFactorial]
  have hden : ((((n + (i : ℕ)).factorial : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hden]

theorem det_H_mul_positive (n : ℕ) :
    (∏ i : Fin n, ((((n + (i : ℕ)).factorial : ℕ) : ℝ))) * (H n).det =
      (((-1 : ℤˣ) ^ n.choose 2 : ℤˣ) : ℝ) *
        ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
          (((n + (j : ℕ) : ℕ) : ℝ) - ((n + (i : ℕ) : ℕ) : ℝ)) := by
  rw [← Matrix.det_mul_column]
  rw [rowScaled_eq]
  change (Matrix.reindex (Equiv.refl (Fin n)) Fin.revPerm (descEval n)).det = _
  rw [Matrix.det_reindex, det_descEval]
  simp [revPerm_sign]

theorem det_H_ne_zero (n : ℕ) : (H n).det ≠ 0 := by
  have h := det_H_mul_positive n
  intro hz
  rw [hz, mul_zero] at h
  have hrhs : ((((-1 : ℤˣ) ^ n.choose 2 : ℤˣ) : ℝ) *
        ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
          (((n + (j : ℕ) : ℕ) : ℝ) - ((n + (i : ℕ) : ℕ) : ℝ))) ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      apply sub_ne_zero.mpr
      have hijFin : i < j := Finset.mem_Ioi.mp hj
      have hij : (i : ℕ) < (j : ℕ) := hijFin
      have hne : n + (j : ℕ) ≠ n + (i : ℕ) := by omega
      exact_mod_cast hne
  exact hrhs h.symm

def detSign (n : ℕ) : ℝ := (-1 : ℝ) ^ n.choose 2

theorem detSign_sq (n : ℕ) : detSign n ^ 2 = 1 := by
  simp [detSign, ← pow_mul]

theorem detSign_succ (n : ℕ) :
    detSign (n + 1) = (-1 : ℝ) ^ n * detSign n := by
  simp [detSign, Nat.choose_succ_succ, pow_add]

theorem det_H_signed_pos (n : ℕ) :
    0 < detSign n * (H n).det := by
  have h := det_H_mul_positive n
  have hprod :
      0 < ∏ i : Fin n, ((((n + (i : ℕ)).factorial : ℕ) : ℝ)) := by
    positivity
  have hvand :
      0 < ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
          (((n + (j : ℕ) : ℕ) : ℝ) - ((n + (i : ℕ) : ℕ) : ℝ)) := by
    apply Finset.prod_pos
    intro i hi
    apply Finset.prod_pos
    intro j hj
    have hijFin : i < j := Finset.mem_Ioi.mp hj
    have hij : (i : ℕ) < (j : ℕ) := hijFin
    apply sub_pos.mpr
    exact_mod_cast (show n + (i : ℕ) < n + (j : ℕ) by omega)
  have hcast :
      ((((-1 : ℤˣ) ^ n.choose 2 : ℤˣ) : ℝ)) = detSign n := by
    change ((((-1 : ℤ) ^ n.choose 2 : ℤ) : ℝ)) =
      (-1 : ℝ) ^ n.choose 2
    norm_cast
  rw [hcast] at h
  have hs := detSign_sq n
  have hEq :
      (∏ i : Fin n, ((((n + (i : ℕ)).factorial : ℕ) : ℝ))) *
          (detSign n * (H n).det) =
        ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
          (((n + (j : ℕ) : ℕ) : ℝ) - ((n + (i : ℕ) : ℕ) : ℝ)) := by
    calc
      _ = detSign n * ((∏ i : Fin n,
            ((((n + (i : ℕ)).factorial : ℕ) : ℝ))) * (H n).det) := by ring
      _ = detSign n * (detSign n *
          (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
            (((n + (j : ℕ) : ℕ) : ℝ) - ((n + (i : ℕ) : ℕ) : ℝ)))) := by rw [h]
      _ = _ := by
        rw [← mul_assoc]
        rw [show detSign n * detSign n = detSign n ^ 2 by ring]
        rw [hs, one_mul]
  have hpos :
      0 < (∏ i : Fin n, ((((n + (i : ℕ)).factorial : ℕ) : ℝ))) *
        (detSign n * (H n).det) := hEq.symm ▸ hvand
  rcases mul_pos_iff.mp hpos with hpp | hnn
  · exact hpp.2
  · exact (not_lt_of_ge hprod.le hnn.1).elim

theorem H_submatrix_castSucc (n : ℕ) :
    (H (n + 1)).submatrix Fin.castSucc Fin.castSucc = H n := by
  ext i j
  simp only [Matrix.submatrix_apply]
  rw [H_apply, H_apply]
  simp

theorem adjugate_H_last (n : ℕ) :
    (H (n + 1)).adjugate (Fin.last n) (Fin.last n) = (H n).det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  rw [show (-1 : ℝ) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ)) = 1 by
    apply Even.neg_one_pow
    exact ⟨n, by simp⟩]
  rw [one_mul, Fin.succAbove_last, H_submatrix_castSucc]

def lastInvDiag (n : ℕ) : ℝ :=
  (H (n + 1))⁻¹ (Fin.last n) (Fin.last n)

theorem lastInvDiag_eq_det_div (n : ℕ) :
    lastInvDiag n = (H n).det / (H (n + 1)).det := by
  rw [lastInvDiag, Matrix.inv_def, Matrix.smul_apply, adjugate_H_last]
  rw [smul_eq_mul]
  simp only [Ring.inverse_eq_inv]
  ring

theorem lastInvDiag_ne_zero (n : ℕ) : lastInvDiag n ≠ 0 := by
  rw [lastInvDiag_eq_det_div]
  exact div_ne_zero (det_H_ne_zero n) (det_H_ne_zero (n + 1))

theorem lastInvDiag_neg_of_odd {n : ℕ} (hn : Odd n) :
    lastInvDiag n < 0 := by
  rw [lastInvDiag_eq_det_div]
  have h0 := det_H_signed_pos n
  have h1 := det_H_signed_pos (n + 1)
  rw [detSign_succ, hn.neg_one_pow] at h1
  have hs := detSign_sq n
  have hprod : (H n).det * (H (n + 1)).det < 0 := by
    nlinarith
  rw [div_neg_iff]
  exact mul_neg_iff.mp hprod

/-- Column `j` is the last inverse column of the leading `(j+1) × (j+1)` block,
extended by zero. -/
def inverseFlagFrame (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if h : (i : ℕ) ≤ (j : ℕ) then
      (H ((j : ℕ) + 1))⁻¹
        ⟨i, Nat.lt_succ_of_le h⟩ (Fin.last (j : ℕ))
    else 0

@[simp] theorem inverseFlagFrame_diagonal (n : ℕ) (i : Fin n) :
    inverseFlagFrame n i i = lastInvDiag (i : ℕ) := by
  rw [inverseFlagFrame, dif_pos (le_refl (i : ℕ))]
  unfold lastInvDiag
  congr 2

theorem inverseFlagFrame_blockTriangular (n : ℕ) :
    (inverseFlagFrame n).BlockTriangular id := by
  intro i j hji
  rw [inverseFlagFrame, dif_neg]
  exact Nat.not_le_of_lt hji

theorem det_inverseFlagFrame (n : ℕ) :
    (inverseFlagFrame n).det = ∏ i : Fin n, lastInvDiag (i : ℕ) := by
  rw [Matrix.det_of_upperTriangular (inverseFlagFrame_blockTriangular n)]
  simp_rw [inverseFlagFrame_diagonal]

theorem det_inverseFlagFrame_ne_zero (n : ℕ) :
    (inverseFlagFrame n).det ≠ 0 := by
  rw [det_inverseFlagFrame]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => lastInvDiag_ne_zero (i : ℕ)

private theorem sum_inverseFlagFrame_column {n : ℕ} (i j : Fin n)
    (hij : (i : ℕ) ≤ (j : ℕ)) :
    ∑ k : Fin n, H n i k * inverseFlagFrame n k j =
      ∑ k : Fin ((j : ℕ) + 1),
        H ((j : ℕ) + 1) ⟨i, Nat.lt_succ_of_le hij⟩ k *
          (H ((j : ℕ) + 1))⁻¹ k (Fin.last (j : ℕ)) := by
  classical
  have hzero : ∀ k ∈ Finset.univ, k ∉ Finset.Iic j →
      H n i k * inverseFlagFrame n k j = 0 := by
    intro k _ hk
    rw [inverseFlagFrame, dif_neg, mul_zero]
    simpa [Finset.mem_Iic] using hk
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.Iic j)) hzero]
  refine Finset.sum_bij
      (fun k hk => (⟨k, Nat.lt_succ_of_le (by
        have hkj := Finset.mem_Iic.mp hk
        exact hkj)⟩ :
        Fin ((j : ℕ) + 1))) ?_ ?_ ?_ ?_
  · intro k hk
    exact Finset.mem_univ _
  · intro a ha b hb hab
    exact Fin.ext (Fin.mk.inj hab)
  · intro b hb
    refine ⟨⟨b, lt_of_le_of_lt (Nat.le_of_lt_succ b.isLt) j.isLt⟩, ?_, ?_⟩
    · simp only [Finset.mem_Iic]
      change (b : ℕ) ≤ (j : ℕ)
      exact Nat.le_of_lt_succ b.isLt
    · apply Fin.ext
      rfl
  · intro k hk
    have hkjFin : k ≤ j := Finset.mem_Iic.mp hk
    have hkj : (k : ℕ) ≤ (j : ℕ) := hkjFin
    rw [inverseFlagFrame, dif_pos hkj, H_apply, H_apply]

theorem H_mul_inverseFlagFrame_of_le {n : ℕ} (i j : Fin n)
    (hij : (i : ℕ) ≤ (j : ℕ)) :
    (H n * inverseFlagFrame n) i j = if i = j then 1 else 0 := by
  rw [Matrix.mul_apply, sum_inverseFlagFrame_column i j hij]
  have hunit : IsUnit (H ((j : ℕ) + 1)).det :=
    isUnit_iff_ne_zero.mpr (det_H_ne_zero ((j : ℕ) + 1))
  have hentry := congrFun
    (congrFun (Matrix.mul_nonsing_inv (H ((j : ℕ) + 1)) hunit)
      ⟨i, Nat.lt_succ_of_le hij⟩) (Fin.last (j : ℕ))
  simpa [Matrix.mul_apply, Matrix.one_apply, Fin.ext_iff] using hentry

theorem H_transpose (n : ℕ) : (H n)ᵀ = H n := by
  ext i j
  rw [Matrix.transpose_apply, H_apply, H_apply]
  rw [show (j : ℕ) + (i : ℕ) + 1 = (i : ℕ) + (j : ℕ) + 1 by omega]

private theorem inverseFlagFrame_congruence_entry_of_le {n : ℕ} (i j : Fin n)
    (hij : i ≤ j) :
    ((inverseFlagFrame n)ᵀ * H n * inverseFlagFrame n) i j =
      if i = j then lastInvDiag (i : ℕ) else 0 := by
  classical
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  have hzero : ∀ k ∈ Finset.univ, k ∉ Finset.Iic i →
      (inverseFlagFrame n)ᵀ i k *
        (H n * inverseFlagFrame n) k j = 0 := by
    intro k _ hk
    have hik : ¬ (k : ℕ) ≤ (i : ℕ) := by
      simpa [Finset.mem_Iic] using hk
    rw [Matrix.transpose_apply, inverseFlagFrame, dif_neg hik, zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.Iic i)) hzero]
  by_cases heq : i = j
  · subst j
    rw [Finset.sum_eq_single i]
    · rw [Matrix.transpose_apply,
        H_mul_inverseFlagFrame_of_le i i (le_refl (i : ℕ))]
      simp
    · intro k hk hki
      have hkiFin : k ≤ i := Finset.mem_Iic.mp hk
      have hkiVal : (k : ℕ) ≤ (i : ℕ) := hkiFin
      rw [H_mul_inverseFlagFrame_of_le k i hkiVal, if_neg hki, mul_zero]
    · simp
  · rw [if_neg heq]
    apply Finset.sum_eq_zero
    intro k hk
    have hkiFin : k ≤ i := Finset.mem_Iic.mp hk
    have hkjFin : k ≤ j := hkiFin.trans hij
    have hkj : (k : ℕ) ≤ (j : ℕ) := hkjFin
    rw [H_mul_inverseFlagFrame_of_le k j hkj, if_neg, mul_zero]
    intro hkjEq
    subst k
    exact heq (hij.antisymm hkiFin)

theorem inverseFlagFrame_congruence (n : ℕ) :
    (inverseFlagFrame n)ᵀ * H n * inverseFlagFrame n =
      Matrix.diagonal (fun i : Fin n => lastInvDiag (i : ℕ)) := by
  ext i j
  by_cases hij : i ≤ j
  · rw [inverseFlagFrame_congruence_entry_of_le i j hij]
    simp [Matrix.diagonal_apply]
  · have hji : j ≤ i := le_of_not_ge hij
    have hsym :
        ((inverseFlagFrame n)ᵀ * H n * inverseFlagFrame n) i j =
          ((inverseFlagFrame n)ᵀ * H n * inverseFlagFrame n) j i := by
      calc
        _ = (((inverseFlagFrame n)ᵀ * H n * inverseFlagFrame n)ᵀ) j i := rfl
        _ = _ := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
            H_transpose]
          rw [Matrix.mul_assoc]
    rw [hsym, inverseFlagFrame_congruence_entry_of_le j i hji]
    have hne : i ≠ j := fun h => hij h.le
    simp [hne, hne.symm]

def complexH (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  (H n).map Complex.ofReal

def complexInverseFlagFrame (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  (inverseFlagFrame n).map Complex.ofReal

theorem complexInverseFlagFrame_conjTranspose (n : ℕ) :
    (complexInverseFlagFrame n)ᴴ = (complexInverseFlagFrame n)ᵀ := by
  ext i j
  simp [complexInverseFlagFrame, Matrix.conjTranspose_apply]

theorem complexInverseFlagFrame_congruence (n : ℕ) :
    (complexInverseFlagFrame n)ᴴ * complexH n * complexInverseFlagFrame n =
      Matrix.diagonal (fun i : Fin n => ((lastInvDiag (i : ℕ) : ℝ) : ℂ)) := by
  rw [complexInverseFlagFrame_conjTranspose]
  have hmap := congrArg
    (fun M : Matrix (Fin n) (Fin n) ℝ => M.map Complex.ofReal)
    (inverseFlagFrame_congruence n)
  change
    (((inverseFlagFrame n)ᵀ * H n * inverseFlagFrame n).map Complex.ofReal) =
      (Matrix.diagonal (fun i : Fin n => lastInvDiag (i : ℕ))).map
        Complex.ofReal at hmap
  convert hmap using 1
  all_goals
    ext i j
    simp [complexInverseFlagFrame, complexH, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.diagonal_apply]
    try (by_cases hij : i = j <;> simp [hij])

theorem complexInverseFlagFrame_isUnit (n : ℕ) :
    IsUnit (complexInverseFlagFrame n) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  rw [show (complexInverseFlagFrame n).det =
      ((inverseFlagFrame n).det : ℂ) by
    exact (Complex.ofRealHom.map_det (inverseFlagFrame n)).symm]
  exact isUnit_iff_ne_zero.mpr
    (Complex.ofReal_ne_zero.mpr (det_inverseFlagFrame_ne_zero n))

def complexInverseFlagEquiv (n : ℕ) :
    (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  LinearEquiv.ofBijective (complexInverseFlagFrame n).mulVecLin
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr (complexInverseFlagFrame_isUnit n),
      Matrix.mulVec_surjective_iff_isUnit.mpr (complexInverseFlagFrame_isUnit n)⟩

@[simp] theorem complexInverseFlagEquiv_apply (n : ℕ) (x : Fin n → ℂ) :
    complexInverseFlagEquiv n x = (complexInverseFlagFrame n).mulVec x := rfl

def reciprocalFactorialNegativeSubspace (n : ℕ) :
    Submodule ℂ (Fin n → ℂ) :=
  (GaloisForLFunctions.HTGeometry.negSupported
    (fun i : Fin n => lastInvDiag (i : ℕ))).map
      (complexInverseFlagEquiv n).toLinearMap

theorem finrank_reciprocalFactorialNegativeSubspace (n : ℕ) :
    Module.finrank ℂ (reciprocalFactorialNegativeSubspace n) =
      GaloisForLFunctions.HTGeometry.negCount
        (fun i : Fin n => lastInvDiag (i : ℕ)) := by
  rw [reciprocalFactorialNegativeSubspace,
    (complexInverseFlagEquiv n).finrank_map_eq]
  exact GaloisForLFunctions.HTGeometry.finrank_negSupported _

private theorem diagonal_quad_neg_on_negSupported {n : ℕ}
    (x : Fin n → ℂ)
    (hx : x ∈ GaloisForLFunctions.HTGeometry.negSupported
      (fun i : Fin n => lastInvDiag (i : ℕ)))
    (hx0 : x ≠ 0) :
    (star x ⬝ᵥ
      (Matrix.diagonal (fun i : Fin n =>
        ((lastInvDiag (i : ℕ) : ℝ) : ℂ))).mulVec x).re < 0 := by
  have hnonempty : ∃ i, x i ≠ 0 := by
    by_contra hnone
    apply hx0
    funext i
    exact not_not.mp ((not_exists.mp hnone) i)
  have hquad :
      (star x ⬝ᵥ
        (Matrix.diagonal (fun i : Fin n =>
          ((lastInvDiag (i : ℕ) : ℝ) : ℂ))).mulVec x).re =
        ∑ i : Fin n, lastInvDiag (i : ℕ) * ‖x i‖ ^ 2 := by
    rw [GaloisForLFunctions.HTGeometry.re_quadForm_diagonal]
  rw [hquad]
  have hle : ∀ i : Fin n, lastInvDiag (i : ℕ) * ‖x i‖ ^ 2 ≤ 0 := by
    intro i
    by_cases hi : lastInvDiag (i : ℕ) < 0
    · exact mul_nonpos_of_nonpos_of_nonneg hi.le (sq_nonneg _)
    · rw [(GaloisForLFunctions.HTGeometry.mem_negSupported _ _).1 hx i hi]
      simp
  obtain ⟨i0, hi0x⟩ := hnonempty
  have hi0neg : lastInvDiag (i0 : ℕ) < 0 := by
    by_contra hi
    exact hi0x ((GaloisForLFunctions.HTGeometry.mem_negSupported _ _).1 hx i0 hi)
  have hi0 : lastInvDiag (i0 : ℕ) * ‖x i0‖ ^ 2 < 0 :=
    mul_neg_of_neg_of_pos hi0neg
      (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hi0x))
  have herase :
      (∑ i ∈ (Finset.univ.erase i0 : Finset (Fin n)),
        lastInvDiag (i : ℕ) * ‖x i‖ ^ 2) ≤ 0 :=
    Finset.sum_nonpos fun i _ => hle i
  rw [← Finset.sum_erase_add Finset.univ
    (fun i : Fin n => lastInvDiag (i : ℕ) * ‖x i‖ ^ 2) (Finset.mem_univ i0)]
  linarith

theorem reciprocalFactorialNegativeSubspace_negDef (n : ℕ) :
    ∀ y ∈ reciprocalFactorialNegativeSubspace n, y ≠ 0 →
      (star y ⬝ᵥ (complexH n).mulVec y).re < 0 := by
  intro y hy hy0
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  have hx0 : x ≠ 0 := by
    intro h
    apply hy0
    rw [h, map_zero]
  have hdiag := diagonal_quad_neg_on_negSupported x hx hx0
  have hcong := complexInverseFlagFrame_congruence n
  have hquad := congrArg
    (fun M : Matrix (Fin n) (Fin n) ℂ => star x ⬝ᵥ M.mulVec x) hcong
  change
    (star ((complexInverseFlagFrame n).mulVec x) ⬝ᵥ
      (complexH n).mulVec ((complexInverseFlagFrame n).mulVec x)).re < 0
  have hquadRe := congrArg Complex.re hquad
  rw [← hquadRe] at hdiag
  simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using hdiag

def oddIndex (m : ℕ) (a : Fin m) : Fin (2 * m) :=
  ⟨2 * (a : ℕ) + 1, by omega⟩

theorem oddIndex_injective (m : ℕ) : Function.Injective (oddIndex m) := by
  intro a b h
  apply Fin.ext
  have hv := Fin.mk.inj h
  omega

def oddNegativeIndex (m : ℕ) (a : Fin m) :
    {i : Fin (2 * m) // lastInvDiag (i : ℕ) < 0} :=
  ⟨oddIndex m a, lastInvDiag_neg_of_odd ⟨(a : ℕ), by
    simp [oddIndex]⟩⟩

theorem oddNegativeIndex_injective (m : ℕ) :
    Function.Injective (oddNegativeIndex m) := by
  intro a b h
  apply oddIndex_injective m
  exact congrArg Subtype.val h

def oddInverseFlagFrame (m : ℕ) :
    Matrix (Fin (2 * m)) (Fin m) ℂ :=
  fun i a => complexInverseFlagFrame (2 * m) i (oddIndex m a)

theorem oddInverseFlagFrame_compression (m : ℕ) :
    (oddInverseFlagFrame m)ᴴ * complexH (2 * m) * oddInverseFlagFrame m =
      Matrix.diagonal (fun a : Fin m =>
        ((lastInvDiag ((oddIndex m a : Fin (2 * m)) : ℕ) : ℝ) : ℂ)) := by
  ext a b
  have hentry := congrFun
    (congrFun (complexInverseFlagFrame_congruence (2 * m))
      (oddIndex m a)) (oddIndex m b)
  by_cases hab : a = b
  · subst b
    simpa [oddInverseFlagFrame, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply] using hentry
  · have hodd : oddIndex m a ≠ oddIndex m b :=
      fun h => hab (oddIndex_injective m h)
    simpa [oddInverseFlagFrame, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply, hab, hodd] using hentry

theorem oddInverseFlagFrame_mulVec_injective (m : ℕ) :
    Function.Injective (oddInverseFlagFrame m).mulVec := by
  intro z w hzw
  have hneg : ∀ a : Fin m,
      ((((lastInvDiag ((oddIndex m a : Fin (2 * m)) : ℕ) : ℝ) : ℂ))).re < 0 :=
    fun a => (oddNegativeIndex m a).2
  have hdiag := (GaloisForLFunctions.diagonal_negative_subspace
    (fun a : Fin m =>
      ((lastInvDiag ((oddIndex m a : Fin (2 * m)) : ℕ) : ℝ) : ℂ)) hneg).2
  let u := z - w
  have hFu : (oddInverseFlagFrame m).mulVec u = 0 := by
    rw [Matrix.mulVec_sub, hzw, sub_self]
  by_contra hne
  have hu0 : u ≠ 0 := sub_ne_zero.mpr hne
  have hlt := hdiag u (by simp) hu0
  have hcong := oddInverseFlagFrame_compression m
  have hquad := congrArg
    (fun M : Matrix (Fin m) (Fin m) ℂ => star u ⬝ᵥ M.mulVec u) hcong
  change
    star u ⬝ᵥ
        (((oddInverseFlagFrame m)ᴴ * complexH (2 * m) *
          oddInverseFlagFrame m).mulVec u) =
      star u ⬝ᵥ
        (Matrix.diagonal (fun a : Fin m =>
          ((lastInvDiag ((oddIndex m a : Fin (2 * m)) : ℕ) : ℝ) : ℂ))).mulVec u
    at hquad
  have hzero :
      star ((oddInverseFlagFrame m).mulVec u) ⬝ᵥ
        (complexH (2 * m)).mulVec ((oddInverseFlagFrame m).mulVec u) = 0 := by
    rw [hFu]
    simp
  have hleft :
      star u ⬝ᵥ
        (((oddInverseFlagFrame m)ᴴ * complexH (2 * m) *
          oddInverseFlagFrame m).mulVec u) = 0 := by
    simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using hzero
  rw [hleft] at hquad
  have : (star u ⬝ᵥ
      (Matrix.diagonal (fun a : Fin m =>
        ((lastInvDiag ((oddIndex m a : Fin (2 * m)) : ℕ) : ℝ) : ℂ))).mulVec u) = 0 :=
    hquad.symm
  rw [this] at hlt
  norm_num at hlt

theorem negCount_lastInvDiag_two_mul_lower (m : ℕ) :
    m ≤ GaloisForLFunctions.HTGeometry.negCount
      (fun i : Fin (2 * m) => lastInvDiag (i : ℕ)) := by
  calc
    m = Fintype.card (Fin m) := by simp
    _ ≤ Fintype.card {i : Fin (2 * m) // lastInvDiag (i : ℕ) < 0} :=
      Fintype.card_le_of_injective (oddNegativeIndex m)
        (oddNegativeIndex_injective m)
    _ = _ := by
      rw [Fintype.card_subtype]
      rfl

/-- The reciprocal-factorial Hankel tower has negative subspaces of arbitrarily
large prescribed dimension. -/
theorem reciprocalFactorialHankel_unbounded_negative_inertia (m : ℕ) :
    m ≤ Module.finrank ℂ (reciprocalFactorialNegativeSubspace (2 * m)) ∧
      ∀ y ∈ reciprocalFactorialNegativeSubspace (2 * m), y ≠ 0 →
        (star y ⬝ᵥ (complexH (2 * m)).mulVec y).re < 0 := by
  constructor
  · rw [finrank_reciprocalFactorialNegativeSubspace]
    exact negCount_lastInvDiag_two_mul_lower m
  · exact reciprocalFactorialNegativeSubspace_negDef (2 * m)

end

end GaloisForLFunctions.HTGeometry.ReciprocalFactorialHankel
