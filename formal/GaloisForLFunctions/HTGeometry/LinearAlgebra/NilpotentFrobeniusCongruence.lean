import GaloisForLFunctions.HTGeometry.PowerSeriesSqrtBranch
import GaloisForLFunctions.HTGeometry.TruncatedToeplitz
import GaloisForLFunctions.HTGeometry.HermitianInertia
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Nilpotent corrections preserve the inertia of a jet residue pairing

The coefficient of `X^(N-1)` in a product of two truncated polynomials is
the reversal pairing. Multiplying the product by `1 + X * P` changes this
pairing by a nilpotent correction. A square root with constant coefficient
one gives an explicit Toeplitz congruence with determinant one.

This applies the square-root argument in Konovalov, arXiv:2611.01508,
Proposition 7.6, to the corpus's truncated Toeplitz matrices. All three
inertia indices are unchanged for every polynomial correction and horizon.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Matrix

noncomputable section

/-- The Gram matrix of the top-coefficient product pairing on `R[X]/(X^N)`. -/
def jetResidueGram {R : Type*} [Zero R] [One R] (N : ℕ) : Matrix (Fin N) (Fin N) R :=
  fun i j => if i.val + j.val + 1 = N then 1 else 0

private theorem jetResidueGram_mul {R : Type*} [CommRing R] (N : ℕ)
    (M : Matrix (Fin N) (Fin N) R) (i j : Fin N) :
    (jetResidueGram (R := R) N * M) i j = M i.rev j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
  · simp only [jetResidueGram, Fin.val_rev]
    rw [if_pos (by omega), one_mul]
  · intro k _ hk
    have hne : i.val + k.val + 1 ≠ N := by
      intro he
      apply hk
      apply Fin.ext
      simp only [Fin.val_rev]
      omega
    simp only [jetResidueGram, if_neg hne, zero_mul]
  · simp

private theorem mul_jetResidueGram {R : Type*} [CommRing R] (N : ℕ)
    (M : Matrix (Fin N) (Fin N) R) (i j : Fin N) :
    (M * jetResidueGram (R := R) N) i j = M i j.rev := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j.rev]
  · simp only [jetResidueGram, Fin.val_rev]
    rw [if_pos (by omega), mul_one]
  · intro k _ hk
    have hne : k.val + j.val + 1 ≠ N := by
      intro he
      apply hk
      apply Fin.ext
      simp only [Fin.val_rev]
      omega
    simp only [jetResidueGram, if_neg hne, mul_zero]
  · simp

/-- Multiplication of jets is self-adjoint for the residue pairing. -/
theorem toeplitz_residue_adjoint {R : Type*} [CommRing R] (N : ℕ) (P : R[X]) :
    (toeplitz N P)ᵀ * jetResidueGram N = jetResidueGram N * toeplitz N P := by
  ext i j
  rw [mul_jetResidueGram, jetResidueGram_mul]
  simp only [Matrix.transpose_apply, toeplitz_apply, Fin.val_rev]
  have hiff : i.val ≤ N - (j.val + 1) ↔ j.val ≤ N - (i.val + 1) := by omega
  have hdiff : N - (j.val + 1) - i.val = N - (i.val + 1) - j.val := by omega
  rw [hiff, hdiff]

private theorem toeplitz_eq_of_trunc_eq {R : Type*} [CommRing R] (N : ℕ)
    (P Q : R[X]) (h : PowerSeries.trunc N (P : PowerSeries R) =
      PowerSeries.trunc N (Q : PowerSeries R)) : toeplitz N P = toeplitz N Q := by
  ext i j
  simp only [toeplitz_apply]
  split_ifs with hji
  · have hij : i.val - j.val < N := lt_of_le_of_lt (Nat.sub_le _ _) i.isLt
    have hc := congrArg (fun F : R[X] => F.coeff (i.val - j.val)) h
    simpa only [PowerSeries.coeff_trunc, if_pos hij, Polynomial.coeff_coe] using hc
  · rfl

private theorem toeplitz_trunc_mul {R : Type*} [CommRing R] (N : ℕ)
    (f g : PowerSeries R) :
    toeplitz N (PowerSeries.trunc N f) * toeplitz N (PowerSeries.trunc N g) =
      toeplitz N (PowerSeries.trunc N (f * g)) := by
  rw [toeplitz_mul]
  apply toeplitz_eq_of_trunc_eq
  simpa only [Polynomial.coe_mul, PowerSeries.trunc_trunc] using
    (PowerSeries.trunc_trunc_mul_trunc (n := N) f g)

/-- Every unipotent jet multiplier has a Toeplitz square root of determinant one. -/
theorem exists_toeplitz_unipotent_squareRoot (n : ℕ) (P : ℝ[X]) :
    ∃ Q : ℝ[X], (toeplitz (n + 1) Q).det = 1 ∧
      toeplitz (n + 1) Q * toeplitz (n + 1) Q = toeplitz (n + 1) (1 + X * P) := by
  obtain ⟨ρ, hρ, hρ0⟩ := exists_powerSeries_sqrt_branch (by norm_num : (2 : ℝ) ≠ 0)
    ((1 + X * P : ℝ[X]) : PowerSeries ℝ) 1 one_ne_zero (by simp)
  refine ⟨PowerSeries.trunc (n + 1) ρ, ?_, ?_⟩
  · rw [det_toeplitz, PowerSeries.coeff_trunc, if_pos (Nat.succ_pos n),
      PowerSeries.coeff_zero_eq_constantCoeff, hρ0, one_pow]
  · rw [toeplitz_trunc_mul, hρ]
    apply toeplitz_eq_of_trunc_eq
    exact PowerSeries.trunc_trunc _

/-- A nilpotent correction of the residue form is absorbed by a determinant-one change of basis. -/
theorem exists_jetResidueGram_congruence (n : ℕ) (P : ℝ[X]) :
    ∃ B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, B.det = 1 ∧
      Bᵀ * jetResidueGram (n + 1) * B =
        jetResidueGram (n + 1) * toeplitz (n + 1) (1 + X * P) := by
  obtain ⟨Q, hdet, hsq⟩ := exists_toeplitz_unipotent_squareRoot n P
  refine ⟨toeplitz (n + 1) Q, hdet, ?_⟩
  rw [toeplitz_residue_adjoint, Matrix.mul_assoc, hsq]

/-- Complexification of the corrected real residue form. -/
def correctedJetResidueGram (n : ℕ) (P : ℝ[X]) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (jetResidueGram (n + 1) * toeplitz (n + 1) (1 + X * P)).map Complex.ofRealHom

/-- Positive, negative, and null indices are unchanged by every nilpotent jet correction. -/
theorem correctedJetResidueGram_inertia (n : ℕ) (P : ℝ[X]) :
    hermPosIndex (correctedJetResidueGram n P) =
        hermPosIndex ((jetResidueGram (n + 1) : Matrix _ _ ℝ).map Complex.ofRealHom) ∧
    hermNegIndex (correctedJetResidueGram n P) =
        hermNegIndex ((jetResidueGram (n + 1) : Matrix _ _ ℝ).map Complex.ofRealHom) ∧
    hermNullIndex (correctedJetResidueGram n P) =
        hermNullIndex ((jetResidueGram (n + 1) : Matrix _ _ ℝ).map Complex.ofRealHom) := by
  obtain ⟨B, hdet, hcong⟩ := exists_jetResidueGram_congruence n P
  let S := B.map Complex.ofRealHom
  have hS : IsUnit S := by
    rw [Matrix.isUnit_iff_isUnit_det]
    change IsUnit (Complex.ofRealHom.mapMatrix B).det
    rw [← RingHom.map_det, hdet, map_one]
    exact isUnit_one
  have hstar : Sᴴ = Bᵀ.map Complex.ofRealHom := by
    ext i j
    simp [S, Matrix.conjTranspose_apply]
  have hc : Sᴴ * ((jetResidueGram (n + 1) : Matrix _ _ ℝ).map Complex.ofRealHom) * S =
      correctedJetResidueGram n P := by
    rw [hstar]
    change Bᵀ.map Complex.ofRealHom * _ * B.map Complex.ofRealHom = _
    rw [← Matrix.map_mul, ← Matrix.map_mul, hcong]
    rfl
  rw [← hc]
  exact ⟨posIndex_conjugate _ hS, negIndex_conjugate _ hS, nullIndex_conjugate _ hS⟩

end

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.correctedJetResidueGram_inertia
