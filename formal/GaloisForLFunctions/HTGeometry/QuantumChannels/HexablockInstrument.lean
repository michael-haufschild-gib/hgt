import GaloisForLFunctions.HTGeometry.FiniteNoiseMixingApplications
import GaloisForLFunctions.HTGeometry.BistochasticKrausDeterminant
import GaloisForLFunctions.HTGeometry.OperatorTheory.HexablockAlgebra
import GaloisForLFunctions.HTGeometry.FiniteQuantumOperationalMemoryLaw

/-!
# The hexablock sum/difference quantum instrument

The channels `(U-1)/2` and `(U+1)/2` form a complete Kraus family for every
unitary matrix. Forgetting the outcome averages identity with unitary
conjugation. The resulting channel is unital and its fixed matrices are
exactly the commutant of `U`.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators NNReal
open Hexablock Matrix
open _root_.RHTower
variable {n : ℕ}

/-- A complete two-outcome instrument constructed from an arbitrary unitary. -/
def hexablockInstrument (U : Matrix.unitaryGroup (Fin n) ℂ) : FiniteKrausChannel n 2 where
  operator := ![halfDiff U.1 1, halfSum U.1 1]
  completeness := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, ← Matrix.star_eq_conjTranspose] using
      half_gram U.1 (Matrix.mem_unitaryGroup_iff'.mp U.2)

/-- Heisenberg evolution is the average of identity and adjoint unitary conjugation. -/
theorem hexablockInstrument_pullback (U : Matrix.unitaryGroup (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin n) ℂ) :
    (hexablockInstrument U).pullbackMatrix T =
      (1 / 2 : ℂ) • (star U.1 * T * U.1 + T) := by
  simpa only [FiniteKrausChannel.pullbackMatrix, hexablockInstrument, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    ← Matrix.star_eq_conjTranspose, star_one, one_mul, mul_one] using polarization U.1 1 T

/-- Schrödinger evolution is the average of identity and unitary conjugation. -/
theorem hexablockInstrument_evolve (U : Matrix.unitaryGroup (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin n) ℂ) :
    (hexablockInstrument U).evolveMatrix T =
      (1 / 2 : ℂ) • (U.1 * T * star U.1 + T) := by
  simpa only [FiniteKrausChannel.evolveMatrix, hexablockInstrument, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    ← Matrix.star_eq_conjTranspose, halfDiff, halfSum, star_smul, star_sub, star_add,
    star_div₀, star_one, star_ofNat, star_star, one_mul, mul_one] using
      polarization (star U.1) 1 T

/-- The instrument is unital as well as trace preserving. -/
theorem hexablockInstrument_unital (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (hexablockInstrument U).evolveMatrix 1 = 1 := by
  rw [hexablockInstrument_evolve, mul_one, Matrix.mem_unitaryGroup_iff.mp U.2, smul_add]
  module

/-- Fixed observables are exactly the unitary commutant. -/
theorem hexablockInstrument_fixed_iff (U : Matrix.unitaryGroup (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin n) ℂ) :
    (hexablockInstrument U).pullbackMatrix T = T ↔ Commute T U.1 := by
  rw [hexablockInstrument_pullback]
  have hl : star U.1 * U.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have hr : U.1 * star U.1 = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  constructor
  · intro h
    have hf : star U.1 * T * U.1 = T := by
      have hh : star U.1 * T * U.1 + T = T + T := by
        calc
          star U.1 * T * U.1 + T =
              (2 : ℂ) • ((1 / 2 : ℂ) • (star U.1 * T * U.1 + T)) := by module
          _ = (2 : ℂ) • T := congrArg (fun X : Matrix (Fin n) (Fin n) ℂ => (2 : ℂ) • X) h
          _ = T + T := by module
      exact add_right_cancel hh
    change T * U.1 = U.1 * T
    calc
      T * U.1 = U.1 * (star U.1 * T * U.1) := by rw [← mul_assoc, ← mul_assoc, hr, one_mul]
      _ = U.1 * T := by rw [hf]
  · intro h
    rw [mul_assoc, h.eq, ← mul_assoc, hl, one_mul, smul_add]
    module

/-- Gram states stay positive under the sum/difference instrument. -/
theorem hexablockInstrument_gram_posSemidef (U : Matrix.unitaryGroup (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ((hexablockInstrument U).evolveMatrix (Aᴴ * A)).PosSemidef :=
  (hexablockInstrument U).evolveMatrix_posSemidef (Matrix.posSemidef_conjTranspose_mul_self A)

/-- The instrument induces an explicit bistochastic mixing of input eigenvalues. -/
def hexablockSpectralMixing (U : Matrix.unitaryGroup (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) : doublyStochastic ℝ (Fin n) := by
  let hX := Matrix.isHermitian_conjTranspose_mul_self A
  let hY := (hexablockInstrument_gram_posSemidef U A).isHermitian
  refine ⟨bistochasticKrausEigenWeight (hexablockInstrument U).operator hX hY,
    mem_doublyStochastic_iff_sum.mpr ⟨?_, ?_, ?_⟩⟩
  · exact bistochasticKrausEigenWeight_nonneg _ _ _
  · apply sum_bistochasticKrausEigenWeight_row
    simpa only [FiniteKrausChannel.evolveMatrix, mul_one] using hexablockInstrument_unital U
  · exact sum_bistochasticKrausEigenWeight_column _ _ _ (hexablockInstrument U).completeness

/-- Exact output-spectrum formula for every Gram input. -/
theorem hexablockSpectralMixing_eigenvalues (U : Matrix.unitaryGroup (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (hexablockInstrument_gram_posSemidef U A).isHermitian.eigenvalues =
      (hexablockSpectralMixing U A).val *ᵥ
        (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues := by
  funext i
  exact eigenvalues_kraus_sum_eq_weighted_sum (hexablockInstrument U).operator
    (Matrix.isHermitian_conjTranspose_mul_self A)
    (hexablockInstrument_gram_posSemidef U A).isHermitian rfl i

/-- No sum of the largest eigenvalues increases under this instrument. -/
theorem hexablockInstrument_spectral_topSum_le (U : Matrix.unitaryGroup (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (r : Fin (n + 1)) :
    topSum r.val (hexablockInstrument_gram_posSemidef U A).isHermitian.eigenvalues ≤
      topSum r.val (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues := by
  rw [hexablockSpectralMixing_eigenvalues]
  exact bistochasticMixing_topSum_le _ _ r

/-- Spectral purity decreases for every Gram input. -/
theorem hexablockInstrument_spectral_purity_le (U : Matrix.unitaryGroup (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, (hexablockInstrument_gram_posSemidef U A).isHermitian.eigenvalues i ^ 2) ≤
      ∑ i, (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i ^ 2 := by
  rw [hexablockSpectralMixing_eigenvalues]
  exact bistochasticMixing_sum_sq_le _ _

/-- The spectral Shannon functional increases under the instrument. -/
theorem hexablockInstrument_spectral_entropy_le (U : Matrix.unitaryGroup (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    entropy (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues ≤
      entropy (hexablockInstrument_gram_posSemidef U A).isHermitian.eigenvalues := by
  let x : Fin n → ℝ≥0 := fun i => ⟨(Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i,
    (Matrix.posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg i⟩
  have h := bistochasticMixing_negMulLog_sum_le (hexablockSpectralMixing U A) x
  change (∑ i, Real.negMulLog ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)) ≤
    ∑ i, Real.negMulLog (((hexablockSpectralMixing U A).val *ᵥ
      (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues) i) at h
  rw [← hexablockSpectralMixing_eigenvalues] at h
  simpa only [entropy, tsum_fintype, Real.negMulLog, neg_mul] using h

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.hexablockInstrument
#print axioms GaloisForLFunctions.HTGeometry.hexablockInstrument_evolve
#print axioms GaloisForLFunctions.HTGeometry.hexablockInstrument_unital
#print axioms GaloisForLFunctions.HTGeometry.hexablockInstrument_fixed_iff

#print axioms GaloisForLFunctions.HTGeometry.hexablockInstrument_spectral_topSum_le
#print axioms GaloisForLFunctions.HTGeometry.hexablockInstrument_spectral_purity_le
#print axioms GaloisForLFunctions.HTGeometry.hexablockInstrument_spectral_entropy_le
