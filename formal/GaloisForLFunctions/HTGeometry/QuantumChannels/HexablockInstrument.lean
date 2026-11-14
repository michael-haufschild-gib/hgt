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

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.hexablockInstrument
#print axioms GaloisForLFunctions.HTGeometry.hexablockInstrument_evolve
#print axioms GaloisForLFunctions.HTGeometry.hexablockInstrument_unital
#print axioms GaloisForLFunctions.HTGeometry.hexablockInstrument_fixed_iff
