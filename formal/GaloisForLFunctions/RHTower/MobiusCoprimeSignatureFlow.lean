import GaloisForLFunctions.RHTower.MobiusCoprimeInertia
import GaloisForLFunctions.RHTower.Sieve.LowHeightMoebius
import GaloisForLFunctions.RHTower.Sieve.MoebiusSignBalance
import GaloisForLFunctions.RHTower.RegularizedDivisorHarmonicLimit

open scoped ArithmeticFunction.Moebius

namespace RHTower

noncomputable section

/-- Spectral signature of the finite coprimality matrix. -/
def finiteMobiusCoprimeSignature (N : ℕ) : ℤ :=
  (GaloisForLFunctions.HTGeometry.hermPosIndex (finiteMobiusCoprimeMatrixComplex N) : ℤ) -
    (GaloisForLFunctions.HTGeometry.hermNegIndex (finiteMobiusCoprimeMatrixComplex N) : ℤ)

private def finiteMobiusCoprimeCoordinateEmbedding (N : ℕ) :
    finiteMobiusCoprimeCoordinate N ↪ ℕ :=
  ⟨Subtype.val, Subtype.val_injective⟩

private theorem card_finiteMobiusCoprimeCoordinate_filter (N : ℕ) (z : ℤ) :
    ({d | μ d.1 = z} : Finset (finiteMobiusCoprimeCoordinate N)).card =
      ((Finset.Icc 1 N).filter fun d => μ d = z).card := by
  let e := finiteMobiusCoprimeCoordinateEmbedding N
  rw [← Finset.card_map e]
  congr 1
  ext n
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc]
  aesop

/-- The signature is the finite sum of the Möbius diagonal entries. -/
theorem finiteMobiusCoprimeSignature_eq_sum_Icc (N : ℕ) :
    finiteMobiusCoprimeSignature N = ∑ d ∈ Finset.Icc 1 N, μ d := by
  have hcomplex := RHTower.Sieve.sum_moebius_eq_card_sub (Finset.Icc 1 N)
  have hinteger :
      ∑ d ∈ Finset.Icc 1 N, μ d =
        (((Finset.Icc 1 N).filter fun d => μ d = 1).card : ℤ) -
          (((Finset.Icc 1 N).filter fun d => μ d = -1).card : ℤ) := by
    exact_mod_cast hcomplex
  rw [finiteMobiusCoprimeSignature,
    hermPosIndex_finiteMobiusCoprimeMatrixComplex,
    hermNegIndex_finiteMobiusCoprimeMatrixComplex,
    card_finiteMobiusCoprimeCoordinate_filter,
    card_finiteMobiusCoprimeCoordinate_filter]
  exact hinteger.symm

/-- Shifted range form of the exact signature law. -/
theorem finiteMobiusCoprimeSignature_eq_sum_range (N : ℕ) :
    finiteMobiusCoprimeSignature N = ∑ j ∈ Finset.range N, μ (j + 1) := by
  rw [finiteMobiusCoprimeSignature_eq_sum_Icc]
  exact RHTower.RegularizedDivisorHarmonic.sum_Icc_one_eq_sum_range _ _

/-- Exact Mertens spectral-signature identity. -/
theorem finiteMobiusCoprimeSignature_eq_mertensM (N : ℕ) :
    ((finiteMobiusCoprimeSignature N : ℤ) : ℝ) = RHTower.Sieve.mertensM N := by
  rw [finiteMobiusCoprimeSignature_eq_sum_range]
  push_cast
  exact RHTower.Sieve.sum_range_moebius_shift_eq_mertensM N

/-- Exact one-step spectral flow of the coprimality matrices. -/
theorem finiteMobiusCoprimeSignature_succ_sub (N : ℕ) :
    finiteMobiusCoprimeSignature (N + 1) - finiteMobiusCoprimeSignature N = μ (N + 1) := by
  rw [finiteMobiusCoprimeSignature_eq_sum_range,
    finiteMobiusCoprimeSignature_eq_sum_range, Finset.sum_range_succ]
  ring

end

end RHTower
