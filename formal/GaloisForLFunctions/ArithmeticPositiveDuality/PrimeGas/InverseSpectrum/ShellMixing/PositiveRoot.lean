import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-! # Positive square roots of bounded complex Hilbert-space operators -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def positiveRoot (A : H →L[ℂ] H) : H →L[ℂ] H := CFC.sqrt A

theorem positiveRoot_positive (A : H →L[ℂ] H) : (positiveRoot A).IsPositive :=
  (nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg A)

theorem positiveRoot_sq {A : H →L[ℂ] H} (h : A.IsPositive) : positiveRoot (A^2) = A :=
  CFC.sqrt_sq A ((nonneg_iff_isPositive _).mpr h)

theorem sq_positiveRoot {A : H →L[ℂ] H} (h : A.IsPositive) : positiveRoot A^2 = A :=
  CFC.sq_sqrt A ((nonneg_iff_isPositive _).mpr h)

#print axioms positiveRoot_sq
#print axioms sq_positiveRoot

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
