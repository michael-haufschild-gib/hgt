import GaloisForLFunctions.RHTower.CriticalPrimeSamplingIncidence
import GaloisForLFunctions.HTGeometry.RectangularGramSpectrum

/-!
# Schatten exponent bridge for critical-prime sampling

The rectangular approximation numbers of a compact sampler square exactly to the approximation
numbers of its positive Gram incidence.  This gives the exact exponent-doubling law used by both
polynomial and rapid Fock carriers.
-/

namespace RHTower

noncomputable section

open ContinuousLinearMap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Exact exponent-doubling law between a compact rectangular sampler and its positive Gram
incidence. -/
theorem memRectSchattenClass_two_mul_iff_memSchattenClass_adjoint_comp_self
    (S : H →L[ℂ] K) (hS : IsCompactOperator S) (q : ℝ) :
    MemRectSchattenClass (2 * q) S ↔ MemSchattenClass q (adjoint S ∘L S) := by
  unfold MemRectSchattenClass MemSchattenClass
  exact summable_congr fun n => by
    calc
      rectApproxNumber S n ^ (2 * q) =
          (rectApproxNumber S n ^ (2 : ℝ)) ^ q :=
        Real.rpow_mul (rectApproxNumber_nonneg S n) 2 q
      _ = (rectApproxNumber S n ^ (2 : ℕ)) ^ q := by
        exact congrArg (fun x : ℝ => x ^ q) (Real.rpow_natCast (rectApproxNumber S n) 2)
      _ = approxNumber (adjoint S ∘L S) n ^ q := by
        rw [rectApproxNumber_sq_eq_approxNumber_adjoint_comp_self S hS n]

/-- Critical-prime specialization of the exact exponent-doubling law. -/
theorem memRectSchattenClass_two_mul_iff_memSchattenClass_criticalPrimeSamplingIncidence
    (S : H →L[ℂ] CriticalPrimeEllTwo) (hS : IsCompactOperator S) (q : ℝ) :
    MemRectSchattenClass (2 * q) S ↔
      MemSchattenClass q (criticalPrimeSamplingIncidence S) := by
  simpa [criticalPrimeSamplingIncidence] using
    memRectSchattenClass_two_mul_iff_memSchattenClass_adjoint_comp_self S hS q

end

end RHTower
