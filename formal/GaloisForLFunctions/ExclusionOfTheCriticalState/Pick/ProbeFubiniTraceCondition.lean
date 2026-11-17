import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeFubiniStudy
import GaloisForLFunctions.HilbertMetric.Geometry.FubiniStudyTraceCondition

/-!
# The trace-condition defect of Weil reflection

For the oriented tangent pair `x, i R x`, the quantum-geometric trace
defect is four times the negative-sector Levi energy. It vanishes exactly
when reflection fixes the vector, and has an exact two-valued law on
individual zero coordinates.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open ArithmeticCastelnuovoSeveri Zeta23 HilbertMetric

/-- The signed quantum-geometric trace defect of a reflection tangent pair. -/
def reflectionTraceDefect (x : ZeroSpace) : ℝ :=
  FubiniStudy.traceDefect x x (Complex.I • zeroReflection x)

/-- The failure of ideal quantum geometry is exactly negative-sector Levi energy. -/
theorem reflectionTraceDefect_eq (x : ZeroSpace) :
    reflectionTraceDefect x = 4 * FubiniStudy.levi x (negativePart x) := by
  rw [reflectionTraceDefect, FubiniStudy.traceDefect_eq_levi]
  have he : x + Complex.I • (Complex.I • zeroReflection x) = (2 : ℂ) • negativePart x := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul, negativePart]
    module
  rw [he, FubiniStudy.levi_smul]
  norm_num

/-- An exact arithmetic formula for the trace-condition defect. -/
theorem reflectionTraceDefect_mass (x : ZeroSpace) :
    reflectionTraceDefect x = 4 * negativeMass x * (1 + positiveMass x) /
      (1 + ‖x‖ ^ 2) ^ 2 := by
  rw [reflectionTraceDefect_eq, levi_negativePart]
  ring

/-- Ideal geometry for this oriented tangent pair is exactly reflection invariance. -/
theorem reflectionTraceDefect_zero_iff (x : ZeroSpace) :
    reflectionTraceDefect x = 0 ↔ zeroReflection x = x := by
  rw [reflectionTraceDefect_eq, mul_eq_zero]
  simp only [OfNat.ofNat_ne_zero, false_or, FubiniStudy.levi_eq_zero_iff]
  rw [negativePart, smul_eq_zero]
  simp only [one_div, inv_eq_zero, OfNat.ofNat_ne_zero, false_or, sub_eq_zero]
  exact eq_comm

/-- The trace defect distinguishes individual critical-line and off-line zeros exactly. -/
theorem reflectionTraceDefect_zeroBasis (z : zetaZeroConfig.carrier) :
    reflectionTraceDefect (zeroBasis z) = if (z : ℂ).re = 1 / 2 then 0 else 3 / 4 := by
  classical
  rw [reflectionTraceDefect_eq, levi_negativePart_zeroBasis]
  by_cases hz : (z : ℂ).re = 1 / 2 <;> simp only [hz, if_true, if_false] <;> norm_num

#print axioms reflectionTraceDefect_eq
#print axioms reflectionTraceDefect_mass
#print axioms reflectionTraceDefect_zero_iff
#print axioms reflectionTraceDefect_zeroBasis
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
