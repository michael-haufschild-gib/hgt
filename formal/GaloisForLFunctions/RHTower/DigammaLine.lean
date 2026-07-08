import GaloisForLFunctions.RHTower.DigammaBounds
import GaloisForLFunctions.RHTower.HardyCarrier

/-!
# Digamma reflection on the critical line

This bridge discharges the non-integer hypothesis in `digamma_reflection` on the
critical-line parametrisation `linePt u = 1/2 + iu`.
-/

namespace RHTower

open Complex

/-- Critical-line points are not integer-cast complex numbers. -/
theorem linePt_ne_intCast (u : ℝ) : ∀ m : ℤ, linePt u ≠ (m : ℂ) := by
  intro m h
  have hre := congrArg Complex.re h
  rw [linePt_re] at hre
  have hm : (m : ℝ) = 1 / 2 := by simpa using hre.symm
  have hm2 : (2 * m : ℝ) = 1 := by linarith
  have hInt : (2 * m : ℤ) = 1 := by exact_mod_cast hm2
  omega

/-- Digamma reflection specialized to the critical line `linePt u`, with the
non-integer hypothesis discharged from real part `1/2`. -/
theorem digamma_reflection_linePt (u : ℝ) :
    digamma (linePt u) - digamma (1 - linePt u)
      = -(Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * linePt u)
        / Complex.sin ((Real.pi : ℂ) * linePt u) := by
  exact digamma_reflection (linePt_ne_intCast u)

end RHTower
