import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaClosureParameters
import Mathlib.Tactic

/-!
# Closure-wall transport

On the vertical-closure graph, zero traveling speed is the wall `Q(m)=(1+m)/3`.  The paper also
writes this as `E(m)/K(m)=(2-m)/3`.  We prove the denominator-free integral equation and show that
the negative/classical modulus equivalence carries the wall to itself.  Thus the paper's two
zero-speed roots are one exact orbit, not an observed numerical coincidence.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Closure meets the zero-speed wall exactly at the paper's complete-integral equation. -/
theorem closureQ_eq_speedWall_iff (m : SubcriticalModulus) :
    closureQ m = (1 + (m : ℝ)) / 3 ↔
      3 * completeEllipticE m =
        (2 - (m : ℝ)) * completeEllipticK m := by
  have hK : completeEllipticK m ≠ 0 := completeEllipticK_ne_zero m
  rw [closureQ]
  constructor <;> intro h
  · field_simp [hK] at h
    linarith
  · field_simp [hK]
    linarith

/-- The complete-integral speed equation is invariant under Appendix A modulus transport. -/
theorem negative_speedIntegral_iff_classical (m : NegativeModulus) :
    3 * completeEllipticE m = (2 - (m : ℝ)) * completeEllipticK m ↔
      3 * completeEllipticE (extendedToClassical m) =
        (2 - (extendedToClassical m : ℝ)) *
          completeEllipticK (extendedToClassical m) := by
  have hm0 : (m : ℝ) < 0 := m.property
  have hm : 1 - (m : ℝ) ≠ 0 := by linarith [hm0]
  have hs : Real.sqrt (1 - (m : ℝ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by linarith [hm0]))
  have hs2 : Real.sqrt (1 - (m : ℝ)) ^ (2 : ℕ) = 1 - (m : ℝ) :=
    Real.sq_sqrt (by linarith [hm0])
  rw [completeEllipticE_negative_transform_raw,
    completeEllipticK_negative_transform_raw, extendedToClassical]
  constructor <;> intro h
  · field_simp [hm, hs] at h ⊢
    rw [hs2] at h
    convert h using 1 <;> ring
  · field_simp [hm, hs] at h ⊢
    rw [hs2]
    convert h using 1 <;> ring

/-- Zero-speed closure points occur in exact negative/classical pairs. -/
theorem closureQ_negative_speedWall_iff_classical (m : NegativeModulus) :
    closureQ m = (1 + (m : ℝ)) / 3 ↔
      closureQ (extendedToClassical m) =
        (1 + (extendedToClassical m : ℝ)) / 3 := by
  have hneg := closureQ_eq_speedWall_iff (negativeAsSubcritical m)
  have hclass :=
    closureQ_eq_speedWall_iff (classicalAsSubcritical (extendedToClassical m))
  have h := hneg.trans ((negative_speedIntegral_iff_classical m).trans hclass.symm)
  simpa [negativeAsSubcritical, classicalAsSubcritical] using h

/-- Classical closure has zero reconstructed speed exactly on the integral wall. -/
theorem classicalClosureParameters_gammaSq_eq_zero_iff (m : ClassicalModulus) :
    gammaSq (classicalClosureParameters m) = 0 ↔
      3 * completeEllipticE m =
        (2 - (m : ℝ)) * completeEllipticK m := by
  rw [gammaSq_eq_zero_iff]
  change 1 + (m : ℝ) = 3 * closureQ m ↔ _
  have hwall : closureQ m = (1 + (m : ℝ)) / 3 ↔
      3 * completeEllipticE m =
        (2 - (m : ℝ)) * completeEllipticK m := by
    simpa [classicalAsSubcritical] using
      closureQ_eq_speedWall_iff (classicalAsSubcritical m)
  constructor
  · intro h
    apply hwall.mp
    linarith
  · intro h
    have := hwall.mpr h
    linarith

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
