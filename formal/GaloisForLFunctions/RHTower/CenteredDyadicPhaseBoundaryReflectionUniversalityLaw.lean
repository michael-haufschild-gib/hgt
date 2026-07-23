import GaloisForLFunctions.RHTower.XiOPUCParaorthogonalPhaseGate
import GaloisForLFunctions.RHTower.BoundaryReflection

/-!
# Centered dyadic phase/boundary-reflection universality

The dyadic phase used by the Xi paraorthogonal gate and the normalized prime boundary coordinate
are two charts of the same critical-locus test. Under the centered Xi map `z ↦ 1/2 + z i`, unit
phase, unit normalized boundary modulus, and fixedness under functional-equation reflection are
equivalent.
-/

namespace GaloisForLFunctions

open Complex

noncomputable section

/-- Unit modulus of the dyadic centered phase is exactly the centered real axis. This supplies the
converse to the one-way phase gate used by the OPUC argument. -/
theorem norm_xiDyadicLogPhase_eq_one_iff (z : ℂ) :
    ‖_root_.RHTower.xiDyadicLogPhase z‖ = 1 ↔ z.im = 0 := by
  rw [_root_.RHTower.norm_xiDyadicLogPhase, Real.exp_eq_one_iff]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor <;> intro h
  · nlinarith
  · simp [h]

/-- **Centered dyadic phase/boundary-reflection universality law.** Under the Xi centered chart,
the paraorthogonal dyadic phase is unimodular exactly when functional-equation reflection fixes the
corresponding point. -/
theorem xiDyadicLogPhase_unit_iff_boundaryReflection_fixed (z : ℂ) :
    ‖_root_.RHTower.xiDyadicLogPhase z‖ = 1 ↔
      _root_.RHTower.lineReflection (1 / 2) (1 / 2 + z * Complex.I) =
        1 / 2 + z * Complex.I := by
  rw [norm_xiDyadicLogPhase_eq_one_iff]
  constructor
  · intro hz
    apply _root_.RHTower.lineReflection_eq_self
    simp [hz]
  · intro hfix
    have hre := congrArg Complex.re hfix
    rw [_root_.RHTower.lineReflection_re] at hre
    simp at hre
    linarith

/-- The same locus is detected by the boundary-normalized dyadic Bohr coordinate. Thus the OPUC
phase gate and scalar prime-boundary gate impose one condition after centering, despite their
different constructions. -/
theorem xiDyadicLogPhase_unit_iff_centeredBoundaryUnitNormalize (z : ℂ) :
    ‖_root_.RHTower.xiDyadicLogPhase z‖ = 1 ↔
      ‖boundaryUnitNormalize 2
        (((2 : ℝ) : ℂ) ^ (-(1 / 2 + z * Complex.I)))‖ = 1 := by
  rw [norm_xiDyadicLogPhase_eq_one_iff,
    diagonalBoundary_unit_norm_iff 2 (by norm_num) (1 / 2 + z * Complex.I)]
  constructor <;> intro h
  · simp [h]
  · have hre := h
    simp only [mul_re, I_re, I_im, mul_zero, mul_one, add_re] at hre
    norm_num at hre
    linarith

end

end GaloisForLFunctions
