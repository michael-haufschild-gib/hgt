import GaloisForLFunctions.HTGeometry.LpReindexCompactDichotomy
import GaloisForLFunctions.HTGeometry.DiagonalEllTwoIndexed
import Mathlib.Analysis.Complex.Circle

/-!
# Concrete bilateral rotation operators

Translations and phase modulations on the native `ℓ²(ℤ)` carrier realize the exact Weyl multiplier.
Their ordered products retain the signed lattice area in their commutation law. This provides the
bounded operator input for applying the proven extended trace-cone ideal weight to rotation data.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open LpDiagonal

abbrev PaperRotationHilbert := LpTwo ℤ

/-- The actual complex rotation multiplier. -/
def paperRotationPhase (t : ℝ) : ℂ := Circle.exp t

@[simp] theorem paperRotationPhase_zero : paperRotationPhase 0 = 1 := by
  simp [paperRotationPhase]

theorem paperRotationPhase_add (s t : ℝ) :
    paperRotationPhase (s + t) = paperRotationPhase s * paperRotationPhase t := by
  simp only [paperRotationPhase, Circle.exp_add, Circle.coe_mul]

@[simp] theorem paperRotationPhase_norm (t : ℝ) : ‖paperRotationPhase t‖ = 1 :=
  Circle.norm_coe _

private def shiftIndex (a : ℤ) : ℤ ≃ ℤ where
  toFun n := n + a
  invFun n := n - a
  left_inv n := by dsimp; omega
  right_inv n := by dsimp; omega

/-- Bilateral integer translation, acting on the full Hilbert space. -/
def paperRotationShift (a : ℤ) : PaperRotationHilbert →L[ℂ] PaperRotationHilbert :=
  lpReindexCLM (shiftIndex a)

@[simp] theorem paperRotationShift_apply (a : ℤ) (v : PaperRotationHilbert) (n : ℤ) :
    (paperRotationShift a v : ℤ → ℂ) n = v (n - a) := rfl

@[simp] theorem paperRotationShift_norm (a : ℤ) (v : PaperRotationHilbert) :
    ‖paperRotationShift a v‖ = ‖v‖ := (lpReindex (shiftIndex a)).norm_map v

theorem paperRotationShift_comp (a b : ℤ) :
    paperRotationShift a ∘L paperRotationShift b = paperRotationShift (a + b) := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext n
  simp only [ContinuousLinearMap.comp_apply, paperRotationShift_apply]
  have hi : n - a - b = n - (a + b) := by omega
  rw [hi]

@[simp] theorem paperRotationShift_zero :
    paperRotationShift 0 = ContinuousLinearMap.id ℂ PaperRotationHilbert := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext n
  simp

/-- Modulation by `exp(i*t*n)` has unit modulus at every integer coordinate. -/
def paperRotationModulation (t : ℝ) : PaperRotationHilbert →L[ℂ] PaperRotationHilbert :=
  _root_.HTGeometry.ellTwoDiagonal (fun n : ℤ => paperRotationPhase (t * n))
    (fun _ => (paperRotationPhase_norm _).le)

@[simp] theorem paperRotationModulation_apply (t : ℝ) (v : PaperRotationHilbert) (n : ℤ) :
    (paperRotationModulation t v : ℤ → ℂ) n = paperRotationPhase (t * n) * v n := rfl

@[simp] theorem paperRotationModulation_norm (t : ℝ) (v : PaperRotationHilbert) :
    ‖paperRotationModulation t v‖ = ‖v‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [paperRotationModulation_apply, norm_mul, paperRotationPhase_norm, one_mul]

theorem paperRotationModulation_comp (s t : ℝ) :
    paperRotationModulation s ∘L paperRotationModulation t =
      paperRotationModulation (s + t) := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext n
  simp only [ContinuousLinearMap.comp_apply, paperRotationModulation_apply,
    add_mul, paperRotationPhase_add, mul_assoc]

@[simp] theorem paperRotationModulation_zero :
    paperRotationModulation 0 = ContinuousLinearMap.id ℂ PaperRotationHilbert := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext n
  simp

/-- The concrete Weyl relation, including its exact signed phase. -/
theorem paperRotationModulation_shift (t : ℝ) (a : ℤ) :
    paperRotationModulation t ∘L paperRotationShift a =
      paperRotationPhase (a * t) • (paperRotationShift a ∘L paperRotationModulation t) := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext n
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    paperRotationShift_apply, paperRotationModulation_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← paperRotationPhase_add]
  congr 2
  push_cast
  ring

/-- Ordered shift/modulation word; no finite support restriction is imposed. -/
def paperRotationWord (a : ℤ) (b : ℝ) : PaperRotationHilbert →L[ℂ] PaperRotationHilbert :=
  paperRotationModulation b ∘L paperRotationShift a

@[simp] theorem paperRotationWord_apply (a : ℤ) (b : ℝ)
    (v : PaperRotationHilbert) (n : ℤ) :
    (paperRotationWord a b v : ℤ → ℂ) n = paperRotationPhase (b * n) * v (n - a) := rfl

@[simp] theorem paperRotationWord_norm (a : ℤ) (b : ℝ) (v : PaperRotationHilbert) :
    ‖paperRotationWord a b v‖ = ‖v‖ := by
  simp only [paperRotationWord, ContinuousLinearMap.comp_apply,
    paperRotationModulation_norm, paperRotationShift_norm]

/-- The cocycle records the order of the two translations. -/
theorem paperRotationWord_comp (a c : ℤ) (b d : ℝ) :
    paperRotationWord a b ∘L paperRotationWord c d =
      paperRotationPhase (-(a : ℝ) * d) • paperRotationWord (a + c) (b + d) := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext n
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    paperRotationWord_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    ← mul_assoc, ← paperRotationPhase_add]
  have hi : n - a - c = n - (a + c) := by omega
  rw [hi]
  congr 2
  push_cast
  ring

/-- Commutation reads the signed area, rather than either coordinate separately. -/
theorem paperRotationWord_commutation (a c : ℤ) (b d : ℝ) :
    paperRotationWord a b ∘L paperRotationWord c d =
      paperRotationPhase (c * b - a * d) •
        (paperRotationWord c d ∘L paperRotationWord a b) := by
  rw [paperRotationWord_comp, paperRotationWord_comp, smul_smul,
    ← paperRotationPhase_add, add_comm c a, add_comm d b]
  congr 1
  congr 1
  ring

/-- A concrete inverse retaining the original order of the two operations. -/
def paperRotationWordUndo (a : ℤ) (b : ℝ) :
    PaperRotationHilbert →L[ℂ] PaperRotationHilbert :=
  paperRotationShift (-a) ∘L paperRotationModulation (-b)

theorem paperRotationWordUndo_left (a : ℤ) (b : ℝ) :
    paperRotationWordUndo a b ∘L paperRotationWord a b =
      ContinuousLinearMap.id ℂ PaperRotationHilbert := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext n
  simp only [paperRotationWordUndo, paperRotationWord, ContinuousLinearMap.comp_apply,
    paperRotationShift_apply, paperRotationModulation_apply, ← mul_assoc,
    ← paperRotationPhase_add]
  have hi : n - -a - a = n := by omega
  rw [hi]
  simp

theorem paperRotationWordUndo_right (a : ℤ) (b : ℝ) :
    paperRotationWord a b ∘L paperRotationWordUndo a b =
      ContinuousLinearMap.id ℂ PaperRotationHilbert := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext n
  simp only [paperRotationWordUndo, paperRotationWord, ContinuousLinearMap.comp_apply,
    paperRotationShift_apply, paperRotationModulation_apply, ← mul_assoc,
    ← paperRotationPhase_add]
  have hi : n - a - -a = n := by omega
  rw [hi]
  simp

end

end GaloisForLFunctions.HTGeometry
