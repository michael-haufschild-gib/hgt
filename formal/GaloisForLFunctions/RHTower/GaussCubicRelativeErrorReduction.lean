import GaloisForLFunctions.RHTower.GaussRelativeOneStep
import GaloisForLFunctions.RHTower.GaussRatioPowerMovingTranslation
import GaloisForLFunctions.RHTower.GaussTripleDefectCap

/-!
# Exact cubic relative-error reduction

The cubic principal moment does not require full vector convergence of `R² 1`.  Self-adjointness
reduces it to the quadratic form of `R` at `R1`.  After writing `R1 = M1 + e`, the genuinely new
term is `⟨e, R e⟩`.  The factorization `R = B S B⁻² S* B` reduces this term exactly to the
inverse-square quadratic form of the single propagated vector `S*(B e)`, hence to its squared norm.
This isolates the sole triple-defect quantity that the `m = 3` arithmetic must kill.
-/

namespace RHTower

open RCLike
open MeasureTheory GaloisForLFunctions Filter Topology

noncomputable section

/-- Literal relative error of the principal step on the cyclic constant vector. -/
def gaussPrincipalRelativeErrorVector {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  gaussPrincipalStepBlock hm k p hp i (fourierLp 2 0) -
    gaussMovingAmplitudeBlock hp
      ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ)) (fourierLp 2 0)

/-- The single additional normalized conjugate block applied to the relative error.  Its norm is
the exact depth-two propagation target for the cubic moment. -/
def gaussCubicPropagatedRelativeErrorVector {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  gaussShiftedBlockOf hm k p i
    (gaussPrimeScaleBlock hp (gaussPrincipalRelativeErrorVector hm k p hp i))

/-- Exact three-vector decomposition of the literal relative error. -/
theorem gaussPrincipalRelativeErrorVector_eq_three_defects
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    gaussPrincipalRelativeErrorVector hm k p hp i =
      gaussPrimeScaleBlock hp
        ((gaussShiftedBlockDiag hm k p i
            (gaussPrimeScaleInvSqBlock hp
              (gaussRotationBlock
                ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
                  (gaussPrimeScaleBlock hp (fourierLp 2 0)))) -
          gaussRotationBlockInv
            ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
            (gaussPrimeScaleInvSqBlock hp
              (gaussRotationBlock
                ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
                  (gaussPrimeScaleBlock hp (fourierLp 2 0))))) +
        (gaussDoubleDefectVector hm k p hp i +
          gaussRotationBlockInv
            ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
            (gaussPrimeScaleInvSqBlock hp
              (gaussShiftedBlockOf hm k p i
                  (gaussPrimeScaleBlock hp (fourierLp 2 0)) -
                gaussRotationBlock
                  ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
                  (gaussPrimeScaleBlock hp (fourierLp 2 0)))))) := by
  set δ : AddCircle (1 : ℝ) :=
    ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ)) with hδ
  set b : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussPrimeScaleBlock hp (fourierLp 2 0) with hb
  have hR : gaussPrincipalStepBlock hm k p hp i (fourierLp 2 0) =
      gaussPrimeScaleBlock hp
        (gaussShiftedBlockDiag hm k p i
          (gaussPrimeScaleInvSqBlock hp (gaussShiftedBlockOf hm k p i b))) := by
    rw [gaussPrincipalStepBlock_apply, hb]
  have hM : gaussMovingAmplitudeBlock hp δ (fourierLp 2 0) =
      gaussPrimeScaleBlock hp
        (gaussRotationBlockInv δ
          (gaussPrimeScaleInvSqBlock hp (gaussRotationBlock δ b))) := by
    rw [← gaussPrimeScaleBlock_translate_invSq_translate hp δ (fourierLp 2 0),
      gaussRotationBlock_eq_translation, gaussRotationBlockInv_eq_translation, hb]
  rw [gaussPrincipalRelativeErrorVector, ← hδ, hR, hM, ← map_sub]
  congr 1
  rw [gaussDoubleDefectVector, ← hδ, ← hb]
  have hadd : gaussShiftedBlockDiag hm k p i
      (gaussPrimeScaleInvSqBlock hp (gaussShiftedBlockOf hm k p i b)) =
      gaussShiftedBlockDiag hm k p i
          (gaussPrimeScaleInvSqBlock hp
            (gaussShiftedBlockOf hm k p i b - gaussRotationBlock δ b)) +
        gaussShiftedBlockDiag hm k p i
          (gaussPrimeScaleInvSqBlock hp (gaussRotationBlock δ b)) := by
    have h := gaussShiftedBlockDiag_sub hm k p i
      (gaussPrimeScaleInvSqBlock hp (gaussShiftedBlockOf hm k p i b))
      (gaussPrimeScaleInvSqBlock hp (gaussRotationBlock δ b))
    rw [← map_sub] at h
    rw [sub_eq_iff_eq_add] at h
    exact h
  rw [hadd]
  abel

/-- Cubic moment fold through self-adjointness. -/
theorem inner_one_gaussPrincipalStep_cube
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    (inner ℂ (fourierLp 2 0)
        ((gaussPrincipalStepBlock hm k p hp i ^ 3) (fourierLp 2 0)) : ℂ) =
      inner ℂ
        (gaussPrincipalStepBlock hm k p hp i (fourierLp 2 0))
        (gaussPrincipalStepBlock hm k p hp i
          (gaussPrincipalStepBlock hm k p hp i (fourierLp 2 0))) := by
  have happ : (gaussPrincipalStepBlock hm k p hp i ^ 3) (fourierLp 2 0) =
      gaussPrincipalStepBlock hm k p hp i
        (gaussPrincipalStepBlock hm k p hp i
          (gaussPrincipalStepBlock hm k p hp i (fourierLp 2 0))) := by
    rw [show (3 : ℕ) = 1 + 1 + 1 by omega, pow_succ', pow_succ', pow_one]
    rfl
  rw [happ, ← gaussPrincipalStepBlock_inner hm k p hp i]

/-- Exact factorization of the quadratic relative-error term through the propagated vector. -/
theorem inner_gaussPrincipalRelativeError_principalStep_eq
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    (inner ℂ (gaussPrincipalRelativeErrorVector hm k p hp i)
        (gaussPrincipalStepBlock hm k p hp i
          (gaussPrincipalRelativeErrorVector hm k p hp i)) : ℂ) =
      inner ℂ (gaussCubicPropagatedRelativeErrorVector hm k p hp i)
        (gaussPrimeScaleInvSqBlock hp
          (gaussCubicPropagatedRelativeErrorVector hm k p hp i)) := by
  rw [gaussPrincipalStepBlock_apply]
  rw [← gaussPrimeScaleBlock_inner hp]
  rw [← gaussShiftedBlockOf_inner hm k p i]
  rfl

/-- The hard cubic quadratic-error term is bounded by the propagated-error norm squared. -/
theorem re_inner_gaussPrincipalRelativeError_principalStep_le
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    re (inner ℂ (gaussPrincipalRelativeErrorVector hm k p hp i)
        (gaussPrincipalStepBlock hm k p hp i
          (gaussPrincipalRelativeErrorVector hm k p hp i))) ≤
      ‖gaussCubicPropagatedRelativeErrorVector hm k p hp i‖ ^ 2 := by
  rw [inner_gaussPrincipalRelativeError_principalStep_eq hm k p hp i]
  set v := gaussCubicPropagatedRelativeErrorVector hm k p hp i
  calc
    re (inner ℂ v (gaussPrimeScaleInvSqBlock hp v))
        ≤ ‖inner ℂ v (gaussPrimeScaleInvSqBlock hp v)‖ := Complex.re_le_norm _
    _ ≤ ‖v‖ * ‖gaussPrimeScaleInvSqBlock hp v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * ‖v‖ := by
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (gaussPrimeScaleInvSqBlock hp).le_opNorm v |>.trans ?_
      exact mul_le_of_le_one_left (norm_nonneg v) (norm_gaussPrimeScaleInvSqBlock_le hp)
    _ = ‖v‖ ^ 2 := by ring

end

end RHTower
