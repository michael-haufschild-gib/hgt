import GaloisForLFunctions.RHTower.GaussCubicRelativeErrorReduction

namespace RHTower

open RCLike
open MeasureTheory GaloisForLFunctions Filter Topology

noncomputable section

/-- Norm control of the hard cubic quadratic-error term. -/
theorem norm_inner_gaussPrincipalRelativeError_principalStep_le
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    ‖(inner ℂ (gaussPrincipalRelativeErrorVector hm k p hp i)
        (gaussPrincipalStepBlock hm k p hp i
          (gaussPrincipalRelativeErrorVector hm k p hp i)) : ℂ)‖ ≤
      ‖gaussCubicPropagatedRelativeErrorVector hm k p hp i‖ ^ (2 : ℕ) := by
  rw [inner_gaussPrincipalRelativeError_principalStep_eq hm k p hp i]
  set v := gaussCubicPropagatedRelativeErrorVector hm k p hp i
  calc
    ‖(inner ℂ v (gaussPrimeScaleInvSqBlock hp v) : ℂ)‖
        ≤ ‖v‖ * ‖gaussPrimeScaleInvSqBlock hp v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * ‖v‖ := by
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (gaussPrimeScaleInvSqBlock hp).le_opNorm v |>.trans ?_
      exact mul_le_of_le_one_left (norm_nonneg v) (norm_gaussPrimeScaleInvSqBlock_le hp)
    _ = ‖v‖ ^ (2 : ℕ) := by ring

/-- Literal moving-amplitude image of the cyclic constant. -/
def gaussMovingAmplitudeOneVector {m : ℕ} (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  gaussMovingAmplitudeBlock hp
    ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ)) (fourierLp 2 0)

/-- Relative principal-step error on the smooth moving-amplitude vector. -/
def gaussMovingAmplitudeStepErrorVector {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  gaussPrincipalStepBlock hm k p hp i (gaussMovingAmplitudeOneVector (m := m) p hp i) -
    gaussMovingAmplitudeBlock hp
      ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
      (gaussMovingAmplitudeOneVector (m := m) p hp i)

/-- Cubic fold for the moving-amplitude model. -/
theorem inner_one_gaussMovingAmplitude_cube {m : ℕ} (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    (inner ℂ (fourierLp 2 0)
        ((gaussMovingAmplitudeBlock hp
          ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ)) ^ (3 : ℕ)) (fourierLp 2 0)) : ℂ) =
      inner ℂ (gaussMovingAmplitudeOneVector (m := m) p hp i)
        (gaussMovingAmplitudeBlock hp
          ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
          (gaussMovingAmplitudeOneVector (m := m) p hp i)) := by
  let M := gaussMovingAmplitudeBlock hp
    ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
  have happ : (M ^ (3 : ℕ)) (fourierLp 2 0) = M (M (M (fourierLp 2 0))) := by
    rw [show (3 : ℕ) = 1 + 1 + 1 by omega, pow_succ', pow_succ', pow_one]
    rfl
  change (inner ℂ (fourierLp 2 0) ((M ^ (3 : ℕ)) (fourierLp 2 0)) : ℂ) =
    inner ℂ (M (fourierLp 2 0)) (M (M (fourierLp 2 0)))
  rw [happ, ← gaussMovingAmplitudeBlock_inner hp]

set_option maxHeartbeats 1000000 in
/-- Exact cubic principal-moment deviation bound.  It reduces the unresolved `m=3` scalar law to
the smooth-input relative error and the one propagated relative-error vector. -/
theorem norm_inner_one_gaussPrincipalStep_cube_sub_movingAmplitude_cube_le
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    ‖(inner ℂ (fourierLp 2 0)
          ((gaussPrincipalStepBlock hm k p hp i ^ (3 : ℕ)) (fourierLp 2 0)) : ℂ) -
        inner ℂ (fourierLp 2 0)
          ((gaussMovingAmplitudeBlock hp
            ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ)) ^ (3 : ℕ))
              (fourierLp 2 0))‖ ≤
      (p : ℝ) * ‖gaussMovingAmplitudeStepErrorVector hm k p hp i‖ +
        2 * ‖gaussPrincipalRelativeErrorVector hm k p hp i‖ *
          ((p : ℝ) ^ (2 : ℕ) + ‖gaussMovingAmplitudeStepErrorVector hm k p hp i‖) +
        ‖gaussCubicPropagatedRelativeErrorVector hm k p hp i‖ ^ (2 : ℕ) := by
  let R := gaussPrincipalStepBlock hm k p hp i
  let M := gaussMovingAmplitudeBlock hp
    ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
  let one : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) := fourierLp 2 0
  let v := M one
  let e := R one - v
  let d := R v - M v
  have hfoldR := inner_one_gaussPrincipalStep_cube hm k p hp i
  have hfoldM := inner_one_gaussMovingAmplitude_cube (m := m) p hp i
  have hsplit : (inner ℂ (R one) (R (R one)) : ℂ) - inner ℂ v (M v) =
      inner ℂ v d + inner ℂ v (R e) + inner ℂ e (R v) + inner ℂ e (R e) := by
    have hone : R one = v + e := by simp [e]
    have hd : R v = M v + d := by simp [d]
    rw [hone, map_add, inner_add_left, inner_add_right, hd, inner_add_right, inner_add_right]
    abel
  rw [hfoldR, hfoldM]
  change ‖(inner ℂ (R one) (R (R one)) : ℂ) - inner ℂ v (M v)‖ ≤
    (p : ℝ) * ‖d‖ + 2 * ‖e‖ * ((p : ℝ) ^ (2 : ℕ) + ‖d‖) +
      ‖gaussCubicPropagatedRelativeErrorVector hm k p hp i‖ ^ (2 : ℕ)
  rw [hsplit]
  have heq : e = gaussPrincipalRelativeErrorVector hm k p hp i := by
    rfl
  have hq : ‖(inner ℂ e (R e) : ℂ)‖ ≤
      ‖gaussCubicPropagatedRelativeErrorVector hm k p hp i‖ ^ (2 : ℕ) := by
    rw [heq]
    simpa only [R] using
      norm_inner_gaussPrincipalRelativeError_principalStep_le hm k p hp i
  have hv : ‖v‖ ≤ (p : ℝ) := by
    refine (M.le_opNorm one).trans ?_
    rw [show ‖one‖ = 1 by exact norm_fourierLp_eq_one 0, mul_one]
    exact norm_gaussMovingAmplitudeBlock_le hp _
  have hMv : ‖M v‖ ≤ (p : ℝ) ^ (2 : ℕ) := by
    refine (M.le_opNorm v).trans ?_
    calc ‖M‖ * ‖v‖ ≤ (p : ℝ) * (p : ℝ) :=
          mul_le_mul (norm_gaussMovingAmplitudeBlock_le hp _) hv (norm_nonneg _) (by positivity)
      _ = (p : ℝ) ^ (2 : ℕ) := by ring
  have hRv : ‖R v‖ ≤ (p : ℝ) ^ (2 : ℕ) + ‖d‖ := by
    have hadd : R v = M v + d := by simp [d]
    rw [hadd]
    exact (norm_add_le _ _).trans (add_le_add hMv le_rfl)
  have h1 : ‖(inner ℂ v d : ℂ)‖ ≤ (p : ℝ) * ‖d‖ :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hv (norm_nonneg _))
  have hcross1 : ‖(inner ℂ v (R e) : ℂ)‖ ≤ ‖e‖ * ‖R v‖ := by
    calc
      ‖(inner ℂ v (R e) : ℂ)‖ = ‖(inner ℂ (R e) v : ℂ)‖ := norm_inner_symm _ _
      _ = ‖(inner ℂ e (R v) : ℂ)‖ := by
        change ‖(inner ℂ (gaussPrincipalStepBlock hm k p hp i e) v : ℂ)‖ =
          ‖(inner ℂ e (gaussPrincipalStepBlock hm k p hp i v) : ℂ)‖
        rw [gaussPrincipalStepBlock_inner hm k p hp i]
      _ ≤ ‖e‖ * ‖R v‖ := norm_inner_le_norm _ _
  have hcross2 : ‖(inner ℂ e (R v) : ℂ)‖ ≤ ‖e‖ * ‖R v‖ :=
    norm_inner_le_norm _ _
  have hcross : ‖(inner ℂ v (R e) : ℂ)‖ + ‖(inner ℂ e (R v) : ℂ)‖ ≤
      2 * ‖e‖ * ((p : ℝ) ^ (2 : ℕ) + ‖d‖) := by
    have he0 := norm_nonneg e
    have hb := mul_le_mul_of_nonneg_left hRv he0
    nlinarith
  calc
    ‖(inner ℂ v d + inner ℂ v (R e) + inner ℂ e (R v) + inner ℂ e (R e) : ℂ)‖
        ≤ ‖(inner ℂ v d + inner ℂ v (R e) + inner ℂ e (R v) : ℂ)‖ +
          ‖(inner ℂ e (R e) : ℂ)‖ := norm_add_le _ _
    _ ≤ (‖(inner ℂ v d + inner ℂ v (R e) : ℂ)‖ +
          ‖(inner ℂ e (R v) : ℂ)‖) + ‖(inner ℂ e (R e) : ℂ)‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ((‖(inner ℂ v d : ℂ)‖ + ‖(inner ℂ v (R e) : ℂ)‖) +
          ‖(inner ℂ e (R v) : ℂ)‖) + ‖(inner ℂ e (R e) : ℂ)‖ :=
      add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ = (‖(inner ℂ v d : ℂ)‖ +
          (‖(inner ℂ v (R e) : ℂ)‖ + ‖(inner ℂ e (R v) : ℂ)‖)) +
          ‖(inner ℂ e (R e) : ℂ)‖ := by ring
    _ ≤ (p : ℝ) * ‖d‖ + 2 * ‖e‖ * ((p : ℝ) ^ (2 : ℕ) + ‖d‖) +
          ‖gaussCubicPropagatedRelativeErrorVector hm k p hp i‖ ^ (2 : ℕ) :=
      add_le_add (add_le_add h1 hcross) hq

end

end RHTower
