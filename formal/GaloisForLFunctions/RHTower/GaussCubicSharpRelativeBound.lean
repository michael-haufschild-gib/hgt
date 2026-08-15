import GaloisForLFunctions.RHTower.GaussCubicSmoothShift

/-!
# Sharp cubic principal-moment bound

The cubic deviation is a single inverse-square quadratic-form perturbation.  Its perturbing vector
is exactly the sum of the smooth shifted-block error and the propagated relative error.  Therefore
the cubic scalar law has only one genuinely new convergence target.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions Filter Topology

noncomputable section

set_option maxHeartbeats 1000000 in
/-- Sharp cubic bound: smooth one-step error plus the single triple-defect propagated vector. -/
theorem norm_inner_one_gaussPrincipalStep_cube_sub_movingAmplitude_cube_le_sharp
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    ‖(inner ℂ (fourierLp 2 0)
          ((gaussPrincipalStepBlock hm k p hp i ^ 3) (fourierLp 2 0)) : ℂ) -
        inner ℂ (fourierLp 2 0)
          ((gaussMovingAmplitudeBlock hp
            ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ)) ^ 3)
              (fourierLp 2 0))‖ ≤
      (‖gaussCubicSmoothShiftErrorVector hm k p hp i‖ +
          ‖gaussCubicPropagatedRelativeErrorVector hm k p hp i‖) *
        (‖gaussCubicSmoothShiftErrorVector hm k p hp i‖ +
          ‖gaussCubicPropagatedRelativeErrorVector hm k p hp i‖ +
          2 * (Real.sqrt (p : ℝ) * (p : ℝ))) := by
  let R := gaussPrincipalStepBlock hm k p hp i
  let M := gaussMovingAmplitudeBlock hp
    ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
  let one : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) := fourierLp 2 0
  let v := M one
  let e := R one - v
  let u := gaussShiftedBlockOf hm k p i (gaussPrimeScaleBlock hp v)
  let t := gaussRotationBlock
    ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ)) (gaussPrimeScaleBlock hp v)
  let a := u - t
  let w := gaussShiftedBlockOf hm k p i (gaussPrimeScaleBlock hp e)
  let x := gaussShiftedBlockOf hm k p i (gaussPrimeScaleBlock hp (R one))
  have heq : e = gaussPrincipalRelativeErrorVector hm k p hp i := by rfl
  have haeq : a = gaussCubicSmoothShiftErrorVector hm k p hp i := by rfl
  have hweq : w = gaussCubicPropagatedRelativeErrorVector hm k p hp i := by
    simp only [w, gaussCubicPropagatedRelativeErrorVector]
    rw [heq]
  have hRone : R one = v + e := by simp [e]
  have hx : x = u + w := by
    simp only [x, u, w]
    rw [hRone, map_add]
    change gaussShiftedBlockOfCLM hm k p i
        (gaussPrimeScaleBlock hp v + gaussPrimeScaleBlock hp e) =
      gaussShiftedBlockOfCLM hm k p i (gaussPrimeScaleBlock hp v) +
        gaussShiftedBlockOfCLM hm k p i (gaussPrimeScaleBlock hp e)
    rw [map_add]
  have hu : u = t + a := by simp [a]
  have hxt : x - t = a + w := by
    rw [hx, hu]
    abel
  have ht : ‖t‖ ≤ Real.sqrt (p : ℝ) * (p : ℝ) := by
    have hv : ‖v‖ ≤ (p : ℝ) := by
      refine (M.le_opNorm one).trans ?_
      rw [show ‖one‖ = 1 by exact norm_fourierLp_eq_one 0, mul_one]
      exact norm_gaussMovingAmplitudeBlock_le hp _
    simp only [t]
    rw [gaussRotationBlock_eq_translation]
    rw [(gaussTranslationBlock
      ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))).norm_map]
    refine (gaussPrimeScaleBlock hp).le_opNorm v |>.trans ?_
    exact mul_le_mul (norm_gaussPrimeScaleBlock_le hp) hv (norm_nonneg _) (Real.sqrt_nonneg _)
  have hdiff : ‖x - t‖ ≤ ‖a‖ + ‖w‖ := by
    rw [hxt]
    exact norm_add_le _ _
  have hxnorm : ‖x‖ + ‖t‖ ≤ ‖a‖ + ‖w‖ + 2 * (Real.sqrt (p : ℝ) * (p : ℝ)) := by
    have htri : ‖x‖ ≤ ‖x - t‖ + ‖t‖ := by
      have h := norm_add_le (x - t) t
      rwa [sub_add_cancel] at h
    linarith
  have hquad := norm_inner_gaussPrimeScaleInvSq_sub_le hp x t
  have hdom : ‖(inner ℂ x (gaussPrimeScaleInvSqBlock hp x) : ℂ) -
        inner ℂ t (gaussPrimeScaleInvSqBlock hp t)‖ ≤
      (‖a‖ + ‖w‖) *
        (‖a‖ + ‖w‖ + 2 * (Real.sqrt (p : ℝ) * (p : ℝ))) := by
    refine hquad.trans ?_
    exact mul_le_mul hdiff hxnorm (by positivity) (by positivity)
  rw [inner_one_gaussPrincipalStep_cube hm k p hp i,
    inner_one_gaussMovingAmplitude_cube (m := m) p hp i]
  change ‖(inner ℂ (R one) (R (R one)) : ℂ) - inner ℂ v (M v)‖ ≤ _
  rw [inner_gaussPrincipalStepBlock_eq_sandwich hm k p hp i (R one),
    inner_gaussMovingAmplitudeBlock_eq_sandwich hp
      ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ)) v]
  change ‖(inner ℂ x (gaussPrimeScaleInvSqBlock hp x) : ℂ) -
      inner ℂ t (gaussPrimeScaleInvSqBlock hp t)‖ ≤ _
  simpa only [haeq, hweq] using hdom

end

end RHTower
