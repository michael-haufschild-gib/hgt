import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailShift
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailFunctionalGrowth

/-!
# Chen--Gupta--Li Lemma 6.2: far-left tail point bound

This multiplies CGL's exact far-line Mellin, length, functional, Euler, and
complementary-Dirichlet estimates.  It is the pointwise analytic input for the
quantitative `I₂` remainder in the source proof.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- On the high part of CGL's far-left line, the literal complementary tail
has the exact `2k + 1/2` functional-equation growth, with every other factor
absorbed into one closed nonnegative budget. -/
theorem cglLemma62_farTail_high_point_bound
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ)
    (M : CGLLemma62TailCutoff) (d : CGLLemma62TailContourDepth) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 2 ≤ |v - t| →
      ‖cglLemma62FarTailIntegrand w N B t M.value d v‖ ≤
        C * (1 + |v - t|) ^ (2 * (d.value : ℝ) + 1 / 2) := by
  rcases cglLemma62_primitiveFunctionalFactor_tail_high_bound B.primitive d with
    ⟨A, hA, hA_bound⟩
  let K := cglLemma62TailMellinUniformBudget w d 0
  let E := cglLemma62TailEulerCorrectionBudget B d
  let D : ℝ := (M.value : ℝ) ^ (-2 * (d.value : ℝ)) / (2 * (d.value : ℝ))
  have hK : 0 ≤ K := by
    dsimp [K, cglLemma62TailMellinUniformBudget]
    apply integral_nonneg
    intro u
    unfold deningerMeyerBoundedMellinMajorant
    apply Finset.sum_nonneg
    intro j hj
    positivity
  have hE : 0 ≤ E := by
    let z : CGLLemma62TailEulerPoint d := ⟨(-2 * (d.value : ℝ) : ℂ), by simp⟩
    exact le_trans (norm_nonneg _) (cglLemma62EulerCorrectionAt_tail_norm_le B d z)
  have hD : 0 ≤ D := by
    dsimp [D]
    have hden : 0 < 2 * (d.value : ℝ) := by
      have : 0 < (d.value : ℝ) := by exact_mod_cast d.positive
      positivity
    positivity
  refine ⟨K * A * E * D, by positivity, ?_⟩
  intro v hv
  let p : CGLLemma62TailMellinPoint d := {
    x := -2 * (d.value : ℝ)
    y := v
    lower := by rfl
    upper := by
      have hd : (1 : ℝ) ≤ d.value := by exact_mod_cast d.positive
      linarith }
  let z : CGLLemma62TailFunctionalHighPoint d := {
    value := cglLemma62FarLeftPoint d v - (t : ℂ) * I
    real_eq := by
      unfold cglLemma62FarLeftPoint
      simp
    high := by
      unfold cglLemma62FarLeftPoint
      simpa using hv }
  let e : CGLLemma62TailEulerPoint d := {
    value := cglLemma62FarLeftPoint d v - (t : ℂ) * I
    real_eq := by
      unfold cglLemma62FarLeftPoint
      simp }
  have hH0 := cglLemma62_mellinTransform_tail_uniformAllOrderDecay w d 0 p
  have hH : ‖cglLemma62MellinTransform w (cglLemma62FarLeftPoint d v)‖ ≤ K := by
    simpa [K, p, cglLemma62FarLeftPoint] using hH0
  have hN0 := cglLemma62_lengthPower_tail_norm_le_one N d p
  have hN : ‖(N.value : ℂ) ^ (cglLemma62FarLeftPoint d v)‖ ≤ 1 := by
    simpa [p, cglLemma62FarLeftPoint] using hN0
  have hG0 := hA_bound z
  have hG : ‖cglLemma62PrimitiveFunctionalFactor B.primitive
      (cglLemma62FarLeftPoint d v - (t : ℂ) * I)‖ ≤
      A * (1 + |v - t|) ^ (2 * (d.value : ℝ) + 1 / 2) := by
    simpa [z, cglLemma62FarLeftPoint] using hG0
  have hE0 := cglLemma62EulerCorrectionAt_tail_norm_le B d e
  have hEcorr : ‖cglLemma62EulerCorrectionAt B
      (cglLemma62FarLeftPoint d v - (t : ℂ) * I)‖ ≤ E := by
    simpa [E, e] using hE0
  have htail0 := cglLemma62_far_dirichletTail_norm_le B t d M v
  have htail : ‖cglLemma62DirichletTail B.character⁻¹ M.value
      (cglLemma62FarRightPointAC t d v)‖ ≤ D := by
    simpa [D] using htail0
  unfold cglLemma62FarTailIntegrand
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  calc
    ‖cglLemma62MellinTransform w (cglLemma62FarLeftPoint d v)‖ *
        ‖(N.value : ℂ) ^ (cglLemma62FarLeftPoint d v)‖ *
          ‖cglLemma62PrimitiveFunctionalFactor B.primitive
            (cglLemma62FarLeftPoint d v - (t : ℂ) * I)‖ *
            ‖cglLemma62EulerCorrectionAt B
              (cglLemma62FarLeftPoint d v - (t : ℂ) * I)‖ *
              ‖cglLemma62DirichletTail B.character⁻¹ M.value
                (cglLemma62FarRightPointAC t d v)‖ ≤
        K * 1 * (A * (1 + |v - t|) ^ (2 * (d.value : ℝ) + 1 / 2)) * E * D := by
          gcongr
    _ = (K * A * E * D) * (1 + |v - t|) ^ (2 * (d.value : ℝ) + 1 / 2) := by ring

end

end RHTower
