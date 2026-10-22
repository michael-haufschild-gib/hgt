import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailEulerSourceBounds
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailFunctionalGrowth

/-!
# Chen--Gupta--Li Lemma 6.2: conductor-sensitive far-left tail bound

This is the source-faithful refinement of the far-left five-factor bound: the
finite Euler correction is controlled by the imprimitive quotient `q / q*`.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- On the high part of CGL's far-left line, the literal complementary tail
has the exact `2k + 1/2` functional-equation growth with the finite Euler
budget restricted to primes of the imprimitive conductor quotient. -/
theorem cglLemma62_farTail_high_conductor_point_bound
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ)
    (M : CGLLemma62TailCutoff) (d : CGLLemma62TailContourDepth) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 2 ≤ |v - t| →
      ‖cglLemma62FarTailIntegrand w N B t M.value d v‖ ≤
        C * (1 + |v - t|) ^ (2 * (d.value : ℝ) + 1 / 2) :=
  cglLemma62_farTail_high_point_bound w N B t M d

/-- The same far-left estimate with the conductor-sensitive Euler and
Dirichlet-tail scales left visible for CGL's source-exponent arithmetic. -/
theorem cglLemma62_farTail_high_conductor_factorized_point_bound
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ)
    (M : CGLLemma62TailCutoff) (d : CGLLemma62TailContourDepth) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 2 ≤ |v - t| →
      ‖cglLemma62FarTailIntegrand w N B t M.value d v‖ ≤
        C * (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
          (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
          cglLemma62TailEulerConductorBudget B d *
          ((M.value : ℝ) ^ (-2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
          (1 + |v - t|) ^ (2 * (d.value : ℝ) + 1 / 2) := by
  rcases cglLemma62_primitiveFunctionalFactor_tail_high_factorized_bound B.primitive d with
    ⟨A, hA, hA_bound⟩
  let K := cglLemma62TailMellinUniformBudget w d 0
  let E := cglLemma62TailEulerConductorBudget B d
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
    exact le_trans (norm_nonneg _)
      (cglLemma62EulerCorrectionAt_far_conductorBudget_norm_le B d z)
  have hD : 0 ≤ D := by
    dsimp [D]
    have hden : 0 < 2 * (d.value : ℝ) := by
      have : 0 < (d.value : ℝ) := by exact_mod_cast d.positive
      positivity
    positivity
  refine ⟨K * A, mul_nonneg hK hA, ?_⟩
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
  have hN := cglLemma62_lengthPower_farLeft_norm_eq N d v
  have hG0 := hA_bound z
  have hG : ‖cglLemma62PrimitiveFunctionalFactor B.primitive
      (cglLemma62FarLeftPoint d v - (t : ℂ) * I)‖ ≤
      A * (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
        (1 + |v - t|) ^ (2 * (d.value : ℝ) + 1 / 2) := by
    simpa [z, cglLemma62FarLeftPoint] using hG0
  have hE0 := cglLemma62EulerCorrectionAt_far_conductorBudget_norm_le B d e
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
        K * (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
          (A * (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
            (1 + |v - t|) ^ (2 * (d.value : ℝ) + 1 / 2)) * E * D := by
          rw [hN]
          gcongr
    _ = (K * A) * (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
        (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) * E * D *
        (1 + |v - t|) ^
        (2 * (d.value : ℝ) + 1 / 2) := by ring

end

end RHTower
