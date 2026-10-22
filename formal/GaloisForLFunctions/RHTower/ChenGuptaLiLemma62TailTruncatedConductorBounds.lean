import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailFarConductorBounds

/-!
# Chen--Gupta--Li Lemma 6.2: conductor-sensitive truncated far-left tail

This carries CGL's `q / q*` Euler cancellation through the literal finite
ordinate window used for the source's `I₂` term.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

private theorem cglLemma62_conductorTailWindow_abs_le
    {t : ℝ} (U : CGLLemma62TailTruncationWindow t)
    {v : ℝ} (hv : v ∈ Set.uIoc (-U.radius) U.radius) : |v| ≤ U.radius :=
  cglLemma62_tailWindow_abs_le U hv

private theorem cglLemma62_conductorTailWindow_high
    {t : ℝ} (U : CGLLemma62TailTruncationWindow t)
    {v : ℝ} (hv : v ∈ Set.uIoc (-U.radius) U.radius) : 2 ≤ |v - t| :=
  cglLemma62_tailWindow_high U hv

/-- The literal far-left complementary tail integrated over a CGL truncation
window, with the finite Euler correction restricted to primes of `q / q*`. -/
theorem cglLemma62_farTail_truncated_conductor_integral_bound
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ)
    (M : CGLLemma62TailCutoff) (d : CGLLemma62TailContourDepth)
    (U : CGLLemma62TailTruncationWindow t) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖∫ v : ℝ in -U.radius..U.radius,
        cglLemma62FarTailIntegrand w N B t M.value d v‖ ≤
        C * (1 + |t| + U.radius) ^ (2 * (d.value : ℝ) + 1 / 2) * (2 * U.radius) :=
  cglLemma62_farTail_truncated_integral_bound w N B t M d U

/-- The conductor-sensitive CGL `I₂` window estimate with the Euler and
complementary-tail scales left explicit for the source exponent arithmetic. -/
theorem cglLemma62_farTail_truncated_conductor_factorized_integral_bound
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ)
    (M : CGLLemma62TailCutoff) (d : CGLLemma62TailContourDepth)
    (U : CGLLemma62TailTruncationWindow t) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖∫ v : ℝ in -U.radius..U.radius,
        cglLemma62FarTailIntegrand w N B t M.value d v‖ ≤
        C * (N.value : ℝ) ^ (-2 * (d.value : ℝ)) *
          (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
          cglLemma62TailEulerConductorBudget B d *
          ((M.value : ℝ) ^ (-2 * (d.value : ℝ)) / (2 * (d.value : ℝ))) *
          (1 + |t| + U.radius) ^ (2 * (d.value : ℝ) + 1 / 2) *
          (2 * U.radius) := by
  rcases cglLemma62_farTail_high_conductor_factorized_point_bound w N B t M d with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  let lengthScale : ℝ := (N.value : ℝ) ^ (-2 * (d.value : ℝ))
  let conductorScale : ℝ :=
    (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ))
  let eulerScale := cglLemma62TailEulerConductorBudget B d
  let tailScale : ℝ := (M.value : ℝ) ^ (-2 * (d.value : ℝ)) / (2 * (d.value : ℝ))
  have hlengthScale : 0 ≤ lengthScale := by
    dsimp [lengthScale]
    positivity
  have hconductorScale : 0 ≤ conductorScale := by
    dsimp [conductorScale]
    positivity
  have heulerScale : 0 ≤ eulerScale := by
    let z : CGLLemma62TailEulerPoint d := ⟨(-2 * (d.value : ℝ) : ℂ), by simp⟩
    exact le_trans (norm_nonneg _)
      (cglLemma62EulerCorrectionAt_far_conductorBudget_norm_le B d z)
  have htailScale : 0 ≤ tailScale := by
    dsimp [tailScale]
    have hden : 0 < 2 * (d.value : ℝ) := by
      have : 0 < (d.value : ℝ) := by exact_mod_cast d.positive
      positivity
    positivity
  have hscale : 0 ≤ C * lengthScale * conductorScale * eulerScale * tailScale := by
    positivity
  have hpoint : ∀ v ∈ Set.uIoc (-U.radius) U.radius,
      ‖cglLemma62FarTailIntegrand w N B t M.value d v‖ ≤
        C * lengthScale * conductorScale * eulerScale * tailScale * (1 + |t| + U.radius) ^
          (2 * (d.value : ℝ) + 1 / 2) := by
    intro v hv
    have hhigh := cglLemma62_conductorTailWindow_high U hv
    have hvabs := cglLemma62_conductorTailWindow_abs_le U hv
    have hbase : 1 + |v - t| ≤ 1 + |t| + U.radius := by
      have htri : |v - t| ≤ |v| + |t| := by
        calc
          |v - t| = |v + (-t)| := by ring_nf
          _ ≤ |v| + |-t| := abs_add_le _ _
          _ = _ := by rw [abs_neg]
      linarith
    have hpow : (1 + |v - t|) ^ (2 * (d.value : ℝ) + 1 / 2) ≤
        (1 + |t| + U.radius) ^ (2 * (d.value : ℝ) + 1 / 2) := by
      apply Real.rpow_le_rpow
      · positivity
      · exact hbase
      · positivity
    have hsource := hbound v hhigh
    have hsource' : ‖cglLemma62FarTailIntegrand w N B t M.value d v‖ ≤
        C * lengthScale * conductorScale * eulerScale * tailScale *
          (1 + |v - t|) ^ (2 * (d.value : ℝ) + 1 / 2) := by
      simpa [lengthScale, conductorScale, eulerScale, tailScale] using hsource
    exact hsource'.trans (mul_le_mul_of_nonneg_left hpow hscale)
  calc
    ‖∫ v : ℝ in -U.radius..U.radius,
        cglLemma62FarTailIntegrand w N B t M.value d v‖ ≤
        (C * lengthScale * conductorScale * eulerScale * tailScale * (1 + |t| + U.radius) ^
          (2 * (d.value : ℝ) + 1 / 2)) * |U.radius - (-U.radius)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = C * lengthScale * conductorScale * eulerScale * tailScale * (1 + |t| + U.radius) ^
        (2 * (d.value : ℝ) + 1 / 2) * (2 * U.radius) := by
      have hwidth : |U.radius - (-U.radius)| = 2 * U.radius := by
        rw [show U.radius - (-U.radius) = 2 * U.radius by ring_nf,
          abs_of_nonneg (mul_nonneg (by norm_num) U.radius_nonneg)]
      rw [hwidth]

end

end RHTower
