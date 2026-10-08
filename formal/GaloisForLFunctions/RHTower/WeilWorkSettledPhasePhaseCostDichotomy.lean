import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCenteredPhaseCost

/-!
# Source rigidity or persistent linear canonical phase cost

The existing coefficient recovery obstruction for centered energy transfers
to the actual canonical phase cost with a sublinear error. This alternative
has only original full positivity as its source premise; eliminating the
second branch is still required for settlement.
-/

open Complex Filter Topology
noncomputable section
namespace RHTower.WeilWorkSettledPhase
open WeilSpectral
variable {lam : ℕ → ℝ}

/-- Nonrigidity cannot have arbitrarily late Gaussian phase costs of size `o(T)`. -/
theorem rigidity_or_gaussianPhaseCost_lower (hW : WeilPositiveFull lam) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ T : ℝ in atTop, κ * T ≤ quantizationGaussianDefect hW T := by
  rcases quantization_rigidity_or_centeredGaussianEnergy_lower hW with hr | ⟨κ, hκ, he⟩
  · exact Or.inl hr
  obtain ⟨C, hC, hb⟩ := exists_gaussianPhaseCost_centeredEnergy_error hW
  have hlim : Tendsto (fun T : ℝ => C * T ^ (-(1 / 6 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (y := 1 / 6) (by norm_num)).const_mul C
  have hsmall : ∀ᶠ T : ℝ in atTop, C * T ^ (-(1 / 6 : ℝ)) < κ :=
    hlim.eventually (gt_mem_nhds hκ)
  refine Or.inr ⟨κ, hκ, ?_⟩
  filter_upwards [he, hsmall, eventually_ge_atTop (1 : ℝ)] with T he hs hT
  have hT0 : 0 < T := by linarith
  have hp : T ^ (5 / 6 : ℝ) = T ^ (-(1 / 6 : ℝ)) * T := by
    conv_rhs => rhs; rw [← Real.rpow_one T]
    rw [← Real.rpow_add hT0]
    norm_num
  have herror : C * T ^ (5 / 6 : ℝ) ≤ κ * T := by
    rw [hp, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hs.le hT0.le
  have hh := (abs_le.mp (hb T hT)).1
  nlinarith

end RHTower.WeilWorkSettledPhase
