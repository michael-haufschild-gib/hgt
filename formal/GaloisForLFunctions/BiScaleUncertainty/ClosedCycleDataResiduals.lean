import GaloisForLFunctions.BiScaleUncertainty.ControlledClosedCycleRecovery

/-!
# Measured closed-cycle arrays and admissible reconstruction errors

A measured array may contain arbitrary real values. Two actual sources that
fit it have pair and spoke discrepancies bounded by the sum of their literal
finite-array residuals. The controlled recovery theorem then applies directly.
-/

noncomputable section
open Set
namespace GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
set_option autoImplicit false
variable {E : ℝ}

/-- Maximum residual against the literal pair/spoke observation array. -/
def literalDataResidual (f : LevyEnergySource E) (R η : ℝ) (n : ℕ)
    (z : Bool × Fin (meshLength R η) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i => |value f (literalObservationCycle R η n i) - z i|)

theorem literal_residual_le_max (f : LevyEnergySource E) (R η : ℝ) (n : ℕ)
    (z : Bool × Fin (meshLength R η) → ℝ) (i : Bool × Fin (meshLength R η)) :
    |value f (literalObservationCycle R η n i) - z i| ≤ literalDataResidual f R η n z := by
  unfold literalDataResidual
  exact Finset.le_sup' (fun j : Bool × Fin (meshLength R η) =>
    |value f (literalObservationCycle R η n j) - z j|) (Finset.mem_univ i)

/-- The same arbitrary measured datum gives the exact sum of the two fitting residuals. -/
theorem literal_discrepancy_le_residual_sum (f g : LevyEnergySource E) (R η : ℝ) (n : ℕ)
    (z : Bool × Fin (meshLength R η) → ℝ) (i : Bool × Fin (meshLength R η)) :
    |value f (literalObservationCycle R η n i) - value g (literalObservationCycle R η n i)| ≤
      literalDataResidual f R η n z + literalDataResidual g R η n z := by
  calc
    _ = |(value f (literalObservationCycle R η n i) - z i) -
        (value g (literalObservationCycle R η n i) - z i)| := by congr 1; ring
    _ ≤ |value f (literalObservationCycle R η n i) - z i| +
        |value g (literalObservationCycle R η n i) - z i| := abs_sub _ _
    _ ≤ _ := add_le_add (literal_residual_le_max f R η n z i)
      (literal_residual_le_max g R η n z i)

/-- Every pair discrepancy is controlled by the actual measured-array fitting errors. -/
theorem pairMeshError_le_residual_sum (f g : LevyEnergySource E) (R η : ℝ) (n : ℕ)
    (z : Bool × Fin (meshLength R η) → ℝ) :
    pairMeshError f g R η n ≤ literalDataResidual f R η n z + literalDataResidual g R η n z := by
  apply Finset.sup'_le
  intro i hi
  have h := literal_discrepancy_le_residual_sum f g R η n z (true, i)
  change |value f [meshPoint R η i / ((n : ℝ) + 1), -(meshPoint R η i / ((n : ℝ) + 1))] -
    value g [meshPoint R η i / ((n : ℝ) + 1), -(meshPoint R η i / ((n : ℝ) + 1))]| ≤ _ at h
  exact h

/-- Every spoke discrepancy is controlled by the same measured-array fitting errors. -/
theorem spokeMeshError_le_residual_sum (f g : LevyEnergySource E) (R η : ℝ) (n : ℕ)
    (z : Bool × Fin (meshLength R η) → ℝ) :
    spokeMeshError f g R η n ≤ literalDataResidual f R η n z + literalDataResidual g R η n z := by
  apply Finset.sup'_le
  intro i hi
  have h := literal_discrepancy_le_residual_sum f g R η n z (false, i)
  change |value f (spoke n (meshPoint R η i)) - value g (spoke n (meshPoint R η i))| ≤ _ at h
  exact h

/-- An actual admissible reconstruction inherits the uniform recovery estimate from its data residual. -/
theorem controlled_recovery_from_measured_array (f g : LevyEnergySource E) {R η ρ κ : ℝ}
    (hR : 0 ≤ R) (hη : 0 < η) (hκ : 0 < κ) (n : ℕ)
    (hn : R ≤ ((n : ℝ) + 1) * ρ)
    (hf : ∀ t, |t| ≤ ρ → κ ≤ f.correlation t)
    (hg : ∀ t, |t| ≤ ρ → κ ≤ g.correlation t)
    (ω : ℝ → ℝ)
    (hωf : ∀ x y, |x - y| ≤ η → |f.correlation x - f.correlation y| ≤ ω η)
    (hωg : ∀ x y, |x - y| ≤ η → |g.correlation x - g.correlation y| ≤ ω η)
    (hsf : ∀ x, R < |x| → f.correlation x = 0)
    (hsg : ∀ x, R < |x| → g.correlation x = 0)
    (z : Bool × Fin (meshLength R η) → ℝ) :
    ‖f.complexCorrelation - g.complexCorrelation‖ ≤
      ((1 + ((n : ℝ) + 1) / (2 * κ)) *
        (literalDataResidual f R η n z + literalDataResidual g R η n z)) / κ ^ (n + 1) +
        2 * ω η := by
  apply (controlled_global_recovery_norm f g hR hη hκ n hn hf hg ω hωf hωg hsf hsg).trans
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ (pow_pos hκ (n + 1)).le
  calc
    _ ≤ (literalDataResidual f R η n z + literalDataResidual g R η n z) +
        ((n : ℝ) + 1) * (literalDataResidual f R η n z + literalDataResidual g R η n z) /
          (2 * κ) := add_le_add (spokeMeshError_le_residual_sum f g R η n z)
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pairMeshError_le_residual_sum f g R η n z) (by positivity))
        (mul_pos (by norm_num) hκ).le)
    _ = _ := by ring

end GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
