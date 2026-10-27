import GaloisForLFunctions.BiScaleUncertainty.FiniteNetClosedCycleRecovery
import GaloisForLFunctions.BiScaleUncertainty.DerivativeCycleConditioning

/-!
# Derivative-conditioned recovery on arbitrary finite nets

Actual source derivative energy gives linear cycle conditioning at every net
point. Moving to the net costs two square-root derivative moduli, and fitting
an arbitrary measured array costs the sum of the two residuals.
-/

noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
set_option autoImplicit false
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The exact linearly conditioned norm bound holds for every finite net of the common support. -/
theorem finiteNet_derivative_recovery_norm {E B R η : ℝ} (f g : LevyEnergySource E)
    (z : ι → ℝ) (hη : 0 ≤ η)
    (hfB : normalizedDirichletEnergy f.source ≤ B)
    (hgB : normalizedDirichletEnergy g.source ≤ B)
    (n : ℕ) (hn : B * R ^ 2 ≤ (n : ℝ) + 1)
    (hz : ∀ i, |z i| ≤ R)
    (hnet : ∀ x : ℝ, |x| ≤ R → ∃ i, |x - z i| ≤ η)
    (hsf : ∀ x, R < |x| → f.correlation x = 0)
    (hsg : ∀ x, R < |x| → g.correlation x = 0) :
    ‖f.complexCorrelation - g.complexCorrelation‖ ≤
      2 * finiteNetSpokeError f g z n + 2 * ((n : ℝ) + 1) * finiteNetPairError f g z n +
        2 * Real.sqrt B * η := by
  have hm (i : ι) : |f.correlation (z i) - g.correlation (z i)| ≤
      2 * finiteNetSpokeError f g z n + 2 * ((n : ℝ) + 1) * finiteNetPairError f g z n := by
    have hp := Finset.le_sup' (s := Finset.univ) (fun j : ι =>
      |value f (finiteNetCycle z n (true, j)) - value g (finiteNetCycle z n (true, j))|)
      (Finset.mem_univ i)
    have hs := Finset.le_sup' (s := Finset.univ) (fun j : ι =>
      |value f (finiteNetCycle z n (false, j)) - value g (finiteNetCycle z n (false, j))|)
      (Finset.mem_univ i)
    exact (derivative_correlation_recovery f g hfB hgB n hn (hz i)).trans
      (add_le_add (mul_le_mul_of_nonneg_left hs (by norm_num))
        (mul_le_mul_of_nonneg_left hp (by positivity)))
  apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
  intro x
  change ‖(f.correlation x : ℂ) - (g.correlation x : ℂ)‖ ≤ _
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  by_cases hx : |x| ≤ R
  · obtain ⟨i, hi⟩ := hnet x hx
    have hfi := (derivative_correlation_modulus f hfB x (z i)).trans
      (mul_le_mul_of_nonneg_left hi (Real.sqrt_nonneg B))
    have hgi := (derivative_correlation_modulus g hgB x (z i)).trans
      (mul_le_mul_of_nonneg_left hi (Real.sqrt_nonneg B))
    have hsample := hm i
    have ht : |f.correlation x - g.correlation x| ≤
        |f.correlation x - f.correlation (z i)| +
          |f.correlation (z i) - g.correlation (z i)| +
          |g.correlation x - g.correlation (z i)| := by
      calc
        _ = |(f.correlation x - f.correlation (z i)) +
            (f.correlation (z i) - g.correlation (z i)) -
            (g.correlation x - g.correlation (z i))| := by congr 1; ring
        _ ≤ _ := (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    linarith only [ht, hsample, hfi, hgi]
  · rw [hsf x (lt_of_not_ge hx), hsg x (lt_of_not_ge hx), sub_self, abs_zero]
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact add_nonneg ((abs_nonneg _).trans (hm i))
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg B)) hη)

/-- Arbitrary data fits retain linear conditioning on every finite net. -/
theorem finiteNet_derivative_recovery_from_measured_array {E B R η : ℝ}
    (f g : LevyEnergySource E) (z : ι → ℝ) (hη : 0 ≤ η)
    (hfB : normalizedDirichletEnergy f.source ≤ B)
    (hgB : normalizedDirichletEnergy g.source ≤ B)
    (n : ℕ) (hn : B * R ^ 2 ≤ (n : ℝ) + 1)
    (hz : ∀ i, |z i| ≤ R)
    (hnet : ∀ x : ℝ, |x| ≤ R → ∃ i, |x - z i| ≤ η)
    (hsf : ∀ x, R < |x| → f.correlation x = 0)
    (hsg : ∀ x, R < |x| → g.correlation x = 0) (a : Bool × ι → ℝ) :
    ‖f.complexCorrelation - g.complexCorrelation‖ ≤
      2 * ((n : ℝ) + 2) *
        (finiteNetDataResidual f z n a + finiteNetDataResidual g z n a) +
        2 * Real.sqrt B * η := by
  have hp : finiteNetPairError f g z n ≤
      finiteNetDataResidual f z n a + finiteNetDataResidual g z n a := by
    apply Finset.sup'_le
    intro i _
    exact finiteNet_discrepancy_le_residual_sum f g z n a (true, i)
  have hs : finiteNetSpokeError f g z n ≤
      finiteNetDataResidual f z n a + finiteNetDataResidual g z n a := by
    apply Finset.sup'_le
    intro i _
    exact finiteNet_discrepancy_le_residual_sum f g z n a (false, i)
  apply (finiteNet_derivative_recovery_norm f g z hη hfB hgB n hn hz hnet hsf hsg).trans
  apply add_le_add _ le_rfl
  calc
    _ ≤ 2 * (finiteNetDataResidual f z n a + finiteNetDataResidual g z n a) +
        2 * ((n : ℝ) + 1) * (finiteNetDataResidual f z n a + finiteNetDataResidual g z n a) :=
      add_le_add (mul_le_mul_of_nonneg_left hs (by norm_num))
        (mul_le_mul_of_nonneg_left hp (by positivity))
    _ = _ := by ring

end GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
