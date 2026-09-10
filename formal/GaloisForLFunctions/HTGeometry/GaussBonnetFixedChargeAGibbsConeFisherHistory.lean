import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsConeSource
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFisherPositiveCone
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsTunableFisherHistory

/-! # Actual Fisher histories for the entire nonnegative source cone -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem shape_scale (c a b : ℝ) (hc : 0 < c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    egbFixedChargeAGibbsCollisionFisherShape (c * a) (c * b) =
      egbFixedChargeAGibbsCollisionFisherShape a b := by
  by_cases h : a + b = 0
  · have haz : a = 0 := by linarith
    have hbz : b = 0 := by linarith
    simp [haz, hbz, egbFixedChargeAGibbsCollisionFisherShape]
  · have hs : c * a + c * b ≠ 0 := by
      rw [← mul_add]
      exact mul_ne_zero hc.ne' h
    unfold egbFixedChargeAGibbsCollisionFisherShape
    field_simp
    <;> ring

/-- One fixed actual Gibbs state realizes the complete Fisher history of any prescribed positive two-atom source. -/
theorem egbFixedChargeAGibbsCone_fisher_history (n k m j : ℕ) (x y : NNReal) :
    egbFixedChargeAGibbsCollisionFisherValue n (m + j) 1 (egbFixedChargeAGibbsConeEnergy n k m x y) =
      egbFixedChargeAGibbsCollisionFisherShape ((4 / 9 : ℝ) ^ j * x) ((1 / 36 : ℝ) ^ j * y) := by
  rw [egbFixedChargeAGibbsCollisionFisherValue_two_mass,
    egbFixedChargeAGibbsCollisionSlowSourceMass_offset, egbFixedChargeAGibbsCollisionFastSourceMass_offset,
    egbFixedChargeAGibbsCone_slow_mass, egbFixedChargeAGibbsCone_fast_mass]
  change egbFixedChargeAGibbsCollisionFisherShape
    ((4 / 9 : ℝ) ^ j * ((egbFixedChargeAGibbsConeScale n k m x y : ℝ) * x))
    ((1 / 36 : ℝ) ^ j * ((egbFixedChargeAGibbsConeScale n k m x y : ℝ) * y)) = _
  calc
    _ = egbFixedChargeAGibbsCollisionFisherShape
        ((egbFixedChargeAGibbsConeScale n k m x y : ℝ) * ((4 / 9 : ℝ) ^ j * x))
        ((egbFixedChargeAGibbsConeScale n k m x y : ℝ) * ((1 / 36 : ℝ) ^ j * y)) := by
      congr 1 <;> ring
    _ = _ := shape_scale _ _ _ (egbFixedChargeAGibbsConeScale_pos n k m x y) (by positivity) (by positivity)

/-- At the selected offset the arbitrary prescribed masses are the exact Fisher shape parameters. -/
theorem egbFixedChargeAGibbsCone_fisher_formula (n k m : ℕ) (x y : NNReal) :
    egbFixedChargeAGibbsCollisionFisherValue n m 1 (egbFixedChargeAGibbsConeEnergy n k m x y) =
      egbFixedChargeAGibbsCollisionFisherShape x y := by
  simpa only [Nat.add_zero, pow_zero, one_mul] using egbFixedChargeAGibbsCone_fisher_history n k m 0 x y

/-- At every observation time, Fisher vanishes exactly when at least one prescribed source mass vanishes. -/
theorem egbFixedChargeAGibbsCone_fisher_zero_iff (n k m l : ℕ) (x y : NNReal) :
    egbFixedChargeAGibbsCollisionFisherValue n l 1 (egbFixedChargeAGibbsConeEnergy n k m x y) = 0 ↔
      x = 0 ∨ y = 0 := by
  have h := egbFixedChargeAGibbsCollisionFisherValue_zero_iff n l 1 (egbFixedChargeAGibbsConeEnergy n k m x y)
  rw [egbFixedChargeAGibbsCone_slow_energy, egbFixedChargeAGibbsCone_fast_energy] at h
  have ha : egbFixedChargeAGibbsConeAmplitude n k m x y ^ 2 ≠ 0 :=
    (sq_pos_of_pos (egbFixedChargeAGibbsConeAmplitude_pos n k m x y)).ne'
  have hb : egbFixedChargeAGibbsConeAmplitude n k m x y ^ 2 * (16 : ℝ) ^ (m + 1) ≠ 0 :=
    mul_ne_zero ha (by positivity)
  simpa [ha, hb] using h

/-- The complete zero-Fisher history is exactly the union of both pure rays and the zero source. -/
theorem egbFixedChargeAGibbsCone_fisher_history_zero_iff (n k m : ℕ) (x y : NNReal) :
    (∀ l : ℕ, egbFixedChargeAGibbsCollisionFisherValue n l 1
      (egbFixedChargeAGibbsConeEnergy n k m x y) = 0) ↔ x = 0 ∨ y = 0 := by
  constructor
  · intro h
    exact (egbFixedChargeAGibbsCone_fisher_zero_iff n k m 0 x y).1 (h 0)
  · intro h l
    exact (egbFixedChargeAGibbsCone_fisher_zero_iff n k m l x y).2 h

end
end GaloisForLFunctions.HTGeometry
