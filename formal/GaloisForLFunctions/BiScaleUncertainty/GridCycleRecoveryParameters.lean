import GaloisForLFunctions.BiScaleUncertainty.GridFiniteCycleRecovery
import GaloisForLFunctions.BiScaleUncertainty.ClosedCycleDataResiduals

/-!
# Explicit finite recovery parameters from singular energy

Energy and target accuracy determine the radius, mesh, cycle order and a
positive noise threshold. The construction uses actual closed products and
also controls two sources fitting the same arbitrary measured array.
-/

noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
set_option autoImplicit false

/-- Effective support radius supplied by the logarithmic-grid tail estimate. -/
def gridRecoveryRadius (E ε : ℝ) : ℝ :=
  max 1 (32 * E / (Real.exp (-(1 / 2 : ℝ)) * ε ^ 2))

/-- Mesh width giving a quarter of the target accuracy for each source. -/
def gridRecoveryMesh (E ε : ℝ) : ℝ :=
  Real.exp (-1 - 128 * E / (Real.exp (-(1 / 2 : ℝ)) * ε ^ 2))

/-- The spoke has this many extra inner edges, in addition to its first inner edge. -/
def gridRecoveryDepth (E ε : ℝ) : ℕ :=
  ⌈gridRecoveryRadius E ε / firstOrderCollarRadius E⌉₊

/-- Amplification of a common error bound on the pair and spoke observations. -/
def gridRecoveryAmplification (E ε : ℝ) : ℝ :=
  (2 : ℝ) ^ (gridRecoveryDepth E ε + 1) * ((gridRecoveryDepth E ε : ℝ) + 2)

/-- Positive admissible discrepancy for the prescribed global accuracy. -/
def gridRecoveryNoise (E ε : ℝ) : ℝ := ε / (2 * gridRecoveryAmplification E ε)

theorem gridRecoveryRadius_one_le (E ε : ℝ) : 1 ≤ gridRecoveryRadius E ε := le_max_left _ _

theorem gridRecoveryRadius_tail_le (E ε : ℝ) :
    32 * E / (Real.exp (-(1 / 2 : ℝ)) * ε ^ 2) ≤ gridRecoveryRadius E ε := le_max_right _ _

theorem gridRecoveryMesh_pos (E ε : ℝ) : 0 < gridRecoveryMesh E ε := Real.exp_pos _

theorem gridRecoveryDepth_admissible (E ε : ℝ) :
    gridRecoveryRadius E ε ≤ ((gridRecoveryDepth E ε : ℝ) + 1) * firstOrderCollarRadius E := by
  have hr := firstOrderCollarRadius_pos E
  have hc : gridRecoveryRadius E ε / firstOrderCollarRadius E ≤
      (gridRecoveryDepth E ε : ℝ) := Nat.le_ceil _
  have hm := (div_le_iff₀ hr).mp hc
  nlinarith only [hm, hr]

theorem gridRecoveryAmplification_pos (E ε : ℝ) : 0 < gridRecoveryAmplification E ε := by
  unfold gridRecoveryAmplification
  positivity

theorem gridRecoveryNoise_pos (E : ℝ) {ε : ℝ} (hε : 0 < ε) :
    0 < gridRecoveryNoise E ε := div_pos hε (mul_pos (by norm_num) (gridRecoveryAmplification_pos E ε))

/-- Labels for all observations; no source-dependent support radius enters this type. -/
abbrev GridRecoveryIndex (E ε : ℝ) :=
  Bool × Fin (meshLength (gridRecoveryRadius E ε) (gridRecoveryMesh E ε))

/-- Literal closed pair/spoke observations determined only by energy and accuracy. -/
def gridRecoveryCycle (E ε : ℝ) (i : GridRecoveryIndex E ε) : List ℝ :=
  literalObservationCycle (gridRecoveryRadius E ε) (gridRecoveryMesh E ε)
    (gridRecoveryDepth E ε) i

theorem gridRecoveryCycle_sum (E ε : ℝ) (i : GridRecoveryIndex E ε) :
    (gridRecoveryCycle E ε i).sum = 0 := literalObservationCycle_sum _ _ _ i

theorem gridRecoveryCycle_length_le (E ε : ℝ) (i : GridRecoveryIndex E ε) :
    (gridRecoveryCycle E ε i).length ≤ gridRecoveryDepth E ε + 2 := by
  have h := literalObservationCycle_length_le (gridRecoveryRadius E ε) (gridRecoveryMesh E ε)
    (gridRecoveryDepth E ε) i
  simpa only [gridRecoveryCycle, max_eq_right (show 2 ≤ gridRecoveryDepth E ε + 2 by omega)] using h

theorem gridRecoveryCycle_count_le (E ε : ℝ) :
    Fintype.card (GridRecoveryIndex E ε) ≤
      2 * (⌈2 * gridRecoveryRadius E ε / gridRecoveryMesh E ε⌉₊ + 1) :=
  literalObservationCycle_count_le (zero_le_one.trans (gridRecoveryRadius_one_le E ε))
    (gridRecoveryMesh_pos E ε)

/-- Automatic parameters retain the exact separate pair and spoke noise coefficients. -/
theorem grid_recovery_automatic {E ε : ℝ} (f g : LevyEnergySource E) (hε : 0 < ε)
    (hfz : ∀ k : ℕ, 2 ≤ k → f.correlation (Real.log (k : ℝ)) = 0)
    (hgz : ∀ k : ℕ, 2 ≤ k → g.correlation (Real.log (k : ℝ)) = 0) :
    let R := gridRecoveryRadius E ε
    let η := gridRecoveryMesh E ε
    let n := gridRecoveryDepth E ε
    ‖f.complexCorrelation - g.complexCorrelation‖ ≤
      max ε ((2 : ℝ) ^ (n + 1) *
        (spokeMeshError f g R η n + ((n : ℝ) + 1) * pairMeshError f g R η n) + ε / 2) :=
  grid_finite_cycle_recovery_norm_exact f g hε (gridRecoveryRadius_one_le E ε)
    (gridRecoveryRadius_tail_le E ε) _ (gridRecoveryDepth_admissible E ε) hfz hgz

/-- A bound on every actual observation gives the explicit global uniform bound. -/
theorem grid_recovery_of_observation_bound {E ε δ : ℝ} (f g : LevyEnergySource E)
    (hε : 0 < ε)
    (hfz : ∀ k : ℕ, 2 ≤ k → f.correlation (Real.log (k : ℝ)) = 0)
    (hgz : ∀ k : ℕ, 2 ≤ k → g.correlation (Real.log (k : ℝ)) = 0)
    (hobs : ∀ i : GridRecoveryIndex E ε,
      |value f (gridRecoveryCycle E ε i) - value g (gridRecoveryCycle E ε i)| ≤ δ) :
    ‖f.complexCorrelation - g.complexCorrelation‖ ≤
      max ε (gridRecoveryAmplification E ε * δ + ε / 2) := by
  let R := gridRecoveryRadius E ε
  let η := gridRecoveryMesh E ε
  let n := gridRecoveryDepth E ε
  have hp : pairMeshError f g R η n ≤ δ := by
    apply Finset.sup'_le
    intro i _
    exact hobs (true, i)
  have hs : spokeMeshError f g R η n ≤ δ := by
    apply Finset.sup'_le
    intro i _
    exact hobs (false, i)
  apply (grid_recovery_automatic f g hε hfz hgz).trans
  apply max_le_max_left ε
  apply add_le_add _ le_rfl
  calc
    _ ≤ (2 : ℝ) ^ (n + 1) * (δ + ((n : ℝ) + 1) * δ) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hs (mul_le_mul_of_nonneg_left hp (by positivity))) (by positivity)
    _ = gridRecoveryAmplification E ε * δ := by
      change (2 : ℝ) ^ (n + 1) * (δ + ((n : ℝ) + 1) * δ) =
        ((2 : ℝ) ^ (n + 1) * ((n : ℝ) + 2)) * δ
      ring

/-- The positive, source-independent noise threshold guarantees the requested accuracy. -/
theorem grid_recovery_at_noise_threshold {E ε : ℝ} (f g : LevyEnergySource E)
    (hε : 0 < ε)
    (hfz : ∀ k : ℕ, 2 ≤ k → f.correlation (Real.log (k : ℝ)) = 0)
    (hgz : ∀ k : ℕ, 2 ≤ k → g.correlation (Real.log (k : ℝ)) = 0)
    (hobs : ∀ i : GridRecoveryIndex E ε,
      |value f (gridRecoveryCycle E ε i) - value g (gridRecoveryCycle E ε i)| ≤
        gridRecoveryNoise E ε) :
    ‖f.complexCorrelation - g.complexCorrelation‖ ≤ ε := by
  have he : gridRecoveryAmplification E ε * gridRecoveryNoise E ε + ε / 2 = ε := by
    unfold gridRecoveryNoise
    field_simp [(gridRecoveryAmplification_pos E ε).ne']
    ring
  have h := grid_recovery_of_observation_bound f g hε hfz hgz hobs
  rwa [he, max_self] at h

/-- Arbitrary measured arrays give the same automatic bound using the sum of fitting residuals. -/
theorem grid_recovery_from_measured_array {E ε : ℝ} (f g : LevyEnergySource E)
    (hε : 0 < ε)
    (hfz : ∀ k : ℕ, 2 ≤ k → f.correlation (Real.log (k : ℝ)) = 0)
    (hgz : ∀ k : ℕ, 2 ≤ k → g.correlation (Real.log (k : ℝ)) = 0)
    (z : GridRecoveryIndex E ε → ℝ) :
    let R := gridRecoveryRadius E ε
    let η := gridRecoveryMesh E ε
    let n := gridRecoveryDepth E ε
    ‖f.complexCorrelation - g.complexCorrelation‖ ≤
      max ε (gridRecoveryAmplification E ε *
        (literalDataResidual f R η n z + literalDataResidual g R η n z) + ε / 2) :=
  grid_recovery_of_observation_bound f g hε hfz hgz
    (literal_discrepancy_le_residual_sum f g _ _ _ z)

/-- Two admissible fits within the explicit total residual threshold are uniformly close. -/
theorem grid_recovery_from_residual_threshold {E ε : ℝ} (f g : LevyEnergySource E)
    (hε : 0 < ε)
    (hfz : ∀ k : ℕ, 2 ≤ k → f.correlation (Real.log (k : ℝ)) = 0)
    (hgz : ∀ k : ℕ, 2 ≤ k → g.correlation (Real.log (k : ℝ)) = 0)
    (z : GridRecoveryIndex E ε → ℝ)
    (hz : literalDataResidual f (gridRecoveryRadius E ε) (gridRecoveryMesh E ε)
        (gridRecoveryDepth E ε) z +
      literalDataResidual g (gridRecoveryRadius E ε) (gridRecoveryMesh E ε)
        (gridRecoveryDepth E ε) z ≤ gridRecoveryNoise E ε) :
    ‖f.complexCorrelation - g.complexCorrelation‖ ≤ ε :=
  grid_recovery_at_noise_threshold f g hε hfz hgz
    (fun i => (literal_discrepancy_le_residual_sum f g _ _ _ z i).trans hz)

end GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
