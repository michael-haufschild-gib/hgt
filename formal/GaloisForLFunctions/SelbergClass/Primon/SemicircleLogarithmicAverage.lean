import GaloisForLFunctions.SelbergClass.Primon.LogarithmicAverage
import GaloisForLFunctions.SelbergClass.Primon.KestenSemicircleLimit

/-!
# Semicircle logarithmic averages and explicit prime errors

The elementary bounds for `log(1-x)` sandwich the prime even-logarithm
mean between `r²(1-1/p)` and `r²`. Uniform convergence of the phase laws
then identifies the semicircle mean with `r²`. The charged logarithmic
factor consequently has semicircle mean `-r²/2`, with a signed prime
correction bounded by `r²/(2p)`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The prime even-logarithm mean lies in an explicit interval below its semicircle limit. -/
theorem kesten_evenPhaseLog_bounds (p : Nat.Primes) (s : ℝ) :
    cavityDiskCoordinate s ^ 2 * (1 - (p : ℝ)⁻¹) ≤
      (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * evenPhaseLogDenominator s t) ∧
    (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * evenPhaseLogDenominator s t) ≤
      cavityDiskCoordinate s ^ 2 := by
  let A := cavityDiskCoordinate s ^ 2
  let q := A / (p : ℝ)
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hp0 : 0 < (p : ℝ) := by linarith only [hp]
  have hp1 : 0 ≤ (p : ℝ) - 1 := by linarith only [hp]
  have hA0 : 0 ≤ A := sq_nonneg _
  have hA1 : A < 1 := by
    have h := pow_lt_one₀ (abs_nonneg (cavityDiskCoordinate s))
      (abs_cavityDiskCoordinate_lt_one s) (by omega : (2 : ℕ) ≠ 0)
    simpa only [sq_abs] using h
  have hq1 : q < 1 := (div_lt_one hp0).2 (hA1.trans hp)
  have hD : 0 < 1 - q := sub_pos.mpr hq1
  have hPA : 0 < (p : ℝ) - A := sub_pos.mpr (hA1.trans hp)
  have hlo := Real.log_le_sub_one_of_pos hD
  have hhi := Real.log_le_sub_one_of_pos (inv_pos.mpr hD)
  rw [Real.log_inv] at hhi
  have hl : q ≤ -Real.log (1 - q) := by linarith only [hlo]
  have hu : -Real.log (1 - q) ≤ q / (1 - q) := by
    apply hhi.trans_eq
    field_simp [hD.ne']
    ring
  rw [integral_kesten_evenPhaseLog]
  change A * (1 - (p : ℝ)⁻¹) ≤ -((p : ℝ) - 1) * Real.log (1 - q) ∧
    -((p : ℝ) - 1) * Real.log (1 - q) ≤ A
  constructor
  · calc
      A * (1 - (p : ℝ)⁻¹) = ((p : ℝ) - 1) * q := by
        dsimp [q]
        field_simp [hp0.ne']
      _ ≤ ((p : ℝ) - 1) * (-Real.log (1 - q)) := mul_le_mul_of_nonneg_left hl hp1
      _ = -((p : ℝ) - 1) * Real.log (1 - q) := by ring
  · calc
      -((p : ℝ) - 1) * Real.log (1 - q) =
          ((p : ℝ) - 1) * (-Real.log (1 - q)) := by ring
      _ ≤ ((p : ℝ) - 1) * (q / (1 - q)) := mul_le_mul_of_nonneg_left hu hp1
      _ = A * ((p : ℝ) - 1) / ((p : ℝ) - A) := by
        dsimp [q]
        field_simp [hp0.ne', hPA.ne']
      _ ≤ A := by
        apply (div_le_iff₀ hPA).2
        have h := mul_nonneg hA0 (sub_nonneg.mpr hA1.le)
        nlinarith only [h]

/-- The explicit prime even-logarithm means tend to the squared disk radius. -/
theorem tendsto_kesten_evenPhaseLog (s : ℝ) :
    Tendsto (fun p : Nat.Primes =>
      ∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * evenPhaseLogDenominator s t)
      cofinite (𝓝 (cavityDiskCoordinate s ^ 2)) := by
  let A := cavityDiskCoordinate s ^ 2
  let E := fun p : Nat.Primes =>
    ∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * evenPhaseLogDenominator s t
  have hb (p : Nat.Primes) : 0 ≤ A - E p ∧ A - E p ≤ A * (p : ℝ)⁻¹ := by
    have h := kesten_evenPhaseLog_bounds p s
    change A * (1 - (p : ℝ)⁻¹) ≤ E p ∧ E p ≤ A at h
    constructor <;> linarith only [h.1, h.2]
  have hi : Tendsto (fun p : Nat.Primes => (p : ℝ)⁻¹) cofinite (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_primeReal_cofinite_atTop
  have hd : Tendsto (fun p => A - E p) cofinite (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun p => (hb p).1)
      (Eventually.of_forall fun p => (hb p).2) (by simpa only [mul_zero] using hi.const_mul A)
  have h := (tendsto_const_nhds (x := A)).sub hd
  have he (p : Nat.Primes) : A - (A - E p) = E p := by ring
  simpa only [he, sub_zero] using h

/-- The semicircle mean of the even local logarithm is the squared disk radius. -/
theorem integral_semicircle_evenPhaseLog (s : ℝ) :
    (∫ t in Ioo (0 : ℝ) 1, semicirclePhaseDensity t * evenPhaseLogDenominator s t) =
      cavityDiskCoordinate s ^ 2 := by
  have h := tendsto_kestenObservableAverage
    ⟨evenPhaseLogDenominator s, continuous_evenPhaseLogDenominator s⟩
  change Tendsto (fun p =>
    ∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * evenPhaseLogDenominator s t) cofinite
      (𝓝 (∫ t in Ioo (0 : ℝ) 1, semicirclePhaseDensity t * evenPhaseLogDenominator s t)) at h
  exact tendsto_nhds_unique h (tendsto_kesten_evenPhaseLog s)

/-- The semicircle charged-boson logarithmic mean is minus half the squared fugacity. -/
theorem integral_semicircle_log_local_factor (s : ℝ) :
    (∫ t in Ioo (0 : ℝ) 1, semicirclePhaseDensity t * (-phaseLogDenominator s t)) =
      -(cavityDiskCoordinate s ^ 2) / 2 := by
  have he (p : Nat.Primes) :
      (-1 / 2 : ℝ) * (∫ t in Ioo (0 : ℝ) 1,
        kestenMcKayDensity p t * evenPhaseLogDenominator s t) =
      ∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * (-phaseLogDenominator s t) := by
    rw [integral_kesten_evenPhaseLog, integral_kesten_log_local_factor]
    ring
  have hl := (tendsto_kesten_evenPhaseLog s).const_mul (-1 / 2)
  simp only [he] at hl
  have h := tendsto_kestenObservableAverage
    ⟨fun t => -phaseLogDenominator s t, (continuous_phaseLogDenominator s).neg⟩
  change Tendsto (fun p =>
    ∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * (-phaseLogDenominator s t)) cofinite
      (𝓝 (∫ t in Ioo (0 : ℝ) 1, semicirclePhaseDensity t * (-phaseLogDenominator s t))) at h
  have hv := tendsto_nhds_unique h hl
  exact hv.trans (by ring)

/-- The signed prime correction to the semicircle logarithmic mean is at most `r²/(2p)`. -/
theorem kesten_log_local_factor_defect_bounds (p : Nat.Primes) (s : ℝ) :
    let D := (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * (-phaseLogDenominator s t)) -
      (∫ t in Ioo (0 : ℝ) 1, semicirclePhaseDensity t * (-phaseLogDenominator s t))
    0 ≤ D ∧ D ≤ cavityDiskCoordinate s ^ 2 / (2 * (p : ℝ)) := by
  have h := kesten_evenPhaseLog_bounds p s
  rw [integral_kesten_evenPhaseLog] at h
  dsimp only
  rw [integral_kesten_log_local_factor, integral_semicircle_log_local_factor]
  constructor
  · nlinarith only [h.2]
  · have he : cavityDiskCoordinate s ^ 2 / (2 * (p : ℝ)) =
        cavityDiskCoordinate s ^ 2 * (p : ℝ)⁻¹ / 2 := by ring
    rw [he]
    nlinarith only [h.1]

end
end GaloisForLFunctions.SelbergClass.Primon
