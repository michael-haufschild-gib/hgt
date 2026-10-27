import GaloisForLFunctions.ConjugateDiagonalGeometry.XiPositiveSourceMetric
import GaloisForLFunctions.ConjugateDiagonalGeometry.UniversalSourceWeight
import GaloisForLFunctions.ConjugateDiagonalGeometry.XiLogL1Convergence
import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceCutoffControl

/-!
# A single arithmetic regulator for the whole source-test space

A fixed positive weight controls all compact source transforms. Choosing the
regulator by one compact weighted current reading fixes the total mass. A
second local logarithmic-error requirement controls moving smooth tests.
The schedule uses only xi, its derivative and planar integration.
-/

open Complex MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Laplacian Topology
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization HTGeometry _root_.RHTower

/-- A normalized compact reading of the positive arithmetic curvature. -/
def xiCompactSourceReading (n k : ℕ) (φ : ℂ → ℝ) : ℝ :=
  Real.pi⁻¹ * ∫ z, sourceCutoff n z * φ z * xiCurvatureDensity (sourceRegulator k) z

/-- The normalized logarithmic current, defined without divisor coordinates. -/
def xiCurrentPairing (φ : ℂ → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ z, Real.log ‖xi z‖ * Δ φ z

/-- The actual multiplicity-weighted divisor trace of a real spectral test. -/
def zetaSourceTrace (φ : ℂ → ℝ) : ℝ :=
  ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * φ ρ

/-- The compact current counts xi zeros with their exact zeta multiplicities. -/
theorem xiCurrentPairing_eq_trace (φ : ℂ → ℝ) (hp : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) : xiCurrentPairing φ = zetaSourceTrace φ := by
  have hPL : IsPoincareLelongOfSmooth xi :=
    entire_isPoincareLelongOfSmooth
      (fun z => xi_analyticOnNhd_univ z (Set.mem_univ z))
      (z₀ := (2 : ℂ)) (xi_ne_zero_of_one_le_re (by norm_num))
  rw [xiCurrentPairing, hPL φ hp hc, xi_realDivisorPairing_eq_carrier φ hc]
  exact inv_mul_cancel_left₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero) _

/-- Regulator removal is valid for each compact smooth source reading. -/
theorem tendsto_xiCompactSourceReading (n : ℕ) (φ : ℂ → ℝ)
    (hp : ContDiff ℝ 2 φ) :
    Tendsto (fun k => xiCompactSourceReading n k φ) atTop
      (𝓝 (xiCurrentPairing (fun z => sourceCutoff n z * φ z))) := by
  have h := (tendsto_integral_xiCurvatureDensity
    (fun z => sourceCutoff n z * φ z) ((sourceCutoff n).contDiff.mul hp)
    (sourceCutoff n).hasCompactSupport.mul_right).const_mul Real.pi⁻¹
  have he : Real.pi⁻¹ * (1 / 2 : ℝ) = (2 * Real.pi)⁻¹ := by ring
  simpa only [xiCompactSourceReading, xiCurrentPairing, ← mul_assoc, he] using h

/-- Fast local accuracy, normalized by the actual derivatives of the fixed cutoff. -/
def sourceLocalAccuracy (n : ℕ) : ℝ :=
  Real.exp (-((n : ℝ) ^ 4)) / sourceCutoffControl n

theorem sourceLocalAccuracy_pos (n : ℕ) : 0 < sourceLocalAccuracy n :=
  div_pos (Real.exp_pos _) (sourceCutoffControl_pos n)

private theorem exists_commonSourceIndex (n : ℕ) :
    ∃ k : ℕ, n ≤ k ∧
      |xiCompactSourceReading n k universalSourceWeight -
        xiCurrentPairing (fun z => sourceCutoff n z * universalSourceWeight z)| <
          sourceRegulator n ∧
      xiLocalLogError 0 ((n : ℝ) + 2) k < sourceLocalAccuracy n := by
  have hw : ∀ᶠ k in atTop,
      |xiCompactSourceReading n k universalSourceWeight -
        xiCurrentPairing (fun z => sourceCutoff n z * universalSourceWeight z)| <
          sourceRegulator n := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
      (tendsto_xiCompactSourceReading n universalSourceWeight contDiff_universalSourceWeight)
      (sourceRegulator n) (sourceRegulator_pos n)
    exact eventually_atTop.mpr ⟨N, fun k hk => by
      simpa only [Real.dist_eq] using hN k hk⟩
  have hl := (tendsto_xiLocalLogError 0 ((n : ℝ) + 2)).eventually_lt_const
    (sourceLocalAccuracy_pos n)
  exact ((eventually_ge_atTop n).and (hw.and hl)).exists

/-- Least regulator index meeting the weighted-mass and local source-error requirements. -/
def commonSourceIndex (n : ℕ) : ℕ := Nat.find (exists_commonSourceIndex n)

theorem commonSourceIndex_ge (n : ℕ) : n ≤ commonSourceIndex n :=
  (Nat.find_spec (exists_commonSourceIndex n)).1

theorem commonSourceIndex_accuracy (n : ℕ) :
    |xiCompactSourceReading n (commonSourceIndex n) universalSourceWeight -
      xiCurrentPairing (fun z => sourceCutoff n z * universalSourceWeight z)| <
        sourceRegulator n :=
  (Nat.find_spec (exists_commonSourceIndex n)).2.1

/-- The same test-independent index controls local error on the expanding source disc. -/
theorem commonSourceIndex_local_accuracy (n : ℕ) :
    xiLocalLogError 0 ((n : ℝ) + 2) (commonSourceIndex n) < sourceLocalAccuracy n :=
  (Nat.find_spec (exists_commonSourceIndex n)).2.2

theorem tendsto_commonSourceIndex : Tendsto commonSourceIndex atTop atTop :=
  tendsto_atTop_mono commonSourceIndex_ge tendsto_id

/-- The same positive source sequence is used for every spectral test. -/
def commonSourceReading (φ : ℂ → ℝ) (n : ℕ) : ℝ :=
  xiCompactSourceReading n (commonSourceIndex n) φ

/-- Exhausting a summable divisor trace is independent of any regulator choice. -/
theorem tendsto_cutoff_zetaSourceTrace (φ : ℂ → ℝ)
    (hs : Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * φ ρ)) :
    Tendsto (fun n => zetaSourceTrace (fun z => sourceCutoff n z * φ z)) atTop
      (𝓝 (zetaSourceTrace φ)) := by
  have h := tendsto_tsum_of_dominated_convergence
    (f := fun n (ρ : zetaZeroConfig.carrier) =>
      sourceCutoff n ρ * ((zetaZeroConfig.mult ρ : ℝ) * φ ρ))
    (g := fun ρ => (zetaZeroConfig.mult ρ : ℝ) * φ ρ)
    (bound := fun ρ => ‖(zetaZeroConfig.mult ρ : ℝ) * φ ρ‖) hs.norm
    (fun ρ => tendsto_const_nhds.congr' ((sourceCutoff_eventually_one ρ).mono
      fun n hn => by dsimp only; rw [hn, one_mul]))
    (Eventually.of_forall fun n ρ => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sourceCutoff n).nonneg]
      exact mul_le_of_le_one_left (norm_nonneg _) (sourceCutoff n).le_one)
  have he (n : ℕ) :
      (∑' ρ : zetaZeroConfig.carrier,
        sourceCutoff n ρ * ((zetaZeroConfig.mult ρ : ℝ) * φ ρ)) =
        zetaSourceTrace (fun z => sourceCutoff n z * φ z) := by
    apply tsum_congr
    intro ρ
    ring
  simpa only [he, zetaSourceTrace] using h

/-- The source schedule fixes the full mass of the universal control channel. -/
theorem tendsto_commonSourceReading_weight :
    Tendsto (commonSourceReading universalSourceWeight) atTop
      (𝓝 (zetaSourceTrace universalSourceWeight)) := by
  have ht : Tendsto
      (fun n => xiCurrentPairing (fun z => sourceCutoff n z * universalSourceWeight z))
      atTop (𝓝 (zetaSourceTrace universalSourceWeight)) := by
    have he (n : ℕ) : xiCurrentPairing (fun z => sourceCutoff n z * universalSourceWeight z) =
        zetaSourceTrace (fun z => sourceCutoff n z * universalSourceWeight z) :=
      xiCurrentPairing_eq_trace _ ((sourceCutoff n).contDiff.mul contDiff_universalSourceWeight)
        (sourceCutoff n).hasCompactSupport.mul_right
    simpa only [he] using
      tendsto_cutoff_zetaSourceTrace universalSourceWeight summable_universalSourceWeight
  rw [Metric.tendsto_atTop] at ht ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := ht (ε / 2) (by positivity)
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp tendsto_sourceRegulator
    (ε / 2) (by positivity)
  refine ⟨max N K, fun n hn => ?_⟩
  have he := commonSourceIndex_accuracy n
  have hk := hK n ((le_max_right _ _).trans hn)
  have ht' := hN n ((le_max_left _ _).trans hn)
  have hreg : sourceRegulator n < ε / 2 := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos (sourceRegulator_pos n)] using hk
  have hd := dist_triangle (commonSourceReading universalSourceWeight n)
    (xiCurrentPairing (fun z => sourceCutoff n z * universalSourceWeight z))
    (zetaSourceTrace universalSourceWeight)
  change |commonSourceReading universalSourceWeight n -
    xiCurrentPairing (fun z => sourceCutoff n z * universalSourceWeight z)| <
      sourceRegulator n at he
  simp only [Real.dist_eq] at hd ht' ⊢
  linarith only [hd, he, ht', hreg]

/-- Every fixed compact set eventually lies in the constant part of the exhaustion. -/
theorem sourceCutoff_eventually_mul_eq_self {φ : ℂ → ℝ}
    (hc : HasCompactSupport φ) :
    ∀ᶠ n : ℕ in atTop, (fun z => sourceCutoff n z * φ z) = φ := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop R]
    with n hn
  funext z
  by_cases hz : φ z = 0
  · simp only [hz, mul_zero]
  have hmem := hR (subset_tsupport φ hz)
  rw [Metric.mem_closedBall, dist_zero_right] at hmem
  have hone : sourceCutoff n z = 1 := by
    apply (sourceCutoff n).one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖z‖ ≤ (n : ℝ) + 1
    linarith only [hmem, hn]
  rw [hone, one_mul]

/-- Local convergence holds along the source schedule, with no test-dependent selection. -/
theorem tendsto_commonSourceReading_compact (φ : ℂ → ℝ)
    (hp : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    Tendsto (commonSourceReading φ) atTop (𝓝 (zetaSourceTrace φ)) := by
  have h := ((tendsto_integral_xiCurvatureDensity φ hp hc).const_mul Real.pi⁻¹).comp
    tendsto_commonSourceIndex
  have htarget : Real.pi⁻¹ * ((1 / 2 : ℝ) *
      (∫ z, Real.log ‖xi z‖ * Δ φ z)) = zetaSourceTrace φ := by
    rw [← xiCurrentPairing_eq_trace φ hp hc, xiCurrentPairing]
    ring
  rw [htarget] at h
  apply h.congr'
  filter_upwards [sourceCutoff_eventually_mul_eq_self hc] with n hn
  change Real.pi⁻¹ * (∫ z, φ z * xiCurvatureDensity (sourceRegulator (commonSourceIndex n)) z) =
    Real.pi⁻¹ * ∫ z, (sourceCutoff n z * φ z) *
      xiCurvatureDensity (sourceRegulator (commonSourceIndex n)) z
  apply congrArg (fun t : ℝ => Real.pi⁻¹ * t)
  apply integral_congr_ae
  filter_upwards with z
  rw [congrFun hn z]

end GaloisForLFunctions.ConjugateDiagonalGeometry
