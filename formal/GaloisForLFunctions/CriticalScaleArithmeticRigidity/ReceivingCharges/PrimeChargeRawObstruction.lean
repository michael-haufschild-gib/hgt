import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeDyadicBands
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheTiltedSplineKeepsAGammaReserveAtEveryOverlap

/-!
# Exact charge with arbitrarily small complete raw cost

Finite dyadic prime bands divide a prescribed receiving charge among
arbitrarily many independent cofactor scales. Their complete raw energy,
raw input square and adjunction mass can all be made arbitrarily small.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory SelectiveMultiscaleArithmeticPositivity
  SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory

/-- Every prescribed receiving charge survives arbitrarily small raw complete cost
at arbitrarily large horizons. -/
theorem exists_receiving_charge_small_complete_raw_cost {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hA : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) (t : ℝ) (R : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (a : ℕ → ℝ), R ≤ N ∧ 2 ≤ N ∧
      harmonicSum N (conductorHorizonProfile N a) = 0 ∧
      packetMean N (arithmeticPrimeGenerator N a) = t ∧
      primeAdjunctionMass N a < ε ∧
      ‖packetVector (normalizedConductorPacket N a) N‖ ^ 2 < ε ∧
      |completeWeilEnergy φ (2 * K * Real.log N ^ (1 / 8 : ℝ)) N
        (packetVector (normalizedConductorPacket N a) N)| < ε := by
  obtain ⟨M, hMlarge⟩ := exists_nat_gt (3 * t ^ 2 / ε + 1)
  have hMpos : (0 : ℝ) < M := by
    have hq : 0 ≤ 3 * t ^ 2 / ε := by positivity
    linarith only [hMlarge, hq]
  have hM : 0 < M := by exact_mod_cast hMpos
  have hcost : 3 * t ^ 2 / (2 * (M : ℝ)) < ε := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (M : ℝ))).mpr
    have hquot : 3 * t ^ 2 / ε < M := by linarith only [hMlarge]
    have hmul := (div_lt_iff₀ hε).mp hquot
    nlinarith only [hmul, mul_pos hMpos hε]
  have henergy := (tendsto_primeChargeDyadic_complete_energy hφ hφ0 hsupp hA hK hM t).abs
  rw [abs_of_nonneg (by positivity : 0 ≤ 3 * t ^ 2 / (2 * (M : ℝ)))] at henergy
  have hsmall := primeChargeDyadic_small_inputs M t
  have hnorm := hsmall.1.pow 2
  simp only [zero_pow two_ne_zero] at hnorm
  obtain ⟨X, hX, hAdj, hNorm, hEnergy⟩ :=
    ((eventually_ge_atTop (max R 2)).and
      ((hsmall.2.eventually (gt_mem_nhds hε)).and
        ((hnorm.eventually (gt_mem_nhds hε)).and
          (henergy.eventually (gt_mem_nhds hcost))))).exists
  have hX2 : 2 ≤ X := (le_max_right R 2).trans hX
  have hD : 0 < primeChargeDyadicHorizon M := by
    unfold primeChargeDyadicHorizon
    positivity
  have hXN : X ≤ X ^ primeChargeDyadicHorizon M := Nat.le_pow hD
  refine ⟨X ^ primeChargeDyadicHorizon M, primeChargeDyadicCoefficients M X t,
    ((le_max_left R 2).trans hX).trans hXN, hX2.trans hXN, ?_, ?_, hAdj, hNorm, hEnergy⟩
  · exact primeChargeDyadic_neutral M (by omega) t
  · exact primeChargeDyadic_receiving_charge hM hX2 t

/-- No fixed multiple of raw input, adjunction and absolute complete energy controls charge. -/
theorem no_receiving_charge_bound_by_complete_raw_cost {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hA : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) :
    ¬ ∃ C : ℝ, ∀ (N : ℕ) (a : ℕ → ℝ), 2 ≤ N →
      harmonicSum N (conductorHorizonProfile N a) = 0 →
      packetMean N (arithmeticPrimeGenerator N a) ^ 2 ≤
        C * (primeAdjunctionMass N a +
          ‖packetVector (normalizedConductorPacket N a) N‖ ^ 2 +
          |completeWeilEnergy φ (2 * K * Real.log N ^ (1 / 8 : ℝ)) N
            (packetVector (normalizedConductorPacket N a) N)|) := by
  rintro ⟨C, hC⟩
  let ε : ℝ := 1 / (3 * (|C| + 1))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨N, a, -, hN, hz, hcharge, hAdj, hNorm, hEnergy⟩ :=
    exists_receiving_charge_small_complete_raw_cost hφ hφ0 hsupp hA hK 1 2 hε
  let V := primeAdjunctionMass N a +
    ‖packetVector (normalizedConductorPacket N a) N‖ ^ 2 +
    |completeWeilEnergy φ (2 * K * Real.log N ^ (1 / 8 : ℝ)) N
      (packetVector (normalizedConductorPacket N a) N)|
  have hV0 : 0 ≤ V := by
    exact add_nonneg (add_nonneg (primeAdjunctionMass_nonneg _ _) (sq_nonneg _)) (abs_nonneg _)
  have hV : V ≤ 3 * ε := by
    dsimp only [V]
    linarith only [hAdj, hNorm, hEnergy]
  have hpaid : 1 ≤ C * V := by
    have h := hC N a hN hz
    rw [hcharge, one_pow] at h
    exact h
  have hupper : C * V ≤ |C| * (3 * ε) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) hV0).trans
      (mul_le_mul_of_nonneg_left hV (abs_nonneg C))
  have hstrict : |C| * (3 * ε) < 1 := by
    have hp : 0 < |C| + 1 := by positivity
    change |C| * (3 * (1 / (3 * (|C| + 1)))) < 1
    rw [show |C| * (3 * (1 / (3 * (|C| + 1)))) = |C| / (|C| + 1) by
      field_simp [hp.ne']]
    exact (div_lt_iff₀ hp).mpr (by linarith only)
  exact (lt_irrefl (1 : ℝ)) ((hpaid.trans hupper).trans_lt hstrict)

/-- The complete tilted-spline family has exact nonzero receiving charge at arbitrarily small raw cost. -/
theorem tiltedPrimeCharge_small_complete_raw_cost {K : ℝ} (hK : 0 < K)
    (t : ℝ) (R : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (a : ℕ → ℝ), R ≤ N ∧ 2 ≤ N ∧
      harmonicSum N (conductorHorizonProfile N a) = 0 ∧
      packetMean N (arithmeticPrimeGenerator N a) = t ∧
      primeAdjunctionMass N a < ε ∧
      ‖packetVector (normalizedConductorPacket N a) N‖ ^ 2 < ε ∧
      |completeWeilEnergy tiltedUnitSpline (2 * K * Real.log N ^ (1 / 8 : ℝ)) N
        (packetVector (normalizedConductorPacket N a) N)| < ε :=
  exists_receiving_charge_small_complete_raw_cost contDiff_tiltedUnitSpline
    (fun u => by
      unfold tiltedUnitSpline atomDilate
      exact BiScaleUncertainty.ChebyshevGauge.splineProbe_nonneg _)
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hK t R hε

#print axioms exists_receiving_charge_small_complete_raw_cost
#print axioms no_receiving_charge_bound_by_complete_raw_cost
#print axioms tiltedPrimeCharge_small_complete_raw_cost

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
