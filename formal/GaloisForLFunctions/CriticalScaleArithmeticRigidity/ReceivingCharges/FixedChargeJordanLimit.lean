import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.FixedPacketCriticalCancellation
import GaloisForLFunctions.ArithmeticDegenerationTheory.TheCriticalConductorFormRetainsThePolarGenus
import GaloisForLFunctions.ArithmeticCountingPositivity.HarmonicParitySpectralCoordinates

/-!
# The exact fixed-cutoff critical energy after harmonic centering

Harmonic centering converges coefficientwise to removal of conductor one.
The complete critical conductor Gram therefore gives the positive Jordan
form of the nonpolar coefficients after multiplication by the seventh
overlap power. The polar genus term vanishes under this exact centering.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  ArithmeticDegenerationTheory ArithmeticHodgeTheoryOfDegenerations
  SpacingScaleHarmonicAnalysis SelectiveMultiscaleArithmeticPositivity

/-- The harmonic mean of a fixed finite conductor packet tends to its constant coefficient. -/
theorem tendsto_harmonicMean_fixedPacket {Q : ℕ} (hQ : 1 ≤ Q) (a : ℕ → ℝ) :
    Tendsto (fun N : ℕ => harmonicSum N (conductorHorizonProfile Q a) / harmonicMass N)
      atTop (𝓝 (a 1)) := by
  have hnum := tendsto_finsetSum (Icc 1 Q) (fun m hm =>
    (tendsto_normalizedRamanujanHorizonVector_gram (mem_Icc.mp hm).1 (by norm_num : 0 < (1 : ℕ))).const_mul
      (a m))
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', if_pos (mem_Icc.mpr ⟨le_rfl, hQ⟩)] at hnum
  have hsum (N : ℕ) : (∑ m ∈ Icc 1 Q,
      a m * ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector 1 N⟫) =
        harmonicSum N (conductorHorizonProfile Q a) / Real.log N := by
    simpa only [sum_inner, real_inner_smul_left] using
      horizonPacket_inner_pole_eq_harmonicSum Q N a
  simp only [hsum] at hnum
  have hden : Tendsto (fun N : ℕ => harmonicMass N / Real.log N) atTop (𝓝 (1 : ℝ)) := by
    simpa only [gaugeHarmonicSum, harmonicMass] using
      ArithmeticCountingPositivity.tendsto_harmonicMass_div_log
  have h := hnum.div hden one_ne_zero
  simp only [div_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hL : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  field_simp [hL, (harmonicMass_pos (by omega : 1 ≤ N)).ne']

/-- Literal harmonic centering converges to deletion of the constant conductor. -/
theorem tendsto_harmonicCentered_fixedCoefficient {Q : ℕ} (hQ : 1 ≤ Q)
    (a : ℕ → ℝ) (m : ℕ) :
    Tendsto (fun N : ℕ => harmonicCenteredCoefficients Q N a m)
      atTop (𝓝 (removeConstantConductor a m)) := by
  by_cases hm : m = 1
  · subst m
    have h := (tendsto_const_nhds (x := a 1) (f := atTop)).sub
      (tendsto_harmonicMean_fixedPacket hQ a)
    simpa only [harmonicCenteredCoefficients, addConstantConductor, if_pos rfl,
      removeConstantConductor, sub_eq_add_neg, add_neg_cancel] using h
  · simpa only [harmonicCenteredCoefficients, addConstantConductor, if_neg hm,
      add_zero, removeConstantConductor] using (tendsto_const_nhds (x := a m) (f := atTop))

/-- Convergent coefficient families in a fixed conductor block retain the critical Jordan and polar forms. -/
theorem tendsto_variable_fixedPacket_rescaled_energy {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (ha : ∀ m ∈ S, Tendsto (fun N => a N m) atTop (𝓝 (b m))) :
    Tendsto (fun N : ℕ => c N ^ 7 *
      completeWeilEnergy tiltedUnitSpline (c N) N
        (∑ m ∈ S, a N m • normalizedRamanujanHorizonVector m N)) atTop
      (𝓝 ((∑ m ∈ S, jordanCoefficient m * b m ^ 2) +
        (if 1 ∈ S then criticalGenusCoefficient R * b 1 ^ 2 else 0))) := by
  have hfixed := tendsto_finsetSum S (fun m hm => tendsto_finsetSum S (fun l hl =>
    (tendsto_critical_rescaledConductorGram hc hR hcrit (hS m hm) (hS l hl)).const_mul (b m * b l)))
  have hval := tendsto_nhds_unique hfixed (tendsto_critical_rescaled_packet hc hR hcrit hS b)
  have h := tendsto_finsetSum S (fun m hm => tendsto_finsetSum S (fun l hl =>
    ((ha m hm).mul (ha l hl)).mul
      (tendsto_critical_rescaledConductorGram hc hR hcrit (hS m hm) (hS l hl))))
  rw [hval] at h
  apply h.congr
  intro N
  simp only [completeWeilEnergy, map_sum, map_smul, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, mul_sum,
    rescaledConductorGram, conductorEntry]
  rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
  exact sum_congr rfl fun m _ => sum_congr rfl fun l _ => by ring

/-- Exact harmonic pole removal leaves the nonpolar Jordan form at every positive critical ratio. -/
theorem tendsto_harmonicCentered_fixedPacket_Jordan_energy {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {Q : ℕ} (hQ : 1 ≤ Q) (a : ℕ → ℝ) :
    Tendsto (fun N : ℕ => c N ^ 7 * completeWeilEnergy tiltedUnitSpline (c N) N
      ((Real.sqrt (Real.log N))⁻¹ • packetVector
        (normalizedConductorPacket Q (harmonicCenteredCoefficients Q N a)) N)) atTop
      (𝓝 (∑ m ∈ Icc 1 Q, jordanCoefficient m * removeConstantConductor a m ^ 2)) := by
  have h := tendsto_variable_fixedPacket_rescaled_energy hc hR hcrit (Icc 1 Q)
    (fun m hm => (mem_Icc.mp hm).1) (fun N => harmonicCenteredCoefficients Q N a)
    (removeConstantConductor a) (fun m _ => tendsto_harmonicCentered_fixedCoefficient hQ a m)
  have hone : removeConstantConductor a 1 = 0 := by
    rw [removeConstantConductor, if_pos rfl]
  simpa only [physicalPacket_eq_sum_normalizedModes, hone, zero_pow two_ne_zero,
    mul_zero, ite_self, add_zero] using h

/-- In raw coordinates a fixed centered packet has a linear-overlap Jordan energy. -/
theorem tendsto_harmonicCentered_fixedPacket_raw_energy_div_overlap {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {Q : ℕ} (hQ : 1 ≤ Q) (a : ℕ → ℝ) :
    Tendsto (fun N : ℕ => completeWeilEnergy tiltedUnitSpline (c N) N
      (packetVector (normalizedConductorPacket Q (harmonicCenteredCoefficients Q N a)) N) /
        c N) atTop
      (𝓝 ((∑ m ∈ Icc 1 Q, jordanCoefficient m * removeConstantConductor a m ^ 2) / R)) := by
  have h := (tendsto_harmonicCentered_fixedPacket_Jordan_energy hc hR hcrit hQ a).div
    hcrit hR.ne'
  have hscale (N : ℕ) :
      completeWeilEnergy tiltedUnitSpline (c N) N
        ((Real.sqrt (Real.log N))⁻¹ • packetVector
          (normalizedConductorPacket Q (harmonicCenteredCoefficients Q N a)) N) =
      completeWeilEnergy tiltedUnitSpline (c N) N
        (packetVector (normalizedConductorPacket Q (harmonicCenteredCoefficients Q N a)) N) /
          Real.log N := by
    simp only [completeWeilEnergy, map_smul, real_inner_smul_left, real_inner_smul_right]
    have hs : (Real.sqrt (Real.log N))⁻¹ ^ 2 = (Real.log N)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
    calc
      _ = (Real.sqrt (Real.log N))⁻¹ ^ 2 *
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
          (packetVector (normalizedConductorPacket Q (harmonicCenteredCoefficients Q N a)) N),
          packetVector (normalizedConductorPacket Q (harmonicCenteredCoefficients Q N a)) N⟫ := by ring
      _ = _ := by rw [hs]; ring
  simp only [hscale] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hc0 : c N ≠ 0 := (zero_lt_one.trans_le (hc N)).ne'
  have hL : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  field_simp [hc0, hL]

/-- Every nonzero nonpolar coefficient gives strictly positive limiting Jordan energy. -/
theorem fixedPacket_Jordan_energy_pos {Q : ℕ} (a : ℕ → ℝ)
    (ha : ∃ m ∈ Icc 2 Q, a m ≠ 0) :
    0 < ∑ m ∈ Icc 1 Q, jordanCoefficient m * removeConstantConductor a m ^ 2 := by
  obtain ⟨m, hm, ha⟩ := ha
  have hm1 : m ≠ 1 := by have := (mem_Icc.mp hm).1; omega
  have hmS : m ∈ Icc 1 Q := mem_Icc.mpr ⟨by have := (mem_Icc.mp hm).1; omega, (mem_Icc.mp hm).2⟩
  refine sum_pos' (fun j hj => mul_nonneg
    (jordanCoefficient_pos (mem_Icc.mp hj).1).le (sq_nonneg _)) ⟨m, hmS, ?_⟩
  rw [removeConstantConductor, if_neg hm1]
  exact mul_pos (jordanCoefficient_pos (mem_Icc.mp hmS).1) (sq_pos_of_ne_zero ha)

/-- Fixed nonpolar packets eventually have positive raw complete energy at every critical ratio. -/
theorem eventually_harmonicCentered_fixedPacket_energy_pos {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {Q : ℕ} (hQ : 1 ≤ Q) (a : ℕ → ℝ) (ha : ∃ m ∈ Icc 2 Q, a m ≠ 0) :
    ∀ᶠ N : ℕ in atTop, 0 < completeWeilEnergy tiltedUnitSpline (c N) N
      (packetVector (normalizedConductorPacket Q (harmonicCenteredCoefficients Q N a)) N) := by
  filter_upwards [(tendsto_harmonicCentered_fixedPacket_raw_energy_div_overlap hc hR hcrit hQ a).
    eventually (lt_mem_nhds (div_pos (fixedPacket_Jordan_energy_pos a ha) hR))] with N hN
  have h := (lt_div_iff₀ (zero_lt_one.trans_le (hc N))).mp hN
  simpa only [zero_mul] using h

#print axioms tendsto_harmonicCentered_fixedCoefficient
#print axioms tendsto_variable_fixedPacket_rescaled_energy
#print axioms tendsto_harmonicCentered_fixedPacket_Jordan_energy
#print axioms tendsto_harmonicCentered_fixedPacket_raw_energy_div_overlap
#print axioms eventually_harmonicCentered_fixedPacket_energy_pos

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
