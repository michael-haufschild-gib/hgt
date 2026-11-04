import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeBandDistributions

/-!
# Arbitrarily small raw complete energy at fixed receiving charge

Dyadic bands approaching the terminal prime scale each have cofactor cost
`3/2`. Dividing charge equally among `M` disjoint bands gives complete energy
`3t²/(2M)`, while the input and adjunction mass vanish.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory SelectiveMultiscaleArithmeticPositivity
  RenormalizedArithmeticPotentialTheory

def primeChargeDyadicHorizon (M : ℕ) : ℕ := 2 ^ (M + 1)

def primeChargeDyadicLower (M i : ℕ) : ℕ := primeChargeDyadicHorizon M - 2 ^ (i + 1)

def primeChargeDyadicUpper (M i : ℕ) : ℕ := primeChargeDyadicHorizon M - 2 ^ i

private theorem dyadic_band_geometry {M i : ℕ} (hi : i ∈ range M) :
    0 < primeChargeDyadicLower M i ∧
    primeChargeDyadicLower M i < primeChargeDyadicUpper M i ∧
    primeChargeDyadicUpper M i ≤ primeChargeDyadicHorizon M := by
  have hiM := mem_range.mp hi
  have hbig : 2 ^ (i + 1) < 2 ^ (M + 1) :=
    Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega)
  have hstep : 2 ^ i < 2 ^ (i + 1) :=
    Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega)
  dsimp only [primeChargeDyadicLower, primeChargeDyadicUpper, primeChargeDyadicHorizon]
  omega

private theorem dyadic_bands_disjoint {M i j : ℕ} (hij : i ≠ j) :
    primeChargeDyadicUpper M i ≤ primeChargeDyadicLower M j ∨
    primeChargeDyadicUpper M j ≤ primeChargeDyadicLower M i := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · right
    have hp : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    dsimp only [primeChargeDyadicUpper, primeChargeDyadicLower]
    omega
  · left
    have hp : 2 ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    dsimp only [primeChargeDyadicUpper, primeChargeDyadicLower]
    omega

private theorem dyadic_band_cost {M i : ℕ} (hi : i ∈ range M) (s : ℝ) :
    s ^ 2 * ((primeChargeDyadicHorizon M : ℝ) -
      ((primeChargeDyadicLower M i : ℝ) + primeChargeDyadicUpper M i) / 2) /
        ((primeChargeDyadicUpper M i : ℝ) - primeChargeDyadicLower M i) = 3 * s ^ 2 / 2 := by
  have hiM := mem_range.mp hi
  have h1 : 2 ^ (i + 1) ≤ primeChargeDyadicHorizon M :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h0 : 2 ^ i ≤ primeChargeDyadicHorizon M :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hp : (2 : ℝ) ^ i ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [primeChargeDyadicLower, primeChargeDyadicUpper, Nat.cast_sub h1,
    Nat.cast_sub h0, Nat.cast_pow, Nat.cast_ofNat]
  simp only [pow_succ]
  rw [show (primeChargeDyadicHorizon M : ℝ) - 2 ^ i -
    ((primeChargeDyadicHorizon M : ℝ) - 2 ^ i * 2) = 2 ^ i by ring]
  field_simp [hp]
  ring

/-- An exactly charged neutral distribution with `M` limiting terminal dyadic bands. -/
def primeChargeDyadicCoefficients (M X : ℕ) (t : ℝ) : ℕ → ℝ :=
  primeChargeBandDistributionCoefficients (range M) (primeChargeDyadicLower M)
    (primeChargeDyadicUpper M) (fun _ => t / M) (primeChargeDyadicHorizon M) X

/-- Equal division among dyadic bands keeps the total receiving charge exact. -/
theorem primeChargeDyadic_receiving_charge {M X : ℕ} (hM : 0 < M) (hX : 2 ≤ X) (t : ℝ) :
    packetMean (X ^ primeChargeDyadicHorizon M)
      (arithmeticPrimeGenerator (X ^ primeChargeDyadicHorizon M)
        (primeChargeDyadicCoefficients M X t)) = t := by
  rw [primeChargeDyadicCoefficients, primeChargeBandDistribution_receiving_charge
    _ _ _ _ hX (fun i hi => (dyadic_band_geometry hi).1)
    (fun i hi => (dyadic_band_geometry hi).2.1)
    (fun i hi => (dyadic_band_geometry hi).2.2)]
  simp only [sum_const, card_range, nsmul_eq_mul]
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp [hMR]

/-- Dyadic charge distributions are exactly harmonic-pole neutral. -/
theorem primeChargeDyadic_neutral (M : ℕ) {X : ℕ} (hX : 1 ≤ X) (t : ℝ) :
    harmonicSum (X ^ primeChargeDyadicHorizon M)
      (conductorHorizonProfile (X ^ primeChargeDyadicHorizon M)
        (primeChargeDyadicCoefficients M X t)) = 0 :=
  primeChargeBandDistribution_neutral _ _ _ _ _ hX

/-- Raw input norm and adjunction mass vanish at every fixed finite dyadic distribution. -/
theorem primeChargeDyadic_small_inputs (M : ℕ) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      ‖packetVector (normalizedConductorPacket (X ^ primeChargeDyadicHorizon M)
        (primeChargeDyadicCoefficients M X t)) (X ^ primeChargeDyadicHorizon M)‖) atTop (𝓝 0) ∧
    Tendsto (fun X : ℕ => primeAdjunctionMass (X ^ primeChargeDyadicHorizon M)
      (primeChargeDyadicCoefficients M X t)) atTop (𝓝 0) :=
  primeChargeBandDistribution_small_inputs _ _ _ _
    (fun _ hi => (dyadic_band_geometry hi).1)
    (fun _ hi => (dyadic_band_geometry hi).2.1)
    (fun _ hi => (dyadic_band_geometry hi).2.2)

/-- The complete raw energy of `M` equal dyadic charges is exactly `3t²/(2M)` in the limit. -/
theorem tendsto_primeChargeDyadic_complete_energy {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hA : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {M : ℕ} (hM : 0 < M) (t : ℝ) :
    Tendsto (fun X : ℕ => completeWeilEnergy φ
      (2 * K * Real.log (X ^ primeChargeDyadicHorizon M : ℕ) ^ (1 / 8 : ℝ))
      (X ^ primeChargeDyadicHorizon M)
      (packetVector (normalizedConductorPacket (X ^ primeChargeDyadicHorizon M)
        (primeChargeDyadicCoefficients M X t)) (X ^ primeChargeDyadicHorizon M)))
      atTop (𝓝 (3 * t ^ 2 / (2 * M))) := by
  have h := tendsto_primeChargeBandDistribution_complete_energy hφ hφ0 hsupp hA hK
    (range M) (primeChargeDyadicLower M) (primeChargeDyadicUpper M) (fun _ => t / M)
    (fun i hi => (dyadic_band_geometry hi).1)
    (fun i hi => (dyadic_band_geometry hi).2.1)
    (fun i hi => (dyadic_band_geometry hi).2.2)
    (fun i _ j _ hij => dyadic_bands_disjoint hij)
  have hc : (∑ i ∈ range M, (t / (M : ℝ)) ^ 2 *
      ((primeChargeDyadicHorizon M : ℝ) -
        ((primeChargeDyadicLower M i : ℝ) + primeChargeDyadicUpper M i) / 2) /
          ((primeChargeDyadicUpper M i : ℝ) - primeChargeDyadicLower M i)) =
      3 * t ^ 2 / (2 * M) := by
    rw [sum_congr rfl (fun i hi => dyadic_band_cost hi (t / M))]
    simp only [sum_const, card_range, nsmul_eq_mul]
    have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    field_simp [hMR]
  rw [hc] at h
  exact h

#print axioms primeChargeDyadic_receiving_charge
#print axioms primeChargeDyadic_small_inputs
#print axioms tendsto_primeChargeDyadic_complete_energy

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
