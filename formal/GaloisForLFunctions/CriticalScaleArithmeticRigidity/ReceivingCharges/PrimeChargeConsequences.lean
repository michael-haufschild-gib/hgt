import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeCompleteEnergy
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheTiltedSplineKeepsAGammaReserveAtEveryOverlap

/-!
# Complete physical energy does not control receiving charge

The explicit neutral coherent family keeps charge one while adjunction
energy, physical input and the absolute complete physical energy all tend
to zero. No fixed linear combination of those three costs bounds its charge.
The raw complete-energy limit remains a nonzero conductor-scale invariant.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  SelectiveMultiscaleArithmeticPositivity SpacingScaleHarmonicAnalysis

private theorem charge_tilted_nonneg (u : ℝ) : 0 ≤ tiltedUnitSpline u := by
  unfold tiltedUnitSpline atomDilate
  exact BiScaleUncertainty.ChebyshevGauge.splineProbe_nonneg _

/-- The literal tilted-spline form retains the raw scale invariant and erases the physical energy. -/
theorem tiltedPrimeCharge_polynomial_energy {K : ℝ} (hK : 0 < K)
    {a d : ℕ} (ha : 0 < a) (had : a ≤ d) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      completeWeilEnergy tiltedUnitSpline
        (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
        (packetVector (normalizedConductorPacket (X ^ a)
          (harmonicPrimeChargeCoefficients (X ^ a) (X ^ d) t)) (X ^ d)))
      atTop (𝓝 (t ^ 2 * ((d : ℝ) / a - 1 / 2))) ∧
    Tendsto (fun X : ℕ =>
      completeWeilEnergy tiltedUnitSpline
        (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) (X ^ d)
        (harmonicPrimeChargeVector (X ^ a) (X ^ d) t)) atTop (𝓝 0) :=
  ⟨tendsto_harmonicPrimeCharge_polynomial_complete_energy
    contDiff_tiltedUnitSpline charge_tilted_nonneg tiltedUnitSpline_eq_zero
    integral_tiltedUnitSpline_sq_pos hK ha had t,
   tendsto_harmonicPrimeCharge_polynomial_physical_energy
    contDiff_tiltedUnitSpline charge_tilted_nonneg tiltedUnitSpline_eq_zero
    integral_tiltedUnitSpline_sq_pos hK ha had t⟩

/-- Even the sum of all three physical costs fails to bound the exact receiving charge. -/
theorem no_receiving_charge_bound_by_complete_physical_cost {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) :
    ¬ ∃ C : ℝ, ∀ (Q N : ℕ) (a : ℕ → ℝ), 2 ≤ Q → Q ≤ N →
      SelectiveMultiscaleArithmeticPositivity.harmonicSum N (conductorHorizonProfile Q a) = 0 →
      packetMean Q (arithmeticPrimeGenerator Q a) ^ 2 ≤
        C * (primeAdjunctionMass Q a +
          ‖(Real.sqrt (Real.log N))⁻¹ • packetVector (normalizedConductorPacket Q a) N‖ ^ 2 +
          |completeWeilEnergy φ (2 * K * Real.log N ^ (1 / 8 : ℝ)) N
            ((Real.sqrt (Real.log N))⁻¹ • packetVector (normalizedConductorPacket Q a) N)|) := by
  rintro ⟨C, hC⟩
  have hA := tendsto_harmonicPrimeCharge_polynomial_adjunction (a := 2) (by omega) 40 1
  have hV := tendsto_harmonicPrimeCharge_polynomial_physical_norm_sq
    (a := 2) (d := 40) (by omega) (by omega) 1
  have hE := (tendsto_harmonicPrimeCharge_polynomial_physical_energy
    hφ hφ0 hsupp hM hK (a := 2) (d := 40) (by omega) (by omega) 1).abs
  have hlim := ((hA.add hV).add hE).const_mul C
  simp only [abs_zero, add_zero, mul_zero] at hlim
  have hbad : (1 : ℝ) ≤ 0 := ge_of_tendsto hlim (by
    filter_upwards [eventually_ge_atTop 2] with X hX
    have hQ : 2 ≤ X ^ 2 := hX.trans (Nat.le_pow (by omega : 0 < 2))
    have hQN : X ^ 2 ≤ X ^ 40 := Nat.pow_le_pow_right (by omega) (by omega)
    have hN : 1 ≤ X ^ 40 := Nat.one_le_pow 40 X (by omega)
    have hcharge := harmonicPrimeCharge_charge_and_adjunction hQ hN (1 : ℝ)
    have h := hC (X ^ 2) (X ^ 40) (harmonicPrimeChargeCoefficients (X ^ 2) (X ^ 40) 1)
      hQ hQN hcharge.1
    rw [hcharge.2.1, one_pow] at h
    exact h)
  norm_num at hbad

/-- The obstruction holds for the concrete complete Weil family without an analytic premise. -/
theorem tiltedPrimeCharge_has_no_complete_physical_cost_bound {K : ℝ} (hK : 0 < K) :
    ¬ ∃ C : ℝ, ∀ (Q N : ℕ) (a : ℕ → ℝ), 2 ≤ Q → Q ≤ N →
      SelectiveMultiscaleArithmeticPositivity.harmonicSum N (conductorHorizonProfile Q a) = 0 →
      packetMean Q (arithmeticPrimeGenerator Q a) ^ 2 ≤
        C * (primeAdjunctionMass Q a +
          ‖(Real.sqrt (Real.log N))⁻¹ • packetVector (normalizedConductorPacket Q a) N‖ ^ 2 +
          |completeWeilEnergy tiltedUnitSpline (2 * K * Real.log N ^ (1 / 8 : ℝ)) N
            ((Real.sqrt (Real.log N))⁻¹ • packetVector (normalizedConductorPacket Q a) N)|) :=
  no_receiving_charge_bound_by_complete_physical_cost
    contDiff_tiltedUnitSpline charge_tilted_nonneg tiltedUnitSpline_eq_zero
    integral_tiltedUnitSpline_sq_pos hK

#print axioms no_receiving_charge_bound_by_complete_physical_cost
#print axioms tiltedPrimeCharge_polynomial_energy
#print axioms tiltedPrimeCharge_has_no_complete_physical_cost_bound

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
