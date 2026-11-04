import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CommonPrimeFibreAdjunction
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CommonPrimeFibreSignedReceiver
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeConsequences
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeFullHorizon

/-!
# Simultaneous receiving coordinates in the literal complete Weil form

A factorial common exclusion realizes arbitrary charges in every conductor
through a prescribed bound. At cutoff `R! X²` and horizon `X⁴⁰`, adjunction,
physical input and complete physical energy vanish, while the exact
complementary terminal receiver reads each coordinate with factor `1/80`.
The atom is the concrete tilted spline throughout.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  SelectiveMultiscaleArithmeticPositivity SpacingScaleHarmonicAnalysis CompletedArithmeticForms

private theorem receiving_tilted_nonneg (u : ℝ) : 0 ≤ tiltedUnitSpline u := by
  unfold tiltedUnitSpline atomDilate
  exact BiScaleUncertainty.ChebyshevGauge.splineProbe_nonneg _

private theorem receiving_factorial_modes (R : ℕ) :
    ∀ m ∈ Icc 1 R, 0 < m ∧ m ∣ R.factorial := by
  intro m hm
  obtain ⟨hm0, hmR⟩ := mem_Icc.mp hm
  exact ⟨hm0, Nat.dvd_factorial hm0 hmR⟩

/-- Coefficients carrying all prescribed charges through conductor `R`. -/
def simultaneousReceivingCoefficients (R X : ℕ) (t : ℕ → ℝ) : ℕ → ℝ :=
  commonPrimeFibreCoefficients (Icc 1 R) R.factorial (X ^ 2) (X ^ 40) t

/-- The physical packet with its exact global harmonic centering. -/
def simultaneousReceivingPacket (R X : ℕ) (t : ℕ → ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex (X ^ 40)) :=
  commonPrimeFibreVector (Icc 1 R) R.factorial (X ^ 2) (X ^ 40) t

/-- Every prescribed coordinate and harmonic neutrality hold exactly on all sufficiently large horizons. -/
theorem eventually_simultaneousReceiving_coordinates (R : ℕ) (t : ℕ → ℝ) :
    ∀ᶠ X : ℕ in atTop,
      harmonicSum (X ^ 40) (conductorHorizonProfile (R.factorial * X ^ 2)
        (simultaneousReceivingCoefficients R X t)) = 0 ∧
      ∀ m ∈ Icc 1 R,
        packetMean (R.factorial * X ^ 2) (fun n =>
          arithmeticPrimeGenerator (R.factorial * X ^ 2)
            (simultaneousReceivingCoefficients R X t) n * normalizedRamanujanMode m n) = t m := by
  have hX2 : Tendsto (fun X : ℕ => X ^ 2) atTop atTop := tendsto_pow_atTop (by omega)
  have hB := (fibreScale_tendsto_atTop (Nat.factorial_pos R)).comp hX2
  filter_upwards [eventually_ge_atTop 1, hB.eventually_gt_atTop 0] with X hX hb
  refine ⟨commonPrimeFibre_neutral (Nat.factorial_pos R) (Nat.one_le_pow 2 X hX)
    (Nat.one_le_pow 40 X hX) (Icc 1 R) t, ?_⟩
  intro m hm
  simpa only [simultaneousReceivingCoefficients, if_pos hm] using
    commonPrimeFibre_receiving_coordinates (Nat.factorial_pos R)
    (receiving_factorial_modes R m hm).1 (receiving_factorial_modes R m hm).2
      (Icc 1 R) (receiving_factorial_modes R) (X ^ 40) t hb

/-- Every prescribed finite charge vector has adjunction tending to zero. -/
theorem tendsto_simultaneousReceiving_adjunction (R : ℕ) (t : ℕ → ℝ) :
    Tendsto (fun X : ℕ => primeAdjunctionMass (R.factorial * X ^ 2)
      (simultaneousReceivingCoefficients R X t)) atTop (𝓝 0) :=
  tendsto_commonPrimeFibre_adjunction (Nat.factorial_pos R) (Icc 1 R)
    (receiving_factorial_modes R) t (by omega : 0 < 2) 40

/-- The physical input of the prescribed finite charge vector tends to zero. -/
theorem tendsto_simultaneousReceiving_input_sq (R : ℕ) (t : ℕ → ℝ) :
    Tendsto (fun X : ℕ => ‖simultaneousReceivingPacket R X t‖ ^ 2) atTop (𝓝 0) := by
  have hX40 : Tendsto (fun X : ℕ => X ^ 40) atTop atTop := tendsto_pow_atTop (by omega)
  have h := (tendsto_commonPrimeFibre_input_norm_sq (Nat.factorial_pos R)
    (Icc 1 R) (receiving_factorial_modes R) t (a := 2) (d := 40) (by omega) (by omega)).div_atTop
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hX40)
  simp only [Function.comp_apply] at h
  convert h using 1
  funext X
  rw [simultaneousReceivingPacket, commonPrimeFibreVector, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, inv_pow,
    Real.sq_sqrt (Real.log_natCast_nonneg (X ^ 40))]
  ring

/-- The complete raw energy reads the Euclidean square of the receiving vector. -/
theorem tendsto_simultaneousReceiving_raw_energy {K : ℝ} (hK : 0 < K)
    (R : ℕ) (t : ℕ → ℝ) :
    Tendsto (fun X : ℕ =>
      completeWeilEnergy tiltedUnitSpline (2 * K * Real.log (X ^ 40 : ℕ) ^ (1 / 8 : ℝ)) (X ^ 40)
        (packetVector (normalizedConductorPacket (R.factorial * X ^ 2)
          (simultaneousReceivingCoefficients R X t)) (X ^ 40)))
      atTop (𝓝 ((∑ m ∈ Icc 1 R, t m ^ 2) * (39 / 2 : ℝ))) := by
  simpa only [simultaneousReceivingCoefficients, Nat.cast_ofNat,
    show (40 : ℝ) / 2 - 1 / 2 = 39 / 2 by norm_num] using
    tendsto_commonPrimeFibre_complete_energy contDiff_tiltedUnitSpline
    receiving_tilted_nonneg tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hK
      (Nat.factorial_pos R) (Icc 1 R) (receiving_factorial_modes R) t
        (a := 2) (d := 40) (by omega) (by omega)

/-- The literal complete physical energy vanishes at every positive critical multiple. -/
theorem tendsto_simultaneousReceiving_complete_energy {K : ℝ} (hK : 0 < K)
    (R : ℕ) (t : ℕ → ℝ) :
    Tendsto (fun X : ℕ =>
      completeWeilEnergy tiltedUnitSpline (2 * K * Real.log (X ^ 40 : ℕ) ^ (1 / 8 : ℝ)) (X ^ 40)
        (simultaneousReceivingPacket R X t)) atTop (𝓝 0) :=
  tendsto_commonPrimeFibre_physical_energy contDiff_tiltedUnitSpline
    receiving_tilted_nonneg tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hK
      (Nat.factorial_pos R) (Icc 1 R) (receiving_factorial_modes R) t
        (a := 2) (d := 40) (by omega) (by omega)

/-- Every fixed receiving mode has the prescribed signed limit, zero outside the chosen finite vector. -/
theorem tendsto_simultaneousReceiving_signed_pairing {K : ℝ} (hK : 0 < K)
    (R : ℕ) (t : ℕ → ℝ) (l : ℕ+) :
    Tendsto (fun X : ℕ =>
      ⟪Matrix.toEuclideanLin
          (completeWeilMatrix tiltedUnitSpline
            (2 * K * Real.log (X ^ 40 : ℕ) ^ (1 / 8 : ℝ)) (X ^ 40))
          (simultaneousReceivingPacket R X t),
        fibreChargeTerminalReceiver l R.factorial X⟫)
      atTop (𝓝 (if (l : ℕ) ≤ R then t l / 80 else 0)) := by
  have hl1 : 1 ≤ (l : ℕ) := l.property
  have hmem : (l : ℕ) ∈ Icc 1 R ↔ (l : ℕ) ≤ R := by
    simp only [mem_Icc, hl1, true_and]
  simp only [simultaneousReceivingPacket, ← hmem]
  exact tendsto_commonPrimeFibre_complete_terminalReceiver contDiff_tiltedUnitSpline
      receiving_tilted_nonneg tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hK
        (Nat.factorial_pos R) l.property (Icc 1 R) (receiving_factorial_modes R) t

/-- The same literal receivers stay in the full common conductor complement and retain positive norm. -/
theorem simultaneousReceiving_receiver_geometry (R : ℕ) (l : ℕ+) :
    (∀ X : ℕ, fibreChargeTerminalReceiver l R.factorial X ∈
      (conductorSubspace (R.factorial * X ^ 2) (X ^ 40))ᗮ) ∧
    Tendsto (fun X : ℕ => ‖fibreChargeTerminalReceiver l R.factorial X‖ ^ 2)
      atTop (𝓝 (1 / 20 : ℝ)) :=
  ⟨fun X => fibreChargeTerminalReceiver_mem l R.factorial X,
    tendsto_fibreChargeTerminalReceiver_norm_sq l.property (Nat.factorial_pos R)⟩

#print axioms eventually_simultaneousReceiving_coordinates
#print axioms tendsto_simultaneousReceiving_adjunction
#print axioms tendsto_simultaneousReceiving_input_sq
#print axioms tendsto_simultaneousReceiving_raw_energy
#print axioms tendsto_simultaneousReceiving_complete_energy
#print axioms tendsto_simultaneousReceiving_signed_pairing
#print axioms simultaneousReceiving_receiver_geometry

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
