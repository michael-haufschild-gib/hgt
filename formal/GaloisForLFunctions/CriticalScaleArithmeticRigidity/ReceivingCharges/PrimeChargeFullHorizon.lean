import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeComplementReceiver
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeCompleteEnergy
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeDefectHasAnExponentialConductorCutoff

/-!
# At the full horizon there is no complementary receiver

Finite Ramanujan inversion spans the entire horizon with conductors through
that horizon. Thus the cutoff-equals-horizon charge family has vanishing
physical complete energy but exactly zero conductor complement. The choice
of cutoff relative to horizon is part of any signed receiving statement.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  CompletedArithmeticForms SelectiveMultiscaleArithmeticPositivity

/-- Finite Ramanujan inversion spans every physical horizon vector above horizon one. -/
theorem mem_full_horizon_conductorSubspace {N : ℕ} (hN : 2 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) : x ∈ conductorSubspace N N := by
  obtain ⟨a, ha⟩ := exists_horizon_normalizedRamanujan_expansion N
    (fun n => Real.sqrt n * primeHorizonExtension x n)
  have he : packetVector (normalizedConductorPacket N a) N = x := by
    rw [← packetVector_sqrt_extension x]
    ext n
    change (∑ m ∈ Icc 1 N, a m * normalizedRamanujanMode m n) / Real.sqrt (n : ℕ) =
      (Real.sqrt (n : ℕ) * primeHorizonExtension x n) / Real.sqrt (n : ℕ)
    rw [ha n n.property]
  rw [← he]
  exact packetVector_conductor_mem hN N a

/-- Conductors through the full horizon have trivial orthogonal complement. -/
theorem full_horizon_conductor_complement_eq_zero {N : ℕ} (hN : 2 ≤ N)
    {x : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hx : x ∈ (conductorSubspace N N)ᗮ) : x = 0 := by
  have h := Submodule.inner_right_of_mem_orthogonal (mem_full_horizon_conductorSubspace hN x) hx
  rw [real_inner_self_eq_norm_sq] at h
  exact norm_eq_zero.mp (by nlinarith only [h, norm_nonneg x])

/-- No complete-form pairing can survive against the full-horizon conductor complement. -/
theorem complete_pairing_full_horizon_complement {N : ℕ} (hN : 2 ≤ N)
    (φ : ℝ → ℝ) (c : ℝ) (x r : EuclideanSpace ℝ (PrimeHorizonIndex N))
    (hr : r ∈ (conductorSubspace N N)ᗮ) :
    ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) x, r⟫ = 0 := by
  rw [full_horizon_conductor_complement_eq_zero hN hr, inner_zero_right]

/-- At equal cutoff and horizon the charge persists, the physical energy vanishes,
and every literal conductor-complement pairing is zero. -/
theorem harmonicPrimeCharge_full_horizon_classification {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) (t : ℝ) :
    Tendsto (fun N : ℕ => completeWeilEnergy φ (2 * K * Real.log N ^ (1 / 8 : ℝ)) N
      (harmonicPrimeChargeVector N N t)) atTop (𝓝 0) ∧
    ∀ N : ℕ, 2 ≤ N →
      packetMean N (arithmeticPrimeGenerator N (harmonicPrimeChargeCoefficients N N t)) = t ∧
      ∀ r : EuclideanSpace ℝ (PrimeHorizonIndex N), r ∈ (conductorSubspace N N)ᗮ →
        ⟪Matrix.toEuclideanLin (completeWeilMatrix φ (2 * K * Real.log N ^ (1 / 8 : ℝ)) N)
          (harmonicPrimeChargeVector N N t), r⟫ = 0 := by
  refine ⟨tendsto_harmonicPrimeChargeVector_complete_energy hφ hφ0 hsupp hM hK t, ?_⟩
  intro N hN
  refine ⟨(harmonicPrimeCharge_charge_and_adjunction hN (by omega) t).2.1, ?_⟩
  intro r hr
  exact complete_pairing_full_horizon_complement hN φ _ _ r hr

#print axioms full_horizon_conductor_complement_eq_zero
#print axioms harmonicPrimeCharge_full_horizon_classification

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
