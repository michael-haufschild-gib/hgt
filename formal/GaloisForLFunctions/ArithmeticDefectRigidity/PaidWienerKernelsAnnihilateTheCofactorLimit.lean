import GaloisForLFunctions.ArithmeticDefectRigidity.TheCofactorLimitIsAWienerModule
import GaloisForLFunctions.ArithmeticDefectRigidity.WienerCovariancesFollowTheCommonCofactorLimit

/-!
# Paid Wiener kernels annihilate the actual cofactor module

Scalar covariance convergence identifies the source convolution with the completed
Wiener action. On escape, the full paid ideal annihilates the cyclic module, whose
nonempty hull lies in the source obstruction hull.
-/

noncomputable section
set_option autoImplicit false


open Finset Filter Topology RHTower
open scoped InnerProductSpace ComplexConjugate
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.HTGeometry
open WienerAlgebraAt

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

/-- A coordinate of the cyclic Wiener action is a continuous linear functional. -/
def wienerCoordinate {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (j : ℕ+) : WienerAlgebraAt (1 / 2) →L[ℂ] ℂ :=
  (innerSL ℂ (vector L j)).comp
    ((ContinuousLinearMap.apply ℂ (Hilbert L) (vector L 1)).comp (wienerLinear L))

theorem wienerCoordinate_apply {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (j : ℕ+)
    (a : WienerAlgebraAt (1 / 2)) :
    wienerCoordinate L j a = ⟪vector L j, wienerRepresentation L a (vector L 1)⟫_ℂ := rfl

theorem wienerCoordinate_pointMass {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (j : ℕ+) (n : ℕ) :
    wienerCoordinate L j (pointMass n) =
      if hn : 0 < n then (kernel L ⟨n, hn⟩ j : ℂ) else 0 := by
  rw [wienerCoordinate_apply]
  have hpoint : wienerRepresentation L (pointMass n) = naturalDilation L n :=
    sequenceExtension_pointMass (naturalDilation L) (naturalDilation_zero L)
      (norm_naturalDilation_le L) n
  rw [hpoint]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [naturalDilation_zero, dif_neg (Nat.not_lt_zero 0)]
    simp only [zero_apply, inner_zero_right]
  · rw [naturalDilation_pos L n hn, dilation_vector, mul_one, inner_vector, dif_pos hn]

/-- The cyclic action and the limiting covariance series are the same functional. -/
theorem wienerCoordinate_eq_tsum {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (j : ℕ+)
    (a : WienerAlgebraAt (1 / 2)) :
    wienerCoordinate L j a =
      ∑' n, a.toFn n * (if hn : 0 < n then (kernel L ⟨n, hn⟩ j : ℂ) else 0) := by
  have h := (wienerCoordinate L j).hasSum (hasSum_pointMass a)
  simp only [map_smul, wienerCoordinate_pointMass, smul_eq_mul] at h
  exact h.tsum_eq.symm

/-- Full Wiener covariances converge to the completed module coordinates. -/
theorem wienerCofactorCovariance_tendsto_coordinate {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (a : WienerAlgebraAt (1 / 2)) (j : ℕ+) :
    Tendsto (fun m => wienerCofactorCovariance ε (subsequence L m) j a) atTop
      (𝓝 (wienerCoordinate L j a)) := by
  rw [wienerCoordinate_eq_tsum]
  exact wienerCofactorCovariance_tendsto ε (subsequence L) (kernel L)
    L.converges a j

/-- Orthogonality to every cofactor coordinate kills a vector in the Gram completion. -/
theorem eq_zero_of_inner_vectors_eq_zero {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (w : Hilbert L)
    (hw : ∀ j : ℕ+, ⟪vector L j, w⟫_ℂ = 0) : w = 0 := by
  have hL : innerSL ℂ w = 0 := by
    apply KernelHilbert.ext_on_vectors (complexKernel L)
    intro j
    change ⟪w, vector L j⟫_ℂ = 0
    exact inner_eq_zero_symm.mp (hw j)
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  exact congrArg (fun L : Hilbert L →L[ℂ] ℂ => L w) hL

/-- On escape every paid Wiener kernel annihilates the full cyclic module,
including kernels with infinite support. -/
theorem admits_or_paidIdeal_le_annihilator {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    Admits dampedMobiusEnergy ε ∨
      paidIdeal (pmPowerDampedRealWeight ε)
        (TransHorizonIncidenceMechanics.summable_abs_pmPowerDamped_div ε.property.1) ≤
          annihilator L := by
  rcases admits_or_paid_wienerCofactorCovariance_vanishes ε with h | h
  · exact Or.inl h
  · refine Or.inr fun a ha => (mem_annihilator_iff L a).mpr ?_
    apply eq_zero_of_inner_vectors_eq_zero L
    intro j
    change wienerCoordinate L j a = 0
    exact tendsto_nhds_unique (wienerCofactorCovariance_tendsto_coordinate L a j)
      ((h a ha j).comp L.strictMono.tendsto_atTop)

/-- The actual escape-module hull is contained in the repairing-ideal hull. -/
theorem admits_or_moduleHull_subset_obstructionHull {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    Admits dampedMobiusEnergy ε ∨
      moduleHull L ⊆ obstructionHull (pmPowerDampedRealWeight ε)
        (TransHorizonIncidenceMechanics.summable_abs_pmPowerDamped_div ε.property.1) := by
  rcases admits_or_paidIdeal_le_annihilator L with h | h
  · exact Or.inl h
  · exact Or.inr fun ω hω a ha => hω a (h ha)

/-- Every escaping receiver produces a nonempty spectral subhull of its obstruction hull. -/
theorem admits_or_moduleHull_nonempty_subset {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    Admits dampedMobiusEnergy ε ∨
      (moduleHull L).Nonempty ∧
        moduleHull L ⊆ obstructionHull (pmPowerDampedRealWeight ε)
          (TransHorizonIncidenceMechanics.summable_abs_pmPowerDamped_div ε.property.1) := by
  rcases admits_or_moduleHull_subset_obstructionHull L with h | h
  · exact Or.inl h
  · exact Or.inr ⟨moduleHull_nonempty L, h⟩


end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

namespace GaloisForLFunctions.ArithmeticDefectRigidity.CofactorLimit

abbrev wienerCoordinate (ε : SubcriticalDamping) (j : ℕ+) : WienerAlgebraAt (1 / 2) →L[ℂ] ℂ :=
  ActualCofactorLimit.wienerCoordinate (ActualCofactorLimit.chosen ε) j

theorem wienerCoordinate_apply (ε : SubcriticalDamping) (j : ℕ+)
    (a : WienerAlgebraAt (1 / 2)) :
    wienerCoordinate ε j a = ⟪vector ε j, wienerRepresentation ε a (vector ε 1)⟫_ℂ :=
  ActualCofactorLimit.wienerCoordinate_apply (ActualCofactorLimit.chosen ε) j a

theorem wienerCoordinate_pointMass (ε : SubcriticalDamping) (j : ℕ+) (n : ℕ) :
    wienerCoordinate ε j (pointMass n) =
      if hn : 0 < n then (kernel ε ⟨n, hn⟩ j : ℂ) else 0 :=
  ActualCofactorLimit.wienerCoordinate_pointMass (ActualCofactorLimit.chosen ε) j n

theorem wienerCoordinate_eq_tsum (ε : SubcriticalDamping) (j : ℕ+)
    (a : WienerAlgebraAt (1 / 2)) :
    wienerCoordinate ε j a =
      ∑' n, a.toFn n * (if hn : 0 < n then (kernel ε ⟨n, hn⟩ j : ℂ) else 0) :=
  ActualCofactorLimit.wienerCoordinate_eq_tsum (ActualCofactorLimit.chosen ε) j a

theorem wienerCofactorCovariance_tendsto_coordinate (ε : SubcriticalDamping)
    (a : WienerAlgebraAt (1 / 2)) (j : ℕ+) :
    Tendsto (fun m => wienerCofactorCovariance ε (subsequence ε m) j a) atTop
      (𝓝 (wienerCoordinate ε j a)) :=
  ActualCofactorLimit.wienerCofactorCovariance_tendsto_coordinate (ActualCofactorLimit.chosen ε) a j

theorem eq_zero_of_inner_vectors_eq_zero (ε : SubcriticalDamping) (w : Hilbert ε)
    (hw : ∀ j : ℕ+, ⟪vector ε j, w⟫_ℂ = 0) : w = 0 :=
  ActualCofactorLimit.eq_zero_of_inner_vectors_eq_zero (ActualCofactorLimit.chosen ε) w hw

theorem admits_or_paidIdeal_le_annihilator (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨
      paidIdeal (pmPowerDampedRealWeight ε)
        (TransHorizonIncidenceMechanics.summable_abs_pmPowerDamped_div ε.property.1) ≤
          annihilator ε :=
  ActualCofactorLimit.admits_or_paidIdeal_le_annihilator (ActualCofactorLimit.chosen ε)

theorem admits_or_moduleHull_subset_obstructionHull (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨
      moduleHull ε ⊆ obstructionHull (pmPowerDampedRealWeight ε)
        (TransHorizonIncidenceMechanics.summable_abs_pmPowerDamped_div ε.property.1) :=
  ActualCofactorLimit.admits_or_moduleHull_subset_obstructionHull (ActualCofactorLimit.chosen ε)

theorem admits_or_moduleHull_nonempty_subset (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨
      (moduleHull ε).Nonempty ∧
        moduleHull ε ⊆ obstructionHull (pmPowerDampedRealWeight ε)
          (TransHorizonIncidenceMechanics.summable_abs_pmPowerDamped_div ε.property.1) :=
  ActualCofactorLimit.admits_or_moduleHull_nonempty_subset (ActualCofactorLimit.chosen ε)

end GaloisForLFunctions.ArithmeticDefectRigidity.CofactorLimit
