import GaloisForLFunctions.HTGeometry.GomesTruncatedJetInternalUnits
import GaloisForLFunctions.HTGeometry.GomesTruncatedJetUnitSymmetries
import GaloisForLFunctions.HTGeometry.GomesTruncatedJetSymmetryComparison

/-!
# The invertible symmetries detect the entire joint algebra

The previously constructed order shear is an actual unit. Its membership alone
recovers the clock-power generator, so group inclusion and algebra inclusion
have exactly the same finite-resonance classification.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The universally invertible order shear, packaged as an ambient matrix unit. -/
def gomesTruncatedJetOrderShearUnit (n : ℕ) (z : ℂ) :
    (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ :=
  (gomesTruncatedJetOrderShear_isUnit n z).unit

/-- The packaged unit has the original shear as its underlying matrix. -/
theorem gomesTruncatedJetOrderShearUnit_val (n : ℕ) (z : ℂ) :
    (gomesTruncatedJetOrderShearUnit n z).val = gomesTruncatedJetOrderShear n z :=
  (gomesTruncatedJetOrderShear_isUnit n z).unit_spec

/-- The order shear belongs to the actual gauge group at every phase. -/
theorem gomesTruncatedJetOrderShearUnit_mem (n : ℕ) (z : ℂ) :
    gomesTruncatedJetOrderShearUnit n z ∈ gomesTruncatedJetGaugeGroup n z := by
  rw [gomesTruncatedJetGaugeGroup_mem_iff, gomesTruncatedJetOrderShearUnit_val]
  exact gomesTruncatedJetOrderShear_mem n z

/-- Inclusion of actual invertible symmetries is equivalent to inclusion of the full joint algebras. -/
theorem gomesTruncatedJetGaugeGroup_le_iff_algebra (n : ℕ) (z w : ℂ) :
    gomesTruncatedJetGaugeGroup n z ≤ gomesTruncatedJetGaugeGroup n w ↔
      gomesTruncatedJetJointAlgebra n z ≤ gomesTruncatedJetJointAlgebra n w := by
  constructor
  · intro h
    have hs := h (gomesTruncatedJetOrderShearUnit_mem n z)
    rw [gomesTruncatedJetGaugeGroup_mem_iff, gomesTruncatedJetOrderShearUnit_val] at hs
    have hD : fockShiftMatrix (n + 1) ^ orderOf z ∈ gomesTruncatedJetJointAlgebra n w := by
      simpa only [gomesTruncatedJetOrderShear, add_sub_cancel_left] using
        (gomesTruncatedJetJointAlgebra n w).sub_mem hs (gomesTruncatedJetJointAlgebra n w).one_mem
    rw [gomesTruncatedJetJointAlgebra_eq_adjoin_orderPower n z]
    apply Algebra.adjoin_le
    intro M hM
    obtain rfl := Set.mem_singleton_iff.mp hM
    exact hD
  · intro h u hu
    exact h hu

/-- Equality of actual invertible symmetries remembers exactly the joint algebra. -/
theorem gomesTruncatedJetGaugeGroup_eq_iff_algebra (n : ℕ) (z w : ℂ) :
    gomesTruncatedJetGaugeGroup n z = gomesTruncatedJetGaugeGroup n w ↔
      gomesTruncatedJetJointAlgebra n z = gomesTruncatedJetJointAlgebra n w := by
  rw [le_antisymm_iff, le_antisymm_iff, gomesTruncatedJetGaugeGroup_le_iff_algebra,
    gomesTruncatedJetGaugeGroup_le_iff_algebra]

/-- The finite resonant weights completely classify inclusion between gauge groups. -/
theorem gomesTruncatedJetGaugeGroup_le_iff_weights (n : ℕ) (z w : ℂ) :
    gomesTruncatedJetGaugeGroup n z ≤ gomesTruncatedJetGaugeGroup n w ↔
      ∀ k : Fin (n + 1), orderOf z ∣ k.val → orderOf w ∣ k.val := by
  rw [gomesTruncatedJetGaugeGroup_le_iff_algebra, gomesTruncatedJetJointAlgebra_le_iff_weights]

/-- Two phases give the same invertible symmetries exactly when their finite resonances coincide. -/
theorem gomesTruncatedJetGaugeGroup_eq_iff_weights (n : ℕ) (z w : ℂ) :
    gomesTruncatedJetGaugeGroup n z = gomesTruncatedJetGaugeGroup n w ↔
      ∀ k : Fin (n + 1), orderOf z ∣ k.val ↔ orderOf w ∣ k.val := by
  rw [gomesTruncatedJetGaugeGroup_eq_iff_algebra, gomesTruncatedJetJointAlgebra_eq_iff_weights]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
