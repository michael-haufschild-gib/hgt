import GaloisForLFunctions.HTGeometry.BesselOrderDifferentialRelation
import GaloisForLFunctions.HTGeometry.BesselOrderGaloisScalingContradiction
import GaloisForLFunctions.HTGeometry.BesselOrderPhysicalScan

/-!
# Modified-Bessel order and intensity hypertranscendence

The relation-adapted parameterized Picard--Vessiot quotient, its full determinant-one Galois
closure, unconditional comparison-basis independence, and scalar-orbit contradiction close the
order-variable theorem.  The existing quartic intensity recovery and physical-scan transfer then
give the intensity and calibrated extremal-radiation conclusions.
-/

namespace GaloisForLFunctions.HTGeometry.BesselDifferentialClosure

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

/-- For every positive argument, the modified Bessel function is hypertranscendental in its order.
-/
theorem hypertranscendental_modifiedBesselKOrder :
    ∀ s : ℝ, 0 < s → Hypertranscendental (modifiedBesselKOrder s) := by
  intro s hs hDA
  obtain ⟨P, hPne, hPrel⟩ :=
    exists_nonzero_besselScalarRelation_of_differentiallyAlgebraic s hs hDA
  obtain ⟨data, hPmem⟩ :=
    exists_besselOrderParameterizedPVData_containing_relation s hs P hPrel
  exact false_of_besselRelation s hs P hPne data hPmem

/-- For every positive argument, the reflected modified-Bessel intensity is hypertranscendental in
its order. -/
theorem hypertranscendental_modifiedBesselOrderIntensity :
    ∀ s : ℝ, 0 < s → Hypertranscendental (modifiedBesselOrderIntensity s) := by
  intro s hs
  exact hypertranscendental_modifiedBesselOrderIntensity_of_order s hs
    (hypertranscendental_modifiedBesselKOrder s hs)

/-- Good's calibrated extremal Bessel intensity scan is hypertranscendental for all positive
physical scales. -/
theorem hypertranscendental_extremalBesselIntensityScan :
    ∀ kappa s : ℝ, 0 < kappa → 0 < s →
      Hypertranscendental (extremalBesselIntensityScan kappa s) := by
  intro kappa s hkappa hs
  exact hypertranscendental_extremalBesselIntensityScan_of_intensity hkappa hs
    (hypertranscendental_modifiedBesselOrderIntensity s hs)

end

end GaloisForLFunctions.HTGeometry.BesselDifferentialClosure
