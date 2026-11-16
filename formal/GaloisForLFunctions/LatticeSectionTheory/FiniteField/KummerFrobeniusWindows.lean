import GaloisForLFunctions.LatticeSectionTheory.HeckeCorrespondencesAreSimilitudesOfThePrimitiveH1
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Zeta.KummerCurveDatum

/-!
# Kummer point counts calibrate Frobenius-window effectivity

The exact extension counts give a unitary curve datum in every
characteristic. The existing Frobenius-window criterion then proves
Hodge index, Künneth effectivity, and nonnegativity of primitive h¹ for
that point-count model, without an assumed positivity input.
-/

noncomputable section
namespace GaloisForLFunctions.LatticeSectionTheory
open ArithmeticCastelnuovoSeveri ArithmeticEffectivityTheory ArithmeticOrientationGeometry
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
local notation "D" => primePowerKummerCurveDatum p d n r

/-- The datum calibrated by actual Kummer extension counts satisfies Hodge index on every window. -/
theorem kummer_pointCount_window_hodgeIndex (W : Finset ℕ) :
    ((D).windowSurface W).HodgeIndex :=
  (D).windowSurface_hodgeIndex_iff_unitary.mpr (primePowerKummerCurveDatum_unitary p d n r) W

/-- The Kummer point-count model satisfies the Künneth Riemann inequality and degree bounds on every window. -/
theorem kummer_pointCount_kunneth_effectivity (W : Finset ℕ) :
    RiemannInequality ((D).windowSurface W) 0 0 (kunnethH0 ((D).windowSurface W)) ∧
      DegreeBounded ((D).windowSurface W) (kunnethH0 ((D).windowSurface W)) :=
  (kunneth_effectivity_iff _).mpr (kummer_pointCount_window_hodgeIndex p d n r W)

/-- The primitive h¹ of the Kummer point-count model is nonnegative on every class and every window. -/
theorem kummer_pointCount_primitiveH1_nonneg (W : Finset ℕ) (x : SpanCycle) :
    0 ≤ primitiveH1 ((D).windowSurface W) x := by
  have h := ((D).windowSurface W).castelnuovoSeveri_iff_defect_nonneg.mp
    (((D).windowSurface W).hodgeIndex_iff_castelnuovoSeveri.mp
      (kummer_pointCount_window_hodgeIndex p d n r W)) x
  rw [primitiveH1_eq]
  linarith only [h]

end GaloisForLFunctions.LatticeSectionTheory
