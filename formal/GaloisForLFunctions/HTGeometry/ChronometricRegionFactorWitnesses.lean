import GaloisForLFunctions.HTGeometry.ChronometricRegionLocalization

/-!
# Laws that factor through a region exist

Region rigidity assumes a law determined by the chronometric field over one region.  Constant laws
factor through every region, and every law of the restricted field factors through its own region
by construction — which is the general form, since factoring through a region is exactly being a
function of the restriction.
-/

namespace GaloisForLFunctions.HTGeometry

namespace ChronometricMetricField

variable {Event : Type u} {Tangent : Type v} [AddCommGroup Tangent] [Module ℝ Tangent]

/-- A constant law factors through every region. -/
theorem factorsThroughRegion_const {Source : Type w} (W : Set Event) (s : Source) :
    FactorsThroughRegion W (fun _ : ChronometricMetricField Event Tangent => s) :=
  fun _ _ _ => rfl

/-- **Every law of the restricted field factors through its region.** -/
theorem factorsThroughRegion_comp_restrictRegion {Source : Type w} (W : Set Event)
    (F : ChronometricMetricField (W : Type u) Tangent → Source) :
    FactorsThroughRegion W (fun g => F (restrictRegion W g)) := by
  intro g h hgh
  show F (restrictRegion W g) = F (restrictRegion W h)
  rw [hgh]

end ChronometricMetricField

end GaloisForLFunctions.HTGeometry
