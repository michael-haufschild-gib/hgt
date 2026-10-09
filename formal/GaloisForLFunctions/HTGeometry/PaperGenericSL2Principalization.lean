import GaloisForLFunctions.HTGeometry.GenericSpecialLinearTorsor
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.BundlePrincipalization

/-!
# Exact ideal certificates in the native generic SL₂ torsor

The source's global Bézout identity principalizes a distinguished pair of
polynomials in the native determinant-one coordinates. The coefficient ring is
arbitrary: the identity also applies in positive characteristic and over rings
with nilpotents.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

variable (k : Type*) [CommRing k]

/-- The source's explicit principal generator in the native torsor algebra. -/
def paperGenericSL2BundleGenerator (u : genericSL k 2) : genericSL k 2 :=
  Bundle.v (torsorMatrix k 2 0 0) (torsorMatrix k 2 1 0) (torsorMatrix k 2 0 1) u

/-- The distinguished two-generator ideal in the native generic SL₂ algebra. -/
def paperGenericSL2BundleIdeal (u : genericSL k 2) : Ideal (genericSL k 2) :=
  Ideal.span {Bundle.f₀ (torsorMatrix k 2 0 0) (torsorMatrix k 2 1 0)
      (torsorMatrix k 2 0 1) (torsorMatrix k 2 1 1) u,
    Bundle.g₀ (torsorMatrix k 2 0 0) (torsorMatrix k 2 1 0)
      (torsorMatrix k 2 0 1) (torsorMatrix k 2 1 1) u}

private theorem native_determinant_relation :
    torsorMatrix k 2 0 0 * torsorMatrix k 2 1 1 -
      torsorMatrix k 2 0 1 * torsorMatrix k 2 1 0 = 1 := by
  simpa [Matrix.det_fin_two] using (det_torsorMatrix (I := k) (N := 2))

/-- Exact principalization, with the determinant condition discharged by the native torsor. -/
theorem paperGenericSL2BundleIdeal_eq_span (u : genericSL k 2) :
    paperGenericSL2BundleIdeal k u = Ideal.span {paperGenericSL2BundleGenerator k u} :=
  Bundle.principalization _ _ _ _ _ (native_determinant_relation k)

/-- An explicit Bézout certificate recovers the generator globally. -/
theorem paperGenericSL2BundleGenerator_bezout (u : genericSL k 2) :
    Bundle.coeffA (torsorMatrix k 2 0 0) (torsorMatrix k 2 1 0) (torsorMatrix k 2 0 1) *
        Bundle.f₀ (torsorMatrix k 2 0 0) (torsorMatrix k 2 1 0)
          (torsorMatrix k 2 0 1) (torsorMatrix k 2 1 1) u +
      Bundle.coeffB (torsorMatrix k 2 0 0) (torsorMatrix k 2 1 0) (torsorMatrix k 2 0 1) u *
        Bundle.g₀ (torsorMatrix k 2 0 0) (torsorMatrix k 2 1 0)
          (torsorMatrix k 2 0 1) (torsorMatrix k 2 1 1) u =
      paperGenericSL2BundleGenerator k u :=
  Bundle.generator_bezout _ _ _ _ _ (native_determinant_relation k)

/-- Ideal membership is exactly divisibility by the displayed polynomial. -/
theorem paperGenericSL2BundleIdeal_mem_iff (u r : genericSL k 2) :
    r ∈ paperGenericSL2BundleIdeal k u ↔ paperGenericSL2BundleGenerator k u ∣ r := by
  rw [paperGenericSL2BundleIdeal_eq_span, Ideal.mem_span_singleton]

end

end GaloisForLFunctions.HTGeometry
