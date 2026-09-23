import GaloisForLFunctions.HTGeometry.StokesResistance.MirrorSymmetricResponse
import GaloisForLFunctions.HTGeometry.RepresentationFracture

/-!
# Mirror-response fracture in continuous representation families

The corpus's representation-fracture theorem says the character of an involution cannot vary in a
continuous family on a fixed carrier. Moreau's mirror-fixed reciprocal-response dimension depends
only on carrier dimension and the square of that character. Therefore the response dimension also
cannot jump.
-/

open scoped Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry.StokesResistance

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Mirror-compatible reciprocal-response dimension is constant along continuous involutions. -/
theorem continuous_mirrorSymmetricResponse_finrank_constant
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (A : X → Matrix n n ℂ) (hA : Continuous A)
    (hinvolution : ∀ x, A x * A x = 1) (x y : X) :
    Module.finrank ℂ
        (LinearMap.range (mirrorSymmetricResponseProjection (A x)).toLin') =
      Module.finrank ℂ
        (LinearMap.range (mirrorSymmetricResponseProjection (A y)).toLin') := by
  have htrace := GaloisForLFunctions.HTGeometry.continuous_involution_trace_constant
    A hA hinvolution x y
  have hx := trace_mirrorSymmetricResponseProjection_eq_finrank (A x) (hinvolution x)
  have hy := trace_mirrorSymmetricResponseProjection_eq_finrank (A y) (hinvolution y)
  have hcast :
      (Module.finrank ℂ
          (LinearMap.range (mirrorSymmetricResponseProjection (A x)).toLin') : ℂ) =
        (Module.finrank ℂ
          (LinearMap.range (mirrorSymmetricResponseProjection (A y)).toLin') : ℂ) := by
    calc
      _ = Matrix.trace (mirrorSymmetricResponseProjection (A x)) := hx.symm
      _ = ((Fintype.card n : ℂ) ^ (2 : ℕ) + 2 * Fintype.card n +
          Matrix.trace (A x) ^ (2 : ℕ)) / 4 :=
        trace_mirrorSymmetricResponseProjection (A x) (hinvolution x)
      _ = ((Fintype.card n : ℂ) ^ (2 : ℕ) + 2 * Fintype.card n +
          Matrix.trace (A y) ^ (2 : ℕ)) / 4 := by rw [htrace]
      _ = Matrix.trace (mirrorSymmetricResponseProjection (A y)) :=
        (trace_mirrorSymmetricResponseProjection (A y) (hinvolution y)).symm
      _ = _ := hy
  exact_mod_cast hcast

/-- The same rigidity for an order-two element in a continuous representation family. -/
theorem continuous_representation_mirrorResponse_finrank_constant
    {X G : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Monoid G]
    (rho : X → G →* Matrix n n ℂ) (z : G) (hz : z * z = 1)
    (hrho : Continuous fun x => rho x z) (x y : X) :
    Module.finrank ℂ
        (LinearMap.range
          (mirrorSymmetricResponseProjection (rho x z)).toLin') =
      Module.finrank ℂ
        (LinearMap.range
          (mirrorSymmetricResponseProjection (rho y z)).toLin') := by
  apply continuous_mirrorSymmetricResponse_finrank_constant
    (fun w => rho w z) hrho
  intro w
  rw [← map_mul, hz, map_one]

end GaloisForLFunctions.HTGeometry.StokesResistance
