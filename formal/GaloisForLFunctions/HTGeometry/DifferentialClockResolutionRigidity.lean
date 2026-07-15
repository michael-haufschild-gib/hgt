import GaloisForLFunctions.HTGeometry.DifferentialClockEmbeddingCovariance
import GaloisForLFunctions.HTGeometry.HypertranscendentalObservableNet

/-!
# Differential reference-frame embeddings preserve clock resolution

A derivation-preserving field embedding carries each finite jet-observable field onto the target
field at the same resolution.  Hypertranscendence makes that resolution rigid: inclusion and
equality of the transported field recover the numerical order of the clock slices.

Thus even an irreversible, one-way change of differential reference frame cannot relabel the
observable clock.  No inverse ambient field map and no temporal evolution are assumed.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {F E L : Type*} [Field F] [Field E] [Field L]
  [Differential E] [Differential L] [Algebra F E] [Algebra F L]

/-- Inclusion of a transported finite observable field in a target clock slice is equivalent to
the corresponding order relation between resolutions. -/
theorem jetObservableField_map_algHom_le_iff_resolution_le
    (e : E →ₐ[F] L) (hderiv : ∀ z : E, e z′ = (e z)′)
    {x : E} (hx : HypertranscendentalOver F x) (M N : ℕ) :
    (jetObservableField F x M).map e ≤ jetObservableField F (e x) N ↔ M ≤ N := by
  rw [jetObservableField_map_algHom e hderiv x M]
  have htarget : HypertranscendentalOver F (e x) :=
    (hypertranscendentalOver_algHom_iff e hderiv x).mpr hx
  exact hypertranscendental_jetObservableField_le_iff htarget M N

/-- **Clock-resolution rigidity under a differential embedding.**  A transported source slice is
equal to a target slice exactly when their resolution indices agree. -/
theorem jetObservableField_map_algHom_eq_iff_resolution_eq
    (e : E →ₐ[F] L) (hderiv : ∀ z : E, e z′ = (e z)′)
    {x : E} (hx : HypertranscendentalOver F x) (M N : ℕ) :
    (jetObservableField F x M).map e = jetObservableField F (e x) N ↔ M = N := by
  rw [jetObservableField_map_algHom e hderiv x M]
  have htarget : HypertranscendentalOver F (e x) :=
    (hypertranscendentalOver_algHom_iff e hderiv x).mpr hx
  exact hypertranscendental_jetObservableField_eq_iff htarget M N

end

end GaloisForLFunctions.HTGeometry
