import GaloisForLFunctions.HTGeometry.ABHN.AzumayaScalarExtension
import GaloisForLFunctions.HTGeometry.ABHN.CentralSimpleAzumaya

/-!
# Simplicity after scalar extension

Over a field, an Azumaya algebra is a simple ring.  Combining that fact with arbitrary-base
Azumaya scalar extension gives a direct field-level simplicity theorem without packaging the
algebra first as a central simple algebra.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

/-- Scalar extension of an Azumaya algebra between fields is a simple ring. In particular this
applies to every finite-dimensional central simple algebra. -/
theorem isSimpleRing_scalarExtension {K L A : Type*} [Field K] [Field L] [Algebra K L]
    [Ring A] [Algebra K A] [IsAzumaya K A] : IsSimpleRing (L ⊗[K] A) := by
  letI : IsAzumaya L (L ⊗[K] A) :=
    AzumayaScalarExtension.isAzumaya_scalarExtension (R := K) (S := L) (A := A)
  exact isSimpleRing_of_isAzumaya (K := L) (L ⊗[K] A)

end GaloisForLFunctions.HTGeometry.ABHN
