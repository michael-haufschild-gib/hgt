import GaloisForLFunctions.HTGeometry.ABHN.BrauerFoundations
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Raw scalar extension for Albert--Brauer--Hasse--Noether

For `A` central simple over `K` and a field extension `L/K`, the local Brauer map must be induced
by `L ⊗[K] A`.  Mathlib already constructs this algebra and proves finite dimensionality.  The
missing upgrade to a `CSA L` is deliberately not hidden: it requires forward centrality and the
central-simple tensor-product theorem, neither of which is currently available in Mathlib.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- The raw `L`-algebra underlying scalar extension of a central simple `K`-algebra. -/
noncomputable def scalarExtensionAlg {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (A : CSA.{u, w} K) : AlgCat L :=
  AlgCat.of L (L ⊗[K] A.carrier)

/-- Canonical map from `A` into its raw scalar extension. -/
noncomputable def scalarExtensionMap {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (A : CSA.{u, w} K) : A.carrier →ₐ[K] L ⊗[K] A.carrier :=
  Algebra.TensorProduct.includeRight

/-- Scalar extension preserves finite dimensionality over the extended field. -/
theorem scalarExtensionAlg_finiteDimensional {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (A : CSA.{u, w} K) : FiniteDimensional L (L ⊗[K] A.carrier) := by
  infer_instance

end GaloisForLFunctions.HTGeometry.ABHN
