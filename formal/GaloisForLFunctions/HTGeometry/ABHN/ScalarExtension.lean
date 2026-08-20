import GaloisForLFunctions.HTGeometry.ABHN.BrauerFoundations
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
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

/-- Scalar extension of a central algebra remains central over the extended field. -/
theorem scalarExtensionAlg_isCentral {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (A : CSA.{u, w} K) : Algebra.IsCentral L (L ⊗[K] A.carrier) := by
  constructor
  intro z hz
  rw [Subalgebra.mem_center_iff] at hz
  rw [Algebra.mem_bot]
  have hz' : z ∈ Subalgebra.centralizer K
      (↑(Algebra.TensorProduct.includeRight : A.carrier →ₐ[K] L ⊗[K] A.carrier).range) := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro g ⟨a, rfl⟩
    exact hz _
  rw [Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct K L A.carrier] at hz'
  rcases hz' with ⟨x, hx⟩
  subst z
  clear hz
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul l a =>
      obtain ⟨k, hk⟩ := (Algebra.IsCentral.mem_center_iff K).mp a.prop
      refine ⟨l * algebraMap K L k, ?_⟩
      simpa [Algebra.TensorProduct.map_tmul, hk, Algebra.smul_def, mul_comm] using
        (TensorProduct.tmul_smul (R := K) (R' := K) (M := L) (N := A.carrier)
          k l (1 : A.carrier)).symm
  | add x y hx hy =>
      obtain ⟨lx, hx⟩ := hx
      obtain ⟨ly, hy⟩ := hy
      refine ⟨lx + ly, ?_⟩
      change algebraMap L (L ⊗[K] A.carrier) (lx + ly) = _
      rw [map_add, map_add, hx, hy]

end GaloisForLFunctions.HTGeometry.ABHN
