import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Character of left and right composition

The dual tensor model of endomorphisms identifies A ↦ RAS with S* ⊗ R.
Its trace is therefore the product of the traces of R and S. This supplies
the conjugation character needed for finite-hull character averaging.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.OperatorCharacter
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Left and right composition, regarded as a linear operator on all endomorphisms. -/
def sandwich (R S : Module.End K V) : Module.End K (Module.End K V) where
  toFun A := R * A * S
  map_add' A B := by simp only [mul_add, add_mul]
  map_smul' c A := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

/-- The character of left/right composition is the product of the two ordinary traces. -/
theorem trace_sandwich (R S : Module.End K V) :
    LinearMap.trace K (Module.End K V) (sandwich R S) =
      LinearMap.trace K V R * LinearMap.trace K V S := by
  let e := dualTensorHomEquiv K V V
  have he : (sandwich R S).comp e.toLinearMap =
      e.toLinearMap.comp (TensorProduct.map (Module.Dual.transpose S) R) := by
    apply TensorProduct.ext
    ext f v w
    change R (f (S w) • v) = f (S w) • R v
    exact R.map_smul _ _
  have hc : sandwich R S = e.conj (TensorProduct.map (Module.Dual.transpose S) R) := by
    apply LinearMap.ext
    intro A
    obtain ⟨x, rfl⟩ := e.surjective A
    have h := LinearMap.congr_fun he x
    change sandwich R S (e x) = e ((TensorProduct.map (Module.Dual.transpose S) R) (e.symm (e x)))
    rw [e.symm_apply_apply]
    exact h
  have ht := LinearMap.trace_conj' (R := K)
    (M := TensorProduct K (Module.Dual K V) V) (N := Module.End K V)
    (TensorProduct.map (Module.Dual.transpose S) R) e
  rw [hc, ht, LinearMap.trace_tensorProduct' (Module.Dual.transpose S) R,
    LinearMap.trace_transpose' S, mul_comm]

#print axioms trace_sandwich
end GaloisForLFunctions.RepresentationLifting.OperatorCharacter
