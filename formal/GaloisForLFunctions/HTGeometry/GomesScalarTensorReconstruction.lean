import GaloisForLFunctions.HTGeometry.GomesTensorConjugation

/-!
# Exact diagonal loss in a composite scalar matter fibre

Gomes, arXiv:2607.24901v1, Section 4.3, identifies the diagonal kernel as a
source of lost generating data. On the actual complex tensor product of two
lines, factorwise scalar actions remember exactly the product of the two
scalars. The complete fibre of indistinguishable unit-valued presentations
is the reciprocal diagonal orbit. This is an exact two-line model of the
reconstruction mechanism, not a computation of the Standard Model kernel.
-/

open scoped TensorProduct
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Product scalar action on the composite matter line. -/
def scalarMatterTensorAction (a b : ℂ) : (ℂ ⊗[ℂ] ℂ) →ₗ[ℂ] (ℂ ⊗[ℂ] ℂ) :=
  (a*b) • LinearMap.id

/-- This is precisely the factorwise tensor action. -/
theorem scalarMatterTensorAction_tmul (a b z w : ℂ) :
    scalarMatterTensorAction a b (z ⊗ₜ[ℂ] w) = (a*z) ⊗ₜ[ℂ] (b*w) := by
  apply (TensorProduct.lid ℂ ℂ).injective
  simp [scalarMatterTensorAction, smul_eq_mul]
  ring

/-- Composite matter actions agree exactly when their product scalars agree. -/
theorem scalarMatterTensorAction_eq_iff (a b c d : ℂ) :
    scalarMatterTensorAction a b = scalarMatterTensorAction c d ↔ a*b = c*d := by
  constructor
  · intro h
    have ht := LinearMap.congr_fun h ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))
    have hm := congrArg (TensorProduct.lid ℂ ℂ) ht
    simpa [scalarMatterTensorAction, smul_eq_mul] using hm
  · intro h
    simp only [scalarMatterTensorAction, h]

/-- The exact invisible subgroup consists of reciprocal scalar pairs. -/
theorem scalarMatterTensorAction_unit_kernel (a b : ℂˣ) :
    scalarMatterTensorAction (a : ℂ) (b : ℂ) = LinearMap.id ↔ b = a⁻¹ := by
  have hid : scalarMatterTensorAction 1 1 = (LinearMap.id :
      (ℂ ⊗[ℂ] ℂ) →ₗ[ℂ] (ℂ ⊗[ℂ] ℂ)) := by simp [scalarMatterTensorAction]
  rw [← hid, scalarMatterTensorAction_eq_iff, one_mul]
  change ((a*b : ℂˣ) : ℂ) = ((1 : ℂˣ) : ℂ) ↔ _
  rw [Units.val_inj]
  constructor
  · intro h
    calc
      b = a⁻¹ * (a*b) := by group
      _ = a⁻¹ := by rw [h, mul_one]
  · rintro rfl
    exact mul_inv_cancel a

/-- Reciprocal rescaling of the fundamental factors is invisible to all composite tensors. -/
theorem scalarMatterTensorAction_reciprocal (a b u : ℂˣ) :
    scalarMatterTensorAction ((a*u : ℂˣ) : ℂ) ((u⁻¹*b : ℂˣ) : ℂ) =
      scalarMatterTensorAction (a : ℂ) (b : ℂ) := by
  apply (scalarMatterTensorAction_eq_iff _ _ _ _).mpr
  change (((a*u)*(u⁻¹*b) : ℂˣ) : ℂ) = ((a*b : ℂˣ) : ℂ)
  congr 1
  group

/-- Reciprocal rescaling accounts for every ambiguity, with no missing presentation. -/
theorem scalarMatterTensorAction_complete_fibre (a b c d : ℂˣ) :
    scalarMatterTensorAction (a : ℂ) (b : ℂ) =
        scalarMatterTensorAction (c : ℂ) (d : ℂ) ↔
      ∃ u : ℂˣ, c = a*u ∧ d = u⁻¹*b := by
  constructor
  · intro h
    have he : a*b = c*d := Units.ext ((scalarMatterTensorAction_eq_iff _ _ _ _).mp h)
    refine ⟨a⁻¹*c, ?_, ?_⟩
    · group
    · calc
        d = c⁻¹ * (c*d) := by group
        _ = c⁻¹ * (a*b) := by rw [← he]
        _ = (a⁻¹*c)⁻¹*b := by group
  · rintro ⟨u, rfl, rfl⟩
    exact (scalarMatterTensorAction_reciprocal a b u).symm

/-- Remembering either nonzero generating factor removes the composite ambiguity. -/
theorem scalarMatterTensorAction_marked_reconstruction (a b c d : ℂˣ) :
    (a = c ∧ scalarMatterTensorAction (a : ℂ) (b : ℂ) =
      scalarMatterTensorAction (c : ℂ) (d : ℂ)) ↔ a = c ∧ b = d := by
  rw [scalarMatterTensorAction_eq_iff]
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, mul_left_cancel (Units.ext h : a*b = a*d)⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

end GaloisForLFunctions.HTGeometry
