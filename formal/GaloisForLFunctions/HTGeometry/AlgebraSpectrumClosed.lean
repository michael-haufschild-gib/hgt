import GaloisForLFunctions.HTGeometry.AlgebraSpectrumChart

/-!
# The complex-point space is Hausdorff and closed in the function space

Being a `ℂ`-algebra homomorphism is a pointwise-closed condition, so the space of complex points of
a `ℂ`-algebra is a closed subspace of the product `B → ℂ`.  With the Cauchy root bound this makes
the projection to the parameter line a proper map — by Tychonoff, and with no reference to charts —
which is the second half of the covering property for the general simple connectedness of the
affine line.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

namespace AlgSpec

variable {B : Type*} [CommRing B] [Algebra ℂ B]

instance : T2Space (AlgSpec B) := isEmbedding_coe.t2Space

/-- The image of the complex-point space inside the function space is closed. -/
theorem isClosed_range_algSpec_coe :
    IsClosed (Set.range fun χ : AlgSpec B => (χ : B → ℂ)) := by
  have hset : (Set.range fun χ : AlgSpec B => (χ : B → ℂ)) =
      {φ : B → ℂ | (∀ x y, φ (x + y) = φ x + φ y) ∧ (∀ x y, φ (x * y) = φ x * φ y) ∧
        φ 1 = 1 ∧ ∀ c : ℂ, φ (algebraMap ℂ B c) = c} := by
    ext φ
    constructor
    · rintro ⟨χ, rfl⟩
      exact ⟨fun x y => map_add _ _ _, fun x y => map_mul _ _ _, map_one _,
        fun c => (χ : B →ₐ[ℂ] ℂ).commutes c⟩
    · rintro ⟨hadd, hmul, hone, hcomm⟩
      have hzero : φ 0 = 0 := by
        have := hcomm 0
        simpa using this
      let f : B →+* ℂ :=
        { toFun := φ, map_one' := hone, map_mul' := hmul, map_zero' := hzero, map_add' := hadd }
      exact ⟨(AlgHom.mk' f (by intro c x; simp [f, Algebra.smul_def, hmul, hcomm]) :
        B →ₐ[ℂ] ℂ), rfl⟩
  rw [hset]
  have h1 : IsClosed {φ : B → ℂ | ∀ x y, φ (x + y) = φ x + φ y} := by
    have he : {φ : B → ℂ | ∀ x y, φ (x + y) = φ x + φ y} =
        ⋂ x : B, ⋂ y : B, {φ : B → ℂ | φ (x + y) = φ x + φ y} := by
      ext φ; simp
    rw [he]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply (x + y)) ((continuous_apply x).add (continuous_apply y))
  have h2 : IsClosed {φ : B → ℂ | ∀ x y, φ (x * y) = φ x * φ y} := by
    have he : {φ : B → ℂ | ∀ x y, φ (x * y) = φ x * φ y} =
        ⋂ x : B, ⋂ y : B, {φ : B → ℂ | φ (x * y) = φ x * φ y} := by
      ext φ; simp
    rw [he]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply (x * y)) ((continuous_apply x).mul (continuous_apply y))
  have h3 : IsClosed {φ : B → ℂ | φ 1 = 1} :=
    isClosed_eq (continuous_apply 1) continuous_const
  have h4 : IsClosed {φ : B → ℂ | ∀ c : ℂ, φ (algebraMap ℂ B c) = c} := by
    have he : {φ : B → ℂ | ∀ c : ℂ, φ (algebraMap ℂ B c) = c} =
        ⋂ c : ℂ, {φ : B → ℂ | φ (algebraMap ℂ B c) = c} := by
      ext φ; simp
    rw [he]
    exact isClosed_iInter fun c =>
      isClosed_eq (continuous_apply (algebraMap ℂ B c)) continuous_const
  exact h1.inter (h2.inter (h3.inter h4))

end AlgSpec


end

end GaloisForLFunctions.HTGeometry
