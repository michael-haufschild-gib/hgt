import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Realification kills torsion, and a vanishing degree two kills products

Two algebraic ingredients of the two-term real Milnor amplitude.

First, realification is insensitive to torsion: a torsion element tensored with a real number is
zero because the real number is divisible by the annihilating integer, so the torsion submodule
tensors to zero, and right exactness of the tensor product turns the quotient map by the torsion
into an isomorphism after realification.  For the multiplicative group of a field the torsion is
the group of roots of unity, so `F^× ⊗ ℝ` is `(F^×/μ) ⊗ ℝ`.

Second, in a graded algebra whose degree-two part vanishes, the product of two degree-one classes
is zero, since it lands in degree two.  That is the square-zero statement of the amplitude
theorem.

* `deningerTorsion_tmul_real_eq_zero`, `deningerTorsionTensorReal_eq_zero` : torsion dies.
* `deningerRealification_torsionQuotient_bijective` : `A ⊗ ℝ ≅ (A/torsion) ⊗ ℝ`.
* `deningerGradedDegreeOne_mul_eq_zero` : vanishing degree two makes degree one square zero.
-/

namespace RHTower

open scoped TensorProduct

open LinearMap

section Realification

variable {A : Type*} [AddCommGroup A]

/-- **A torsion element tensored with a real number vanishes.**  The annihilating integer is
invertible on the reals. -/
theorem deningerTorsion_tmul_real_eq_zero {t : A} {n : ℤ} (hn : n ≠ 0) (ht : n • t = 0) (r : ℝ) :
    (t ⊗ₜ[ℤ] r : A ⊗[ℤ] ℝ) = 0 := by
  have hn' : ((n : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hrw : (t ⊗ₜ[ℤ] r : A ⊗[ℤ] ℝ) = (n • t) ⊗ₜ[ℤ] ((n : ℝ)⁻¹ * r) := by
    rw [TensorProduct.smul_tmul]
    congr 1
    rw [zsmul_eq_mul]
    field_simp
  rw [hrw, ht, TensorProduct.zero_tmul]

/-- **The realification of the torsion submodule vanishes.** -/
theorem deningerTorsionTensorReal_eq_zero
    (x : (Submodule.torsion ℤ A) ⊗[ℤ] ℝ) : x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul t r =>
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (t : A)).mp t.2
    have hne : (a : ℤ) ≠ 0 := nonZeroDivisors.ne_zero a.2
    have hzero : ((a : ℤ)) • (t : A) = 0 := ha
    have htt : ((a : ℤ)) • t = 0 := by
      refine Subtype.ext ?_
      show ((a : ℤ)) • (t : A) = 0
      exact hzero
    exact deningerTorsion_tmul_real_eq_zero (A := (Submodule.torsion ℤ A)) hne htt r
  | add x y hx hy =>
    rw [hx, hy, add_zero]

/-- **Realification only sees the quotient by torsion.**  The map induced by the quotient by the
torsion submodule is a linear isomorphism after tensoring with the reals; for the multiplicative
group of a field this is `F^× ⊗ ℝ ≅ (F^×/μ) ⊗ ℝ`. -/
theorem deningerRealification_torsionQuotient_bijective :
    Function.Bijective
      (LinearMap.rTensor ℝ (Submodule.torsion ℤ A).mkQ) := by
  constructor
  · rw [← LinearMap.ker_eq_bot]
    rw [rTensor_mkQ ℝ (Submodule.torsion ℤ A)]
    refine le_antisymm ?_ bot_le
    rintro _ ⟨x, rfl⟩
    rw [deningerTorsionTensorReal_eq_zero x, map_zero]
    exact Submodule.zero_mem _
  · exact LinearMap.rTensor_surjective ℝ (Submodule.mkQ_surjective _)

/-- The realification isomorphism `(3)`. -/
noncomputable def deningerRealificationTorsionEquiv :
    (A ⊗[ℤ] ℝ) ≃ₗ[ℤ] ((A ⧸ Submodule.torsion ℤ A) ⊗[ℤ] ℝ) :=
  LinearEquiv.ofBijective _ deningerRealification_torsionQuotient_bijective

end Realification

section GradedSquareZero

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜]

/-- **A vanishing degree two makes degree one square zero.**  The product of two degree-one classes
lies in degree two, so it vanishes as soon as the degree-two part does; this is the square-zero
statement of the two-term amplitude. -/
theorem deningerGradedDegreeOne_mul_eq_zero (h : 𝒜 2 = ⊥) {x y : A} (hx : x ∈ 𝒜 1)
    (hy : y ∈ 𝒜 1) : x * y = 0 := by
  have hmul : x * y ∈ 𝒜 (1 + 1) := SetLike.mul_mem_graded hx hy
  have h2 : x * y ∈ 𝒜 2 := by
    have : (1 : ℕ) + 1 = 2 := rfl
    rwa [this] at hmul
  rw [h] at h2
  exact h2

end GradedSquareZero

end RHTower
