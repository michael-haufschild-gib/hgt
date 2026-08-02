import GaloisForLFunctions.HTGeometry.ProjectiveTensorSeminorm

/-!
# Density survives the projective tensor product

The algebraic tensor product of two dense subspaces is dense for the projective seminorm.  For a
pure tensor this is the splitting
`x ⊗ y − a ⊗ b = (x − a) ⊗ y + a ⊗ (y − b)`,
which the projective seminorm estimates by `p(x − a) q(y) + p(a) q(y − b)`; a general tensor is a
finite sum of pure ones, and the error is halved at each step.

This is the sentence of the tensor transport that "density survives completed tensoring because the
algebraic tensor of dense subspaces is dense": a dense core of the coefficient and a dense core of
the radial space tensor to a dense core of the tensor product, so the completed tensor product is
computed by the cores.

* `tensorSubmodule` : the subspace spanned by the tensors of two subspaces.
* `exists_tmul_approx` : **a pure tensor is approximated by the tensors of dense subspaces.**
* `exists_tensor_approx` : **the algebraic tensor of dense subspaces is dense.**
-/

open scoped TensorProduct

noncomputable section

namespace GaloisForLFunctions

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- The subspace of the algebraic tensor product spanned by the tensors of two subspaces. -/
def tensorSubmodule (A : Submodule 𝕜 E) (B : Submodule 𝕜 F) : Submodule 𝕜 (E ⊗[𝕜] F) :=
  Submodule.span 𝕜 {t | ∃ a ∈ A, ∃ b ∈ B, t = a ⊗ₜ[𝕜] b}

theorem tmul_mem_tensorSubmodule {A : Submodule 𝕜 E} {B : Submodule 𝕜 F} {a : E} {b : F}
    (ha : a ∈ A) (hb : b ∈ B) : a ⊗ₜ[𝕜] b ∈ tensorSubmodule A B :=
  Submodule.subset_span ⟨a, ha, b, hb, rfl⟩

/-- **A pure tensor is approximated by the tensors of dense subspaces.** -/
theorem exists_tmul_approx (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (A : Submodule 𝕜 E)
    (B : Submodule 𝕜 F)
    (hA : ∀ (x : E) (ε : ℝ), 0 < ε → ∃ a ∈ A, p (x - a) < ε)
    (hB : ∀ (y : F) (ε : ℝ), 0 < ε → ∃ b ∈ B, q (y - b) < ε)
    (x : E) (y : F) {ε : ℝ} (hε : 0 < ε) :
    ∃ w ∈ tensorSubmodule A B, projTensorSeminorm p q (x ⊗ₜ[𝕜] y - w) < ε := by
  have hqy : (0 : ℝ) < q y + 1 := by linarith [apply_nonneg q y]
  obtain ⟨a, haA, ha⟩ := hA x (ε / (2 * (q y + 1))) (by positivity)
  have hpa : (0 : ℝ) < p a + 1 := by linarith [apply_nonneg p a]
  obtain ⟨b, hbB, hb⟩ := hB y (ε / (2 * (p a + 1))) (by positivity)
  refine ⟨a ⊗ₜ[𝕜] b, tmul_mem_tensorSubmodule haA hbB, ?_⟩
  have hsplit : x ⊗ₜ[𝕜] y - a ⊗ₜ[𝕜] b = (x - a) ⊗ₜ[𝕜] y + a ⊗ₜ[𝕜] (y - b) := by
    rw [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    abel
  rw [hsplit]
  refine lt_of_le_of_lt (map_add_le_add (projTensorSeminorm p q) _ _) ?_
  have h1 : projTensorSeminorm p q ((x - a) ⊗ₜ[𝕜] y) ≤ p (x - a) * q y :=
    projTensorSeminorm_tmul_le p q _ _
  have h2 : projTensorSeminorm p q (a ⊗ₜ[𝕜] (y - b)) ≤ p a * q (y - b) :=
    projTensorSeminorm_tmul_le p q _ _
  have h1' : p (x - a) * q y < ε / 2 := by
    calc p (x - a) * q y ≤ p (x - a) * (q y + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (apply_nonneg p _)
      _ < (ε / (2 * (q y + 1))) * (q y + 1) := mul_lt_mul_of_pos_right ha hqy
      _ = ε / 2 := by field_simp
  have h2' : p a * q (y - b) < ε / 2 := by
    calc p a * q (y - b) ≤ (p a + 1) * q (y - b) :=
          mul_le_mul_of_nonneg_right (by linarith) (apply_nonneg q _)
      _ < (p a + 1) * (ε / (2 * (p a + 1))) := mul_lt_mul_of_pos_left hb hpa
      _ = ε / 2 := by field_simp
  linarith

/-- **The algebraic tensor product of two dense subspaces is dense** for the projective
seminorm. -/
theorem exists_tensor_approx (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 F) (A : Submodule 𝕜 E)
    (B : Submodule 𝕜 F)
    (hA : ∀ (x : E) (ε : ℝ), 0 < ε → ∃ a ∈ A, p (x - a) < ε)
    (hB : ∀ (y : F) (ε : ℝ), 0 < ε → ∃ b ∈ B, q (y - b) < ε)
    (z : E ⊗[𝕜] F) :
    ∀ ε : ℝ, 0 < ε → ∃ w ∈ tensorSubmodule A B, projTensorSeminorm p q (z - w) < ε := by
  induction z using TensorProduct.induction_on with
  | zero =>
    intro ε hε
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [sub_zero, projTensorSeminorm_apply, projTensorSeminormFun_zero]
    exact hε
  | tmul x y =>
    intro ε hε
    exact exists_tmul_approx p q A B hA hB x y hε
  | add z z' hz hz' =>
    intro ε hε
    obtain ⟨w, hw, hlt⟩ := hz (ε / 2) (by linarith)
    obtain ⟨w', hw', hlt'⟩ := hz' (ε / 2) (by linarith)
    refine ⟨w + w', Submodule.add_mem _ hw hw', ?_⟩
    have hsplit : z + z' - (w + w') = (z - w) + (z' - w') := by abel
    rw [hsplit]
    refine lt_of_le_of_lt (map_add_le_add (projTensorSeminorm p q) _ _) ?_
    linarith

/-- **A split injection stays split after tensoring**: the tensor of a left inverse is a left
inverse. -/
theorem lTensor_leftInverse {X Y : Type*} [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y]
    [Module 𝕜 Y] (f : X →ₗ[𝕜] Y) (s : Y →ₗ[𝕜] X) (h : s.comp f = LinearMap.id) :
    (LinearMap.lTensor E s).comp (LinearMap.lTensor E f) = LinearMap.id := by
  rw [← LinearMap.lTensor_comp, h, LinearMap.lTensor_id]

end GaloisForLFunctions

end
