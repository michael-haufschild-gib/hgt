import GaloisForLFunctions.HTGeometry.NuclearTensorEstimate
import GaloisForLFunctions.HTGeometry.ProjectiveTensorQuotientSpace
import GaloisForLFunctions.HTGeometry.InjectiveTensorSubspace
import GaloisForLFunctions.HTGeometry.InjectiveTensorTransport

/-!
# Grothendieck's comparison and strictness of a tensored inclusion

When the comparison map between two seminorm spaces of a coefficient space is trace-class — the
defining property of nuclearity — the projective tensor seminorm built from the smaller seminorm is
bounded by the injective tensor seminorm built from the larger one.  Since the injective seminorm is
subspace-invariant and bounded by the projective one, a subspace inclusion stays strict after
tensoring with a nuclear coefficient space.

* `projTensorSeminorm_le_nuclear_injTensorSeminorm` : **`π_{p₁} ≤ (trace norm) · ε_{p₂}`.**
* `projTensorSeminorm_le_nuclear_subtype` : **a subspace inclusion tensors to a strict inclusion.**
-/

open scoped TensorProduct

noncomputable section

namespace GaloisForLFunctions

variable {𝕜 E F ι : Type*} [RCLike 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- **Grothendieck's comparison**: a trace-class comparison of seminorms bounds the projective
tensor seminorm by the injective one. -/
theorem projTensorSeminorm_le_nuclear_injTensorSeminorm
    {X₁ X₂ : Type*} [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
    [NormedAddCommGroup X₂] [NormedSpace 𝕜 X₂]
    (p₁ p₂ : Seminorm 𝕜 E) (q : Seminorm 𝕜 F)
    (κ₁ : E →ₗ[𝕜] X₁) (κ₂ : E →ₗ[𝕜] X₂) (T : X₂ →ₗ[𝕜] X₁)
    (hsurj : Function.Surjective κ₁) (hnorm₁ : ∀ x, ‖κ₁ x‖ = p₁ x)
    (hnorm₂ : ∀ x, ‖κ₂ x‖ = p₂ x) (hcomm : ∀ x, T (κ₂ x) = κ₁ x)
    (φ : ι → (X₂ →L[𝕜] 𝕜)) (y : ι → X₁) (hsum : Summable fun k => ‖φ k‖ * ‖y k‖)
    (hT : ∀ x, HasSum (fun k => φ k x • y k) (T x)) (z : E ⊗[𝕜] F) :
    projTensorSeminorm p₁ q z ≤ (∑' k, ‖φ k‖ * ‖y k‖) * injTensorSeminorm p₂ q z := by
  have h1 := projTensorSeminorm_le_map_of_surjective p₁ q κ₁ hsurj hnorm₁ z
  have h2 := projTensorSeminorm_nuclear_comp_le q κ₂ κ₁ T hcomm φ y hsum hT z
  have hp2 : (normSeminorm 𝕜 X₂).comp κ₂ = p₂ := by
    refine Seminorm.ext fun x => ?_
    rw [Seminorm.comp_apply]
    exact hnorm₂ x
  rw [hp2] at h2
  exact le_trans h1 h2

/-- **A subspace inclusion tensors to a strict inclusion** for nuclear coefficients: the projective
seminorm on `E ⊗ S` is bounded by the projective seminorm of the image in `E ⊗ B`. -/
theorem projTensorSeminorm_le_nuclear_subtype
    {X₁ X₂ B : Type*} [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
    [NormedAddCommGroup X₂] [NormedSpace 𝕜 X₂] [AddCommGroup B] [Module 𝕜 B]
    (p₁ p₂ : Seminorm 𝕜 E) (q : Seminorm 𝕜 B) (S : Submodule 𝕜 B)
    (κ₁ : E →ₗ[𝕜] X₁) (κ₂ : E →ₗ[𝕜] X₂) (T : X₂ →ₗ[𝕜] X₁)
    (hsurj : Function.Surjective κ₁) (hnorm₁ : ∀ x, ‖κ₁ x‖ = p₁ x)
    (hnorm₂ : ∀ x, ‖κ₂ x‖ = p₂ x) (hcomm : ∀ x, T (κ₂ x) = κ₁ x)
    (φ : ι → (X₂ →L[𝕜] 𝕜)) (y : ι → X₁) (hsum : Summable fun k => ‖φ k‖ * ‖y k‖)
    (hT : ∀ x, HasSum (fun k => φ k x • y k) (T x)) (z : E ⊗[𝕜] S) :
    projTensorSeminorm p₁ (q.comp S.subtype) z
      ≤ (∑' k, ‖φ k‖ * ‖y k‖)
        * projTensorSeminorm p₂ q
          (TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) S.subtype z) := by
  have hnn : (0 : ℝ) ≤ ∑' k, ‖φ k‖ * ‖y k‖ := tsum_nonneg fun k => by positivity
  have h1 := projTensorSeminorm_le_nuclear_injTensorSeminorm p₁ p₂ (q.comp S.subtype)
    κ₁ κ₂ T hsurj hnorm₁ hnorm₂ hcomm φ y hsum hT z
  have h2 : injTensorSeminorm p₂ (q.comp S.subtype) z
      = injTensorSeminorm p₂ q (TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) S.subtype z) :=
    injTensorSeminorm_subtype_eq p₂ q S z
  have h3 : injTensorSeminorm p₂ q (TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) S.subtype z)
      ≤ projTensorSeminorm p₂ q (TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) S.subtype z) :=
    injTensorSeminorm_le_projTensorSeminorm p₂ q _
  rw [h2] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_left h3 hnn)

/-- **A strict injection stays strict after tensoring with a nuclear coefficient space**: if `j` is
injective with `q_A ≤ C q_B ∘ j`, and the comparison of the coefficient seminorms is trace-class,
then the projective seminorm on `E ⊗ A` is bounded by the projective seminorm of the image. -/
theorem projTensorSeminorm_le_nuclear_strict_injection
    {X₁ X₂ A B : Type*} [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
    [NormedAddCommGroup X₂] [NormedSpace 𝕜 X₂] [AddCommGroup A] [Module 𝕜 A]
    [AddCommGroup B] [Module 𝕜 B]
    (p₁ p₂ : Seminorm 𝕜 E) (qA : Seminorm 𝕜 A) (qB : Seminorm 𝕜 B)
    (κ₁ : E →ₗ[𝕜] X₁) (κ₂ : E →ₗ[𝕜] X₂) (T : X₂ →ₗ[𝕜] X₁)
    (hsurj : Function.Surjective κ₁) (hnorm₁ : ∀ x, ‖κ₁ x‖ = p₁ x)
    (hnorm₂ : ∀ x, ‖κ₂ x‖ = p₂ x) (hcomm : ∀ x, T (κ₂ x) = κ₁ x)
    (φ : ι → (X₂ →L[𝕜] 𝕜)) (y : ι → X₁) (hsum : Summable fun k => ‖φ k‖ * ‖y k‖)
    (hT : ∀ x, HasSum (fun k => φ k x • y k) (T x))
    (j : A →ₗ[𝕜] B) (hinj : Function.Injective j) {C : ℝ} (hC : 0 ≤ C)
    (hstrict : ∀ a, qA a ≤ C * qB (j a)) (z : E ⊗[𝕜] A) :
    projTensorSeminorm p₁ qA z
      ≤ (∑' k, ‖φ k‖ * ‖y k‖) * C
        * projTensorSeminorm p₂ qB (TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) j z) := by
  have hnn : (0 : ℝ) ≤ ∑' k, ‖φ k‖ * ‖y k‖ := tsum_nonneg fun k => by positivity
  have h1 := projTensorSeminorm_le_nuclear_injTensorSeminorm p₁ p₂ qA
    κ₁ κ₂ T hsurj hnorm₁ hnorm₂ hcomm φ y hsum hT z
  have h2 : injTensorSeminorm p₂ qA z ≤ C * injTensorSeminorm p₂ (qB.comp j) z := by
    refine injTensorSeminorm_le_mul_of_le p₂ qA (qB.comp j) hC ?_ z
    intro a
    rw [Seminorm.comp_apply]
    exact hstrict a
  have h3 : injTensorSeminorm p₂ (qB.comp j) z
      = injTensorSeminorm p₂ qB (TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) j z) :=
    injTensorSeminorm_injective_eq p₂ qB j hinj z
  have h4 : injTensorSeminorm p₂ qB (TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) j z)
      ≤ projTensorSeminorm p₂ qB (TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) j z) :=
    injTensorSeminorm_le_projTensorSeminorm p₂ qB _
  rw [h3] at h2
  calc projTensorSeminorm p₁ qA z
      ≤ (∑' k, ‖φ k‖ * ‖y k‖) * injTensorSeminorm p₂ qA z := h1
    _ ≤ (∑' k, ‖φ k‖ * ‖y k‖)
        * (C * injTensorSeminorm p₂ qB (TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) j z)) :=
        mul_le_mul_of_nonneg_left h2 hnn
    _ ≤ (∑' k, ‖φ k‖ * ‖y k‖)
        * (C * projTensorSeminorm p₂ qB (TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) j z)) := by
        refine mul_le_mul_of_nonneg_left ?_ hnn
        exact mul_le_mul_of_nonneg_left h4 hC
    _ = (∑' k, ‖φ k‖ * ‖y k‖) * C
        * projTensorSeminorm p₂ qB (TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) j z) := by
        ring

end GaloisForLFunctions

end
