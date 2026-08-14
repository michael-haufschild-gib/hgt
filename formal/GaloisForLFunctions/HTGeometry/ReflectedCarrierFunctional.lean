import GaloisForLFunctions.HTGeometry.ContinuousMapCauchyTransform

/-!
# Doubling a functional across a conjugation-symmetric carrier

A continuous functional on the continuous functions of a compact set `Kc` extends to the
conjugation-symmetric compact `Kt ⊇ Kc` by adding its Schwarz reflection.  The reflection
`h ↦ conj (L (conj ∘ h ∘ conj))` is complex linear because two conjugations compose, so the sum is
again a continuous complex functional.

On a Schwarz-real function the doubled functional takes the real value `2 Re L`, and its Cauchy
transform is the sum of the transform of `L` and the reflected transform.

* `GaloisForLFunctions.HTGeometry.precompCLM`, `GaloisForLFunctions.HTGeometry.sigmaMap`;
* `GaloisForLFunctions.HTGeometry.doubledFunctional`;
* `GaloisForLFunctions.HTGeometry.doubledFunctional_apply_of_sigma_eq`;
* `GaloisForLFunctions.HTGeometry.cauchyTransform_doubledFunctional`.
-/

noncomputable section

open Complex Set

namespace GaloisForLFunctions.HTGeometry

/-- Precomposition with a continuous map between compact spaces, as a continuous linear map. -/
def precompCLM {A B : Type*} [TopologicalSpace A] [CompactSpace A] [TopologicalSpace B]
    [CompactSpace B] (φ : C(A, B)) : C(B, ℂ) →L[ℂ] C(A, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun h => h.comp φ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 fun h => by
      rw [one_mul]
      refine (ContinuousMap.norm_le _ (norm_nonneg h)).2 fun a => ?_
      exact h.norm_coe_le_norm (φ a)

theorem norm_precompCLM_le {A B : Type*} [TopologicalSpace A] [CompactSpace A]
    [TopologicalSpace B] [CompactSpace B] (φ : C(A, B)) (h : C(B, ℂ)) :
    ‖precompCLM φ h‖ ≤ ‖h‖ := by
  refine (ContinuousMap.norm_le _ (norm_nonneg h)).2 fun a => ?_
  exact h.norm_coe_le_norm (φ a)

@[simp] theorem precompCLM_apply {A B : Type*} [TopologicalSpace A] [CompactSpace A]
    [TopologicalSpace B] [CompactSpace B] (φ : C(A, B)) (h : C(B, ℂ)) (a : A) :
    precompCLM φ h a = h (φ a) := rfl

variable {Kc Kt : Set ℂ} [CompactSpace Kc] [CompactSpace Kt]

/-- The inclusion of the upper carrier into the doubled carrier. -/
def inclMap (hsub : Kc ⊆ Kt) : C(Kc, Kt) :=
  ⟨fun z => ⟨(z : ℂ), hsub z.2⟩, Continuous.subtype_mk continuous_subtype_val _⟩

omit [CompactSpace Kc] [CompactSpace Kt] in
@[simp] theorem inclMap_apply (hsub : Kc ⊆ Kt) (z : Kc) :
    ((inclMap hsub z : Kt) : ℂ) = (z : ℂ) := rfl

/-- Complex conjugation as a self-map of a conjugation-symmetric compact set. -/
def conjMap (hconj : ∀ z ∈ Kt, (starRingEnd ℂ) z ∈ Kt) : C(Kt, Kt) :=
  ⟨fun z => ⟨(starRingEnd ℂ) (z : ℂ), hconj (z : ℂ) z.2⟩,
    Continuous.subtype_mk (Complex.continuous_conj.comp continuous_subtype_val) _⟩

omit [CompactSpace Kt] in
@[simp] theorem conjMap_apply (hconj : ∀ z ∈ Kt, (starRingEnd ℂ) z ∈ Kt) (z : Kt) :
    ((conjMap hconj z : Kt) : ℂ) = (starRingEnd ℂ) (z : ℂ) := rfl

/-- The Schwarz reflection of a continuous function on a conjugation-symmetric compact set. -/
def sigmaMap (hconj : ∀ z ∈ Kt, (starRingEnd ℂ) z ∈ Kt) (h : C(Kt, ℂ)) : C(Kt, ℂ) :=
  ⟨fun z => (starRingEnd ℂ) (h (conjMap hconj z)),
    Complex.continuous_conj.comp (h.continuous.comp (conjMap hconj).continuous)⟩

omit [CompactSpace Kt] in
@[simp] theorem sigmaMap_apply (hconj : ∀ z ∈ Kt, (starRingEnd ℂ) z ∈ Kt) (h : C(Kt, ℂ))
    (z : Kt) : sigmaMap hconj h z = (starRingEnd ℂ) (h (conjMap hconj z)) := rfl

omit [CompactSpace Kt] in
theorem sigmaMap_add (hconj : ∀ z ∈ Kt, (starRingEnd ℂ) z ∈ Kt) (h₁ h₂ : C(Kt, ℂ)) :
    sigmaMap hconj (h₁ + h₂) = sigmaMap hconj h₁ + sigmaMap hconj h₂ := by
  ext z
  simp

omit [CompactSpace Kt] in
theorem sigmaMap_smul (hconj : ∀ z ∈ Kt, (starRingEnd ℂ) z ∈ Kt) (c : ℂ) (h : C(Kt, ℂ)) :
    sigmaMap hconj (c • h) = ((starRingEnd ℂ) c) • sigmaMap hconj h := by
  ext z
  simp

theorem norm_sigmaMap_le (hconj : ∀ z ∈ Kt, (starRingEnd ℂ) z ∈ Kt) (h : C(Kt, ℂ)) :
    ‖sigmaMap hconj h‖ ≤ ‖h‖ := by
  refine (ContinuousMap.norm_le _ (norm_nonneg h)).2 fun z => ?_
  rw [sigmaMap_apply, RCLike.norm_conj]
  exact h.norm_coe_le_norm _

/-- The Schwarz reflection of a functional, transported to the doubled carrier. -/
def reflFunctional (hsub : Kc ⊆ Kt) (hconj : ∀ z ∈ Kt, (starRingEnd ℂ) z ∈ Kt)
    (L : C(Kc, ℂ) →L[ℂ] ℂ) : C(Kt, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun h => (starRingEnd ℂ) (L (precompCLM (inclMap hsub) (sigmaMap hconj h)))
      map_add' := fun h₁ h₂ => by
        rw [sigmaMap_add, map_add, map_add, map_add]
      map_smul' := fun c h => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [sigmaMap_smul, map_smul, map_smul, smul_eq_mul, map_mul,
          Complex.conj_conj] }
    ‖L‖ fun h => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, RCLike.norm_conj]
      refine le_trans (L.le_opNorm _) ?_
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg L)
      exact le_trans (norm_precompCLM_le _ _) (norm_sigmaMap_le hconj h)

@[simp] theorem reflFunctional_apply (hsub : Kc ⊆ Kt)
    (hconj : ∀ z ∈ Kt, (starRingEnd ℂ) z ∈ Kt) (L : C(Kc, ℂ) →L[ℂ] ℂ) (h : C(Kt, ℂ)) :
    reflFunctional hsub hconj L h
      = (starRingEnd ℂ) (L (precompCLM (inclMap hsub) (sigmaMap hconj h))) := rfl

/-- The doubled functional: the given functional on the upper carrier plus its Schwarz
reflection. -/
def doubledFunctional (hsub : Kc ⊆ Kt) (hconj : ∀ z ∈ Kt, (starRingEnd ℂ) z ∈ Kt)
    (L : C(Kc, ℂ) →L[ℂ] ℂ) : C(Kt, ℂ) →L[ℂ] ℂ :=
  L.comp (precompCLM (inclMap hsub)) + reflFunctional hsub hconj L

@[simp] theorem doubledFunctional_apply (hsub : Kc ⊆ Kt)
    (hconj : ∀ z ∈ Kt, (starRingEnd ℂ) z ∈ Kt) (L : C(Kc, ℂ) →L[ℂ] ℂ) (h : C(Kt, ℂ)) :
    doubledFunctional hsub hconj L h
      = L (precompCLM (inclMap hsub) h)
        + (starRingEnd ℂ) (L (precompCLM (inclMap hsub) (sigmaMap hconj h))) := rfl

/-- **On a Schwarz-real function the doubled functional is twice the real part.** -/
theorem doubledFunctional_apply_of_sigma_eq (hsub : Kc ⊆ Kt)
    (hconj : ∀ z ∈ Kt, (starRingEnd ℂ) z ∈ Kt) (L : C(Kc, ℂ) →L[ℂ] ℂ) {h : C(Kt, ℂ)}
    (hh : sigmaMap hconj h = h) :
    doubledFunctional hsub hconj L h
      = ((2 * (L (precompCLM (inclMap hsub) h)).re : ℝ) : ℂ) := by
  rw [doubledFunctional_apply, hh, Complex.add_conj]

omit [CompactSpace Kc] [CompactSpace Kt] in
theorem conj_notMem_of_notMem (hconj : ∀ z ∈ Kt, (starRingEnd ℂ) z ∈ Kt) {v : ℂ} (hv : v ∉ Kt) :
    (starRingEnd ℂ) v ∉ Kt := fun hc => hv (by simpa using hconj _ hc)

theorem precompCLM_kernelFun (hsub : Kc ⊆ Kt) {v : ℂ} (hv : v ∉ Kt) :
    precompCLM (inclMap hsub) (kernelFun Kt hv) = kernelFun Kc (fun hc => hv (hsub hc)) := by
  ext z
  simp [kernelFun, inclMap]

omit [CompactSpace Kt] in
theorem sigmaMap_kernelFun (hconj : ∀ z ∈ Kt, (starRingEnd ℂ) z ∈ Kt) {v : ℂ} (hv : v ∉ Kt) :
    sigmaMap hconj (kernelFun Kt hv) = kernelFun Kt (conj_notMem_of_notMem hconj hv) := by
  ext z
  simp only [sigmaMap_apply, kernelFun_apply, conjMap_apply, map_inv₀, map_sub, Complex.conj_conj]

/-- **The Cauchy transform of the doubled functional.** -/
theorem cauchyTransform_doubledFunctional (hsub : Kc ⊆ Kt)
    (hconj : ∀ z ∈ Kt, (starRingEnd ℂ) z ∈ Kt) (L : C(Kc, ℂ) →L[ℂ] ℂ) {v : ℂ} (hv : v ∉ Kt) :
    functionalCauchyTransform (doubledFunctional hsub hconj L) v
      = functionalCauchyTransform L v
        + (starRingEnd ℂ) (functionalCauchyTransform L ((starRingEnd ℂ) v)) := by
  have hvc : v ∉ Kc := fun hc => hv (hsub hc)
  have hcv : (starRingEnd ℂ) v ∉ Kt := conj_notMem_of_notMem hconj hv
  have hcvc : (starRingEnd ℂ) v ∉ Kc := fun hc => hcv (hsub hc)
  rw [cauchyTransform_eq _ hv, cauchyTransform_eq L hvc, cauchyTransform_eq L hcvc,
    doubledFunctional_apply, precompCLM_kernelFun hsub hv, sigmaMap_kernelFun hconj hv,
    precompCLM_kernelFun hsub hcv]

/-! ## Transfer between a carrier and its mirror image -/

section Transfer

variable {K₁ K₂ : Set ℂ} [CompactSpace K₁] [CompactSpace K₂]

/-- Complex conjugation as a continuous map between two conjugate carriers. -/
def conjTransferMap (hmap : ∀ z ∈ K₁, (starRingEnd ℂ) z ∈ K₂) : C(K₁, K₂) :=
  ⟨fun z => ⟨(starRingEnd ℂ) (z : ℂ), hmap (z : ℂ) z.2⟩,
    Continuous.subtype_mk (Complex.continuous_conj.comp continuous_subtype_val) _⟩

omit [CompactSpace K₁] [CompactSpace K₂] in
@[simp] theorem conjTransferMap_apply (hmap : ∀ z ∈ K₁, (starRingEnd ℂ) z ∈ K₂) (z : K₁) :
    ((conjTransferMap hmap z : K₂) : ℂ) = (starRingEnd ℂ) (z : ℂ) := rfl

/-- The conjugation transfer of a continuous function between two conjugate carriers. -/
def sigmaTransfer (hmap : ∀ z ∈ K₁, (starRingEnd ℂ) z ∈ K₂) (h : C(K₂, ℂ)) : C(K₁, ℂ) :=
  ⟨fun z => (starRingEnd ℂ) (h (conjTransferMap hmap z)),
    Complex.continuous_conj.comp (h.continuous.comp (conjTransferMap hmap).continuous)⟩

omit [CompactSpace K₁] [CompactSpace K₂] in
@[simp] theorem sigmaTransfer_apply (hmap : ∀ z ∈ K₁, (starRingEnd ℂ) z ∈ K₂) (h : C(K₂, ℂ))
    (z : K₁) : sigmaTransfer hmap h z = (starRingEnd ℂ) (h (conjTransferMap hmap z)) := rfl

omit [CompactSpace K₁] [CompactSpace K₂] in
theorem sigmaTransfer_add (hmap : ∀ z ∈ K₁, (starRingEnd ℂ) z ∈ K₂) (h₁ h₂ : C(K₂, ℂ)) :
    sigmaTransfer hmap (h₁ + h₂) = sigmaTransfer hmap h₁ + sigmaTransfer hmap h₂ := by
  ext z
  simp

omit [CompactSpace K₁] [CompactSpace K₂] in
theorem sigmaTransfer_smul (hmap : ∀ z ∈ K₁, (starRingEnd ℂ) z ∈ K₂) (c : ℂ) (h : C(K₂, ℂ)) :
    sigmaTransfer hmap (c • h) = ((starRingEnd ℂ) c) • sigmaTransfer hmap h := by
  ext z
  simp

theorem norm_sigmaTransfer_le (hmap : ∀ z ∈ K₁, (starRingEnd ℂ) z ∈ K₂) (h : C(K₂, ℂ)) :
    ‖sigmaTransfer hmap h‖ ≤ ‖h‖ := by
  refine (ContinuousMap.norm_le _ (norm_nonneg h)).2 fun z => ?_
  rw [sigmaTransfer_apply, RCLike.norm_conj]
  exact h.norm_coe_le_norm _

/-- The conjugate of a functional, transported to the mirror carrier. -/
def conjFunctional (hmap : ∀ z ∈ K₂, (starRingEnd ℂ) z ∈ K₁) (L : C(K₂, ℂ) →L[ℂ] ℂ) :
    C(K₁, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun h => (starRingEnd ℂ) (L (sigmaTransfer hmap h))
      map_add' := fun h₁ h₂ => by
        rw [sigmaTransfer_add, map_add, map_add]
      map_smul' := fun c h => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [sigmaTransfer_smul, map_smul, smul_eq_mul, map_mul, Complex.conj_conj] }
    ‖L‖ fun h => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, RCLike.norm_conj]
      refine le_trans (L.le_opNorm _) ?_
      exact mul_le_mul_of_nonneg_left (norm_sigmaTransfer_le hmap h) (norm_nonneg L)

@[simp] theorem conjFunctional_apply (hmap : ∀ z ∈ K₂, (starRingEnd ℂ) z ∈ K₁)
    (L : C(K₂, ℂ) →L[ℂ] ℂ) (h : C(K₁, ℂ)) :
    conjFunctional hmap L h = (starRingEnd ℂ) (L (sigmaTransfer hmap h)) := rfl

omit [CompactSpace K₁] [CompactSpace K₂] in
theorem conj_notMem_of_notMem_transfer (hmap : ∀ z ∈ K₂, (starRingEnd ℂ) z ∈ K₁) {v : ℂ}
    (hv : v ∉ K₁) : (starRingEnd ℂ) v ∉ K₂ := fun hc => hv (by simpa using hmap _ hc)

omit [CompactSpace K₁] [CompactSpace K₂] in
theorem sigmaTransfer_kernelFun (hmap : ∀ z ∈ K₂, (starRingEnd ℂ) z ∈ K₁) {v : ℂ}
    (hv : v ∉ K₁) (hcv : (starRingEnd ℂ) v ∉ K₂) :
    sigmaTransfer hmap (kernelFun K₁ hv) = kernelFun K₂ hcv := by
  ext z
  simp only [sigmaTransfer_apply, kernelFun_apply, conjTransferMap_apply, map_inv₀, map_sub,
    Complex.conj_conj]

/-- **The Cauchy transform of the conjugate functional.** -/
theorem cauchyTransform_conjFunctional (hmap : ∀ z ∈ K₂, (starRingEnd ℂ) z ∈ K₁)
    (L : C(K₂, ℂ) →L[ℂ] ℂ) {v : ℂ} (hv : v ∉ K₁) :
    functionalCauchyTransform (conjFunctional hmap L) v
      = (starRingEnd ℂ) (functionalCauchyTransform L ((starRingEnd ℂ) v)) := by
  have hcv : (starRingEnd ℂ) v ∉ K₂ := conj_notMem_of_notMem_transfer hmap hv
  rw [cauchyTransform_eq _ hv, cauchyTransform_eq L hcv, conjFunctional_apply,
    sigmaTransfer_kernelFun hmap hv hcv]

end Transfer

/-! ## Pullback along the functional-equation reflection -/

section Reflection

variable {K₁ K₂ : Set ℂ} [CompactSpace K₁] [CompactSpace K₂]

/-- The reflection `z ↦ 1 - z` as a map between two carriers exchanged by it. -/
def feReflMap (hmap : ∀ z ∈ K₁, 1 - z ∈ K₂) : C(K₁, K₂) :=
  ⟨fun z => ⟨1 - (z : ℂ), hmap (z : ℂ) z.2⟩,
    Continuous.subtype_mk (continuous_const.sub continuous_subtype_val) _⟩

omit [CompactSpace K₁] [CompactSpace K₂] in
@[simp] theorem feReflMap_apply (hmap : ∀ z ∈ K₁, 1 - z ∈ K₂) (z : K₁) :
    ((feReflMap hmap z : K₂) : ℂ) = 1 - (z : ℂ) := rfl

/-- Pullback of a functional along the reflection: a functional on the reflected carrier. -/
def feReflFunctional (hmap : ∀ z ∈ K₁, 1 - z ∈ K₂) (L : C(K₁, ℂ) →L[ℂ] ℂ) :
    C(K₂, ℂ) →L[ℂ] ℂ := L.comp (precompCLM (feReflMap hmap))

@[simp] theorem feReflFunctional_apply (hmap : ∀ z ∈ K₁, 1 - z ∈ K₂)
    (L : C(K₁, ℂ) →L[ℂ] ℂ) (h : C(K₂, ℂ)) :
    feReflFunctional hmap L h = L (precompCLM (feReflMap hmap) h) := rfl

omit [CompactSpace K₁] [CompactSpace K₂] in
theorem one_sub_notMem_of_notMem (hmap : ∀ z ∈ K₁, 1 - z ∈ K₂) {v : ℂ} (hv : v ∉ K₂) :
    1 - v ∉ K₁ := fun hc => hv (by simpa using hmap _ hc)

theorem precompCLM_feReflMap_kernelFun (hmap : ∀ z ∈ K₁, 1 - z ∈ K₂) {v : ℂ} (hv : v ∉ K₂) :
    precompCLM (feReflMap hmap) (kernelFun K₂ hv)
      = -kernelFun K₁ (one_sub_notMem_of_notMem hmap hv) := by
  ext z
  simp only [precompCLM_apply, kernelFun_apply, feReflMap_apply, ContinuousMap.neg_apply]
  rw [show v - (1 - (z : ℂ)) = -((1 - v) - (z : ℂ)) by ring, inv_neg]

/-- **The Cauchy transform of the reflected pullback.** -/
theorem cauchyTransform_feReflFunctional (hmap : ∀ z ∈ K₁, 1 - z ∈ K₂)
    (L : C(K₁, ℂ) →L[ℂ] ℂ) {v : ℂ} (hv : v ∉ K₂) :
    functionalCauchyTransform (feReflFunctional hmap L) v
      = -functionalCauchyTransform L (1 - v) := by
  rw [cauchyTransform_eq _ hv, cauchyTransform_eq L (one_sub_notMem_of_notMem hmap hv),
    feReflFunctional_apply, precompCLM_feReflMap_kernelFun hmap hv, map_neg]

end Reflection

/-- The Cauchy transform is unchanged by restricting a functional from a larger carrier. -/
theorem cauchyTransform_comp_precompCLM (hsub : Kc ⊆ Kt) (F : C(Kc, ℂ) →L[ℂ] ℂ) {v : ℂ}
    (hv : v ∉ Kt) :
    functionalCauchyTransform (F.comp (precompCLM (inclMap hsub))) v
      = functionalCauchyTransform F v := by
  rw [cauchyTransform_eq _ hv, cauchyTransform_eq F (fun hc => hv (hsub hc)),
    ContinuousLinearMap.comp_apply, precompCLM_kernelFun hsub hv]

end GaloisForLFunctions.HTGeometry
