import GaloisForLFunctions.HTGeometry.CDGARelTensor

/-!
# The tensor product over the algebra is functorial in the right variable

A morphism of the right factor carries a relator to the relator with the cell argument replaced by
its image, because the morphism is equivariant.  So the relations are preserved and the map
descends.

* `HTGeometry.tensorMapRight_relTensorRelator` : the relator correspondence.
* `HTGeometry.relTensorMapRight` : the descended morphism.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  {N' : ℕ → Type w} [∀ n, AddCommGroup (N' n)] [∀ n, Module R (N' n)]
  {P : CDGAModuleStructure A M} {Q : CDGAModuleStructure A N} {Q' : CDGAModuleStructure A N'}

/-- Functoriality in the right variable on a single-bidegree element. -/
theorem tensorMapRight_tensorSingle (P : CDGAModuleStructure A M) (ψ : CDGAModuleHom Q Q')
    {n a b : ℕ} (h : (a, b).1 + (a, b).2 = n) (z : TensorProduct R (M a) (N b)) :
    (tensorMapRight P ψ).toFun n (tensorSingle (N := N) ⟨(a, b), h⟩ z)
      = tensorSingle (N := N') ⟨(a, b), h⟩
        (TensorProduct.map LinearMap.id (ψ.mapₗ b) z) := by
  funext p
  obtain ⟨⟨a', b'⟩, h'⟩ := p
  rw [tensorMapRight_toFun]
  by_cases hab : a' = a ∧ b' = b
  · obtain ⟨rfl, rfl⟩ := hab
    rw [tensorSingle_same, tensorSingle_same]
  · rw [tensorSingle_ne _ (by
      rw [Ne, tensorIndex_eq_iff]
      omega), map_zero, tensorSingle_ne _ (by
      rw [Ne, tensorIndex_eq_iff]
      omega)]

/-- **A morphism of the right factor carries a relator to a relator.** -/
theorem tensorMapRight_relTensorRelator (P : CDGAModuleStructure A M) (ψ : CDGAModuleHom Q Q')
    {c a b n α β : ℕ} (hα : c + a = α) (hβ : c + b = β)
    (hn : (α, b).1 + (α, b).2 = n) (hn' : (a, β).1 + (a, β).2 = n)
    (x : X c) (m : M a) (v : N b) :
    (tensorMapRight P ψ).toFun n (relTensorRelator P Q hα hβ hn hn' x m v)
      = relTensorRelator P Q' hα hβ hn hn' x m (ψ.toFun b v) := by
  show (tensorMapRight P ψ).mapₗ n (relTensorRelator P Q hα hβ hn hn' x m v) = _
  simp only [relTensorRelator]
  rw [map_sub, map_smul]
  show ((-1 : R)) ^ (c * a)
      • (tensorMapRight P ψ).toFun n
        (tensorSingle (N := N) ⟨(α, b), hn⟩ (P.act hα x m ⊗ₜ[R] v))
      - (tensorMapRight P ψ).toFun n
        (tensorSingle (N := N) ⟨(a, β), hn'⟩ (m ⊗ₜ[R] Q.act hβ x v)) = _
  rw [tensorMapRight_tensorSingle, tensorMapRight_tensorSingle, TensorProduct.map_tmul,
    TensorProduct.map_tmul]
  show ((-1 : R)) ^ (c * a) • tensorSingle (N := N') ⟨(α, b), hn⟩
        ((LinearMap.id (P.act hα x m) : M α) ⊗ₜ[R] (ψ.mapₗ b v : N' b))
      - tensorSingle (N := N') ⟨(a, β), hn'⟩
        ((LinearMap.id m : M a) ⊗ₜ[R] (ψ.mapₗ β (Q.act hβ x v) : N' β)) = _
  rw [show (ψ.mapₗ β (Q.act hβ x v) : N' β) = Q'.act hβ x (ψ.toFun b v) from ψ.map_act hβ x v]
  rfl

/-- Functoriality in the right variable preserves the relations. -/
theorem relTensorRel_map_right (P : CDGAModuleStructure A M) (ψ : CDGAModuleHom Q Q') (n : ℕ)
    (f : TensorCarrier (R := R) M N n) (hf : f ∈ relTensorRel P Q n) :
    (tensorMapRight P ψ).toFun n f ∈ relTensorRel P Q' n := by
  refine Submodule.span_induction
    (p := fun g _ => (tensorMapRight P ψ).toFun n g ∈ relTensorRel P Q' n) ?_ ?_ ?_ ?_ hf
  · rintro g ⟨c, a, b, α, β, hα, hβ, hn, hn', x, m, v, rfl⟩
    rw [tensorMapRight_relTensorRelator]
    exact relTensorRelator_mem P Q' hα hβ hn hn' x m (ψ.toFun b v)
  · rw [show (tensorMapRight P ψ).toFun n 0 = 0 from ((tensorMapRight P ψ).mapₗ n).map_zero]
    exact Submodule.zero_mem _
  · intro g g' _ _ hg hg'
    rw [(tensorMapRight P ψ).map_add]
    exact Submodule.add_mem _ hg hg'
  · intro r g _ hg
    rw [(tensorMapRight P ψ).map_smul]
    exact Submodule.smul_mem _ _ hg

/-- **The tensor product over the algebra is functorial in the right variable.** -/
noncomputable def relTensorMapRight (P : CDGAModuleStructure A M) (ψ : CDGAModuleHom Q Q') :
    CDGAModuleHom (relTensorModule P Q) (relTensorModule P Q') where
  toFun n f :=
    Submodule.mapQ (relTensorRel P Q n) (relTensorRel P Q' n) ((tensorMapRight P ψ).mapₗ n)
      (fun g hg => relTensorRel_map_right P ψ n g hg) f
  map_add n f f' := by
    refine Quotient.inductionOn₂' f f' fun z z' => ?_
    exact congrArg (Submodule.Quotient.mk) ((tensorMapRight P ψ).map_add n z z')
  map_smul n r f := by
    refine Quotient.inductionOn' f fun z => ?_
    exact congrArg (Submodule.Quotient.mk) ((tensorMapRight P ψ).map_smul n r z)
  map_act h x f := by
    refine Quotient.inductionOn' f fun z => ?_
    exact congrArg (Submodule.Quotient.mk) ((tensorMapRight P ψ).map_act h x z)
  map_d n f := by
    refine Quotient.inductionOn' f fun z => ?_
    exact congrArg (Submodule.Quotient.mk) ((tensorMapRight P ψ).map_d n z)

@[simp] theorem relTensorMapRight_mk (P : CDGAModuleStructure A M) (ψ : CDGAModuleHom Q Q')
    (n : ℕ) (f : TensorCarrier (R := R) M N n) :
    (relTensorMapRight P ψ).toFun n (Submodule.Quotient.mk f)
      = Submodule.Quotient.mk ((tensorMapRight P ψ).toFun n f) := rfl

/-- The projection to the tensor product over the algebra is natural in the right variable. -/
theorem relTensorProj_naturality_right (P : CDGAModuleStructure A M) (ψ : CDGAModuleHom Q Q') :
    (relTensorMapRight P ψ).comp (relTensorProj P Q)
      = (relTensorProj P Q').comp (tensorMapRight P ψ) :=
  CDGAModuleHom.hom_ext fun _ _ => rfl

end GaloisForLFunctions.HTGeometry
