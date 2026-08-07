import GaloisForLFunctions.HTGeometry.CDGARelTensor

/-!
# The twist of a cell attachment descends to the tensor product over the algebra

The twist induced on a tensor product by a twist of the right factor carries a relator to a scalar
multiple of a relator — the sign of the twisting cochain against the algebra is exactly the sign the
relator changes by.  So it descends to the quotient, and the tensor product over the algebra of a
cell attachment has the twist it should.

* `HTGeometry.tensorSigmaR_tensorSingle` : the right-factor family on a single-bidegree element.
* `HTGeometry.tensorSigmaR_relTensorRelator` : its value on a relator.
* `HTGeometry.relTensorTwistR` : the descended twist.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  {C : ℕ → Type w} [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]

/-- A right-factor family on a single-bidegree element is a single-bidegree element. -/
theorem tensorSigmaR_tensorSingle (σ : ∀ n, C n →ₗ[R] N (n + 1)) {m a b : ℕ}
    (h : (a, b).1 + (a, b).2 = m) (z : TensorProduct R (M a) (C b)) :
    tensorSigmaR (M := M) σ m (tensorSingle (N := C) ⟨(a, b), h⟩ z)
      = tensorSingle (N := N) (⟨(a, b + 1), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = m + 1})
        (((-1 : R)) ^ a • TensorProduct.map LinearMap.id (σ b) z) := by
  funext p
  obtain ⟨⟨a', b'⟩, h'⟩ := p
  cases b' with
  | zero =>
      rw [tensorSigmaR_zero, tensorSingle_ne _ (by
        rw [Ne, tensorIndex_eq_iff]
        omega)]
  | succ b'' =>
      rw [tensorSigmaR_succ]
      by_cases hab : a' = a ∧ b'' = b
      · obtain ⟨rfl, rfl⟩ := hab
        rw [tensorSingle_same, tensorSingle_same]
      · rw [tensorSingle_ne _ (by
          rw [Ne, tensorIndex_eq_iff]
          omega), map_zero, smul_zero, tensorSingle_ne _ (by
          rw [Ne, tensorIndex_eq_iff]
          omega)]

section Descent

variable (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
  (Qc : CDGAModuleStructure A C)

/-- **The induced twist carries a relator to a multiple of a relator.**  The sign the twisting
cochain picks up against the algebra is exactly the sign the relator changes by. -/
theorem tensorSigmaR_relTensorRelator (t : CDGATwist Q Qc) {c a b n α β : ℕ}
    (hα : c + a = α) (hβ : c + b = β)
    (hn : (α, b).1 + (α, b).2 = n) (hn' : (a, β).1 + (a, β).2 = n)
    (x : X c) (m : M a) (v : C b) :
    tensorSigmaR (M := M) (fun k => t.τₗ k) n
        (relTensorRelator P Qc hα hβ hn hn' x m v)
      = ((-1 : R)) ^ (a + c) • relTensorRelator P Q hα
          (show c + (b + 1) = β + 1 by omega)
          (show (α, b + 1).1 + (α, b + 1).2 = n + 1 by omega)
          (show (a, β + 1).1 + (a, β + 1).2 = n + 1 by omega) x m (t.τ b v) := by
  simp only [relTensorRelator]
  rw [show tensorSigmaR (M := M) (fun k => t.τₗ k) n
        (((-1 : R)) ^ (c * a) • tensorSingle (N := C) ⟨(α, b), hn⟩ (P.act hα x m ⊗ₜ[R] v)
          - tensorSingle (N := C) ⟨(a, β), hn'⟩ (m ⊗ₜ[R] Qc.act hβ x v))
      = ((-1 : R)) ^ (c * a) • tensorSigmaR (M := M) (fun k => t.τₗ k) n
          (tensorSingle (N := C) ⟨(α, b), hn⟩ (P.act hα x m ⊗ₜ[R] v))
        - tensorSigmaR (M := M) (fun k => t.τₗ k) n
          (tensorSingle (N := C) ⟨(a, β), hn'⟩ (m ⊗ₜ[R] Qc.act hβ x v)) by
      rw [show ((-1 : R)) ^ (c * a) • tensorSingle (N := C) ⟨(α, b), hn⟩
            (P.act hα x m ⊗ₜ[R] v)
          - tensorSingle (N := C) ⟨(a, β), hn'⟩ (m ⊗ₜ[R] Qc.act hβ x v)
        = ((-1 : R)) ^ (c * a) • tensorSingle (N := C) ⟨(α, b), hn⟩ (P.act hα x m ⊗ₜ[R] v)
          + (-1 : R) • tensorSingle (N := C) ⟨(a, β), hn'⟩ (m ⊗ₜ[R] Qc.act hβ x v) by
        rw [neg_one_smul, ← sub_eq_add_neg],
        tensorSigmaR_add, tensorSigmaR_smul, tensorSigmaR_smul, neg_one_smul,
        ← sub_eq_add_neg],
    tensorSigmaR_tensorSingle, tensorSigmaR_tensorSingle, TensorProduct.map_tmul,
    TensorProduct.map_tmul]
  show ((-1 : R)) ^ (c * a) • tensorSingle (N := N)
        (⟨(α, b + 1), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n + 1})
        (((-1 : R)) ^ α • ((LinearMap.id (P.act hα x m) : M α) ⊗ₜ[R] t.τ b v))
      - tensorSingle (N := N) (⟨(a, β + 1), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n + 1})
        (((-1 : R)) ^ a • ((LinearMap.id m : M a) ⊗ₜ[R] t.τ β (Qc.act hβ x v))) = _
  rw [t.τ_act hβ x v]
  show _ = ((-1 : R)) ^ (a + c) •
      (((-1 : R)) ^ (c * a) • tensorSingle (N := N)
          (⟨(α, b + 1), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n + 1})
          (P.act hα x m ⊗ₜ[R] t.τ b v)
        - tensorSingle (N := N) (⟨(a, β + 1), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n + 1})
          (m ⊗ₜ[R] Q.act (show c + (b + 1) = β + 1 by omega) x (t.τ b v)))
  rw [TensorProduct.tmul_smul, tensorSingle_smul, tensorSingle_smul, tensorSingle_smul,
    smul_smul, smul_smul, smul_sub, smul_smul]
  have h1 : ((-1 : R)) ^ (c * a) * ((-1 : R)) ^ α
      = ((-1 : R)) ^ (a + c) * ((-1 : R)) ^ (c * a) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have h2 : ((-1 : R)) ^ a * ((-1 : R)) ^ c = ((-1 : R)) ^ (a + c) := by
    rw [← pow_add]
  rw [h1, h2]
  rfl

/-- The right-factor family kills zero. -/
theorem tensorSigmaR_zero_apply (σ : ∀ n, C n →ₗ[R] N (n + 1)) (m : ℕ) :
    tensorSigmaR (M := M) σ m (0 : TensorCarrier (R := R) M C m) = 0 := by
  have h := tensorSigmaR_smul (M := M) σ m (0 : R) 0
  rwa [zero_smul, zero_smul] at h

/-- The right-factor family as a linear map. -/
noncomputable def tensorSigmaRₗ (σ : ∀ n, C n →ₗ[R] N (n + 1)) (m : ℕ) :
    TensorCarrier (R := R) M C m →ₗ[R] TensorCarrier (R := R) M N (m + 1) where
  toFun := tensorSigmaR (M := M) σ m
  map_add' := tensorSigmaR_add (M := M) σ m
  map_smul' := fun r f => tensorSigmaR_smul (M := M) σ m r f

/-- **The induced twist preserves the relations.** -/
theorem relTensorRel_tensorSigmaR (t : CDGATwist Q Qc) (n : ℕ)
    (f : TensorCarrier (R := R) M C n) (hf : f ∈ relTensorRel P Qc n) :
    tensorSigmaR (M := M) (fun k => t.τₗ k) n f ∈ relTensorRel P Q (n + 1) := by
  refine Submodule.span_induction
    (p := fun g _ => tensorSigmaR (M := M) (fun k => t.τₗ k) n g ∈ relTensorRel P Q (n + 1))
    ?_ ?_ ?_ ?_ hf
  · rintro g ⟨c, a, b, α, β, hα, hβ, hn, hn', x, m, v, rfl⟩
    rw [tensorSigmaR_relTensorRelator P Q Qc t hα hβ hn hn' x m v]
    exact Submodule.smul_mem _ _ (relTensorRelator_mem P Q _ _ _ _ x m (t.τ b v))
  · rw [tensorSigmaR_zero_apply]
    exact Submodule.zero_mem _
  · intro g g' _ _ hg hg'
    rw [tensorSigmaR_add]
    exact Submodule.add_mem _ hg hg'
  · intro r g _ hg
    rw [tensorSigmaR_smul]
    exact Submodule.smul_mem _ _ hg

/-- **The twist of a cell attachment descends to the tensor product over the algebra.** -/
noncomputable def relTensorTwistR (t : CDGATwist Q Qc) :
    CDGATwist (relTensorModule P Q) (relTensorModule P Qc) where
  τ n v := Submodule.mapQ (relTensorRel P Qc n) (relTensorRel P Q (n + 1))
    (tensorSigmaRₗ (M := M) (fun k => t.τₗ k) n)
    (fun g hg => relTensorRel_tensorSigmaR P Q Qc t n g hg) v
  τ_add n v v' := by
    refine Quotient.inductionOn₂' v v' fun z z' => ?_
    exact congrArg (Submodule.Quotient.mk) (tensorSigmaR_add (M := M) (fun k => t.τₗ k) n z z')
  τ_smul n r v := by
    refine Quotient.inductionOn' v fun z => ?_
    exact congrArg (Submodule.Quotient.mk) (tensorSigmaR_smul (M := M) (fun k => t.τₗ k) n r z)
  τ_act h x v := by
    refine Quotient.inductionOn' v fun z => ?_
    exact congrArg (Submodule.Quotient.mk)
      (tensorSigmaR_tensorAct P Q Qc (fun k => t.τₗ k) h x z)
  τ_d n v := by
    refine Quotient.inductionOn' v fun z => ?_
    exact congrArg (Submodule.Quotient.mk)
      (tensorD_tensorSigmaR_add P Q Qc (fun k => t.τₗ k) (fun k z => t.τ_d k z) n z)

@[simp] theorem relTensorTwistR_mk (t : CDGATwist Q Qc) (n : ℕ)
    (z : TensorCarrier (R := R) M C n) :
    (relTensorTwistR P Q Qc t).τ n (Submodule.Quotient.mk z)
      = Submodule.Quotient.mk (tensorSigmaR (M := M) (fun k => t.τₗ k) n z) := rfl

end Descent

section Splitting

variable (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
  (Qc : CDGAModuleStructure A C)

/-- Distributivity of a single-bidegree element. -/
theorem tensorProdRight_tensorSingle {n a b : ℕ} (h : (a, b).1 + (a, b).2 = n)
    (z : TensorProduct R (M a) (N b × C b)) :
    tensorProdRight (R := R) (M := M) (N := N) (C := C) n
        (tensorSingle (N := fun k => N k × C k) ⟨(a, b), h⟩ z)
      = (tensorSingle (N := N) ⟨(a, b), h⟩
          (TensorProduct.prodRight R R (M a) (N b) (C b) z).1,
         tensorSingle (N := C) ⟨(a, b), h⟩
          (TensorProduct.prodRight R R (M a) (N b) (C b) z).2) := by
  refine Prod.ext ?_ ?_
  · funext p
    show (tensorProdRight (R := R) (M := M) (N := N) (C := C) n
        (tensorSingle (N := fun k => N k × C k) ⟨(a, b), h⟩ z)).1 p
      = tensorSingle (N := N) ⟨(a, b), h⟩
        (TensorProduct.prodRight R R (M a) (N b) (C b) z).1 p
    rw [tensorProdRight_fst]
    by_cases hp : p = (⟨(a, b), h⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
    · subst hp
      rw [tensorSingle_same, tensorSingle_same]
    · rw [tensorSingle_ne _ hp, map_zero, Prod.fst_zero, tensorSingle_ne _ hp]
  · funext p
    show (tensorProdRight (R := R) (M := M) (N := N) (C := C) n
        (tensorSingle (N := fun k => N k × C k) ⟨(a, b), h⟩ z)).2 p
      = tensorSingle (N := C) ⟨(a, b), h⟩
        (TensorProduct.prodRight R R (M a) (N b) (C b) z).2 p
    rw [tensorProdRight_snd]
    by_cases hp : p = (⟨(a, b), h⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
    · subst hp
      rw [tensorSingle_same, tensorSingle_same]
    · rw [tensorSingle_ne _ hp, map_zero, Prod.snd_zero, tensorSingle_ne _ hp]

/-- **A relator of a cell attachment splits into the pair of relators of the two factors.**  The
action on a cell attachment is componentwise — the twist enters only the differential — so nothing
mixes. -/
theorem tensorProdRight_relTensorRelator (t : CDGATwist Q Qc) {c a b n α β : ℕ}
    (hα : c + a = α) (hβ : c + b = β)
    (hn : (α, b).1 + (α, b).2 = n) (hn' : (a, β).1 + (a, β).2 = n)
    (x : X c) (m : M a) (v : N b × C b) :
    tensorProdRight (R := R) (M := M) (N := N) (C := C) n
        (relTensorRelator P (CDGAModuleStructure.twisted Q Qc t) hα hβ hn hn' x m v)
      = (relTensorRelator P Q hα hβ hn hn' x m v.1,
         relTensorRelator P Qc hα hβ hn hn' x m v.2) := by
  simp only [relTensorRelator]
  rw [show ((-1 : R)) ^ (c * a) • tensorSingle (N := fun k => N k × C k) ⟨(α, b), hn⟩
        (P.act hα x m ⊗ₜ[R] v)
      - tensorSingle (N := fun k => N k × C k) ⟨(a, β), hn'⟩
        (m ⊗ₜ[R] (CDGAModuleStructure.twisted Q Qc t).act hβ x v)
    = ((-1 : R)) ^ (c * a) • tensorSingle (N := fun k => N k × C k) ⟨(α, b), hn⟩
        (P.act hα x m ⊗ₜ[R] v)
      + (-1 : R) • tensorSingle (N := fun k => N k × C k) ⟨(a, β), hn'⟩
        (m ⊗ₜ[R] (CDGAModuleStructure.twisted Q Qc t).act hβ x v) by
      rw [neg_one_smul, ← sub_eq_add_neg],
    map_add, map_smul, map_smul, tensorProdRight_tensorSingle, tensorProdRight_tensorSingle]
  refine Prod.ext ?_ ?_
  · show ((-1 : R)) ^ (c * a) • tensorSingle (N := N) ⟨(α, b), hn⟩
        (TensorProduct.prodRight R R (M α) (N b) (C b) (P.act hα x m ⊗ₜ[R] v)).1
      + (-1 : R) • tensorSingle (N := N) ⟨(a, β), hn'⟩
        (TensorProduct.prodRight R R (M a) (N β) (C β)
          (m ⊗ₜ[R] (CDGAModuleStructure.twisted Q Qc t).act hβ x v)).1 = _
    rw [TensorProduct.prodRight_tmul, TensorProduct.prodRight_tmul, neg_one_smul,
      ← sub_eq_add_neg]
    rfl
  · show ((-1 : R)) ^ (c * a) • tensorSingle (N := C) ⟨(α, b), hn⟩
        (TensorProduct.prodRight R R (M α) (N b) (C b) (P.act hα x m ⊗ₜ[R] v)).2
      + (-1 : R) • tensorSingle (N := C) ⟨(a, β), hn'⟩
        (TensorProduct.prodRight R R (M a) (N β) (C β)
          (m ⊗ₜ[R] (CDGAModuleStructure.twisted Q Qc t).act hβ x v)).2 = _
    rw [TensorProduct.prodRight_tmul, TensorProduct.prodRight_tmul, neg_one_smul,
      ← sub_eq_add_neg]
    rfl

end Splitting

end GaloisForLFunctions.HTGeometry
