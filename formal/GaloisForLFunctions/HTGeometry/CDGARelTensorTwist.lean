import GaloisForLFunctions.HTGeometry.CDGARelTensor
import GaloisForLFunctions.HTGeometry.CDGACellInvariance

/-!
# The twist of a cell attachment descends to the tensor product over the algebra

The twist induced on a tensor product by a twist of the right factor carries a relator to a scalar
multiple of a relator — the sign of the twisting cochain against the algebra is exactly the sign the
relator changes by.  So it descends to the quotient, and the tensor product over the algebra of a
cell attachment has the twist it should.

* `HTGeometry.tensorSigmaR_tensorSingle` : the right-factor family on a single-bidegree element.
* `HTGeometry.tensorSigmaR_relTensorRelator` : its value on a relator.
* `HTGeometry.relTensorTwistR` : the descended twist.
* `HTGeometry.relTensorProdRightHom` : tensoring over the algebra commutes with attaching a cell.
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

/-- A relator is linear in its cell argument, so it vanishes there. -/
theorem relTensorRelator_zero {c a b n α β : ℕ} (hα : c + a = α) (hβ : c + b = β)
    (hn : (α, b).1 + (α, b).2 = n) (hn' : (a, β).1 + (a, β).2 = n) (x : X c) (m : M a) :
    relTensorRelator P Q hα hβ hn hn' x m (0 : N b) = 0 := by
  simp only [relTensorRelator]
  rw [show Q.act hβ x (0 : N b) = 0 from (Q.actₗ hβ x).map_zero,
    TensorProduct.tmul_zero, TensorProduct.tmul_zero, tensorSingle_zero, tensorSingle_zero,
    smul_zero, sub_zero]

/-- The preimage of a relator of the first factor is a relator of the cell attachment. -/
theorem mem_relTensorRel_of_fst (t : CDGATwist Q Qc) (n : ℕ) (r : TensorCarrier (R := R) M N n)
    (hr : r ∈ relTensorRel P Q n) :
    (tensorProdRight (R := R) (M := M) (N := N) (C := C) n).symm (r, 0)
      ∈ relTensorRel P (CDGAModuleStructure.twisted Q Qc t) n := by
  refine Submodule.span_induction
    (p := fun g _ => (tensorProdRight (R := R) (M := M) (N := N) (C := C) n).symm (g, 0)
      ∈ relTensorRel P (CDGAModuleStructure.twisted Q Qc t) n) ?_ ?_ ?_ ?_ hr
  · rintro g ⟨c, a, b, α, β, hα, hβ, hn, hn', x, m, v, rfl⟩
    have hsplit := tensorProdRight_relTensorRelator P Q Qc t hα hβ hn hn' x m (v, (0 : C b))
    rw [show ((v, (0 : C b)) : N b × C b).1 = v from rfl,
      show ((v, (0 : C b)) : N b × C b).2 = 0 from rfl,
      relTensorRelator_zero P Qc hα hβ hn hn' x m] at hsplit
    rw [← hsplit, LinearEquiv.symm_apply_apply]
    exact relTensorRelator_mem P (CDGAModuleStructure.twisted Q Qc t) hα hβ hn hn' x m (v, 0)
  · rw [show ((0 : TensorCarrier (R := R) M N n), (0 : TensorCarrier (R := R) M C n))
        = 0 from rfl, map_zero (tensorProdRight (R := R) (M := M) (N := N) (C := C) n).symm]
    exact Submodule.zero_mem _
  · intro g g' _ _ hg hg'
    rw [show ((g + g' : TensorCarrier (R := R) M N n),
        (0 : TensorCarrier (R := R) M C n)) = (g, 0) + (g', 0) from by
      refine Prod.ext rfl ?_
      exact (add_zero _).symm, map_add (tensorProdRight (R := R) (M := M) (N := N) (C := C) n).symm]
    exact Submodule.add_mem _ hg hg'
  · intro r' g _ hg
    rw [show ((r' • g : TensorCarrier (R := R) M N n),
        (0 : TensorCarrier (R := R) M C n)) = r' • (g, 0) from by
      refine Prod.ext rfl ?_
      exact (smul_zero _).symm, map_smul (tensorProdRight (R := R) (M := M) (N := N) (C := C) n).symm]
    exact Submodule.smul_mem _ _ hg

/-- The preimage of a relator of the second factor is a relator of the cell attachment. -/
theorem mem_relTensorRel_of_snd (t : CDGATwist Q Qc) (n : ℕ) (r : TensorCarrier (R := R) M C n)
    (hr : r ∈ relTensorRel P Qc n) :
    (tensorProdRight (R := R) (M := M) (N := N) (C := C) n).symm (0, r)
      ∈ relTensorRel P (CDGAModuleStructure.twisted Q Qc t) n := by
  refine Submodule.span_induction
    (p := fun g _ => (tensorProdRight (R := R) (M := M) (N := N) (C := C) n).symm (0, g)
      ∈ relTensorRel P (CDGAModuleStructure.twisted Q Qc t) n) ?_ ?_ ?_ ?_ hr
  · rintro g ⟨c, a, b, α, β, hα, hβ, hn, hn', x, m, v, rfl⟩
    have hsplit := tensorProdRight_relTensorRelator P Q Qc t hα hβ hn hn' x m ((0 : N b), v)
    rw [show (((0 : N b), v) : N b × C b).1 = 0 from rfl,
      show (((0 : N b), v) : N b × C b).2 = v from rfl,
      relTensorRelator_zero P Q hα hβ hn hn' x m] at hsplit
    rw [← hsplit, LinearEquiv.symm_apply_apply]
    exact relTensorRelator_mem P (CDGAModuleStructure.twisted Q Qc t) hα hβ hn hn' x m (0, v)
  · rw [show ((0 : TensorCarrier (R := R) M N n), (0 : TensorCarrier (R := R) M C n))
        = 0 from rfl, map_zero (tensorProdRight (R := R) (M := M) (N := N) (C := C) n).symm]
    exact Submodule.zero_mem _
  · intro g g' _ _ hg hg'
    rw [show ((0 : TensorCarrier (R := R) M N n),
        (g + g' : TensorCarrier (R := R) M C n)) = (0, g) + (0, g') from by
      refine Prod.ext ?_ rfl
      exact (add_zero _).symm, map_add (tensorProdRight (R := R) (M := M) (N := N) (C := C) n).symm]
    exact Submodule.add_mem _ hg hg'
  · intro r' g _ hg
    rw [show ((0 : TensorCarrier (R := R) M N n),
        (r' • g : TensorCarrier (R := R) M C n)) = r' • (0, g) from by
      refine Prod.ext ?_ rfl
      exact (smul_zero _).symm, map_smul (tensorProdRight (R := R) (M := M) (N := N) (C := C) n).symm]
    exact Submodule.smul_mem _ _ hg

/-- **A class of the cell attachment is trivial exactly when both of its components are.**  This is
where the linearity of a relator in its cell argument is used: the image of the relator submodule
contains each factor separately, hence the whole product. -/
theorem relTensorRel_of_prodRight (t : CDGATwist Q Qc) (n : ℕ)
    (z : TensorCarrier (R := R) M (fun k => N k × C k) n)
    (h1 : (tensorProdRight (R := R) (M := M) (N := N) (C := C) n z).1 ∈ relTensorRel P Q n)
    (h2 : (tensorProdRight (R := R) (M := M) (N := N) (C := C) n z).2 ∈ relTensorRel P Qc n) :
    z ∈ relTensorRel P (CDGAModuleStructure.twisted Q Qc t) n := by
  have hz : z = (tensorProdRight (R := R) (M := M) (N := N) (C := C) n).symm
        ((tensorProdRight (R := R) (M := M) (N := N) (C := C) n z).1,
          (0 : TensorCarrier (R := R) M C n))
      + (tensorProdRight (R := R) (M := M) (N := N) (C := C) n).symm
        ((0 : TensorCarrier (R := R) M N n),
          (tensorProdRight (R := R) (M := M) (N := N) (C := C) n z).2) := by
    refine (tensorProdRight (R := R) (M := M) (N := N) (C := C) n).injective ?_
    rw [LinearEquiv.map_add, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · exact (add_zero _).symm
    · exact (zero_add _).symm
  rw [hz]
  exact Submodule.add_mem _ (mem_relTensorRel_of_fst P Q Qc t n _ h1)
    (mem_relTensorRel_of_snd P Q Qc t n _ h2)

end Splitting

section Comparison

variable (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
  (Qc : CDGAModuleStructure A C)

/-- The comparison of a cell attachment with the attachment of the comparisons, before descent. -/
noncomputable def relTensorProdRightMap (n : ℕ) :
    TensorCarrier (R := R) M (fun k => N k × C k) n →ₗ[R]
      (RelTensorCarrier P Q n × RelTensorCarrier P Qc n) :=
  (LinearMap.prodMap (relTensorRel P Q n).mkQ (relTensorRel P Qc n).mkQ).comp
    (tensorProdRight (R := R) (M := M) (N := N) (C := C) n).toLinearMap

@[simp] theorem relTensorProdRightMap_apply (n : ℕ)
    (z : TensorCarrier (R := R) M (fun k => N k × C k) n) :
    relTensorProdRightMap P Q Qc n z
      = (Submodule.Quotient.mk (tensorProdRight (R := R) (M := M) (N := N) (C := C) n z).1,
         Submodule.Quotient.mk (tensorProdRight (R := R) (M := M) (N := N) (C := C) n z).2) :=
  rfl

/-- The comparison kills the relations of the cell attachment. -/
theorem relTensorProdRightMap_ker (t : CDGATwist Q Qc) (n : ℕ)
    (z : TensorCarrier (R := R) M (fun k => N k × C k) n)
    (hz : z ∈ relTensorRel P (CDGAModuleStructure.twisted Q Qc t) n) :
    relTensorProdRightMap P Q Qc n z = 0 := by
  refine Submodule.span_induction
    (p := fun g _ => relTensorProdRightMap P Q Qc n g = 0) ?_ ?_ ?_ ?_ hz
  · rintro g ⟨c, a, b, α, β, hα, hβ, hn, hn', x, m, v, rfl⟩
    rw [relTensorProdRightMap_apply,
      tensorProdRight_relTensorRelator P Q Qc t hα hβ hn hn' x m v]
    refine Prod.ext ?_ ?_
    · exact (Submodule.Quotient.mk_eq_zero _).2
        (relTensorRelator_mem P Q hα hβ hn hn' x m v.1)
    · exact (Submodule.Quotient.mk_eq_zero _).2
        (relTensorRelator_mem P Qc hα hβ hn hn' x m v.2)
  · exact map_zero _
  · intro g g' _ _ hg hg'
    rw [map_add, hg, hg', add_zero]
  · intro r g _ hg
    rw [map_smul, hg, smul_zero]

/-- **Tensoring over the algebra commutes with attaching a cell.** -/
noncomputable def relTensorProdRightHom (t : CDGATwist Q Qc) :
    CDGAModuleHom (relTensorModule P (CDGAModuleStructure.twisted Q Qc t))
      (CDGAModuleStructure.twisted (relTensorModule P Q) (relTensorModule P Qc)
        (relTensorTwistR P Q Qc t)) where
  toFun n f := Submodule.liftQ _ (relTensorProdRightMap P Q Qc n)
    (fun g hg => relTensorProdRightMap_ker P Q Qc t n g hg) f
  map_add n f f' := by
    refine Quotient.inductionOn₂' f f' fun z z' => ?_
    exact map_add (relTensorProdRightMap P Q Qc n) z z'
  map_smul n r f := by
    refine Quotient.inductionOn' f fun z => ?_
    exact map_smul (relTensorProdRightMap P Q Qc n) r z
  map_act h x f := by
    refine Quotient.inductionOn' f fun z => ?_
    show relTensorProdRightMap P Q Qc _
        (tensorAct P (CDGAModuleStructure.twisted Q Qc t) h x z) = _
    rw [relTensorProdRightMap_apply, tensorProdRight_tensorAct]
    rfl
  map_d n f := by
    refine Quotient.inductionOn' f fun z => ?_
    show relTensorProdRightMap P Q Qc (n + 1)
        (tensorD P (CDGAModuleStructure.twisted Q Qc t) n z) = _
    rw [relTensorProdRightMap_apply,
      show tensorD P (CDGAModuleStructure.twisted Q Qc t) n z
          = tensorDL P (CDGAModuleStructure.twisted Q Qc t) n z
            + tensorDR P (CDGAModuleStructure.twisted Q Qc t) n z from rfl,
      map_add, tensorProdRight_tensorDL, tensorProdRight_tensorDR]
    refine Prod.ext ?_ rfl
    show Submodule.Quotient.mk (tensorDL P Q n _ + (tensorDR P Q n _ + tensorSigmaR _ n _))
      = Submodule.Quotient.mk (tensorD P Q n _) + Submodule.Quotient.mk (tensorSigmaR _ n _)
    rw [← Submodule.Quotient.mk_add]
    exact congrArg _ (add_assoc _ _ _).symm

@[simp] theorem relTensorProdRightHom_mk (t : CDGATwist Q Qc) (n : ℕ)
    (z : TensorCarrier (R := R) M (fun k => N k × C k) n) :
    (relTensorProdRightHom P Q Qc t).toFun n (Submodule.Quotient.mk z)
      = relTensorProdRightMap P Q Qc n z := rfl

/-- **The comparison is a degreewise bijection.** -/
theorem relTensorProdRightHom_bijective (t : CDGATwist Q Qc) (n : ℕ) :
    Function.Bijective ((relTensorProdRightHom P Q Qc t).toFun n) := by
  constructor
  · refine fun a b => Quotient.inductionOn₂' a b fun z z' hzz => ?_
    have h1 : Submodule.Quotient.mk
          (tensorProdRight (R := R) (M := M) (N := N) (C := C) n z).1
        = (Submodule.Quotient.mk
          (tensorProdRight (R := R) (M := M) (N := N) (C := C) n z').1
          : RelTensorCarrier P Q n) := congrArg Prod.fst hzz
    have h2 : Submodule.Quotient.mk
          (tensorProdRight (R := R) (M := M) (N := N) (C := C) n z).2
        = (Submodule.Quotient.mk
          (tensorProdRight (R := R) (M := M) (N := N) (C := C) n z').2
          : RelTensorCarrier P Qc n) := congrArg Prod.snd hzz
    refine (Submodule.Quotient.eq _).2 ?_
    refine relTensorRel_of_prodRight P Q Qc t n (z - z') ?_ ?_
    · rw [map_sub]
      exact (Submodule.Quotient.eq _).1 h1
    · rw [map_sub]
      exact (Submodule.Quotient.eq _).1 h2
  · rintro ⟨u, v⟩
    refine Quotient.inductionOn' u fun zu => ?_
    refine Quotient.inductionOn' v fun zv => ?_
    refine ⟨Submodule.Quotient.mk
      ((tensorProdRight (R := R) (M := M) (N := N) (C := C) n).symm (zu, zv)), ?_⟩
    show relTensorProdRightMap P Q Qc n _ = _
    rw [relTensorProdRightMap_apply, LinearEquiv.apply_symm_apply]
    rfl

/-- **Tensoring over the algebra with a cell attachment is a full quasi-isomorphism onto the cell
attachment of the tensor products.** -/
theorem relTensorProdRightHom_isQuasiIsoFull (t : CDGATwist Q Qc) :
    (relTensorProdRightHom P Q Qc t).IsQuasiIsoFull :=
  CDGAModuleHom.IsQuasiIsoFull.of_bijective (relTensorProdRightHom_bijective P Q Qc t)

end Comparison

end GaloisForLFunctions.HTGeometry
