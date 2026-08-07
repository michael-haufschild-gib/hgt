import GaloisForLFunctions.HTGeometry.CDGATensorSingle

/-!
# The tensor product of differential graded modules over the algebra

`tensorModule` is the tensor product over the ground ring, with the algebra acting through the left
factor.  The tensor product *over the algebra* is its quotient by the relators that move an element
of the algebra across the tensor sign, with the Koszul sign of the transposition — a left module
being a right module through `m · x = (−1)^{|x||m|} x · m`.

The point of the construction is that the relators are stable under both structure maps, so the
quotient is again a differential graded module:

* under the differential a relator becomes a combination of three relators, one for each of the
  three factors being differentiated, with the signs the Leibniz rule produces;
* under the action a relator becomes a single relator, with no sign at all — the sign of graded
  commutativity in the algebra cancels against the sign of the relator.

* `HTGeometry.relTensorRelator` : the relator.
* `HTGeometry.tensorAct_relTensorRelator`, `HTGeometry.tensorD_relTensorRelator` : the two
  stability computations.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]

section Relator

variable (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)

/-- **The relator of the tensor product over the algebra.**  The two target degrees are supplied
separately so that a differentiated factor can be placed where the Leibniz rule puts it. -/
noncomputable def relTensorRelator {c a b n α β : ℕ} (hα : c + a = α) (hβ : c + b = β)
    (hn : (α, b).1 + (α, b).2 = n) (hn' : (a, β).1 + (a, β).2 = n)
    (x : X c) (m : M a) (v : N b) : TensorCarrier (R := R) M N n :=
  ((-1 : R)) ^ (c * a) • tensorSingle (N := N) ⟨(α, b), hn⟩ (P.act hα x m ⊗ₜ[R] v)
    - tensorSingle (N := N) ⟨(a, β), hn'⟩ (m ⊗ₜ[R] Q.act hβ x v)

/-- **The action carries a relator to a relator**, with no sign: the sign of graded commutativity in
the algebra cancels against the sign of the relator. -/
theorem tensorAct_relTensorRelator {d c a b n α β m' : ℕ} (hy : d + n = m')
    (hα : c + a = α) (hβ : c + b = β)
    (hn : (α, b).1 + (α, b).2 = n) (hn' : (a, β).1 + (a, β).2 = n)
    (y : X d) (x : X c) (m : M a) (v : N b) :
    tensorAct P Q hy y (relTensorRelator P Q hα hβ hn hn' x m v)
      = relTensorRelator P Q (show c + (d + a) = d + α by omega) hβ
          (show (d + α, b).1 + (d + α, b).2 = m' by omega)
          (show (d + a, β).1 + (d + a, β).2 = m' by omega)
          x (P.act (rfl : d + a = d + a) y m) v := by
  show tensorAct P Q hy y
      (((-1 : R)) ^ (c * a) • tensorSingle (N := N) ⟨(α, b), hn⟩ (P.act hα x m ⊗ₜ[R] v)
        - tensorSingle (N := N) ⟨(a, β), hn'⟩ (m ⊗ₜ[R] Q.act hβ x v)) = _
  rw [show ((-1 : R)) ^ (c * a) • tensorSingle (N := N) ⟨(α, b), hn⟩ (P.act hα x m ⊗ₜ[R] v)
        - tensorSingle (N := N) ⟨(a, β), hn'⟩ (m ⊗ₜ[R] Q.act hβ x v)
      = ((-1 : R)) ^ (c * a) • tensorSingle (N := N) ⟨(α, b), hn⟩ (P.act hα x m ⊗ₜ[R] v)
        + (-1 : R) • tensorSingle (N := N) ⟨(a, β), hn'⟩ (m ⊗ₜ[R] Q.act hβ x v) by
      rw [neg_one_smul, ← sub_eq_add_neg],
    tensorAct_add_right, tensorAct_smul_right, tensorAct_smul_right,
    tensorAct_tensorSingle, tensorAct_tensorSingle, TensorProduct.map_tmul,
    TensorProduct.map_tmul]
  show ((-1 : R)) ^ (c * a) • tensorSingle (N := N)
        (⟨(d + α, b), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = m'})
        (P.act (rfl : d + α = d + α) y (P.act hα x m) ⊗ₜ[R] (LinearMap.id v : N b))
      + (-1 : R) • tensorSingle (N := N)
        (⟨(d + a, β), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = m'})
        (P.act (rfl : d + a = d + a) y m ⊗ₜ[R] (LinearMap.id (Q.act hβ x v) : N β))
      = _
  show _ = ((-1 : R)) ^ (c * (d + a)) • tensorSingle (N := N)
        (⟨(d + α, b), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = m'})
        (P.act (show c + (d + a) = d + α by omega) x
          (P.act (rfl : d + a = d + a) y m) ⊗ₜ[R] v)
      - tensorSingle (N := N) (⟨(d + a, β), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = m'})
        (P.act (rfl : d + a = d + a) y m ⊗ₜ[R] Q.act hβ x v)
  rw [neg_one_smul, ← sub_eq_add_neg]
  congr 1
  have hxy : P.act (show c + (d + a) = d + α by omega) x (P.act (rfl : d + a = d + a) y m)
      = ((-1 : R)) ^ (c * d) • P.act (rfl : d + α = d + α) y (P.act hα x m) := by
    rw [← P.act_assoc (show c + d = c + d from rfl) (show c + d + a = d + α by omega)
      (rfl : d + a = d + a) (show c + (d + a) = d + α by omega) x y m,
      A.mul_comm (show c + d = c + d from rfl) (show d + c = c + d by omega) x y,
      P.act_smul_left, P.act_assoc (show d + c = c + d by omega)
        (show c + d + a = d + α by omega) hα (rfl : d + α = d + α) y x m]
  have hpow : ((-1 : R)) ^ (c * (d + a) + c * d) = ((-1 : R)) ^ (c * a) := by
    rw [show c * (d + a) + c * d = c * a + 2 * (c * d) by ring, pow_add, pow_mul]
    norm_num
  rw [hxy, ← TensorProduct.smul_tmul', tensorSingle_smul, smul_smul, ← pow_add, hpow]
  rfl

/-- The differential of a difference. -/
theorem tensorD_sub (n : ℕ) (f g : TensorCarrier (R := R) M N n) :
    tensorD P Q n (f - g) = tensorD P Q n f - tensorD P Q n g := by
  rw [show f - g = f + (-1 : R) • g by rw [neg_one_smul, ← sub_eq_add_neg],
    tensorD_add, tensorD_smul, neg_one_smul, ← sub_eq_add_neg]

/-- **The differential carries a relator to a combination of three relators**, one for each factor
being differentiated, with the signs the Leibniz rule produces. -/
theorem tensorD_relTensorRelator {c a b n α β : ℕ} (hα : c + a = α) (hβ : c + b = β)
    (hn : (α, b).1 + (α, b).2 = n) (hn' : (a, β).1 + (a, β).2 = n)
    (x : X c) (m : M a) (v : N b) :
    tensorD P Q n (relTensorRelator P Q hα hβ hn hn' x m v)
      = ((-1 : R)) ^ a • relTensorRelator P Q
            (show c + 1 + a = α + 1 by omega) (show c + 1 + b = β + 1 by omega)
            (show (α + 1, b).1 + (α + 1, b).2 = n + 1 by omega)
            (show (a, β + 1).1 + (a, β + 1).2 = n + 1 by omega) (A.d c x) m v
        + relTensorRelator P Q
            (show c + (a + 1) = α + 1 by omega) hβ
            (show (α + 1, b).1 + (α + 1, b).2 = n + 1 by omega)
            (show (a + 1, β).1 + (a + 1, β).2 = n + 1 by omega) x (P.d a m) v
        + ((-1 : R)) ^ (a + c) • relTensorRelator P Q hα
            (show c + (b + 1) = β + 1 by omega)
            (show (α, b + 1).1 + (α, b + 1).2 = n + 1 by omega)
            (show (a, β + 1).1 + (a, β + 1).2 = n + 1 by omega) x m (Q.d b v) := by
  have hS1 : tensorD P Q n (tensorSingle (N := N) ⟨(α, b), hn⟩ (P.act hα x m ⊗ₜ[R] v))
      = tensorSingle (N := N)
          (⟨(α + 1, b), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n + 1})
          (P.act (show c + 1 + a = α + 1 by omega) (A.d c x) m ⊗ₜ[R] v)
        + ((-1 : R)) ^ c • tensorSingle (N := N)
          (⟨(α + 1, b), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n + 1})
          (P.act (show c + (a + 1) = α + 1 by omega) x (P.d a m) ⊗ₜ[R] v)
        + ((-1 : R)) ^ α • tensorSingle (N := N)
          (⟨(α, b + 1), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n + 1})
          (P.act hα x m ⊗ₜ[R] Q.d b v) := by
    rw [tensorD_tensorSingle, TensorProduct.map_tmul, TensorProduct.map_tmul]
    show tensorSingle (N := N)
          (⟨(α + 1, b), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n + 1})
          (P.d α (P.act hα x m) ⊗ₜ[R] (LinearMap.id v : N b))
        + tensorSingle (N := N)
          (⟨(α, b + 1), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n + 1})
          (((-1 : R)) ^ α • ((LinearMap.id (P.act hα x m) : M α) ⊗ₜ[R] Q.d b v)) = _
    rw [P.d_act hα x m, TensorProduct.add_tmul, tensorSingle_add,
      ← TensorProduct.smul_tmul', tensorSingle_smul, tensorSingle_smul]
    abel
  have hS2 : tensorD P Q n (tensorSingle (N := N) ⟨(a, β), hn'⟩ (m ⊗ₜ[R] Q.act hβ x v))
      = tensorSingle (N := N)
          (⟨(a + 1, β), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n + 1})
          (P.d a m ⊗ₜ[R] Q.act hβ x v)
        + ((-1 : R)) ^ a • tensorSingle (N := N)
          (⟨(a, β + 1), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n + 1})
          (m ⊗ₜ[R] Q.act (show c + 1 + b = β + 1 by omega) (A.d c x) v)
        + ((-1 : R)) ^ (a + c) • tensorSingle (N := N)
          (⟨(a, β + 1), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n + 1})
          (m ⊗ₜ[R] Q.act (show c + (b + 1) = β + 1 by omega) x (Q.d b v)) := by
    rw [tensorD_tensorSingle, TensorProduct.map_tmul, TensorProduct.map_tmul]
    show tensorSingle (N := N)
          (⟨(a + 1, β), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n + 1})
          (P.d a m ⊗ₜ[R] (LinearMap.id (Q.act hβ x v) : N β))
        + tensorSingle (N := N)
          (⟨(a, β + 1), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n + 1})
          (((-1 : R)) ^ a • ((LinearMap.id m : M a) ⊗ₜ[R] Q.d β (Q.act hβ x v))) = _
    rw [Q.d_act hβ x v, TensorProduct.tmul_add, TensorProduct.tmul_smul, smul_add,
      tensorSingle_add, tensorSingle_smul, tensorSingle_smul, tensorSingle_smul, smul_smul,
      ← pow_add]
    abel
  have hc1 : ((-1 : R)) ^ a * ((-1 : R)) ^ ((c + 1) * a) = ((-1 : R)) ^ (c * a) := by
    rw [← pow_add, show a + (c + 1) * a = c * a + 2 * a by ring, pow_add, pow_mul]
    norm_num
  have hc2 : ((-1 : R)) ^ (c * (a + 1)) = ((-1 : R)) ^ (c * a) * ((-1 : R)) ^ c := by
    rw [← pow_add, show c * a + c = c * (a + 1) by ring]
  have hc3 : ((-1 : R)) ^ (a + c) * ((-1 : R)) ^ (c * a)
      = ((-1 : R)) ^ (c * a) * ((-1 : R)) ^ α := by
    rw [mul_comm]
    congr 1
    rw [← hα]
    congr 1
    omega
  simp only [relTensorRelator]
  rw [tensorD_sub, tensorD_smul, hS1, hS2]
  simp only [smul_add, smul_sub, smul_smul]
  rw [hc1, hc2, hc3]
  abel

theorem tensorD_zero (n : ℕ) : tensorD P Q n (0 : TensorCarrier (R := R) M N n) = 0 := by
  have h := tensorD_smul P Q n 0 (0 : TensorCarrier (R := R) M N n)
  rw [zero_smul, zero_smul] at h
  exact h

theorem tensorAct_zero {b n m : ℕ} (h : b + n = m) (x : X b) :
    tensorAct P Q h x (0 : TensorCarrier (R := R) M N n) = 0 := by
  have h0 := tensorAct_smul_right P Q h 0 x (0 : TensorCarrier (R := R) M N n)
  rw [zero_smul, zero_smul] at h0
  exact h0

end Relator

section Quotient

variable (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)

/-- The set of relators in a total degree. -/
def relTensorSet (n : ℕ) : Set (TensorCarrier (R := R) M N n) :=
  {f | ∃ (c a b α β : ℕ) (hα : c + a = α) (hβ : c + b = β)
      (hn : (α, b).1 + (α, b).2 = n) (hn' : (a, β).1 + (a, β).2 = n)
      (x : X c) (m : M a) (v : N b), f = relTensorRelator P Q hα hβ hn hn' x m v}

/-- **The relations defining the tensor product over the algebra.** -/
noncomputable def relTensorRel (n : ℕ) : Submodule R (TensorCarrier (R := R) M N n) :=
  Submodule.span R (relTensorSet P Q n)

theorem relTensorRelator_mem {c a b n α β : ℕ} (hα : c + a = α) (hβ : c + b = β)
    (hn : (α, b).1 + (α, b).2 = n) (hn' : (a, β).1 + (a, β).2 = n)
    (x : X c) (m : M a) (v : N b) :
    relTensorRelator P Q hα hβ hn hn' x m v ∈ relTensorRel P Q n :=
  Submodule.subset_span ⟨c, a, b, α, β, hα, hβ, hn, hn', x, m, v, rfl⟩

/-- **The differential preserves the relations.** -/
theorem relTensorRel_tensorD (n : ℕ) (f : TensorCarrier (R := R) M N n)
    (hf : f ∈ relTensorRel P Q n) : tensorD P Q n f ∈ relTensorRel P Q (n + 1) := by
  refine Submodule.span_induction
    (p := fun g _ => tensorD P Q n g ∈ relTensorRel P Q (n + 1)) ?_ ?_ ?_ ?_ hf
  · rintro g ⟨c, a, b, α, β, hα, hβ, hn, hn', x, m, v, rfl⟩
    rw [tensorD_relTensorRelator]
    exact Submodule.add_mem _
      (Submodule.add_mem _
        (Submodule.smul_mem _ _ (relTensorRelator_mem P Q _ _ _ _ (A.d c x) m v))
        (relTensorRelator_mem P Q _ _ _ _ x (P.d a m) v))
      (Submodule.smul_mem _ _ (relTensorRelator_mem P Q _ _ _ _ x m (Q.d b v)))
  · rw [tensorD_zero]
    exact Submodule.zero_mem _
  · intro g g' _ _ hg hg'
    rw [tensorD_add]
    exact Submodule.add_mem _ hg hg'
  · intro r g _ hg
    rw [tensorD_smul]
    exact Submodule.smul_mem _ _ hg

/-- **The action preserves the relations.** -/
theorem relTensorRel_tensorAct {b n m : ℕ} (h : b + n = m) (y : X b)
    (f : TensorCarrier (R := R) M N n) (hf : f ∈ relTensorRel P Q n) :
    tensorAct P Q h y f ∈ relTensorRel P Q m := by
  refine Submodule.span_induction
    (p := fun g _ => tensorAct P Q h y g ∈ relTensorRel P Q m) ?_ ?_ ?_ ?_ hf
  · rintro g ⟨c, a, b', α, β, hα, hβ, hn, hn', x, m', v, rfl⟩
    rw [tensorAct_relTensorRelator]
    exact relTensorRelator_mem P Q _ _ _ _ x (P.act (rfl : b + a = b + a) y m') v
  · rw [tensorAct_zero]
    exact Submodule.zero_mem _
  · intro g g' _ _ hg hg'
    rw [tensorAct_add_right]
    exact Submodule.add_mem _ hg hg'
  · intro r g _ hg
    rw [tensorAct_smul_right]
    exact Submodule.smul_mem _ _ hg

/-- **The tensor product over the algebra**, degree by degree. -/
noncomputable abbrev RelTensorCarrier (n : ℕ) : Type w :=
  TensorCarrier (R := R) M N n ⧸ relTensorRel P Q n

/-- The total differential as a linear map. -/
noncomputable def tensorDₗ (n : ℕ) :
    TensorCarrier (R := R) M N n →ₗ[R] TensorCarrier (R := R) M N (n + 1) where
  toFun := tensorD P Q n
  map_add' := tensorD_add P Q n
  map_smul' := fun r f => tensorD_smul P Q n r f

/-- The action as a linear map. -/
noncomputable def tensorActₗ {b n m : ℕ} (h : b + n = m) (x : X b) :
    TensorCarrier (R := R) M N n →ₗ[R] TensorCarrier (R := R) M N m where
  toFun := tensorAct P Q h x
  map_add' := tensorAct_add_right P Q h x
  map_smul' := fun r f => tensorAct_smul_right P Q h r x f

/-- The differential of the tensor product over the algebra. -/
noncomputable def relTensorD (n : ℕ) :
    RelTensorCarrier P Q n →ₗ[R] RelTensorCarrier P Q (n + 1) :=
  Submodule.mapQ _ _ (tensorDₗ P Q n) fun f hf => relTensorRel_tensorD P Q n f hf

/-- The action on the tensor product over the algebra. -/
noncomputable def relTensorAct {b n m : ℕ} (h : b + n = m) (x : X b) :
    RelTensorCarrier P Q n →ₗ[R] RelTensorCarrier P Q m :=
  Submodule.mapQ _ _ (tensorActₗ P Q h x) fun f hf => relTensorRel_tensorAct P Q h x f hf

@[simp] theorem relTensorD_mk (n : ℕ) (f : TensorCarrier (R := R) M N n) :
    relTensorD P Q n (Submodule.Quotient.mk f) = Submodule.Quotient.mk (tensorD P Q n f) := rfl

@[simp] theorem relTensorAct_mk {b n m : ℕ} (h : b + n = m) (x : X b)
    (f : TensorCarrier (R := R) M N n) :
    relTensorAct P Q h x (Submodule.Quotient.mk f)
      = Submodule.Quotient.mk (tensorAct P Q h x f) := rfl

/-- **The tensor product of two differential graded modules over the algebra.** -/
noncomputable def relTensorModule : CDGAModuleStructure A (RelTensorCarrier P Q) where
  act h x f := relTensorAct P Q h x f
  d n f := relTensorD P Q n f
  act_add_left h x x' f := by
    refine Quotient.inductionOn' f fun z => ?_
    exact congrArg (Submodule.Quotient.mk) (tensorAct_add_left P Q h x x' z)
  act_add_right h x f f' := by
    refine Quotient.inductionOn₂' f f' fun z z' => ?_
    exact congrArg (Submodule.Quotient.mk) (tensorAct_add_right P Q h x z z')
  act_smul_left h r x f := by
    refine Quotient.inductionOn' f fun z => ?_
    exact congrArg (Submodule.Quotient.mk) (tensorAct_smul_left P Q h r x z)
  act_smul_right h r x f := by
    refine Quotient.inductionOn' f fun z => ?_
    exact congrArg (Submodule.Quotient.mk) (tensorAct_smul_right P Q h r x z)
  act_assoc h₁ h₂ h₃ h₄ x y f := by
    refine Quotient.inductionOn' f fun z => ?_
    exact congrArg (Submodule.Quotient.mk) (tensorAct_assoc P Q h₁ h₂ h₃ h₄ x y z)
  d_add n f f' := by
    refine Quotient.inductionOn₂' f f' fun z z' => ?_
    exact congrArg (Submodule.Quotient.mk) (tensorD_add P Q n z z')
  d_smul n r f := by
    refine Quotient.inductionOn' f fun z => ?_
    exact congrArg (Submodule.Quotient.mk) (tensorD_smul P Q n r z)
  d_d n f := by
    refine Quotient.inductionOn' f fun z => ?_
    exact congrArg (Submodule.Quotient.mk) (tensorD_tensorD P Q n z)
  d_act h x f := by
    refine Quotient.inductionOn' f fun z => ?_
    exact congrArg (Submodule.Quotient.mk) (tensorD_tensorAct P Q h x z)

/-- **The tensor product over the ground ring maps onto the tensor product over the algebra.** -/
noncomputable def relTensorProj : CDGAModuleHom (tensorModule P Q) (relTensorModule P Q) where
  toFun _ f := Submodule.Quotient.mk f
  map_add _ _ _ := rfl
  map_smul _ _ _ := rfl
  map_act _ _ _ := rfl
  map_d _ _ := rfl

theorem relTensorProj_surjective (n : ℕ) :
    Function.Surjective ((relTensorProj P Q).toFun n) :=
  Submodule.Quotient.mk_surjective _

/-- **The defining relation holds in the tensor product over the algebra**: an element of the
algebra moves across the tensor sign at the cost of the Koszul sign. -/
theorem relTensorProj_relator {c a b n α β : ℕ} (hα : c + a = α) (hβ : c + b = β)
    (hn : (α, b).1 + (α, b).2 = n) (hn' : (a, β).1 + (a, β).2 = n)
    (x : X c) (m : M a) (v : N b) :
    (relTensorProj P Q).toFun n
        (((-1 : R)) ^ (c * a) • tensorSingle (N := N) ⟨(α, b), hn⟩ (P.act hα x m ⊗ₜ[R] v))
      = (relTensorProj P Q).toFun n
        (tensorSingle (N := N) ⟨(a, β), hn'⟩ (m ⊗ₜ[R] Q.act hβ x v)) := by
  refine sub_eq_zero.1 ?_
  show Submodule.Quotient.mk (relTensorRelator P Q hα hβ hn hn' x m v) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact relTensorRelator_mem P Q hα hβ hn hn' x m v

end Quotient

section Functoriality

variable {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  {P : CDGAModuleStructure A M} {P' : CDGAModuleStructure A M'}

/-- Functoriality in the left variable on a single-bidegree element. -/
theorem tensorMapLeft_tensorSingle (φ : CDGAModuleHom P P') (Q : CDGAModuleStructure A N)
    {n a b : ℕ} (h : (a, b).1 + (a, b).2 = n) (z : TensorProduct R (M a) (N b)) :
    (tensorMapLeft φ Q).toFun n (tensorSingle (N := N) ⟨(a, b), h⟩ z)
      = tensorSingle (N := N) ⟨(a, b), h⟩
        (TensorProduct.map (φ.mapₗ a) LinearMap.id z) := by
  funext p
  obtain ⟨⟨a', b'⟩, h'⟩ := p
  rw [tensorMapLeft_toFun]
  by_cases hab : a' = a ∧ b' = b
  · obtain ⟨rfl, rfl⟩ := hab
    rw [tensorSingle_same, tensorSingle_same]
  · rw [tensorSingle_ne _ (by
      rw [Ne, tensorIndex_eq_iff]
      omega), map_zero, tensorSingle_ne _ (by
      rw [Ne, tensorIndex_eq_iff]
      omega)]

/-- **Functoriality in the left variable carries a relator to a relator.** -/
theorem tensorMapLeft_relTensorRelator (φ : CDGAModuleHom P P') (Q : CDGAModuleStructure A N)
    {c a b n α β : ℕ} (hα : c + a = α) (hβ : c + b = β)
    (hn : (α, b).1 + (α, b).2 = n) (hn' : (a, β).1 + (a, β).2 = n)
    (x : X c) (m : M a) (v : N b) :
    (tensorMapLeft φ Q).toFun n (relTensorRelator P Q hα hβ hn hn' x m v)
      = relTensorRelator P' Q hα hβ hn hn' x (φ.toFun a m) v := by
  show (tensorMapLeft φ Q).mapₗ n (relTensorRelator P Q hα hβ hn hn' x m v) = _
  simp only [relTensorRelator]
  rw [map_sub, map_smul]
  show ((-1 : R)) ^ (c * a)
      • (tensorMapLeft φ Q).toFun n (tensorSingle (N := N) ⟨(α, b), hn⟩ (P.act hα x m ⊗ₜ[R] v))
      - (tensorMapLeft φ Q).toFun n
        (tensorSingle (N := N) ⟨(a, β), hn'⟩ (m ⊗ₜ[R] Q.act hβ x v)) = _
  rw [tensorMapLeft_tensorSingle, tensorMapLeft_tensorSingle, TensorProduct.map_tmul,
    TensorProduct.map_tmul]
  show ((-1 : R)) ^ (c * a) • tensorSingle (N := N) ⟨(α, b), hn⟩
        ((φ.mapₗ α (P.act hα x m) : M' α) ⊗ₜ[R] (LinearMap.id v : N b))
      - tensorSingle (N := N) ⟨(a, β), hn'⟩
        ((φ.mapₗ a m : M' a) ⊗ₜ[R] (LinearMap.id (Q.act hβ x v) : N β)) = _
  rw [show (φ.mapₗ α (P.act hα x m) : M' α) = P'.act hα x (φ.toFun a m) from φ.map_act hα x m]
  rfl

/-- Functoriality in the left variable preserves the relations. -/
theorem relTensorRel_map (φ : CDGAModuleHom P P') (Q : CDGAModuleStructure A N) (n : ℕ)
    (f : TensorCarrier (R := R) M N n) (hf : f ∈ relTensorRel P Q n) :
    (tensorMapLeft φ Q).toFun n f ∈ relTensorRel P' Q n := by
  refine Submodule.span_induction
    (p := fun g _ => (tensorMapLeft φ Q).toFun n g ∈ relTensorRel P' Q n) ?_ ?_ ?_ ?_ hf
  · rintro g ⟨c, a, b, α, β, hα, hβ, hn, hn', x, m, v, rfl⟩
    rw [tensorMapLeft_relTensorRelator]
    exact relTensorRelator_mem P' Q hα hβ hn hn' x (φ.toFun a m) v
  · rw [show (tensorMapLeft φ Q).toFun n 0 = 0 from ((tensorMapLeft φ Q).mapₗ n).map_zero]
    exact Submodule.zero_mem _
  · intro g g' _ _ hg hg'
    rw [(tensorMapLeft φ Q).map_add]
    exact Submodule.add_mem _ hg hg'
  · intro r g _ hg
    rw [(tensorMapLeft φ Q).map_smul]
    exact Submodule.smul_mem _ _ hg

/-- **The tensor product over the algebra is functorial in the left variable.** -/
noncomputable def relTensorMapLeft (φ : CDGAModuleHom P P') (Q : CDGAModuleStructure A N) :
    CDGAModuleHom (relTensorModule P Q) (relTensorModule P' Q) where
  toFun n f :=
    Submodule.mapQ (relTensorRel P Q n) (relTensorRel P' Q n) ((tensorMapLeft φ Q).mapₗ n)
      (fun g hg => relTensorRel_map φ Q n g hg) f
  map_add n f f' := by
    refine Quotient.inductionOn₂' f f' fun z z' => ?_
    exact congrArg (Submodule.Quotient.mk) ((tensorMapLeft φ Q).map_add n z z')
  map_smul n r f := by
    refine Quotient.inductionOn' f fun z => ?_
    exact congrArg (Submodule.Quotient.mk) ((tensorMapLeft φ Q).map_smul n r z)
  map_act h x f := by
    refine Quotient.inductionOn' f fun z => ?_
    exact congrArg (Submodule.Quotient.mk) ((tensorMapLeft φ Q).map_act h x z)
  map_d n f := by
    refine Quotient.inductionOn' f fun z => ?_
    exact congrArg (Submodule.Quotient.mk) ((tensorMapLeft φ Q).map_d n z)

@[simp] theorem relTensorMapLeft_mk (φ : CDGAModuleHom P P') (Q : CDGAModuleStructure A N)
    (n : ℕ) (f : TensorCarrier (R := R) M N n) :
    (relTensorMapLeft φ Q).toFun n (Submodule.Quotient.mk f)
      = Submodule.Quotient.mk ((tensorMapLeft φ Q).toFun n f) := rfl

/-- The projection to the tensor product over the algebra is natural in the left variable. -/
theorem relTensorProj_naturality (φ : CDGAModuleHom P P') (Q : CDGAModuleStructure A N) :
    (relTensorMapLeft φ Q).comp (relTensorProj P Q)
      = (relTensorProj P' Q).comp (tensorMapLeft φ Q) :=
  CDGAModuleHom.hom_ext fun _ _ => rfl

end Functoriality

end GaloisForLFunctions.HTGeometry
