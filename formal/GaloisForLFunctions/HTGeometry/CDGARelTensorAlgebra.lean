import GaloisForLFunctions.HTGeometry.CDGATensorAlgebraIncl
import GaloisForLFunctions.HTGeometry.CDGARestrictScalars
import GaloisForLFunctions.HTGeometry.CDGARelTensor

/-!
# The relations of a relative tensor product form an ideal

For two algebras over a base algebra, the relations defining the tensor product over the base are
carried into themselves by multiplication: a relator times a single-bidegree element is a scalar
multiple of a relator.  The scalar is forced — the cell has to move past the first factor of the
second argument, and the Koszul sign of the product itself contributes — and it works out to
`(−1)^{(c+b)a'}`.

* `HTGeometry.tensorAlgMul_sub_left` : the product is additive on differences.
* `HTGeometry.tensorAlgMul_relTensorRelator` : a relator times a single is a relator.
-/

universe u w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R]
  {Wc : ℕ → Type w} [∀ n, AddCommGroup (Wc n)] [∀ n, Module R (Wc n)]
  {X : ℕ → Type w} [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]
  {Y : ℕ → Type w} [∀ n, AddCommGroup (Y n)] [∀ n, Module R (Y n)]
  {C : CDGAStructure R Wc} (A : CDGAStructure R X) (B : CDGAStructure R Y)

theorem tensorAlgMul_sub_left {a b n : ℕ} (h : a + b = n)
    (f f' : TensorCarrier (R := R) X Y a) (g : TensorCarrier (R := R) X Y b) :
    tensorAlgMul A B h (f - f') g = tensorAlgMul A B h f g - tensorAlgMul A B h f' g := by
  rw [show f - f' = f + (-1 : R) • f' by rw [neg_one_smul, ← sub_eq_add_neg],
    tensorAlgMul_add_left, tensorAlgMul_smul_left, neg_one_smul, ← sub_eq_add_neg]

variable {A B}

/-- **A relator times a single-bidegree element is a relator.** -/
theorem tensorAlgMul_relTensorRelator (f : CDGAHom C A) (g : CDGAHom C B)
    {cd a b n α β : ℕ} (hα : cd + a = α) (hβ : cd + b = β)
    (hn : (α, b).1 + (α, b).2 = n) (hn' : (a, β).1 + (a, β).2 = n)
    (γ : Wc cd) (x : X a) (y : Y b)
    {a' b' n' m : ℕ} (hab' : (a', b').1 + (a', b').2 = n') (hm : n + n' = m)
    (x' : X a') (y' : Y b')
    (hα2 : cd + (a + a') = α + a') (hβ2 : cd + (b + b') = β + b')
    (hm1 : (α + a', b + b').1 + (α + a', b + b').2 = m)
    (hm2 : (a + a', β + b').1 + (a + a', β + b').2 = m) :
    tensorAlgMul A B hm
        (relTensorRelator f.restrictModule g.restrictModule hα hβ hn hn' γ x y)
        (tensorSingle (M := X) (N := Y) ⟨(a', b'), hab'⟩ (x' ⊗ₜ[R] y'))
      = ((-1 : R)) ^ ((cd + b) * a') •
        relTensorRelator f.restrictModule g.restrictModule hα2 hβ2 hm1 hm2 γ
          (A.mul (rfl : a + a' = a + a') x x') (B.mul (rfl : b + b' = b + b') y y') := by
  subst hα
  subst hβ
  simp only [relTensorRelator]
  rw [tensorAlgMul_sub_left, tensorAlgMul_smul_left,
    tensorAlgMul_tensorSingle_eq_single A B hm _ _ _ _ hm1,
    tensorAlgMul_tensorSingle_eq_single A B hm _ _ _ _ hm2,
    tensorPairₗ_tmul, tensorPairₗ_tmul]
  simp only [tensorSingle_smul, smul_sub, smul_smul, ← pow_add]
  refine congrArg₂ (· - ·) ?_ ?_
  · rw [show A.mul (rfl : cd + a + a' = cd + a + a')
          (f.restrictModule.act (rfl : cd + a = cd + a) γ x) x'
        = f.restrictModule.act hα2 γ (A.mul (rfl : a + a' = a + a') x x') from
        A.mul_assoc (rfl : cd + a = cd + a) (rfl : cd + a + a' = cd + a + a')
          (rfl : a + a' = a + a') hα2 (f.toFun cd γ) x x']
    refine congrArg (fun r : R => r • tensorSingle (M := X) (N := Y) ⟨(cd + a + a', b + b'), hm1⟩
      (f.restrictModule.act hα2 γ (A.mul (rfl : a + a' = a + a') x x')
        ⊗ₜ[R] B.mul (rfl : b + b' = b + b') y y')) ?_
    exact neg_one_pow_eq_of_even_add _ _ (cd * a + b * a' + cd * a') (by ring)
  · rw [show B.mul (rfl : cd + b + b' = cd + b + b')
          (g.restrictModule.act (rfl : cd + b = cd + b) γ y) y'
        = g.restrictModule.act hβ2 γ (B.mul (rfl : b + b' = b + b') y y') from
        B.mul_assoc (rfl : cd + b = cd + b) (rfl : cd + b + b' = cd + b + b')
          (rfl : b + b' = b + b') hβ2 (g.toFun cd γ) y y']

/-- The product is additive over a finite sum in the right variable. -/
theorem tensorAlgMul_sum_right {a b n : ℕ} (h : a + b = n) (z : TensorCarrier (R := R) X Y a)
    {ι : Type*} (s : Finset ι) (w : ι → TensorCarrier (R := R) X Y b) :
    tensorAlgMul A B h z (∑ i ∈ s, w i) = ∑ i ∈ s, tensorAlgMul A B h z (w i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty,
      show tensorAlgMul A B h z (0 : TensorCarrier (R := R) X Y b) = 0 by
        rw [show (0 : TensorCarrier (R := R) X Y b) = (0 : R) • 0 by rw [zero_smul],
          tensorAlgMul_smul_right, zero_smul]]
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, tensorAlgMul_add_right, ih]

/-- **The relations are stable under multiplication on the right.** -/
theorem relTensorRel_tensorAlgMul_left (f : CDGAHom C A) (g : CDGAHom C B) {a b n : ℕ}
    (h : a + b = n) (z : TensorCarrier (R := R) X Y a)
    (hz : z ∈ relTensorRel f.restrictModule g.restrictModule a)
    (w : TensorCarrier (R := R) X Y b) :
    tensorAlgMul A B h z w ∈ relTensorRel f.restrictModule g.restrictModule n := by
  classical
  induction hz using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨cd, a₀, b₀, α, β, hα, hβ, hn, hn', γ, x, y, rfl⟩ := hu
      rw [tensorCarrier_eq_sum_single (M := X) (N := Y) w, tensorAlgMul_sum_right]
      refine Submodule.sum_mem _ fun p _ => ?_
      obtain ⟨⟨a', b'⟩, hab'⟩ := p
      induction (w ⟨(a', b'), hab'⟩) using TensorProduct.induction_on with
      | zero =>
          rw [tensorSingle_zero,
            show tensorAlgMul A B h
                (relTensorRelator f.restrictModule g.restrictModule hα hβ hn hn' γ x y) 0 = 0 by
              rw [show (0 : TensorCarrier (R := R) X Y b) = (0 : R) • 0 by rw [zero_smul],
                tensorAlgMul_smul_right, zero_smul]]
          exact Submodule.zero_mem _
      | tmul x' y' =>
          rw [tensorAlgMul_relTensorRelator f g hα hβ hn hn' γ x y hab' h x' y'
            (by omega) (by omega) (by simp only; omega) (by simp only; omega)]
          exact Submodule.smul_mem _ _
            (relTensorRelator_mem f.restrictModule g.restrictModule _ _ _ _ γ _ _)
      | add u u' hu hu' =>
          rw [tensorSingle_add, tensorAlgMul_add_right]
          exact Submodule.add_mem _ hu hu'
  | zero =>
      rw [show tensorAlgMul A B h (0 : TensorCarrier (R := R) X Y a) w = 0 by
        rw [show (0 : TensorCarrier (R := R) X Y a) = (0 : R) • 0 by rw [zero_smul],
          tensorAlgMul_smul_left, zero_smul]]
      exact Submodule.zero_mem _
  | add u u' _ _ hu hu' =>
      rw [tensorAlgMul_add_left]
      exact Submodule.add_mem _ hu hu'
  | smul r u _ hu =>
      rw [tensorAlgMul_smul_left]
      exact Submodule.smul_mem _ _ hu

/-- **The relations are stable under multiplication on the left**, by graded commutativity. -/
theorem relTensorRel_tensorAlgMul_right (f : CDGAHom C A) (g : CDGAHom C B) {a b n : ℕ}
    (h : a + b = n) (w : TensorCarrier (R := R) X Y a)
    (z : TensorCarrier (R := R) X Y b)
    (hz : z ∈ relTensorRel f.restrictModule g.restrictModule b) :
    tensorAlgMul A B h w z ∈ relTensorRel f.restrictModule g.restrictModule n := by
  rw [tensorAlgMul_comm A B h (show b + a = n by omega) w z]
  exact Submodule.smul_mem _ _
    (relTensorRel_tensorAlgMul_left f g (show b + a = n by omega) z hz w)

section Descent

variable (f : CDGAHom C A) (g : CDGAHom C B)

/-- The product with a fixed representative, into the quotient. -/
noncomputable def relAlgMulPre {a b n : ℕ} (h : a + b = n)
    (z : TensorCarrier (R := R) X Y a) :
    TensorCarrier (R := R) X Y b →ₗ[R]
      RelTensorCarrier f.restrictModule g.restrictModule n where
  toFun w := Submodule.Quotient.mk (tensorAlgMul A B h z w)
  map_add' w w' := by
    rw [tensorAlgMul_add_right, Submodule.Quotient.mk_add]
  map_smul' c w := by
    rw [tensorAlgMul_smul_right]
    rfl

/-- The product with a fixed representative, descended in the second variable. -/
noncomputable def relAlgMulRight {a b n : ℕ} (h : a + b = n)
    (z : TensorCarrier (R := R) X Y a) :
    RelTensorCarrier f.restrictModule g.restrictModule b →ₗ[R]
      RelTensorCarrier f.restrictModule g.restrictModule n :=
  Submodule.liftQ _ (relAlgMulPre f g h z)
    (fun w hw => (Submodule.Quotient.mk_eq_zero _).2
      (relTensorRel_tensorAlgMul_right f g h z w hw))

/-- The product, before descending in the first variable. -/
noncomputable def relAlgMulLeftPre {a b n : ℕ} (h : a + b = n) :
    TensorCarrier (R := R) X Y a →ₗ[R]
      (RelTensorCarrier f.restrictModule g.restrictModule b →ₗ[R]
        RelTensorCarrier f.restrictModule g.restrictModule n) where
  toFun z := relAlgMulRight f g h z
  map_add' z z' := by
    refine LinearMap.ext fun w => ?_
    refine Quotient.inductionOn' w fun u => ?_
    show Submodule.Quotient.mk (tensorAlgMul A B h (z + z') u) = _
    rw [tensorAlgMul_add_left, Submodule.Quotient.mk_add]
    rfl
  map_smul' c z := by
    refine LinearMap.ext fun w => ?_
    refine Quotient.inductionOn' w fun u => ?_
    show Submodule.Quotient.mk (tensorAlgMul A B h (c • z) u) = _
    rw [tensorAlgMul_smul_left]
    rfl

/-- **The product of a relative tensor product of algebras.** -/
noncomputable def relAlgMul {a b n : ℕ} (h : a + b = n)
    (z : RelTensorCarrier f.restrictModule g.restrictModule a)
    (w : RelTensorCarrier f.restrictModule g.restrictModule b) :
    RelTensorCarrier f.restrictModule g.restrictModule n :=
  Submodule.liftQ _ (relAlgMulLeftPre f g h)
    (fun u hu => LinearMap.ext fun w' => by
      refine Quotient.inductionOn' w' fun v => ?_
      exact (Submodule.Quotient.mk_eq_zero _).2
        (relTensorRel_tensorAlgMul_left f g h u hu v)) z w

@[simp] theorem relAlgMul_mk {a b n : ℕ} (h : a + b = n)
    (z : TensorCarrier (R := R) X Y a) (w : TensorCarrier (R := R) X Y b) :
    relAlgMul f g h (Submodule.Quotient.mk z) (Submodule.Quotient.mk w)
      = Submodule.Quotient.mk (tensorAlgMul A B h z w) := rfl

/-- **The relative tensor product of two algebras over a base algebra.** -/
noncomputable def relTensorCDGA :
    CDGAStructure R (RelTensorCarrier f.restrictModule g.restrictModule) where
  mul h z w := relAlgMul f g h z w
  d n := relTensorD f.restrictModule g.restrictModule n
  mul_add_left h z z' w := by
    refine Quotient.inductionOn₂' z z' fun u u' => ?_
    refine Quotient.inductionOn' w fun v => ?_
    exact congrArg Submodule.Quotient.mk (tensorAlgMul_add_left A B h u u' v)
  mul_add_right h z w w' := by
    refine Quotient.inductionOn' z fun u => ?_
    refine Quotient.inductionOn₂' w w' fun v v' => ?_
    exact congrArg Submodule.Quotient.mk (tensorAlgMul_add_right A B h u v v')
  mul_smul_left h c z w := by
    refine Quotient.inductionOn' z fun u => ?_
    refine Quotient.inductionOn' w fun v => ?_
    exact congrArg Submodule.Quotient.mk (tensorAlgMul_smul_left A B h c u v)
  mul_smul_right h c z w := by
    refine Quotient.inductionOn' z fun u => ?_
    refine Quotient.inductionOn' w fun v => ?_
    exact congrArg Submodule.Quotient.mk (tensorAlgMul_smul_right A B h c u v)
  mul_assoc h₁ h₂ h₃ h₄ z w t := by
    refine Quotient.inductionOn' z fun u => ?_
    refine Quotient.inductionOn' w fun v => ?_
    refine Quotient.inductionOn' t fun s => ?_
    exact congrArg Submodule.Quotient.mk (tensorAlgMul_assoc A B h₁ h₂ h₃ h₄ u v s)
  mul_comm h h' z w := by
    refine Quotient.inductionOn' z fun u => ?_
    refine Quotient.inductionOn' w fun v => ?_
    exact congrArg Submodule.Quotient.mk (tensorAlgMul_comm A B h h' u v)
  d_add n z w := map_add (relTensorD f.restrictModule g.restrictModule n) z w
  d_smul n c z := map_smul (relTensorD f.restrictModule g.restrictModule n) c z
  d_d n z := by
    refine Quotient.inductionOn' z fun u => ?_
    exact congrArg Submodule.Quotient.mk
      ((tensorModule f.restrictModule g.restrictModule).d_d n u)
  d_mul h z w := by
    refine Quotient.inductionOn' z fun u => ?_
    refine Quotient.inductionOn' w fun v => ?_
    exact congrArg Submodule.Quotient.mk (tensorAlgMul_extTensorD A B h _ _ u v)

end Descent

end GaloisForLFunctions.HTGeometry
