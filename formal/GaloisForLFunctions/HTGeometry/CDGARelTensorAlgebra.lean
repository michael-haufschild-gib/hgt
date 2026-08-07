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

end GaloisForLFunctions.HTGeometry
