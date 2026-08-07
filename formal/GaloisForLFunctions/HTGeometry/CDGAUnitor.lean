import GaloisForLFunctions.HTGeometry.CDGARelTensor
import GaloisForLFunctions.HTGeometry.CDGAUnital
import GaloisForLFunctions.HTGeometry.CDGACellInvariance

/-!
# The unitor of the tensor product over the algebra

A module tensored over the algebra with the algebra itself is the module again, provided the algebra
has a unit and the action is unital.  The comparison in one direction is the right action summed
over the finitely many bidegrees — a left module is a right module through
`m · x = (−1)^{|x||m|} x · m` — and in the other direction it is `m ↦ m ⊗ 1`.

The right action kills the relators for a reason worth naming: on the relator of `x, m, v` the two
terms differ by moving `v` past `x` inside the algebra and by the change of the relator's own sign,
and those two signs are equal.

* `HTGeometry.rightActₗ` : the right action on one bidegree.
* `HTGeometry.unitorToₗ` : its sum over all bidegrees.
* `HTGeometry.relUnitorTo` : the induced map on the tensor product over the algebra.
* `HTGeometry.unitorToₗ_unitorFromₗ` : one composite is the identity.
-/

universe u w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type w} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]

section RightAct

variable (P : CDGAModuleStructure A M)

/-- **The right action of the algebra on a left module**, `m · x = (−1)^{|x||m|} x · m`, as a linear
map out of one bidegree of the tensor product. -/
noncomputable def rightActₗ {a c n : ℕ} (h : a + c = n) :
    TensorProduct R (M a) (X c) →ₗ[R] M n :=
  TensorProduct.lift (LinearMap.mk₂ R
    (fun (m : M a) (x : X c) => ((-1 : R)) ^ (c * a) • P.act (show c + a = n by omega) x m)
    (fun m m' x => by rw [P.act_add_right, smul_add])
    (fun r m x => by rw [P.act_smul_right, smul_comm])
    (fun m x x' => by rw [P.act_add_left, smul_add])
    (fun r m x => by rw [P.act_smul_left, smul_comm]))

@[simp] theorem rightActₗ_tmul {a c n : ℕ} (h : a + c = n) (m : M a) (x : X c) :
    rightActₗ P h (m ⊗ₜ[R] x) = ((-1 : R)) ^ (c * a) • P.act (show c + a = n by omega) x m := rfl

/-- The right action summed over all bidegrees. -/
noncomputable def unitorToₗ (n : ℕ) : TensorCarrier (R := R) M X n →ₗ[R] M n :=
  ∑ p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}, (rightActₗ P p.2).comp (LinearMap.proj p)

theorem unitorToₗ_tensorSingle {n : ℕ} (q : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
    (z : TensorProduct R (M q.1.1) (X q.1.2)) :
    unitorToₗ P n (tensorSingle (N := X) q z) = rightActₗ P q.2 z := by
  show (∑ p : {ab : ℕ × ℕ // ab.1 + ab.2 = n},
      (rightActₗ P p.2).comp (LinearMap.proj p)) (tensorSingle (N := X) q z) = _
  rw [LinearMap.sum_apply]
  rw [Finset.sum_eq_single q (fun p _ hne => by
      show rightActₗ P p.2 (tensorSingle (N := X) q z p) = 0
      rw [tensorSingle_ne _ hne, map_zero])
    (fun h => absurd (Finset.mem_univ q) h)]
  show rightActₗ P q.2 (tensorSingle (N := X) q z q) = _
  rw [tensorSingle_same]

end RightAct

section Unitor

variable (P : CDGAModuleStructure A M)

/-- **The right action kills the relators.**  The sign of moving the second algebra element past the
first equals the change in the relator's own sign. -/
theorem unitorToₗ_relTensorRelator {c a b n α β : ℕ} (hα : c + a = α) (hβ : c + b = β)
    (hn : (α, b).1 + (α, b).2 = n) (hn' : (a, β).1 + (a, β).2 = n)
    (x : X c) (m : M a) (v : X b) :
    unitorToₗ P n (relTensorRelator P (CDGAStructure.selfModule A) hα hβ hn hn' x m v) = 0 := by
  simp only [relTensorRelator]
  rw [map_sub, map_smul, unitorToₗ_tensorSingle, unitorToₗ_tensorSingle]
  show ((-1 : R)) ^ (c * a) • rightActₗ P hn (P.act hα x m ⊗ₜ[R] v)
      - rightActₗ P hn' (m ⊗ₜ[R] A.mul hβ x v) = 0
  rw [rightActₗ_tmul, rightActₗ_tmul, smul_smul, ← pow_add]
  have hassoc : P.act (show b + α = n by omega) v (P.act hα x m)
      = ((-1 : R)) ^ (b * c) • P.act (show β + a = n by omega) (A.mul hβ x v) m := by
    rw [← P.act_assoc (show b + c = β by omega) (show β + a = n by omega) hα
      (show b + α = n by omega) v x m,
      A.mul_comm (show b + c = β by omega) hβ v x, P.act_smul_left]
  rw [hassoc, smul_smul, ← pow_add]
  have hsign : ((-1 : R)) ^ (c * a + b * α + b * c) = ((-1 : R)) ^ (β * a) := by
    rw [show c * a + b * α + b * c = β * a + 2 * (b * c) by
      subst hα
      subst hβ
      ring, pow_add, pow_mul]
    norm_num
  rw [hsign, sub_self]

/-- The unitor is compatible with the relations. -/
theorem relTensorRel_unitorTo (n : ℕ) (f : TensorCarrier (R := R) M X n)
    (hf : f ∈ relTensorRel P (CDGAStructure.selfModule A) n) : unitorToₗ P n f = 0 := by
  refine Submodule.span_induction
    (p := fun g _ => unitorToₗ P n g = 0) ?_ ?_ ?_ ?_ hf
  · rintro g ⟨c, a, b, α, β, hα, hβ, hn, hn', x, m, v, rfl⟩
    exact unitorToₗ_relTensorRelator P hα hβ hn hn' x m v
  · exact map_zero _
  · intro g g' _ _ hg hg'
    rw [map_add, hg, hg', add_zero]
  · intro r g _ hg
    rw [map_smul, hg, smul_zero]

/-- **The unitor**: the tensor product of a module with the algebra maps to the module. -/
noncomputable def relUnitorTo (n : ℕ) :
    RelTensorCarrier P (CDGAStructure.selfModule A) n →ₗ[R] M n :=
  Submodule.liftQ _ (unitorToₗ P n) (fun f hf => relTensorRel_unitorTo P n f hf)

@[simp] theorem relUnitorTo_mk (n : ℕ) (f : TensorCarrier (R := R) M X n) :
    relUnitorTo P n (Submodule.Quotient.mk f) = unitorToₗ P n f := rfl

variable (u : CDGAUnit A)

/-- The section of the unitor: an element of the module tensored with the unit. -/
noncomputable def unitorFromₗ (n : ℕ) : M n →ₗ[R] TensorCarrier (R := R) M X n where
  toFun m := tensorSingle (N := X)
    (⟨(n, 0), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) (m ⊗ₜ[R] u.one)
  map_add' m m' := by
    rw [TensorProduct.add_tmul, tensorSingle_add]
  map_smul' r m := by
    rw [← TensorProduct.smul_tmul', tensorSingle_smul]
    rfl

/-- **The unitor is a retraction of `m ↦ m ⊗ 1`** exactly when the action is unital. -/
theorem unitorToₗ_unitorFromₗ (hP : CDGAModuleUnital u P) (n : ℕ) (m : M n) :
    unitorToₗ P n (unitorFromₗ u n m) = m := by
  show unitorToₗ P n (tensorSingle (N := X)
    (⟨(n, 0), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) (m ⊗ₜ[R] u.one)) = m
  rw [unitorToₗ_tensorSingle, rightActₗ_tmul, Nat.zero_mul, pow_zero, one_smul]
  exact hP.act_one n m

/-- **The unitor is equivariant.** -/
theorem unitorToₗ_tensorAct {d n m' : ℕ} (h : d + n = m') (y : X d)
    (f : TensorCarrier (R := R) M X n) :
    unitorToₗ P m' (tensorActₗ P (CDGAStructure.selfModule A) h y f)
      = P.actₗ h y (unitorToₗ P n f) := by
  have hf := tensorCarrier_eq_sum_single (N := X) f
  rw [hf, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨⟨i, c⟩, hq⟩ := q
  induction (f ⟨(i, c), hq⟩) using TensorProduct.induction_on with
  | zero => rw [tensorSingle_zero, map_zero, map_zero, map_zero, map_zero]
  | tmul m x =>
      show unitorToₗ P m' (tensorAct P (CDGAStructure.selfModule A) h y
          (tensorSingle (N := X) ⟨(i, c), hq⟩ (m ⊗ₜ[R] x))) = _
      rw [tensorAct_tensorSingle, TensorProduct.map_tmul, unitorToₗ_tensorSingle,
        unitorToₗ_tensorSingle, rightActₗ_tmul, rightActₗ_tmul]
      show ((-1 : R)) ^ (c * (d + i))
          • P.act (show c + (d + i) = m' by omega) x (P.act (rfl : d + i = d + i) y m)
        = P.act h y (((-1 : R)) ^ (c * i) • P.act (show c + i = n by omega) x m)
      rw [P.act_smul_right]
      have hxy : P.act (show c + (d + i) = m' by omega) x
            (P.act (rfl : d + i = d + i) y m)
          = ((-1 : R)) ^ (c * d) • P.act h y (P.act (show c + i = n by omega) x m) := by
        rw [← P.act_assoc (show c + d = c + d from rfl) (show c + d + i = m' by omega)
          (rfl : d + i = d + i) (show c + (d + i) = m' by omega) x y m,
          A.mul_comm (show c + d = c + d from rfl) (show d + c = c + d by omega) x y,
          P.act_smul_left, P.act_assoc (show d + c = c + d by omega)
            (show c + d + i = m' by omega) (show c + i = n by omega) h y x m]
      rw [hxy, smul_smul, ← pow_add,
        show c * (d + i) + c * d = c * i + 2 * (c * d) by ring, pow_add, pow_mul]
      norm_num
  | add z z' hz hz' =>
      rw [tensorSingle_add, map_add, map_add, map_add, map_add, hz, hz']

/-- **The unitor commutes with the differential.** -/
theorem unitorToₗ_tensorD (n : ℕ) (f : TensorCarrier (R := R) M X n) :
    unitorToₗ P (n + 1) (tensorDₗ P (CDGAStructure.selfModule A) n f)
      = P.dₗ n (unitorToₗ P n f) := by
  have hf := tensorCarrier_eq_sum_single (N := X) f
  rw [hf, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨⟨a, c⟩, hq⟩ := q
  induction (f ⟨(a, c), hq⟩) using TensorProduct.induction_on with
  | zero => rw [tensorSingle_zero, map_zero, map_zero, map_zero, map_zero]
  | tmul m x =>
      show unitorToₗ P (n + 1) (tensorD P (CDGAStructure.selfModule A) n
          (tensorSingle (N := X) ⟨(a, c), hq⟩ (m ⊗ₜ[R] x)))
        = P.d n (unitorToₗ P n (tensorSingle (N := X) ⟨(a, c), hq⟩ (m ⊗ₜ[R] x)))
      rw [unitorToₗ_tensorSingle, rightActₗ_tmul, P.d_smul, P.d_act,
        tensorD_tensorSingle, TensorProduct.map_tmul, TensorProduct.map_tmul, map_add,
        unitorToₗ_tensorSingle, unitorToₗ_tensorSingle, map_smul, rightActₗ_tmul,
        rightActₗ_tmul]
      simp only [smul_add, smul_smul, ← pow_add]
      have h1 : ((-1 : R)) ^ (a + (c + 1) * a) = ((-1 : R)) ^ (c * a) := by
        rw [show a + (c + 1) * a = c * a + 2 * a by ring, pow_add, pow_mul]
        norm_num
      have h2 : ((-1 : R)) ^ (c * (a + 1)) = ((-1 : R)) ^ (c * a + c) := by
        rw [show c * (a + 1) = c * a + c by ring]
      rw [h1, h2]
      exact add_comm _ _
  | add z z' hz hz' =>
      rw [tensorSingle_add, map_add, map_add, map_add, map_add, hz, hz']

/-- The section is a section, on a single-bidegree element: this is where the relation does its
work, rewriting `m ⊗ x` as `(±x · m) ⊗ 1`. -/
theorem relUnitor_single (n : ℕ) (q : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
    (z : TensorProduct R (M q.1.1) (X q.1.2)) :
    (Submodule.Quotient.mk (unitorFromₗ u n (unitorToₗ P n (tensorSingle (N := X) q z)))
      : RelTensorCarrier P (CDGAStructure.selfModule A) n)
      = Submodule.Quotient.mk (tensorSingle (N := X) q z) := by
  obtain ⟨⟨a, c⟩, h⟩ := q
  induction z using TensorProduct.induction_on with
  | zero =>
      rw [tensorSingle_zero, map_zero, map_zero]
  | tmul m x =>
      rw [unitorToₗ_tensorSingle, rightActₗ_tmul]
      show (Submodule.Quotient.mk (tensorSingle (N := X)
          (⟨(n, 0), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
          ((((-1 : R)) ^ (c * a) • P.act (show c + a = n by omega) x m) ⊗ₜ[R] u.one))
        : RelTensorCarrier P (CDGAStructure.selfModule A) n) = _
      rw [← TensorProduct.smul_tmul', tensorSingle_smul]
      refine sub_eq_zero.1 ?_
      rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
      have hrel := relTensorRelator_mem P (CDGAStructure.selfModule A)
        (show c + a = n by omega) (Nat.add_zero c)
        (show (n, 0).1 + (n, 0).2 = n by omega) (show (a, c).1 + (a, c).2 = n by omega)
        x m u.one
      have hval : relTensorRelator P (CDGAStructure.selfModule A)
          (show c + a = n by omega) (Nat.add_zero c)
          (show (n, 0).1 + (n, 0).2 = n by omega) (show (a, c).1 + (a, c).2 = n by omega)
          x m u.one
        = ((-1 : R)) ^ (c * a) • tensorSingle (N := X)
            (⟨(n, 0), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
            (P.act (show c + a = n by omega) x m ⊗ₜ[R] u.one)
          - tensorSingle (N := X) (⟨(a, c), h⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
            (m ⊗ₜ[R] x) := by
        show ((-1 : R)) ^ (c * a) • tensorSingle (N := X) _ _
          - tensorSingle (N := X) _ (m ⊗ₜ[R] A.mul (Nat.add_zero c) x u.one) = _
        rw [u.mul_one c x]
      rwa [hval] at hrel
  | add z z' hz hz' =>
      rw [tensorSingle_add, map_add, map_add, Submodule.Quotient.mk_add,
        Submodule.Quotient.mk_add, hz, hz']

/-- **The section is a section.**  Together with `unitorToₗ_unitorFromₗ` this makes the unitor a
degreewise bijection. -/
theorem relUnitor_leftInverse (n : ℕ) (f : TensorCarrier (R := R) M X n) :
    (Submodule.Quotient.mk (unitorFromₗ u n (unitorToₗ P n f))
      : RelTensorCarrier P (CDGAStructure.selfModule A) n) = Submodule.Quotient.mk f := by
  have hf := tensorCarrier_eq_sum_single (N := X) f
  show (relTensorRel P (CDGAStructure.selfModule A) n).mkQ
      (unitorFromₗ u n (unitorToₗ P n f))
    = (relTensorRel P (CDGAStructure.selfModule A) n).mkQ f
  rw [hf, map_sum, map_sum, map_sum, map_sum]
  exact Finset.sum_congr rfl fun q _ => relUnitor_single P u n q (f q)

/-- **The unitor is a degreewise isomorphism** when the algebra has a unit acting as the identity:
a module tensored over the algebra with the algebra is the module. -/
noncomputable def relUnitorEquiv (hP : CDGAModuleUnital u P) (n : ℕ) :
    RelTensorCarrier P (CDGAStructure.selfModule A) n ≃ₗ[R] M n where
  toFun := relUnitorTo P n
  map_add' := map_add _
  map_smul' := map_smul _
  invFun m := Submodule.Quotient.mk (unitorFromₗ u n m)
  left_inv f := by
    refine Quotient.inductionOn' f fun z => ?_
    exact relUnitor_leftInverse P u n z
  right_inv m := unitorToₗ_unitorFromₗ P u hP n m

/-- **The unitor as a map of differential graded modules.** -/
noncomputable def relUnitorHom :
    CDGAModuleHom (relTensorModule P (CDGAStructure.selfModule A)) P where
  toFun n f := relUnitorTo P n f
  map_add n f f' := map_add (relUnitorTo P n) f f'
  map_smul n r f := map_smul (relUnitorTo P n) r f
  map_act h x f := by
    refine Quotient.inductionOn' f fun z => ?_
    exact unitorToₗ_tensorAct P h x z
  map_d n f := by
    refine Quotient.inductionOn' f fun z => ?_
    exact unitorToₗ_tensorD P n z

/-- **A module tensored over the algebra with the algebra is the module**, as a full
quasi-isomorphism of differential graded modules, whenever the algebra has a unit acting as the
identity.  This is the base case that makes the tensor product over the algebra computable on
cells. -/
theorem relUnitorHom_isQuasiIsoFull (hP : CDGAModuleUnital u P) :
    (relUnitorHom P).IsQuasiIsoFull :=
  CDGAModuleHom.IsQuasiIsoFull.of_bijective fun n => (relUnitorEquiv P u hP n).bijective

end Unitor

end GaloisForLFunctions.HTGeometry
