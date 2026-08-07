import GaloisForLFunctions.HTGeometry.CDGARelTensor
import GaloisForLFunctions.HTGeometry.CDGAUnital
import GaloisForLFunctions.HTGeometry.CDGACellInvariance

/-!
# The left unitor of the tensor product over the algebra

The algebra tensored over itself with a module is the module again.  The comparison is the action
summed over the finitely many bidegrees, and — unlike the right unitor — it carries no sign at all:
the relator's sign is exactly the sign of graded commutativity in the algebra, so the two cancel.

* `HTGeometry.leftActₗ` : the action on one bidegree.
* `HTGeometry.leftUnitorToₗ` : its sum over all bidegrees.
* `HTGeometry.relLeftUnitorHom` : `A ⊗_A M ≅ M` as differential graded modules.
-/

universe u w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type w} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]

section LeftAct

variable (P : CDGAModuleStructure A M)

/-- The action of the algebra as a linear map out of one bidegree of the tensor product. -/
noncomputable def leftActₗ {a c n : ℕ} (h : a + c = n) :
    TensorProduct R (X a) (M c) →ₗ[R] M n :=
  TensorProduct.lift (LinearMap.mk₂ R (fun (y : X a) (m : M c) => P.act h y m)
    (fun y y' m => P.act_add_left h y y' m)
    (fun r y m => P.act_smul_left h r y m)
    (fun y m m' => P.act_add_right h y m m')
    (fun r y m => P.act_smul_right h r y m))

@[simp] theorem leftActₗ_tmul {a c n : ℕ} (h : a + c = n) (y : X a) (m : M c) :
    leftActₗ P h (y ⊗ₜ[R] m) = P.act h y m := rfl

/-- The action summed over all bidegrees. -/
noncomputable def leftUnitorToₗ (n : ℕ) : TensorCarrier (R := R) X M n →ₗ[R] M n :=
  ∑ p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}, (leftActₗ P p.2).comp (LinearMap.proj p)

theorem leftUnitorToₗ_tensorSingle {n : ℕ} (q : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
    (z : TensorProduct R (X q.1.1) (M q.1.2)) :
    leftUnitorToₗ P n (tensorSingle (M := X) (N := M) q z) = leftActₗ P q.2 z := by
  show (∑ p : {ab : ℕ × ℕ // ab.1 + ab.2 = n},
      (leftActₗ P p.2).comp (LinearMap.proj p)) (tensorSingle (M := X) (N := M) q z) = _
  rw [LinearMap.sum_apply]
  rw [Finset.sum_eq_single q (fun p _ hne => by
      show leftActₗ P p.2 (tensorSingle (M := X) (N := M) q z p) = 0
      rw [tensorSingle_ne _ hne, map_zero])
    (fun h => absurd (Finset.mem_univ q) h)]
  show leftActₗ P q.2 (tensorSingle (M := X) (N := M) q z q) = _
  rw [tensorSingle_same]

end LeftAct

section Unitor

variable (P : CDGAModuleStructure A M)

/-- **The action kills the relators.**  The relator's sign is the sign of graded commutativity in
the algebra, so the two terms agree. -/
theorem leftUnitorToₗ_relTensorRelator {c a b n α β : ℕ} (hα : c + a = α) (hβ : c + b = β)
    (hn : (α, b).1 + (α, b).2 = n) (hn' : (a, β).1 + (a, β).2 = n)
    (x : X c) (y : X a) (m : M b) :
    leftUnitorToₗ P n
      (relTensorRelator (CDGAStructure.selfModule A) P hα hβ hn hn' x y m) = 0 := by
  simp only [relTensorRelator]
  rw [map_sub, map_smul, leftUnitorToₗ_tensorSingle, leftUnitorToₗ_tensorSingle]
  show ((-1 : R)) ^ (c * a) • leftActₗ P hn (A.mul hα x y ⊗ₜ[R] m)
      - leftActₗ P hn' (y ⊗ₜ[R] P.act hβ x m) = 0
  rw [leftActₗ_tmul, leftActₗ_tmul]
  have hα' : a + c = α := by omega
  have hsecond : P.act hn' y (P.act hβ x m)
      = ((-1 : R)) ^ (a * c) • P.act hn (A.mul hα x y) m := by
    rw [← P.act_assoc hα' hn hβ hn' y x m, A.mul_comm hα' hα y x, P.act_smul_left]
  rw [hsecond, show c * a = a * c by ring, sub_self]

/-- The left unitor is compatible with the relations. -/
theorem relTensorRel_leftUnitorTo (n : ℕ) (f : TensorCarrier (R := R) X M n)
    (hf : f ∈ relTensorRel (CDGAStructure.selfModule A) P n) : leftUnitorToₗ P n f = 0 := by
  refine Submodule.span_induction
    (p := fun g _ => leftUnitorToₗ P n g = 0) ?_ ?_ ?_ ?_ hf
  · rintro g ⟨c, a, b, α, β, hα, hβ, hn, hn', x, y, m, rfl⟩
    exact leftUnitorToₗ_relTensorRelator P hα hβ hn hn' x y m
  · exact map_zero _
  · intro g g' _ _ hg hg'
    rw [map_add, hg, hg', add_zero]
  · intro r g _ hg
    rw [map_smul, hg, smul_zero]

/-- **The left unitor**: the algebra tensored over itself with a module maps to the module. -/
noncomputable def relLeftUnitorTo (n : ℕ) :
    RelTensorCarrier (CDGAStructure.selfModule A) P n →ₗ[R] M n :=
  Submodule.liftQ _ (leftUnitorToₗ P n) (fun f hf => relTensorRel_leftUnitorTo P n f hf)

variable (u : CDGAUnit A)

/-- The section of the left unitor: the unit tensored with an element of the module. -/
noncomputable def leftUnitorFromₗ (n : ℕ) : M n →ₗ[R] TensorCarrier (R := R) X M n where
  toFun m := tensorSingle (M := X) (N := M)
    (⟨(0, n), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) (u.one ⊗ₜ[R] m)
  map_add' m m' := by
    rw [TensorProduct.tmul_add, tensorSingle_add]
  map_smul' r m := by
    rw [TensorProduct.tmul_smul, tensorSingle_smul]
    rfl

/-- **The left unitor is a retraction of `m ↦ 1 ⊗ m`** exactly when the action is unital. -/
theorem leftUnitorToₗ_leftUnitorFromₗ (hP : CDGAModuleUnital u P) (n : ℕ) (m : M n) :
    leftUnitorToₗ P n (leftUnitorFromₗ (M := M) u n m) = m := by
  show leftUnitorToₗ P n (tensorSingle (M := X) (N := M)
    (⟨(0, n), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) (u.one ⊗ₜ[R] m)) = m
  rw [leftUnitorToₗ_tensorSingle, leftActₗ_tmul]
  exact hP.act_one n m

/-- **The left unitor is equivariant.** -/
theorem leftUnitorToₗ_tensorAct {d n m' : ℕ} (h : d + n = m') (w : X d)
    (f : TensorCarrier (R := R) X M n) :
    leftUnitorToₗ P m' (tensorActₗ (CDGAStructure.selfModule A) P h w f)
      = P.actₗ h w (leftUnitorToₗ P n f) := by
  have hf := tensorCarrier_eq_sum_single (M := X) (N := M) f
  rw [hf, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨⟨i, c⟩, hq⟩ := q
  induction (f ⟨(i, c), hq⟩) using TensorProduct.induction_on with
  | zero => rw [tensorSingle_zero, map_zero, map_zero, map_zero, map_zero]
  | tmul y m =>
      show leftUnitorToₗ P m' (tensorAct (CDGAStructure.selfModule A) P h w
          (tensorSingle (M := X) (N := M) ⟨(i, c), hq⟩ (y ⊗ₜ[R] m))) = _
      rw [tensorAct_tensorSingle, TensorProduct.map_tmul, leftUnitorToₗ_tensorSingle,
        leftUnitorToₗ_tensorSingle, leftActₗ_tmul, leftActₗ_tmul]
      show P.act (show d + i + c = m' by omega) (A.mul (rfl : d + i = d + i) w y)
          (LinearMap.id m)
        = P.act h w (P.act (show i + c = n by omega) y m)
      exact P.act_assoc (rfl : d + i = d + i) (show d + i + c = m' by omega)
        (show i + c = n by omega) h w y m
  | add z z' hz hz' =>
      rw [tensorSingle_add, map_add, map_add, map_add, map_add, hz, hz']

/-- **The left unitor commutes with the differential**, which is the Leibniz rule. -/
theorem leftUnitorToₗ_tensorD (n : ℕ) (f : TensorCarrier (R := R) X M n) :
    leftUnitorToₗ P (n + 1) (tensorDₗ (CDGAStructure.selfModule A) P n f)
      = P.dₗ n (leftUnitorToₗ P n f) := by
  have hf := tensorCarrier_eq_sum_single (M := X) (N := M) f
  rw [hf, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨⟨a, c⟩, hq⟩ := q
  induction (f ⟨(a, c), hq⟩) using TensorProduct.induction_on with
  | zero => rw [tensorSingle_zero, map_zero, map_zero, map_zero, map_zero]
  | tmul y m =>
      show leftUnitorToₗ P (n + 1) (tensorD (CDGAStructure.selfModule A) P n
          (tensorSingle (M := X) (N := M) ⟨(a, c), hq⟩ (y ⊗ₜ[R] m)))
        = P.d n (leftUnitorToₗ P n (tensorSingle (M := X) (N := M) ⟨(a, c), hq⟩ (y ⊗ₜ[R] m)))
      rw [tensorD_tensorSingle, TensorProduct.map_tmul, TensorProduct.map_tmul, map_add,
        leftUnitorToₗ_tensorSingle, leftUnitorToₗ_tensorSingle, map_smul, leftActₗ_tmul,
        leftActₗ_tmul, leftUnitorToₗ_tensorSingle, leftActₗ_tmul]
      exact (P.d_act hq y m).symm
  | add z z' hz hz' =>
      rw [tensorSingle_add, map_add, map_add, map_add, map_add, hz, hz']

/-- The section is a section on a single-bidegree element: the relation rewrites `y ⊗ m` as
`1 ⊗ (y · m)`. -/
theorem relLeftUnitor_single (n : ℕ) (q : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
    (z : TensorProduct R (X q.1.1) (M q.1.2)) :
    (Submodule.Quotient.mk
        (leftUnitorFromₗ (M := M) u n (leftUnitorToₗ P n (tensorSingle (M := X) (N := M) q z)))
      : RelTensorCarrier (CDGAStructure.selfModule A) P n)
      = Submodule.Quotient.mk (tensorSingle (M := X) (N := M) q z) := by
  obtain ⟨⟨a, c⟩, h⟩ := q
  induction z using TensorProduct.induction_on with
  | zero => rw [tensorSingle_zero, map_zero, map_zero]
  | tmul y m =>
      rw [leftUnitorToₗ_tensorSingle, leftActₗ_tmul]
      refine sub_eq_zero.1 ?_
      rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
      have hrel := relTensorRelator_mem (CDGAStructure.selfModule A) P
        (Nat.add_zero a) h
        (show (a, c).1 + (a, c).2 = n by omega) (show (0, n).1 + (0, n).2 = n by omega)
        y u.one m
      have hval : relTensorRelator (CDGAStructure.selfModule A) P (Nat.add_zero a) h
          (show (a, c).1 + (a, c).2 = n by omega) (show (0, n).1 + (0, n).2 = n by omega)
          y u.one m
        = tensorSingle (M := X) (N := M) (⟨(a, c), h⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
            (y ⊗ₜ[R] m)
          - tensorSingle (M := X) (N := M)
            (⟨(0, n), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
            (u.one ⊗ₜ[R] P.act h y m) := by
        show ((-1 : R)) ^ (a * 0) • tensorSingle (M := X) (N := M) _
            (A.mul (Nat.add_zero a) y u.one ⊗ₜ[R] m) - _ = _
        rw [u.mul_one a y, Nat.mul_zero, pow_zero, one_smul]
      rw [hval] at hrel
      have hswap : (leftUnitorFromₗ (M := M) u n (P.act h y m)
          : TensorCarrier (R := R) X M n)
        = tensorSingle (M := X) (N := M)
            (⟨(0, n), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = n})
            (u.one ⊗ₜ[R] P.act h y m) := rfl
      rw [hswap, ← neg_sub]
      exact Submodule.neg_mem _ hrel
  | add z z' hz hz' =>
      rw [tensorSingle_add, map_add, map_add, Submodule.Quotient.mk_add,
        Submodule.Quotient.mk_add, hz, hz']

/-- **The section is a section.** -/
theorem relLeftUnitor_leftInverse (n : ℕ) (f : TensorCarrier (R := R) X M n) :
    (Submodule.Quotient.mk (leftUnitorFromₗ (M := M) u n (leftUnitorToₗ P n f))
      : RelTensorCarrier (CDGAStructure.selfModule A) P n) = Submodule.Quotient.mk f := by
  have hf := tensorCarrier_eq_sum_single (M := X) (N := M) f
  show (relTensorRel (CDGAStructure.selfModule A) P n).mkQ
      (leftUnitorFromₗ (M := M) u n (leftUnitorToₗ P n f))
    = (relTensorRel (CDGAStructure.selfModule A) P n).mkQ f
  rw [hf, map_sum, map_sum, map_sum, map_sum]
  exact Finset.sum_congr rfl fun q _ => relLeftUnitor_single P u n q (f q)

/-- **The left unitor is a degreewise isomorphism**: the algebra tensored over itself with a module
is the module. -/
noncomputable def relLeftUnitorEquiv (hP : CDGAModuleUnital u P) (n : ℕ) :
    RelTensorCarrier (CDGAStructure.selfModule A) P n ≃ₗ[R] M n where
  toFun := relLeftUnitorTo P n
  map_add' := map_add _
  map_smul' := map_smul _
  invFun m := Submodule.Quotient.mk (leftUnitorFromₗ (M := M) u n m)
  left_inv f := by
    refine Quotient.inductionOn' f fun z => ?_
    exact relLeftUnitor_leftInverse P u n z
  right_inv m := leftUnitorToₗ_leftUnitorFromₗ P u hP n m

/-- **The left unitor as a map of differential graded modules.** -/
noncomputable def relLeftUnitorHom :
    CDGAModuleHom (relTensorModule (CDGAStructure.selfModule A) P) P where
  toFun n f := relLeftUnitorTo P n f
  map_add n f f' := map_add (relLeftUnitorTo P n) f f'
  map_smul n r f := map_smul (relLeftUnitorTo P n) r f
  map_act h x f := by
    refine Quotient.inductionOn' f fun z => ?_
    exact leftUnitorToₗ_tensorAct P h x z
  map_d n f := by
    refine Quotient.inductionOn' f fun z => ?_
    exact leftUnitorToₗ_tensorD P n z

/-- **`A ⊗_A M ≅ M`**, as a full quasi-isomorphism of differential graded modules. -/
theorem relLeftUnitorHom_isQuasiIsoFull (hP : CDGAModuleUnital u P) :
    (relLeftUnitorHom P).IsQuasiIsoFull :=
  CDGAModuleHom.IsQuasiIsoFull.of_bijective fun n => (relLeftUnitorEquiv P u hP n).bijective

end Unitor

end GaloisForLFunctions.HTGeometry
