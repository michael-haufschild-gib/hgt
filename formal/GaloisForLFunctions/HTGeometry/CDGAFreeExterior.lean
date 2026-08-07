import GaloisForLFunctions.HTGeometry.CDGATotalAlgebra
import GaloisForLFunctions.HTGeometry.ExteriorGradedMul

/-!
# The exterior algebra as a commutative differential graded algebra

The exterior powers of a module, with the product of the exterior algebra and the zero differential,
form a commutative differential graded algebra: the product adds degrees, is associative, and is
graded commutative with the sign the exterior algebra already carries.  The unit is the unit of the
exterior algebra, which lies in degree zero.

* `exteriorModuleCDGA` : the exterior algebra of a module, graded by exterior powers.
* `exteriorModuleCDGAUnit` : its unit.
-/

universe u v

namespace GaloisForLFunctions.HTGeometry

open exteriorPower

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- **The exterior algebra of a module, graded by exterior powers, with the zero differential.** -/
noncomputable def exteriorModuleCDGA : CDGAStructure R (fun n => ⋀[R]^n M) where
  mul h y z := exteriorMulOf h y z
  d _ _ := 0
  mul_add_left h := exteriorMulOf_add_left h
  mul_add_right h := exteriorMulOf_add_right h
  mul_smul_left h c := exteriorMulOf_smul_left h c
  mul_smul_right h c := exteriorMulOf_smul_right h c
  mul_assoc h₁ h₂ h₃ h₄ := exteriorMulOf_assoc h₁ h₂ h₃ h₄
  mul_comm h h' := exteriorMulOf_comm h h'
  d_add _ _ _ := (add_zero (0 : ⋀[R]^_ M)).symm
  d_smul _ c _ := (smul_zero c).symm
  d_d _ _ := rfl
  d_mul h x y := by
    show (0 : ⋀[R]^_ M) = exteriorMulOf _ (0 : ⋀[R]^_ M) y + _ • exteriorMulOf _ x (0 : ⋀[R]^_ M)
    rw [exteriorMulOf_zero_left', exteriorMulOf_zero_right', smul_zero, add_zero]

/-- **The unit of the exterior algebra**, in degree zero. -/
noncomputable def exteriorModuleCDGAUnit : CDGAUnit (exteriorModuleCDGA R M) where
  one := ⟨1, SetLike.one_mem_graded _⟩
  one_mul b y := by
    refine Subtype.ext ?_
    show (1 : ExteriorAlgebra R M) * (y : ExteriorAlgebra R M) = (y : ExteriorAlgebra R M)
    rw [one_mul]
  d_one := rfl

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open exteriorPower

section Universal

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {X : ℕ → Type v} [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]
  {A : CDGAStructure R X} (u : CDGAUnit A) (φ : M →ₗ[R] X 1)

/-- The inclusion turns the graded product into the product of the total algebra, in the degree
prescribed by an equation. -/
theorem cdgaTotalOf_mul_of {a b n : ℕ} (h : a + b = n) (x : X a) (y : X b) :
    cdgaTotalOf A u a x * cdgaTotalOf A u b y = cdgaTotalOf A u n (A.mul h x y) := by
  cases h
  exact cdgaTotalOf_mul A u x y

/-- A degree-one map into a unital algebra, as a map into its total algebra. -/
noncomputable def freeExteriorTotalMap : M →ₗ[R] CDGATotal A u :=
  (cdgaTotalOf A u 1).comp φ

theorem freeExteriorTotalMap_sq (hsq : ∀ v : M, A.mul rfl (φ v) (φ v) = 0) (v : M) :
    freeExteriorTotalMap u φ v * freeExteriorTotalMap u φ v = 0 := by
  show cdgaTotalOf A u 1 (φ v) * cdgaTotalOf A u 1 (φ v) = 0
  rw [cdgaTotalOf_mul, hsq, map_zero]

/-- **The algebra map on the exterior algebra determined by a degree-one map whose squares
vanish.** -/
noncomputable def freeExteriorAlgHom (hsq : ∀ v : M, A.mul rfl (φ v) (φ v) = 0) :
    ExteriorAlgebra R M →ₐ[R] CDGATotal A u :=
  ExteriorAlgebra.lift R ⟨freeExteriorTotalMap u φ, freeExteriorTotalMap_sq u φ hsq⟩

@[simp] theorem freeExteriorAlgHom_ι (hsq : ∀ v : M, A.mul rfl (φ v) (φ v) = 0) (v : M) :
    freeExteriorAlgHom u φ hsq (ExteriorAlgebra.ι R v) = cdgaTotalOf A u 1 (φ v) := by
  rw [freeExteriorAlgHom, ExteriorAlgebra.lift_ι_apply]
  rfl

/-- The image of a wedge of `n` vectors lies in degree `n`. -/
theorem freeExteriorAlgHom_ιMulti (hsq : ∀ v : M, A.mul rfl (φ v) (φ v) = 0) :
    ∀ (n : ℕ) (v : Fin n → M),
      ∃ y : X n, freeExteriorAlgHom u φ hsq (ExteriorAlgebra.ιMulti R n v) = cdgaTotalOf A u n y
  | 0, v => ⟨u.one, by rw [ExteriorAlgebra.ιMulti_zero_apply, map_one, cdgaTotalOf_one]⟩
  | (n + 1), v => by
      obtain ⟨y, hy⟩ := freeExteriorAlgHom_ιMulti u φ hsq n (Matrix.vecTail v)
      refine ⟨A.mul (by omega : 1 + n = n + 1) (φ (v 0)) y, ?_⟩
      rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul, freeExteriorAlgHom_ι, hy,
        cdgaTotalOf_mul_of]

/-- **The image of the `n`-th exterior power lies in degree `n`.** -/
theorem freeExteriorAlgHom_mem (hsq : ∀ v : M, A.mul rfl (φ v) (φ v) = 0) (n : ℕ)
    (w : ⋀[R]^n M) :
    ∃ y : X n, freeExteriorAlgHom u φ hsq (w : ExteriorAlgebra R M) = cdgaTotalOf A u n y := by
  have hmem : (w : ExteriorAlgebra R M)
      ∈ Submodule.span R (Set.range (ExteriorAlgebra.ιMulti R n)) := by
    rw [exteriorPower.ιMulti_span_fixedDegree]
    exact w.2
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem
  · rintro z ⟨v, rfl⟩
    exact freeExteriorAlgHom_ιMulti u φ hsq n v
  · exact ⟨0, by rw [map_zero, map_zero]⟩
  · rintro z z' - - ⟨y, hy⟩ ⟨y', hy'⟩
    exact ⟨y + y', by rw [map_add, hy, hy', map_add]⟩
  · rintro c z - ⟨y, hy⟩
    exact ⟨c • y, by rw [map_smul, hy, map_smul]⟩

end Universal

end GaloisForLFunctions.HTGeometry
