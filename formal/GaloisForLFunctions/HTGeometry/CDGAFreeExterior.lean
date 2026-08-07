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
      obtain ⟨y, hy⟩ := freeExteriorAlgHom_ιMulti hsq n (Matrix.vecTail v)
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

/-- The projection recovers the element of a degree. -/
theorem cdgaTotalOf_component (n : ℕ) (y : X n) :
    DirectSum.component R ℕ (CDGATotalCarrier A u) n (cdgaTotalOf A u n y) = y :=
  DirectSum.component.lof_self R n (y : CDGATotalCarrier A u n)

theorem cdgaTotalOf_injective (n : ℕ) : Function.Injective (cdgaTotalOf A u n) := by
  intro x y hxy
  have h := congrArg (DirectSum.component R ℕ (CDGATotalCarrier A u) n) hxy
  rwa [cdgaTotalOf_component, cdgaTotalOf_component] at h

/-- **The degree `n` component of the algebra map**, a linear map on the `n`-th exterior power. -/
noncomputable def freeExteriorComponent (hsq : ∀ v : M, A.mul rfl (φ v) (φ v) = 0) (n : ℕ) :
    (⋀[R]^n M) →ₗ[R] X n :=
  (DirectSum.component R ℕ (CDGATotalCarrier A u) n).comp
    (((freeExteriorAlgHom u φ hsq).toLinearMap).comp (⋀[R]^n M).subtype)

theorem freeExteriorComponent_spec (hsq : ∀ v : M, A.mul rfl (φ v) (φ v) = 0) (n : ℕ)
    (w : ⋀[R]^n M) :
    freeExteriorAlgHom u φ hsq (w : ExteriorAlgebra R M)
      = cdgaTotalOf A u n (freeExteriorComponent u φ hsq n w) := by
  obtain ⟨y, hy⟩ := freeExteriorAlgHom_mem u φ hsq n w
  have hcomp : freeExteriorComponent u φ hsq n w = y := by
    show DirectSum.component R ℕ (CDGATotalCarrier A u) n
      (freeExteriorAlgHom u φ hsq (w : ExteriorAlgebra R M)) = y
    rw [hy, cdgaTotalOf_component]
  rw [hcomp, hy]

/-- **The component map is multiplicative.** -/
theorem freeExteriorComponent_mul (hsq : ∀ v : M, A.mul rfl (φ v) (φ v) = 0) {a b n : ℕ}
    (h : a + b = n) (x : ⋀[R]^a M) (y : ⋀[R]^b M) :
    freeExteriorComponent u φ hsq n (exteriorMulOf h x y)
      = A.mul h (freeExteriorComponent u φ hsq a x) (freeExteriorComponent u φ hsq b y) := by
  refine cdgaTotalOf_injective (A := A) (u := u) n ?_
  rw [← freeExteriorComponent_spec, ← cdgaTotalOf_mul_of, ← freeExteriorComponent_spec,
    ← freeExteriorComponent_spec, ← map_mul]
  rfl

/-- The component map sends a vector to its prescribed image. -/
theorem freeExteriorComponent_one (hsq : ∀ v : M, A.mul rfl (φ v) (φ v) = 0) (v : M) :
    freeExteriorComponent u φ hsq 1 (exteriorι R v) = φ v := by
  refine cdgaTotalOf_injective (A := A) (u := u) 1 ?_
  rw [← freeExteriorComponent_spec]
  show freeExteriorAlgHom u φ hsq (ExteriorAlgebra.ι R v) = cdgaTotalOf A u 1 (φ v)
  rw [freeExteriorAlgHom_ι]

theorem freeExteriorComponent_ιMulti_zero (hsq : ∀ v : M, A.mul rfl (φ v) (φ v) = 0)
    (v : Fin 0 → M) : freeExteriorComponent u φ hsq 0 (exteriorPower.ιMulti R 0 v) = u.one := by
  refine cdgaTotalOf_injective (A := A) (u := u) 0 ?_
  rw [← freeExteriorComponent_spec, cdgaTotalOf_one]
  show freeExteriorAlgHom u φ hsq (ExteriorAlgebra.ιMulti R 0 v) = 1
  rw [ExteriorAlgebra.ιMulti_zero_apply, map_one]

theorem freeExteriorComponent_ιMulti_succ (hsq : ∀ v : M, A.mul rfl (φ v) (φ v) = 0) (n : ℕ)
    (v : Fin (n + 1) → M) :
    freeExteriorComponent u φ hsq (n + 1) (exteriorPower.ιMulti R (n + 1) v)
      = A.mul (by omega : 1 + n = n + 1) (φ (v 0))
        (freeExteriorComponent u φ hsq n (exteriorPower.ιMulti R n (Matrix.vecTail v))) := by
  refine cdgaTotalOf_injective (A := A) (u := u) (n + 1) ?_
  rw [← freeExteriorComponent_spec, ← cdgaTotalOf_mul_of, ← freeExteriorComponent_spec]
  show freeExteriorAlgHom u φ hsq (ExteriorAlgebra.ιMulti R (n + 1) v)
    = cdgaTotalOf A u 1 (φ (v 0)) * freeExteriorAlgHom u φ hsq
      (ExteriorAlgebra.ιMulti R n (Matrix.vecTail v))
  rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul, freeExteriorAlgHom_ι]

/-- The image of a wedge of vectors is a cocycle, by the Leibniz rule and the vanishing of the
differential on the generators. -/
theorem freeExteriorComponent_ιMulti_d (hsq : ∀ v : M, A.mul rfl (φ v) (φ v) = 0)
    (hd : ∀ v : M, A.d 1 (φ v) = 0) :
    ∀ (n : ℕ) (v : Fin n → M),
      A.d n (freeExteriorComponent u φ hsq n (exteriorPower.ιMulti R n v)) = 0
  | 0, v => by rw [freeExteriorComponent_ιMulti_zero]; exact u.d_one
  | (n + 1), v => by
      rw [freeExteriorComponent_ιMulti_succ, A.d_mul, hd,
        freeExteriorComponent_ιMulti_d hsq hd n (Matrix.vecTail v)]
      have hz1 : ∀ z : X n, A.mul (show 1 + 1 + n = n + 1 + 1 by omega) (0 : X (1 + 1)) z = 0 := by
        intro z
        have h0 : (0 : X (1 + 1)) = (0 : R) • (0 : X (1 + 1)) := (zero_smul R _).symm
        rw [h0, A.mul_smul_left, zero_smul]
      have hz2 : ∀ w : X 1,
          A.mul (show 1 + (n + 1) = n + 1 + 1 by omega) w (0 : X (n + 1)) = 0 := by
        intro w
        have h0 : (0 : X (n + 1)) = (0 : R) • (0 : X (n + 1)) := (zero_smul R _).symm
        rw [h0, A.mul_smul_right, zero_smul]
      rw [hz1, hz2, smul_zero, add_zero]

/-- **Every value of the component map is a cocycle.** -/
theorem freeExteriorComponent_d (hsq : ∀ v : M, A.mul rfl (φ v) (φ v) = 0)
    (hd : ∀ v : M, A.d 1 (φ v) = 0) (n : ℕ) (w : ⋀[R]^n M) :
    A.d n (freeExteriorComponent u φ hsq n w) = 0 := by
  have hmem : w ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n (M := M))) := by
    rw [exteriorPower.ιMulti_span R n M]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem
  · rintro z ⟨v, rfl⟩
    exact freeExteriorComponent_ιMulti_d u φ hsq hd n v
  · rw [map_zero]
    have h0 : (0 : X n) = (0 : R) • (0 : X n) := (zero_smul R _).symm
    rw [h0, A.d_smul, zero_smul]
  · intro z z' _ _ hz hz'
    rw [map_add, A.d_add, hz, hz', add_zero]
  · intro c z _ hz
    rw [map_smul, A.d_smul, hz, smul_zero]

/-- **The universal property of the exterior algebra as a commutative differential graded
algebra.**  A linear map from a module to the degree-one cocycles of a unital algebra, whose values
have vanishing squares, extends to a morphism out of the exterior algebra. -/
noncomputable def freeExteriorCDGAHom (hsq : ∀ v : M, A.mul rfl (φ v) (φ v) = 0)
    (hd : ∀ v : M, A.d 1 (φ v) = 0) : CDGAHom (exteriorModuleCDGA R M) A where
  toFun n w := freeExteriorComponent u φ hsq n w
  map_add n := map_add (freeExteriorComponent u φ hsq n)
  map_smul n c := (freeExteriorComponent u φ hsq n).map_smul c
  map_mul h x y := freeExteriorComponent_mul u φ hsq h x y
  map_d n x := by
    show freeExteriorComponent u φ hsq (n + 1) 0 = A.d n (freeExteriorComponent u φ hsq n x)
    rw [map_zero, freeExteriorComponent_d u φ hsq hd n x]

@[simp] theorem freeExteriorCDGAHom_ι (hsq : ∀ v : M, A.mul rfl (φ v) (φ v) = 0)
    (hd : ∀ v : M, A.d 1 (φ v) = 0) (v : M) :
    (freeExteriorCDGAHom u φ hsq hd).toFun 1 (exteriorι R v) = φ v :=
  freeExteriorComponent_one u φ hsq v

/-- A wedge of `n + 1` vectors is the product of the first with the wedge of the rest. -/
theorem exteriorPower_ιMulti_succ_mulOf (n : ℕ) (v : Fin (n + 1) → M) :
    exteriorPower.ιMulti R (n + 1) v
      = exteriorMulOf (by omega : 1 + n = n + 1) (exteriorι R (v 0))
        (exteriorPower.ιMulti R n (Matrix.vecTail v)) := by
  refine Subtype.ext ?_
  rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply]
  rfl

/-- **Uniqueness in the universal property.**  Two morphisms out of the exterior algebra that agree
on the unit and on the degree-one generators agree everywhere: the exterior powers are generated by
products of generators, and both morphisms are multiplicative. -/
theorem freeExteriorCDGAHom_unique {F G : CDGAHom (exteriorModuleCDGA R M) A}
    (huni : F.toFun 0 (exteriorModuleCDGAUnit R M).one
      = G.toFun 0 (exteriorModuleCDGAUnit R M).one)
    (hone : ∀ v : M, F.toFun 1 (exteriorι R v) = G.toFun 1 (exteriorι R v)) :
    ∀ (n : ℕ) (w : ⋀[R]^n M), F.toFun n w = G.toFun n w := by
  have hgen : ∀ (n : ℕ) (v : Fin n → M),
      F.toFun n (exteriorPower.ιMulti R n v) = G.toFun n (exteriorPower.ιMulti R n v) := by
    intro n
    induction n with
    | zero =>
        intro v
        have hone0 : exteriorPower.ιMulti R 0 v = (exteriorModuleCDGAUnit R M).one := by
          refine Subtype.ext ?_
          rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply]
          rfl
        rw [hone0, huni]
    | succ p ih =>
        intro v
        rw [exteriorPower_ιMulti_succ_mulOf]
        show F.toFun (p + 1) ((exteriorModuleCDGA R M).mul (by omega : 1 + p = p + 1)
            (exteriorι R (v 0)) (exteriorPower.ιMulti R p (Matrix.vecTail v)))
          = G.toFun (p + 1) ((exteriorModuleCDGA R M).mul (by omega : 1 + p = p + 1)
            (exteriorι R (v 0)) (exteriorPower.ιMulti R p (Matrix.vecTail v)))
        have hF := F.map_mul (by omega : 1 + p = p + 1) (exteriorι R (v 0))
          (exteriorPower.ιMulti R p (Matrix.vecTail v))
        have hG := G.map_mul (by omega : 1 + p = p + 1) (exteriorι R (v 0))
          (exteriorPower.ιMulti R p (Matrix.vecTail v))
        rw [hF, hG, hone, ih (Matrix.vecTail v)]
  intro n w
  have hmem : w ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n (M := M))) := by
    rw [exteriorPower.ιMulti_span R n M]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem
  · rintro z ⟨v, rfl⟩
    exact hgen n v
  · rw [show (0 : ⋀[R]^n M) = (0 : R) • (0 : ⋀[R]^n M) from (zero_smul R _).symm,
      F.map_smul, G.map_smul, zero_smul, zero_smul]
  · intro z z' _ _ hz hz'
    rw [F.map_add, G.map_add, hz, hz']
  · intro c z _ hz
    rw [F.map_smul, G.map_smul, hz]

end Universal

end GaloisForLFunctions.HTGeometry
