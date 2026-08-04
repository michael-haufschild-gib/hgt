import GaloisForLFunctions.RHTower.CyclicBarTraceAugmentation

/-!
# Module-valued traces and constant cyclic modules

A trace need not be scalar-valued.  If `tau : A -> M` is linear and cyclic,
then `a_0 tensor ... tensor a_n |-> tau (a_0 ... a_n)` is a morphism from
the cyclic bar of `A` to the constant cyclic module on `M`.

This is the exact reusable mechanism needed to impose a closed linear trace
condition (for example, diagonal trace modulo a Schwartz subspace) without
pretending that the condition is multiplicative.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RHTower

universe u

variable {R A M : Type u}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/-! ## Module-valued cyclic trace augmentation -/

/-- Degreewise module-valued trace of the ordered cyclic product. -/
def cyclicBarModuleTraceAugmentation (tau : A →ₗ[R] M) (n : ℕ) :
    CyclicBarTensor R A n →ₗ[R] M :=
  tau.comp (cyclicBarTotalProduct n)

@[simp]
theorem cyclicBarModuleTraceAugmentation_zero_tprod
    (tau : A →ₗ[R] M) (x : Fin 1 → A) :
    cyclicBarModuleTraceAugmentation tau 0
        (PiTensorProduct.tprod R x) = tau (x 0) := by
  change tau (cyclicBarDegreeZeroProduct (R := R)
    (PiTensorProduct.tprod R x)) = tau (x 0)
  rw [cyclicBarDegreeZeroProduct_tprod]

/-- Every face preserves a module-valued cyclic trace. -/
theorem cyclicBarModuleTraceAugmentation_comp_face
    (tau : A →ₗ[R] M) (htau : ∀ a b, tau (a * b) = tau (b * a)) :
    ∀ (n : ℕ) (i : Fin (n + 2)),
      (cyclicBarModuleTraceAugmentation tau n).comp
          (cyclicBarFace (R := R) (A := A) i) =
        cyclicBarModuleTraceAugmentation tau (n + 1) := by
  intro n
  induction n with
  | zero =>
      intro i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          have hi : i = 0 := Fin.eq_zero i
          subst i
          apply PiTensorProduct.ext
          ext x
          change
            tau (cyclicBarDegreeZeroProduct (R := R)
              (cyclicBarFace (R := R) (A := A) (1 : Fin 2)
                (PiTensorProduct.tprod R x))) =
            tau (cyclicBarDegreeZeroProduct (R := R)
              (cyclicBarFace (R := R) (A := A) (0 : Fin 2)
                (PiTensorProduct.tprod R x)))
          rw [cyclicBarFace_tprod, cyclicBarFace_tprod,
            cyclicBarDegreeZeroProduct_tprod,
            cyclicBarDegreeZeroProduct_tprod]
          change tau (x 1 * x 0) = tau (x 0 * x 1)
          exact htau (x 1) (x 0)
  | succ n ih =>
      intro i
      cases i using Fin.cases with
      | zero => rfl
      | succ j =>
          change
            ((cyclicBarModuleTraceAugmentation tau n).comp
                (cyclicBarFace (R := R) (A := A) 0)).comp
                (cyclicBarFace (R := R) (A := A) j.succ) = _
          rw [LinearMap.comp_assoc,
            cyclicBarFace_comp_face (R := R) (A := A)
              (0 : Fin (n + 2)) j (Fin.zero_le j),
            ← LinearMap.comp_assoc, ih j]
          rfl

/-- Inserting a unit preserves every module-valued product trace. -/
theorem cyclicBarModuleTraceAugmentation_comp_degeneracy
    (tau : A →ₗ[R] M) :
    ∀ (n : ℕ) (i : Fin (n + 1)),
      (cyclicBarModuleTraceAugmentation tau (n + 1)).comp
          (cyclicBarDegeneracy (R := R) (A := A) i) =
        cyclicBarModuleTraceAugmentation tau n := by
  intro n
  induction n with
  | zero =>
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      change
        ((cyclicBarModuleTraceAugmentation tau 0).comp
            (cyclicBarFace (R := R) (A := A) 0)).comp
            (cyclicBarDegeneracy (R := R) (A := A) 0) = _
      have hface := cyclicBarFace_comp_degeneracy_self
        (R := R) (A := A) (0 : Fin 1)
      change
        (cyclicBarFace (R := R) (A := A) (0 : Fin 2)).comp
            (cyclicBarDegeneracy (R := R) (A := A) (0 : Fin 1)) =
          LinearMap.id at hface
      rw [LinearMap.comp_assoc, hface]
      rfl
  | succ n ih =>
      intro i
      cases i using Fin.cases with
      | zero =>
          change
            ((cyclicBarModuleTraceAugmentation tau (n + 1)).comp
                (cyclicBarFace (R := R) (A := A) 0)).comp
                (cyclicBarDegeneracy (R := R) (A := A) 0) = _
          have hface := cyclicBarFace_comp_degeneracy_self
            (R := R) (A := A) (0 : Fin (n + 2))
          change
            (cyclicBarFace (R := R) (A := A) (0 : Fin (n + 3))).comp
                (cyclicBarDegeneracy (R := R) (A := A) (0 : Fin (n + 2))) =
              LinearMap.id at hface
          rw [LinearMap.comp_assoc, hface]
          rfl
      | succ j =>
          change
            ((cyclicBarModuleTraceAugmentation tau (n + 1)).comp
                (cyclicBarFace (R := R) (A := A) 0)).comp
                (cyclicBarDegeneracy (R := R) (A := A) j.succ) = _
          have hface := cyclicBarFace_comp_degeneracy_of_le
            (R := R) (A := A) (0 : Fin (n + 2)) j (Fin.zero_le _)
          change
            (cyclicBarFace (R := R) (A := A) (0 : Fin (n + 3))).comp
                (cyclicBarDegeneracy (R := R) (A := A) j.succ) =
              (cyclicBarDegeneracy (R := R) (A := A) j).comp
                (cyclicBarFace (R := R) (A := A) (0 : Fin (n + 2))) at hface
          rw [LinearMap.comp_assoc, hface, ← LinearMap.comp_assoc, ih j]
          rfl

/-- Cyclic rotation preserves a module-valued cyclic trace. -/
theorem cyclicBarModuleTraceAugmentation_comp_rotate
    (tau : A →ₗ[R] M) (htau : ∀ a b, tau (a * b) = tau (b * a))
    (n : ℕ) :
    (cyclicBarModuleTraceAugmentation tau n).comp
        (cyclicBarRotate (R := R) (A := A) n).toLinearMap =
      cyclicBarModuleTraceAugmentation tau n := by
  cases n with
  | zero =>
      apply LinearMap.ext
      intro y
      induction y using PiTensorProduct.induction_on' with
      | tprodCoeff r x =>
          rw [PiTensorProduct.tprodCoeff_eq_smul_tprod,
            map_smul, map_smul, LinearMap.comp_apply]
          change r • cyclicBarModuleTraceAugmentation tau 0
              (cyclicBarRotate (R := R) (A := A) 0
                (PiTensorProduct.tprod R x)) =
            r • cyclicBarModuleTraceAugmentation tau 0
              (PiTensorProduct.tprod R x)
          rw [cyclicBarRotate_tprod]
          simp [cyclicBarModuleTraceAugmentation,
            cyclicBarTotalProduct, cyclicBarRotateTuple]
          congr 2
      | add x y hx hy => simp only [map_add, hx, hy]
  | succ n =>
      change
        ((cyclicBarModuleTraceAugmentation tau n).comp
            (cyclicBarFace (R := R) (A := A) 0)).comp
            (cyclicBarRotate (R := R) (A := A) (n + 1)).toLinearMap = _
      rw [LinearMap.comp_assoc,
        cyclicBarRotate_comp_face_zero (R := R) (A := A),
        cyclicBarModuleTraceAugmentation_comp_face tau htau n
          (Fin.last (n + 1))]

/-! ## Constant module cyclic object -/

/-- Constant presented simplicial module with value `M`. -/
def moduleConstantPresentedSimplicial :
    PresentedSimplicialObject (ModuleCat R) :=
  (Functor.const SimplexCategoryGenRelᵒᵖ).obj (ModuleCat.of R M)

@[simp]
theorem moduleConstantPresentedSimplicial_map
    {j k : SimplexCategoryGenRelᵒᵖ} (f : j ⟶ k) :
    (moduleConstantPresentedSimplicial (R := R) (M := M)).map f = 𝟙 _ :=
  rfl

/-- Constant cyclic module on an arbitrary `R`-module. -/
def moduleConstantCyclicModule : CyclicModule R where
  simplicial := moduleConstantPresentedSimplicial (R := R) (M := M)
  cyclic _ := 𝟙 _
  cyclic_order n := by
    change categoricalEndIterate (𝟙 (ModuleCat.of R M)) (n + 1) = 𝟙 _
    induction n + 1 with
    | zero => rfl
    | succ n ih => simp [categoricalEndIterate, ih]
  cyclic_face_zero n := by simp
  cyclic_face_succ n i := by simp
  cyclic_degeneracy_zero n := by simp
  cyclic_degeneracy_succ n i := by simp

@[simp]
theorem moduleConstantCyclicModule_cyclic (n : ℕ) :
    (moduleConstantCyclicModule (R := R) (M := M)).cyclic n = 𝟙 _ :=
  rfl

/-! ## The induced cyclic morphism -/

/-- Module-valued trace component at every simplex object. -/
def cyclicBarModuleTraceComponent (tau : A →ₗ[R] M) :
    ∀ a : SimplexCategoryGenRel,
      (cyclicBarPresentedSimplicial (R := R) (A := A)).obj
          (Opposite.op a) ⟶ ModuleCat.of R M :=
  SimplexCategoryGenRel.rec fun n =>
    ModuleCat.ofHom (cyclicBarModuleTraceAugmentation tau n)

theorem cyclicBarModuleTraceAugmentation_naturality
    (tau : A →ₗ[R] M) (htau : ∀ a b, tau (a * b) = tau (b * a))
    {a b : SimplexCategoryGenRel} (f : a ⟶ b) :
    (cyclicBarPresentedSimplicial (R := R) (A := A)).map f.op ≫
        cyclicBarModuleTraceComponent tau a =
      cyclicBarModuleTraceComponent tau b := by
  let P : MorphismProperty SimplexCategoryGenRel := fun a b f =>
    (cyclicBarPresentedSimplicial (R := R) (A := A)).map f.op ≫
        cyclicBarModuleTraceComponent tau a =
      cyclicBarModuleTraceComponent tau b
  apply SimplexCategoryGenRel.hom_induction P
  · intro n
    dsimp [P]
    simp
  · intro n m u i hu
    change
      (cyclicBarPresentedSimplicial (R := R) (A := A)).map u.op ≫
          cyclicBarModuleTraceComponent tau (.mk n) =
        cyclicBarModuleTraceComponent tau (.mk m) at hu
    change
      (cyclicBarPresentedSimplicial (R := R) (A := A)).map
            ((SimplexCategoryGenRel.δ i).op ≫ u.op) ≫
          cyclicBarModuleTraceComponent tau (.mk n) =
        cyclicBarModuleTraceComponent tau (.mk (m + 1))
    rw [Functor.map_comp, Category.assoc, hu]
    apply ModuleCat.hom_ext
    exact cyclicBarModuleTraceAugmentation_comp_face tau htau m i
  · intro n m u i hu
    change
      (cyclicBarPresentedSimplicial (R := R) (A := A)).map u.op ≫
          cyclicBarModuleTraceComponent tau (.mk n) =
        cyclicBarModuleTraceComponent tau (.mk (m + 1)) at hu
    change
      (cyclicBarPresentedSimplicial (R := R) (A := A)).map
            ((SimplexCategoryGenRel.σ i).op ≫ u.op) ≫
          cyclicBarModuleTraceComponent tau (.mk n) =
        cyclicBarModuleTraceComponent tau (.mk m)
    rw [Functor.map_comp, Category.assoc, hu]
    apply ModuleCat.hom_ext
    exact cyclicBarModuleTraceAugmentation_comp_degeneracy tau m i

/-- Simplicial morphism induced by a module-valued trace. -/
def cyclicBarModuleTraceSimplicialHom
    (tau : A →ₗ[R] M) (htau : ∀ a b, tau (a * b) = tau (b * a)) :
    (cyclicBarCyclicModule (R := R) (A := A)).simplicial ⟶
      (moduleConstantCyclicModule (R := R) (M := M)).simplicial where
  app j := cyclicBarModuleTraceComponent tau j.unop
  naturality {j k} f := by
    have h := cyclicBarModuleTraceAugmentation_naturality tau htau f.unop
    change
      (cyclicBarPresentedSimplicial (R := R) (A := A)).map f ≫
          cyclicBarModuleTraceComponent tau k.unop =
        cyclicBarModuleTraceComponent tau j.unop ≫ 𝟙 _
    rw [Category.comp_id]
    exact h

/-- Genuine cyclic morphism induced by a module-valued trace. -/
def cyclicBarModuleTraceCyclicHom
    (tau : A →ₗ[R] M) (htau : ∀ a b, tau (a * b) = tau (b * a)) :
    CyclicModule.Hom (cyclicBarCyclicModule (R := R) (A := A))
      (moduleConstantCyclicModule (R := R) (M := M)) where
  simplicial := cyclicBarModuleTraceSimplicialHom tau htau
  cyclic_naturality n := by
    simp only [cyclicBarCyclicModule_cyclic,
      moduleConstantCyclicModule_cyclic, Category.comp_id]
    apply ModuleCat.hom_ext
    exact cyclicBarModuleTraceAugmentation_comp_rotate tau htau n

end GaloisForLFunctions.RHTower
