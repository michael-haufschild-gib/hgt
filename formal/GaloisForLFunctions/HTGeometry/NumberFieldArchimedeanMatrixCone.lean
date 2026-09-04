import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanCone
import GaloisForLFunctions.HTGeometry.FiniteCuspMacbeathConvexSubset
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Corrected raw archimedean matrix cone over a number field

At real and complex infinite places, positive-definite matrices lie in proper symmetric or
Hermitian linear subspaces of the raw matrix ambient space.  Thus their locus is not open in the
raw ambient space.  It is, however, a nonempty convex subset of a locally convex real topological
vector space, which is exactly the setting of the convex-subset Macbeath criterion.

This module constructs that raw cone, its continuous `SL_n(𝓞 K)` congruence action, and a
canonical equivariant homeomorphism to the existing self-adjoint positive-form model.  No topology
is lost by changing models.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField Pointwise
open scoped Classical ComplexOrder NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-- Raw real/complex matrix coordinates at all infinite places.  Function notation is deliberate:
it exposes the canonical locally convex structure to typeclass synthesis. -/
abbrev numberFieldArchimedeanMatrixForms (K : Type*) [Field K] (n : ℕ) :=
  ({w : InfinitePlace K // w.IsReal} → Fin n → Fin n → ℝ) ×
    ({w : InfinitePlace K // w.IsComplex} → Fin n → Fin n → ℂ)

/-- Placewise positive-definite matrices inside raw coordinates. -/
def numberFieldArchimedeanMatrixCone (K : Type*) [Field K] (n : ℕ) :
    Set (numberFieldArchimedeanMatrixForms K n) :=
  {A | (∀ w, (show Matrix (Fin n) (Fin n) ℝ from A.1 w).PosDef) ∧
    ∀ w, (show Matrix (Fin n) (Fin n) ℂ from A.2 w).PosDef}

omit [NumberField K] in
/-- Identity matrices give a point of the raw archimedean cone. -/
theorem numberFieldArchimedeanMatrixCone_nonempty :
    (numberFieldArchimedeanMatrixCone K n).Nonempty := by
  let Ireal : {w : InfinitePlace K // w.IsReal} → Fin n → Fin n → ℝ :=
    fun _ => show Fin n → Fin n → ℝ from (1 : Matrix (Fin n) (Fin n) ℝ)
  let Icomplex : {w : InfinitePlace K // w.IsComplex} → Fin n → Fin n → ℂ :=
    fun _ => show Fin n → Fin n → ℂ from (1 : Matrix (Fin n) (Fin n) ℂ)
  refine ⟨(Ireal, Icomplex), ?_, ?_⟩
  · intro w
    change (1 : Matrix (Fin n) (Fin n) ℝ).PosDef
    exact Matrix.PosDef.one
  · intro w
    change (1 : Matrix (Fin n) (Fin n) ℂ).PosDef
    exact Matrix.PosDef.one

omit [NumberField K] in
/-- The raw archimedean matrix cone is convex over `ℝ`. -/
theorem convex_numberFieldArchimedeanMatrixCone :
    Convex ℝ (numberFieldArchimedeanMatrixCone K n) := by
  intro A hA B hB a b ha hb hab
  constructor
  · intro w
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hB.1 w
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      simpa [hb0, ha1] using hA.1 w
    exact ((hA.1 w).smul (lt_of_le_of_ne ha (Ne.symm ha0))).add
      ((hB.1 w).smul (lt_of_le_of_ne hb (Ne.symm hb0)))
  · intro w
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hB.2 w
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      simpa [hb0, ha1] using hA.2 w
    exact ((hA.2 w).smul (lt_of_le_of_ne ha (Ne.symm ha0))).add
      ((hB.2 w).smul (lt_of_le_of_ne hb (Ne.symm hb0)))

/-- Raw placewise congruence by an integral special-linear matrix. -/
def numberFieldArchimedeanMatrixConj
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
    (A : numberFieldArchimedeanMatrixForms K n) :
    numberFieldArchimedeanMatrixForms K n :=
  (fun w =>
    let G := numberFieldRealOrderMatrixAt w (g : Matrix (Fin n) (Fin n) (𝓞 K))
    show Fin n → Fin n → ℝ from
      G * (show Matrix (Fin n) (Fin n) ℝ from A.1 w) * Gᴴ,
   fun w =>
    let G := numberFieldComplexOrderMatrixAt w (g : Matrix (Fin n) (Fin n) (𝓞 K))
    show Fin n → Fin n → ℂ from
      G * (show Matrix (Fin n) (Fin n) ℂ from A.2 w) * Gᴴ)

omit [NumberField K] in
@[simp]
theorem numberFieldArchimedeanMatrixConj_one
    (A : numberFieldArchimedeanMatrixForms K n) :
    numberFieldArchimedeanMatrixConj
      (1 : Matrix.SpecialLinearGroup (Fin n) (𝓞 K)) A = A := by
  apply Prod.ext <;> funext w
  · simp [numberFieldArchimedeanMatrixConj]
  · simp [numberFieldArchimedeanMatrixConj]

omit [NumberField K] in
theorem numberFieldArchimedeanMatrixConj_mul
    (g h : Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
    (A : numberFieldArchimedeanMatrixForms K n) :
    numberFieldArchimedeanMatrixConj (g * h) A =
      numberFieldArchimedeanMatrixConj g
        (numberFieldArchimedeanMatrixConj h A) := by
  apply Prod.ext <;> funext w
  · simp [numberFieldArchimedeanMatrixConj, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · simp [numberFieldArchimedeanMatrixConj, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]

omit [NumberField K] in
theorem numberFieldArchimedeanMatrixConj_mem
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
    {A : numberFieldArchimedeanMatrixForms K n}
    (hA : A ∈ numberFieldArchimedeanMatrixCone K n) :
    numberFieldArchimedeanMatrixConj g A ∈
      numberFieldArchimedeanMatrixCone K n := by
  constructor
  · intro w
    exact (hA.1 w).mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_of_isUnit (numberFieldRealSpecialLinearAt_isUnit w g))
  · intro w
    exact (hA.2 w).mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_of_isUnit (numberFieldComplexSpecialLinearAt_isUnit w g))

noncomputable instance numberFieldArchimedeanMatrixConeMulAction :
    MulAction (Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
      (numberFieldArchimedeanMatrixCone K n) where
  smul g A := ⟨numberFieldArchimedeanMatrixConj g A.1,
    numberFieldArchimedeanMatrixConj_mem g A.2⟩
  one_smul A := Subtype.ext (numberFieldArchimedeanMatrixConj_one A.1)
  mul_smul g h A := Subtype.ext (numberFieldArchimedeanMatrixConj_mul g h A.1)

omit [NumberField K] in
/-- Every fixed raw congruence map is continuous. -/
theorem continuous_numberFieldArchimedeanMatrixConj
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K)) :
    Continuous (numberFieldArchimedeanMatrixConj (K := K) g) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro w
    have hAw : Continuous (fun A : numberFieldArchimedeanMatrixForms K n =>
        (show Matrix (Fin n) (Fin n) ℝ from A.1 w)) :=
      (continuous_apply w).comp continuous_fst
    exact (continuous_const.matrix_mul hAw).matrix_mul continuous_const
  · apply continuous_pi
    intro w
    have hAw : Continuous (fun A : numberFieldArchimedeanMatrixForms K n =>
        (show Matrix (Fin n) (Fin n) ℂ from A.2 w)) :=
      (continuous_apply w).comp continuous_snd
    exact (continuous_const.matrix_mul hAw).matrix_mul continuous_const

noncomputable instance numberFieldArchimedeanMatrixConeContinuousConstSMul :
    ContinuousConstSMul (Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
      (numberFieldArchimedeanMatrixCone K n) where
  continuous_const_smul g :=
    Continuous.subtype_mk
      ((continuous_numberFieldArchimedeanMatrixConj g).comp continuous_subtype_val) _

/-- Convert raw positive-definite coordinates to existing self-adjoint positive forms. -/
def numberFieldArchimedeanMatrixConeToPositiveForms
    (A : numberFieldArchimedeanMatrixCone K n) :
    numberFieldArchimedeanPositiveForms K n :=
  ⟨(fun w => ⟨(show Matrix (Fin n) (Fin n) ℝ from A.1.1 w),
      (A.2.1 w).isHermitian⟩,
    fun w => ⟨(show Matrix (Fin n) (Fin n) ℂ from A.1.2 w),
      (A.2.2 w).isHermitian⟩), A.2⟩

/-- Forget self-adjoint wrappers from existing positive forms. -/
def numberFieldArchimedeanPositiveFormsToMatrixCone
    (A : numberFieldArchimedeanPositiveForms K n) :
    numberFieldArchimedeanMatrixCone K n :=
  ⟨((fun w i j => (A.1.1 w : Matrix (Fin n) (Fin n) ℝ) i j),
    fun w i j => (A.1.2 w : Matrix (Fin n) (Fin n) ℂ) i j), A.2⟩

omit [NumberField K] in
@[simp]
theorem numberFieldArchimedeanMatrixConeToPositiveForms_toMatrixCone
    (A : numberFieldArchimedeanMatrixCone K n) :
    numberFieldArchimedeanPositiveFormsToMatrixCone
      (numberFieldArchimedeanMatrixConeToPositiveForms A) = A := by
  apply Subtype.ext
  apply Prod.ext <;> funext w <;> funext i <;> funext j <;> rfl

omit [NumberField K] in
@[simp]
theorem numberFieldArchimedeanPositiveFormsToMatrixCone_toPositiveForms
    (A : numberFieldArchimedeanPositiveForms K n) :
    numberFieldArchimedeanMatrixConeToPositiveForms
      (numberFieldArchimedeanPositiveFormsToMatrixCone A) = A := by
  apply Subtype.ext
  apply Prod.ext <;> funext w <;> apply Subtype.ext <;> funext i <;> funext j <;> rfl

/-- Algebraic equivalence between raw and self-adjoint cone models. -/
def numberFieldArchimedeanMatrixConeEquiv :
    numberFieldArchimedeanMatrixCone K n ≃
      numberFieldArchimedeanPositiveForms K n where
  toFun := numberFieldArchimedeanMatrixConeToPositiveForms
  invFun := numberFieldArchimedeanPositiveFormsToMatrixCone
  left_inv := numberFieldArchimedeanMatrixConeToPositiveForms_toMatrixCone
  right_inv := numberFieldArchimedeanPositiveFormsToMatrixCone_toPositiveForms

omit [NumberField K] in
theorem continuous_numberFieldArchimedeanMatrixConeToPositiveForms :
    Continuous (numberFieldArchimedeanMatrixConeToPositiveForms (K := K) (n := n)) := by
  refine Continuous.subtype_mk ?_ _
  apply Continuous.prodMk
  · apply continuous_pi
    intro w
    exact Continuous.subtype_mk
      (((continuous_apply w).comp continuous_fst).comp continuous_subtype_val) _
  · apply continuous_pi
    intro w
    exact Continuous.subtype_mk
      (((continuous_apply w).comp continuous_snd).comp continuous_subtype_val) _

omit [NumberField K] in
theorem continuous_numberFieldArchimedeanPositiveFormsToMatrixCone :
    Continuous (numberFieldArchimedeanPositiveFormsToMatrixCone (K := K) (n := n)) := by
  refine Continuous.subtype_mk ?_ _
  apply Continuous.prodMk
  · apply continuous_pi
    intro w
    exact ((((continuous_apply w).comp continuous_fst).comp
      continuous_subtype_val).subtype_val)
  · apply continuous_pi
    intro w
    exact ((((continuous_apply w).comp continuous_snd).comp
      continuous_subtype_val).subtype_val)

/-- Equivariant homeomorphism between raw and self-adjoint positive-form models. -/
def numberFieldArchimedeanMatrixConeHomeomorph :
    numberFieldArchimedeanMatrixCone K n ≃ₜ
      numberFieldArchimedeanPositiveForms K n :=
  ⟨numberFieldArchimedeanMatrixConeEquiv,
    continuous_numberFieldArchimedeanMatrixConeToPositiveForms,
    continuous_numberFieldArchimedeanPositiveFormsToMatrixCone⟩

omit [NumberField K] in
@[simp]
theorem numberFieldArchimedeanMatrixConeHomeomorph_smul
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
    (A : numberFieldArchimedeanMatrixCone K n) :
    numberFieldArchimedeanMatrixConeHomeomorph (g • A) =
      g • numberFieldArchimedeanMatrixConeHomeomorph A := rfl

/-- Finite-cusp reduction on the corrected archimedean cone presents the integral special-linear
group.  Convexity, nonemptiness, topology, and continuity of the action are discharged here; only
the arithmetic reduction data remain. -/
theorem isFinitelyPresented_specialLinearGroup_of_numberFieldArchimedeanMatrixFiniteCusps
    {C : Type*} (S : Finset C)
    (V : C → Set (numberFieldArchimedeanMatrixCone K n))
    (hVopen : ∀ i ∈ S, IsOpen (V i))
    (hVne : ∃ i ∈ S, (V i).Nonempty)
    (hVconn : IsPreconnected (finiteCuspUnion S V))
    (hcover : ⋃ g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K),
      g • finiteCuspUnion S V = Set.univ)
    (hfinite : ∀ i ∈ S, ∀ j ∈ S,
      {g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K) |
        ∃ x ∈ V i, g • x ∈ V j}.Finite) :
    IsFinitelyPresented (Matrix.SpecialLinearGroup (Fin n) (𝓞 K)) :=
  isFinitelyPresented_of_finiteCuspMacbeath_convexSubset
    (numberFieldArchimedeanMatrixCone K n)
    convex_numberFieldArchimedeanMatrixCone
    numberFieldArchimedeanMatrixCone_nonempty
    S V hVopen hVne hVconn hcover hfinite

end

end GaloisForLFunctions.HTGeometry
