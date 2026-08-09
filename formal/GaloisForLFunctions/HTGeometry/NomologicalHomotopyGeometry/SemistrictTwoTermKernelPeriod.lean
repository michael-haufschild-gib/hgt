import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.HigherPeriodSpencer
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Semistrict two-term kernel local systems and higher periods

The algebraic section constructs the homotopy kernel and cokernel of a two-term `L∞` algebra,
descends the binary bracket to the cokernel, descends its action to the kernel, and proves the
representation identity after the ternary correction vanishes on cycles.  The connection section
uses the two relevant components of the universal `L∞` Bianchi identity to prove fake-flat kernel
reduction.  Higher-period and Spencer generation then follow from the shared period theorem.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.SemistrictTwoTermKernelPeriod

open HigherPeriodSpencer

/-- Algebraic two-term `L∞` data and exactly the identities used on homology. -/
structure TwoTermLInfinity (Vneg Vzero : Type*)
    [AddCommGroup Vneg] [AddCommGroup Vzero] [Module ℝ Vneg] [Module ℝ Vzero] where
  μ₁ : Vneg →ₗ[ℝ] Vzero
  μ₂₀₀ : Vzero →ₗ[ℝ] Vzero →ₗ[ℝ] Vzero
  μ₂₀₁ : Vzero →ₗ[ℝ] Vneg →ₗ[ℝ] Vneg
  μ₃ : Vzero →ₗ[ℝ] Vzero →ₗ[ℝ] Vzero →ₗ[ℝ] Vneg
  μ₂₀₀_skew : ∀ x y, μ₂₀₀ x y = -μ₂₀₀ y x
  differential_action : ∀ x v, μ₁ (μ₂₀₁ x v) = μ₂₀₀ x (μ₁ v)
  jacobiator : ∀ x y z,
    μ₂₀₀ x (μ₂₀₀ y z) + μ₂₀₀ y (μ₂₀₀ z x) + μ₂₀₀ z (μ₂₀₀ x y) =
      μ₁ (μ₃ x y z)
  boundary_action_kernel : ∀ v k, μ₁ k = 0 → μ₂₀₁ (μ₁ v) k = 0
  representation_defect : ∀ x y k,
    μ₂₀₁ x (μ₂₀₁ y k) - μ₂₀₁ y (μ₂₀₁ x k) - μ₂₀₁ (μ₂₀₀ x y) k =
      μ₃ x y (μ₁ k)
  μ₃_zero_right : ∀ x y, μ₃ x y 0 = 0

namespace TwoTermLInfinity

variable {Vneg Vzero : Type*}
variable [AddCommGroup Vneg] [AddCommGroup Vzero] [Module ℝ Vneg] [Module ℝ Vzero]
variable (L : TwoTermLInfinity Vneg Vzero)

/-- Homotopy kernel `ker μ₁`. -/
abbrev homotopyKernel := LinearMap.ker L.μ₁

/-- Degree-zero homology `V₀ / im μ₁`. -/
abbrev homologyZero := Vzero ⧸ LinearMap.range L.μ₁

/-- The degree-zero action preserves the homotopy kernel. -/
def kernelActionAt (x : Vzero) : Module.End ℝ L.homotopyKernel where
  toFun k := ⟨L.μ₂₀₁ x k, by
    rw [LinearMap.mem_ker, L.differential_action, k.property]
    simp⟩
  map_add' k l := by ext; simp
  map_smul' c k := by ext; simp

/-- The kernel action is linear in the degree-zero input. -/
def kernelAction : Vzero →ₗ[ℝ] Module.End ℝ L.homotopyKernel where
  toFun := L.kernelActionAt
  map_add' x y := by ext k; simp [kernelActionAt]
  map_smul' c x := by ext k; simp [kernelActionAt]

/-- Boundaries act trivially on the homotopy kernel. -/
theorem boundaryRange_le_kernelAction :
    LinearMap.range L.μ₁ ≤ LinearMap.ker L.kernelAction := by
  rintro _ ⟨v, rfl⟩
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro k
  apply Subtype.ext
  exact L.boundary_action_kernel v k k.property

/-- Honest action of degree-zero homology on the homotopy kernel. -/
def homologyAction : L.homologyZero →ₗ[ℝ] Module.End ℝ L.homotopyKernel :=
  (LinearMap.range L.μ₁).liftQ L.kernelAction L.boundaryRange_le_kernelAction

@[simp]
theorem homologyAction_mk (x : Vzero) :
    L.homologyAction (Submodule.Quotient.mk x) = L.kernelAction x :=
  rfl

/-- The ternary correction vanishes on the homotopy kernel, leaving the representation law. -/
theorem kernelAction_commutator (x y : Vzero) (k : L.homotopyKernel) :
    L.kernelActionAt x (L.kernelActionAt y k) -
        L.kernelActionAt y (L.kernelActionAt x k) =
      L.kernelActionAt (L.μ₂₀₀ x y) k := by
  apply Subtype.ext
  have h := L.representation_defect x y (k : Vneg)
  rw [k.property, L.μ₃_zero_right] at h
  change L.μ₂₀₁ x (L.μ₂₀₁ y k) - L.μ₂₀₁ y (L.μ₂₀₁ x k) =
    L.μ₂₀₁ (L.μ₂₀₀ x y) k
  exact sub_eq_zero.mp h

/-- Binary bracket followed by projection to degree-zero homology. -/
def bracketToHomology : Vzero →ₗ[ℝ] Vzero →ₗ[ℝ] L.homologyZero where
  toFun x := (LinearMap.range L.μ₁).mkQ.comp (L.μ₂₀₀ x)
  map_add' x y := by ext z; simp
  map_smul' c x := by ext z; simp

/-- A boundary in the left input maps to zero in degree-zero homology. -/
theorem boundary_le_bracketToHomology_ker :
    LinearMap.range L.μ₁ ≤ LinearMap.ker L.bracketToHomology := by
  rintro _ ⟨v, rfl⟩
  rw [LinearMap.mem_ker]
  ext x
  rw [LinearMap.zero_apply]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨-L.μ₂₀₁ x v, ?_⟩
  calc
    L.μ₁ (-L.μ₂₀₁ x v) = -L.μ₂₀₀ x (L.μ₁ v) := by
      rw [map_neg, L.differential_action]
    _ = L.μ₂₀₀ (L.μ₁ v) x := (L.μ₂₀₀_skew (L.μ₁ v) x).symm

/-- A boundary in the right input maps to zero in degree-zero homology. -/
theorem boundary_le_flipped_bracketToHomology_ker :
    LinearMap.range L.μ₁ ≤ LinearMap.ker L.bracketToHomology.flip := by
  rintro _ ⟨v, rfl⟩
  rw [LinearMap.mem_ker]
  ext x
  rw [LinearMap.zero_apply]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨L.μ₂₀₁ x v, L.differential_action x v⟩

/-- Binary operation induced on degree-zero homology. -/
def homologyBracket : L.homologyZero →ₗ[ℝ] L.homologyZero →ₗ[ℝ] L.homologyZero :=
  L.bracketToHomology.liftQ₂ (LinearMap.range L.μ₁) (LinearMap.range L.μ₁)
    L.boundary_le_bracketToHomology_ker L.boundary_le_flipped_bracketToHomology_ker

@[simp]
theorem homologyBracket_mk (x y : Vzero) :
    L.homologyBracket (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (L.μ₂₀₀ x y) :=
  rfl

/-- The quotient bracket satisfies Jacobi on all representative classes; every quotient class has
such a representative. -/
theorem homologyBracket_jacobi_mk (x y z : Vzero) :
    L.homologyBracket (Submodule.Quotient.mk x)
          (L.homologyBracket (Submodule.Quotient.mk y) (Submodule.Quotient.mk z)) +
        L.homologyBracket (Submodule.Quotient.mk y)
          (L.homologyBracket (Submodule.Quotient.mk z) (Submodule.Quotient.mk x)) +
        L.homologyBracket (Submodule.Quotient.mk z)
          (L.homologyBracket (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)) = 0 := by
  rw [L.homologyBracket_mk, L.homologyBracket_mk, L.homologyBracket_mk,
    L.homologyBracket_mk, L.homologyBracket_mk, L.homologyBracket_mk]
  change
    (LinearMap.range L.μ₁).mkQ (L.μ₂₀₀ x (L.μ₂₀₀ y z)) +
        (LinearMap.range L.μ₁).mkQ (L.μ₂₀₀ y (L.μ₂₀₀ z x)) +
        (LinearMap.range L.μ₁).mkQ (L.μ₂₀₀ z (L.μ₂₀₀ x y)) = 0
  have hj := congrArg (LinearMap.range L.μ₁).mkQ (L.jacobiator x y z)
  simp only [map_add] at hj
  rw [hj]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨L.μ₃ x y z, rfl⟩

end TwoTermLInfinity

/-- Form-level semistrict curvature calculus.  The two Bianchi component equations are retained
before fake-flat specialization, so kernel-valuedness and closure are derived below. -/
structure SemistrictCurvatureCalculus
    (A₁ B₂ F₂ F₃ H₃ H₄ K₀ K₂ : Type*)
    [AddCommGroup A₁] [AddCommGroup B₂] [AddCommGroup F₂] [AddCommGroup F₃]
    [AddCommGroup H₃] [AddCommGroup H₄] [AddCommGroup K₀] [AddCommGroup K₂]
    [Module ℝ A₁] [Module ℝ B₂] [Module ℝ F₂] [Module ℝ F₃]
    [Module ℝ H₃] [Module ℝ H₄] [Module ℝ K₀] [Module ℝ K₂] where
  ordinaryCurvature : A₁ → F₂
  boundary₂ : B₂ →ₗ[ℝ] F₂
  threeCurvature : A₁ → B₂ → H₃
  boundary₃ : H₃ →ₗ[ℝ] F₃
  boundaryBianchi : F₂ →ₗ[ℝ] F₃
  covariantH₃ : A₁ → H₃ → H₄
  covariantBianchi : A₁ → F₂ →ₗ[ℝ] H₄
  connectionSquare : A₁ → K₀ → K₂
  curvatureAction : F₂ →ₗ[ℝ] K₀ →ₗ[ℝ] K₂
  connectionSquare_eq : ∀ A k,
    connectionSquare A k = curvatureAction (ordinaryCurvature A) k
  boundaryAction_zero : ∀ B k, curvatureAction (boundary₂ B) k = 0
  boundary_threeCurvature : ∀ A B,
    boundary₃ (threeCurvature A B) = boundaryBianchi (ordinaryCurvature A - boundary₂ B)
  covariant_threeCurvature : ∀ A B,
    covariantH₃ A (threeCurvature A B) =
      covariantBianchi A (ordinaryCurvature A - boundary₂ B)

namespace SemistrictCurvatureCalculus

variable {A₁ B₂ F₂ F₃ H₃ H₄ K₀ K₂ : Type*}
variable [AddCommGroup A₁] [AddCommGroup B₂] [AddCommGroup F₂] [AddCommGroup F₃]
variable [AddCommGroup H₃] [AddCommGroup H₄] [AddCommGroup K₀] [AddCommGroup K₂]
variable [Module ℝ A₁] [Module ℝ B₂] [Module ℝ F₂] [Module ℝ F₃]
variable [Module ℝ H₃] [Module ℝ H₄] [Module ℝ K₀] [Module ℝ K₂]
variable (D : SemistrictCurvatureCalculus A₁ B₂ F₂ F₃ H₃ H₄ K₀ K₂)

/-- Fake-flat semistrict two-connection. -/
structure FakeFlatConnection where
  A : A₁
  B : B₂
  fakeFlat : D.ordinaryCurvature A - D.boundary₂ B = 0

/-- Fake flatness makes the homotopy-kernel connection flat. -/
theorem kernel_connectionSquare_eq_zero (C : D.FakeFlatConnection) (k : K₀) :
    D.connectionSquare C.A k = 0 := by
  rw [D.connectionSquare_eq]
  have hcurvature : D.ordinaryCurvature C.A = D.boundary₂ C.B :=
    sub_eq_zero.mp C.fakeFlat
  rw [hcurvature, D.boundaryAction_zero]

/-- Semistrict three-curvature is homotopy-kernel-valued under fake flatness. -/
theorem threeCurvature_mem_kernel (C : D.FakeFlatConnection) :
    D.threeCurvature C.A C.B ∈ LinearMap.ker D.boundary₃ := by
  rw [LinearMap.mem_ker, D.boundary_threeCurvature, C.fakeFlat, map_zero]

/-- The homotopy-kernel-valued three-curvature is covariantly closed. -/
theorem threeCurvature_covariantly_closed (C : D.FakeFlatConnection) :
    D.covariantH₃ C.A (D.threeCurvature C.A C.B) = 0 := by
  rw [D.covariant_threeCurvature, C.fakeFlat, map_zero]

/-- Complete semistrict kernel reduction, including flatness and the two Bianchi consequences. -/
theorem fakeFlat_kernel_reduction (C : D.FakeFlatConnection) :
    (∀ k : K₀, D.connectionSquare C.A k = 0) ∧
      D.threeCurvature C.A C.B ∈ LinearMap.ker D.boundary₃ ∧
      D.covariantH₃ C.A (D.threeCurvature C.A C.B) = 0 :=
  ⟨D.kernel_connectionSquare_eq_zero C, D.threeCurvature_mem_kernel C,
    D.threeCurvature_covariantly_closed C⟩

end SemistrictCurvatureCalculus

section HigherPeriods

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Transported semistrict ternary curvature generates the lifted period algebra. -/
theorem semistrict_higher_ambroseSinger {ι σ : Type*}
    (P : PeriodGeometry (V := V) ι σ) (_harity : P.arity = 3) :
    P.restrictedAlgebra = Submodule.span ℝ (Set.range P.curvatureValue) :=
  P.higher_ambroseSinger

/-- Analytic covariant jets generate the same semistrict lifted period algebra. -/
theorem semistrict_higher_ambroseSinger_spencer {ι σ κ : Type*}
    (A : AnalyticSpencerGeometry (V := V) ι σ κ) (_harity : A.arity = 3) :
    A.toPeriodGeometry.restrictedAlgebra = A.jetSpan :=
  A.higher_ambroseSinger_spencer

end HigherPeriods

end HTGeometry.NomologicalHomotopyGeometry.SemistrictTwoTermKernelPeriod
