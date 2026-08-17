import GaloisForLFunctions.HTGeometry.ConstitutiveUnitaryJordanFormationFracture
import GaloisForLFunctions.HTGeometry.ConstitutiveFormationDepthProperness
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Universal unitary formation radical

Finite generalized fixed histories carry exact unipotent formation depth.  Every linear reporter
intertwining formation with a Hilbert-space isometry kills their displacements.  Those forced-zero
directions form a canonical submodule, and every such reporter factors uniquely through its
quotient.  A cofinal tower of finite-depth primitives therefore extinguishes every boundary it
generates; if those boundaries span, the reporter is zero.
-/

namespace GaloisForLFunctions.HTGeometry

open Module
open scoped BigOperators
open Complex

variable {V H : Type*} [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Linear displacement of a formation automorphism. -/
def linearFormationDisplacement (T : V ≃ₗ[ℝ] V) : Module.End ℝ V :=
  T.toLinearMap - 1

/-- Finite generalized fixed histories of a formation automorphism. -/
def finiteUnipotentFormationSubmodule (T : V ≃ₗ[ℝ] V) : Submodule ℝ V :=
  Module.End.genEigenspace T.toLinearMap 1 ⊤

/-- Displacements of finite generalized fixed histories. -/
def unitaryFormationRadical (T : V ≃ₗ[ℝ] V) : Submodule ℝ V :=
  Submodule.map (linearFormationDisplacement T) (finiteUnipotentFormationSubmodule T)

lemma reporter_intertwines_linearFormationDisplacement
    (T : V ≃ₗ[ℝ] V) (r : V →ₗ[ℝ] H) (U : H ≃ₗᵢ[ℝ] H)
    (hintertwine : ∀ v, r (T v) = U (r v)) (v : V) :
    r (linearFormationDisplacement T v) = U (r v) - r v := by
  simp [linearFormationDisplacement, hintertwine]

lemma reporter_intertwines_displacement_power
    (T : V ≃ₗ[ℝ] V) (r : V →ₗ[ℝ] H) (U : H ≃ₗᵢ[ℝ] H)
    (hintertwine : ∀ v, r (T v) = U (r v)) :
    ∀ (n : ℕ) (v : V),
      r ((linearFormationDisplacement T ^ n) v) =
        iteratedIsometricDisplacement U n (r v) := by
  intro n
  induction n with
  | zero =>
      intro v
      simp [iteratedIsometricDisplacement]
  | succ n ih =>
      intro v
      rw [pow_succ]
      change r ((linearFormationDisplacement T ^ n)
        (linearFormationDisplacement T v)) = _
      rw [ih]
      simp only [iteratedIsometricDisplacement]
      rw [reporter_intertwines_linearFormationDisplacement T r U hintertwine]

lemma finiteUnipotentFormationSubmodule_le_reporterDisplacement_ker
    (T : V ≃ₗ[ℝ] V) (r : V →ₗ[ℝ] H) (U : H ≃ₗᵢ[ℝ] H)
    (hintertwine : ∀ v, r (T v) = U (r v)) :
    finiteUnipotentFormationSubmodule T ≤
      (r.comp (linearFormationDisplacement T)).ker := by
  intro v hv
  rw [finiteUnipotentFormationSubmodule, Module.End.mem_genEigenspace_top] at hv
  obtain ⟨n, hn⟩ := hv
  rw [LinearMap.mem_ker] at hn ⊢
  cases n with
  | zero =>
      simp at hn
      subst v
      simp
  | succ n =>
      have hn' : (linearFormationDisplacement T ^ (n + 1)) v = 0 := by
        simpa [linearFormationDisplacement] using hn
      have hzero : iteratedIsometricDisplacement U (n + 1) (r v) = 0 := by
        rw [← reporter_intertwines_displacement_power T r U hintertwine]
        rw [hn', map_zero]
      have hfixed :=
        linearIsometryEquiv_fixed_of_iterated_displacement_eq_zero U (r v) n hzero
      change r (linearFormationDisplacement T v) = 0
      rw [reporter_intertwines_linearFormationDisplacement T r U hintertwine, hfixed, sub_self]

/-- Every equivariant unitary reporter kills the universal finite-formation radical. -/
theorem unitaryFormationRadical_le_reporter_ker
    (T : V ≃ₗ[ℝ] V) (r : V →ₗ[ℝ] H) (U : H ≃ₗᵢ[ℝ] H)
    (hintertwine : ∀ v, r (T v) = U (r v)) :
    unitaryFormationRadical T ≤ r.ker := by
  rintro y ⟨v, hv, rfl⟩
  rw [LinearMap.mem_ker]
  exact finiteUnipotentFormationSubmodule_le_reporterDisplacement_ker
    T r U hintertwine hv

/-- Canonical factor of an equivariant unitary reporter through formation semisimplification. -/
def unitaryReporterSemisimpleFactor
    (T : V ≃ₗ[ℝ] V) (r : V →ₗ[ℝ] H) (U : H ≃ₗᵢ[ℝ] H)
    (hintertwine : ∀ v, r (T v) = U (r v)) :
    V ⧸ unitaryFormationRadical T →ₗ[ℝ] H :=
  Submodule.liftQ (unitaryFormationRadical T) r
    (unitaryFormationRadical_le_reporter_ker T r U hintertwine)

@[simp] theorem unitaryReporterSemisimpleFactor_mk
    (T : V ≃ₗ[ℝ] V) (r : V →ₗ[ℝ] H) (U : H ≃ₗᵢ[ℝ] H)
    (hintertwine : ∀ v, r (T v) = U (r v)) (v : V) :
    unitaryReporterSemisimpleFactor T r U hintertwine
        (Submodule.Quotient.mk v) = r v := by
  exact Submodule.liftQ_apply _ _ _

/-- The semisimple factor is the unique linear factor through the radical quotient. -/
theorem unitaryReporterSemisimpleFactor_unique
    (T : V ≃ₗ[ℝ] V) (r : V →ₗ[ℝ] H) (U : H ≃ₗᵢ[ℝ] H)
    (hintertwine : ∀ v, r (T v) = U (r v))
    (s : V ⧸ unitaryFormationRadical T →ₗ[ℝ] H)
    (hs : s.comp (Submodule.mkQ (unitaryFormationRadical T)) = r) :
    s = unitaryReporterSemisimpleFactor T r U hintertwine := by
  apply LinearMap.ext
  intro q
  refine Submodule.Quotient.induction_on (unitaryFormationRadical T) q ?_
  intro v
  rw [unitaryReporterSemisimpleFactor_mk]
  have hv := LinearMap.congr_fun hs v
  simpa [Submodule.mkQ_apply] using hv

/-- A finite-depth primitive is invisible to every equivariant unitary reporter. -/
theorem unitaryReporter_kills_finiteFormationBoundary
    (T : V ≃ₗ[ℝ] V) (r : V →ₗ[ℝ] H) (U : H ≃ₗᵢ[ℝ] H)
    (hintertwine : ∀ v, r (T v) = U (r v))
    (v : V) (hv : v ∈ finiteUnipotentFormationSubmodule T) :
    r (linearFormationDisplacement T v) = 0 := by
  exact finiteUnipotentFormationSubmodule_le_reporterDisplacement_ker
    T r U hintertwine hv

/-- Cofinal primitive extinction: every boundary with a finite-depth primitive is erased. -/
theorem unitaryReporter_kills_cofinalPrimitiveHistory
    (T : V ≃ₗ[ℝ] V) (r : V →ₗ[ℝ] H) (U : H ≃ₗᵢ[ℝ] H)
    (hintertwine : ∀ v, r (T v) = U (r v))
    (boundary primitive : ℕ → V)
    (hprimitive : ∀ n, linearFormationDisplacement T (primitive n) = boundary n)
    (hfinite : ∀ n, primitive n ∈ finiteUnipotentFormationSubmodule T) :
    ∀ n, r (boundary n) = 0 := by
  intro n
  rw [← hprimitive n]
  exact unitaryReporter_kills_finiteFormationBoundary T r U hintertwine _ (hfinite n)

/-- If cofinal boundaries span the source, every equivariant unitary reporter is zero. -/
theorem unitaryReporter_eq_zero_of_cofinalPrimitive_spans
    (T : V ≃ₗ[ℝ] V) (r : V →ₗ[ℝ] H) (U : H ≃ₗᵢ[ℝ] H)
    (hintertwine : ∀ v, r (T v) = U (r v))
    (boundary primitive : ℕ → V)
    (hprimitive : ∀ n, linearFormationDisplacement T (primitive n) = boundary n)
    (hfinite : ∀ n, primitive n ∈ finiteUnipotentFormationSubmodule T)
    (hspan : Submodule.span ℝ (Set.range boundary) = ⊤) :
    r = 0 := by
  have hboundary : Set.range boundary ⊆ r.ker := by
    rintro _ ⟨n, rfl⟩
    change r (boundary n) = 0
    exact unitaryReporter_kills_cofinalPrimitiveHistory T r U hintertwine
      boundary primitive hprimitive hfinite n
  have htop : (⊤ : Submodule ℝ V) ≤ r.ker := by
    rw [← hspan]
    exact Submodule.span_le.mpr hboundary
  apply LinearMap.ext
  intro v
  have hv : v ∈ r.ker := htop Submodule.mem_top
  rw [LinearMap.mem_ker] at hv
  simpa using hv

noncomputable section

/-- Unit source boundary concentrated at formation depth `N`. -/
def formationHorizon (N : ℕ) : ℕ → ℂ :=
  fun n => if n = N then 1 else 0

lemma summable_formationHorizon (N : ℕ) : Summable (formationHorizon N) := by
  exact (hasSum_ite_eq N (1 : ℂ)).summable

lemma formationMass_formationHorizon (N : ℕ) :
    formationMass (formationHorizon N) = 1 := by
  simp [formationMass, formationHorizon]

lemma formationDepthWork_formationHorizon (N : ℕ) :
    formationDepthWork (formationHorizon N) = N := by
  simp only [formationDepthWork, formationDepthSequence, formationHorizon,
    mul_ite, mul_one, mul_zero]
  rw [tsum_eq_single N]
  · simp
  · intro n hn
    simp [hn]

/-- A normalized horizon escaping to depth `N` has exactly affine source cost `1 + 2N`. -/
theorem formationGauge_formationHorizon (N : ℕ) :
    formationGauge (formationHorizon N) = 1 + 2 * N := by
  rw [formationGauge, formationMass_formationHorizon, formationDepthWork_formationHorizon]
  simp

end

end GaloisForLFunctions.HTGeometry
