import GaloisForLFunctions.RHTower.SuzukiTaHilbertSpace

/-!
# Linear smooth core of Suzuki's energy space

The literal `C_c^∞(-a,a)` core is realized by mathlib's test-function space. This supplies its
native complex vector-space structure and continuous derivative, then proves that the canonical
CCM form realization is linear, injective, and dense in Suzuki's actual energy Hilbert space.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Open interval underlying Suzuki's literal smooth core. -/
def suzukiTaOpenInterval (a : SuzukiPositiveAperture) : TopologicalSpace.Opens ℝ :=
  ⟨Ioo (-a.1) a.1, isOpen_Ioo⟩

/-- Literal complex `C_c^∞(-a,a)` with its native locally convex vector-space structure. -/
abbrev SuzukiTaSmoothCore (a : SuzukiPositiveAperture) :=
  TestFunction (suzukiTaOpenInterval a) ℂ (⊤ : ℕ∞)

/-- Forget the native test-function topology while retaining the exact source data used by CCM. -/
def suzukiTaSmoothCoreToSource (a : SuzukiPositiveAperture) (u : SuzukiTaSmoothCore a) :
    CCMComplexSmoothInteriorSource a where
  toFun := u
  smooth := u.contDiff
  hasCompactSupport := u.hasCompactSupport
  tsupport_subset := u.tsupport_subset

/-- Equip an existing Suzuki smooth source with mathlib's native test-function structure. -/
def ccmComplexSmoothInteriorSourceToSuzukiTaSmoothCore
    (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a) :
    SuzukiTaSmoothCore a where
  toFun := u
  contDiff' := u.smooth
  hasCompactSupport' := u.hasCompactSupport
  tsupport_subset' := u.tsupport_subset

@[simp] theorem suzukiTaSmoothCoreToSource_apply
    {a : SuzukiPositiveAperture} (u : SuzukiTaSmoothCore a) (x : ℝ) :
    suzukiTaSmoothCoreToSource a u x = u x := rfl

@[simp] theorem ccmComplexSmoothInteriorSourceToSuzukiTaSmoothCore_apply
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) (x : ℝ) :
    ccmComplexSmoothInteriorSourceToSuzukiTaSmoothCore a u x = u x := rfl

/-- Pre-existing bundled source and native `C_c^∞` core are exactly equivalent. -/
def suzukiTaSmoothCoreEquivSource (a : SuzukiPositiveAperture) :
    SuzukiTaSmoothCore a ≃ CCMComplexSmoothInteriorSource a where
  toFun := suzukiTaSmoothCoreToSource a
  invFun := ccmComplexSmoothInteriorSourceToSuzukiTaSmoothCore a
  left_inv u := by cases u; rfl
  right_inv u := by cases u; rfl

/-- Canonical CCM form vector attached to a native smooth core vector. -/
def suzukiTaSmoothCoreToCCMFormVector
    (a : SuzukiPositiveAperture) (u : SuzukiTaSmoothCore a) :
    CCMArchimedeanFormDomain a :=
  (suzukiTaSmoothCoreToSource a u).toCCMFormVector

theorem suzukiTaSmoothCoreToCCMFormVector_add
    (a : SuzukiPositiveAperture) (u v : SuzukiTaSmoothCore a) :
    suzukiTaSmoothCoreToCCMFormVector a (u + v) =
      suzukiTaSmoothCoreToCCMFormVector a u + suzukiTaSmoothCoreToCCMFormVector a v := by
  change (suzukiTaSmoothCoreToSource a (u + v)).toCCMFormVector =
    (suzukiTaSmoothCoreToSource a u).toCCMFormVector +
      (suzukiTaSmoothCoreToSource a v).toCCMFormVector
  apply ccmArchimedeanFormToAperture_injective a
  rw [map_add]
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [
    (suzukiTaSmoothCoreToSource a (u + v)).toCCMFormVector_physical_coeFn,
    (suzukiTaSmoothCoreToSource a u).toCCMFormVector_physical_coeFn,
    (suzukiTaSmoothCoreToSource a v).toCCMFormVector_physical_coeFn,
    Lp.coeFn_add
      (ccmArchimedeanFormToAperture a
        (suzukiTaSmoothCoreToSource a u).toCCMFormVector : SoninL2)
      (ccmArchimedeanFormToAperture a
        (suzukiTaSmoothCoreToSource a v).toCCMFormVector : SoninL2)]
      with x huv hu hv hadd
  rw [huv]
  change (suzukiTaSmoothCoreToSource a (u + v)).toFun x =
    (((ccmArchimedeanFormToAperture a
          (suzukiTaSmoothCoreToSource a u).toCCMFormVector : suzukiApertureHilbert a) : SoninL2) +
      ((ccmArchimedeanFormToAperture a
          (suzukiTaSmoothCoreToSource a v).toCCMFormVector : suzukiApertureHilbert a) : SoninL2)) x
  rw [hadd, Pi.add_apply, hu, hv]
  rfl

theorem suzukiTaSmoothCoreToCCMFormVector_smul
    (a : SuzukiPositiveAperture) (c : ℂ) (u : SuzukiTaSmoothCore a) :
    suzukiTaSmoothCoreToCCMFormVector a (c • u) =
      c • suzukiTaSmoothCoreToCCMFormVector a u := by
  change (suzukiTaSmoothCoreToSource a (c • u)).toCCMFormVector =
    c • (suzukiTaSmoothCoreToSource a u).toCCMFormVector
  apply ccmArchimedeanFormToAperture_injective a
  rw [map_smul]
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [
    (suzukiTaSmoothCoreToSource a (c • u)).toCCMFormVector_physical_coeFn,
    (suzukiTaSmoothCoreToSource a u).toCCMFormVector_physical_coeFn,
    Lp.coeFn_smul c
      (ccmArchimedeanFormToAperture a
        (suzukiTaSmoothCoreToSource a u).toCCMFormVector : SoninL2)]
      with x hcu hu hsmul
  rw [hcu]
  change (suzukiTaSmoothCoreToSource a (c • u)).toFun x =
    (c • ((ccmArchimedeanFormToAperture a
      (suzukiTaSmoothCoreToSource a u).toCCMFormVector : suzukiApertureHilbert a) : SoninL2)) x
  rw [hsmul, Pi.smul_apply, hu]
  rfl

/-- Linear canonical realization of `C_c^∞(-a,a)` in the closed CCM form domain. -/
def suzukiTaSmoothCoreToForm (a : SuzukiPositiveAperture) :
    SuzukiTaSmoothCore a →ₗ[ℂ] CCMArchimedeanFormDomain a where
  toFun := suzukiTaSmoothCoreToCCMFormVector a
  map_add' := suzukiTaSmoothCoreToCCMFormVector_add a
  map_smul' := suzukiTaSmoothCoreToCCMFormVector_smul a

theorem suzukiTaSmoothCoreToForm_injective (a : SuzukiPositiveAperture) :
    Function.Injective (suzukiTaSmoothCoreToForm a) := by
  intro u v huv
  apply DFunLike.coe_injective
  have hu := (suzukiTaSmoothCoreToSource a u).toCCMFormVector_physical_coeFn
  rw [show (suzukiTaSmoothCoreToSource a u).toCCMFormVector =
      (suzukiTaSmoothCoreToSource a v).toCCMFormVector from huv] at hu
  have hae : (u : ℝ → ℂ) =ᵐ[volume] v :=
    hu.symm.trans (suzukiTaSmoothCoreToSource a v).toCCMFormVector_physical_coeFn
  exact (Continuous.ae_eq_iff_eq (volume : Measure ℝ)
    u.contDiff.continuous v.contDiff.continuous).mp hae

/-- Linear injection of literal smooth core into Suzuki's energy Hilbert space. -/
def suzukiTaSmoothCoreToHilbert (a : SuzukiPositiveAperture) :
    SuzukiTaSmoothCore a →ₗ[ℂ] SuzukiTaHilbert a :=
  (suzukiTaFromFormCLM a).toLinearMap.comp (suzukiTaSmoothCoreToForm a)

theorem suzukiTaSmoothCoreToHilbert_injective (a : SuzukiPositiveAperture) :
    Function.Injective (suzukiTaSmoothCoreToHilbert a) :=
  (suzukiTaToFormLinearEquiv a).symm.injective.comp
    (suzukiTaSmoothCoreToForm_injective a)

theorem denseRange_suzukiTaSmoothCoreToHilbert (a : SuzukiPositiveAperture) :
    DenseRange (suzukiTaSmoothCoreToHilbert a) := by
  apply (denseRange_ccmComplexSmoothInteriorSource_toSuzukiTa a).mono
  rintro y ⟨u, rfl⟩
  refine ⟨(suzukiTaSmoothCoreEquivSource a).symm u, ?_⟩
  change suzukiTaFromFormCLM a
      ((suzukiTaSmoothCoreEquivSource a
        ((suzukiTaSmoothCoreEquivSource a).symm u)).toCCMFormVector) = _
  rw [(suzukiTaSmoothCoreEquivSource a).apply_symm_apply]

/-- Native complex-linear `i d/dx` on literal smooth core. -/
def suzukiTaSmoothCoreIDeriv (a : SuzukiPositiveAperture) :
    SuzukiTaSmoothCore a →ₗ[ℂ] SuzukiTaSmoothCore a :=
  I • (TestFunction.lineDerivCLM ℂ (1 : ℝ) :
    SuzukiTaSmoothCore a →L[ℂ] SuzukiTaSmoothCore a).toLinearMap

@[simp] theorem suzukiTaSmoothCoreIDeriv_apply
    (a : SuzukiPositiveAperture) (u : SuzukiTaSmoothCore a) (x : ℝ) :
    suzukiTaSmoothCoreIDeriv a u x = I * deriv u x := by
  change I * (TestFunction.lineDerivCLM ℂ (1 : ℝ) u : SuzukiTaSmoothCore a) x = _
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
  rw [(u.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
  rfl

end RHTower
