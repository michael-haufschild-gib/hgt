import GaloisForLFunctions.RHTower.DeningerLocallyConstantTestSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The integral of a locally constant test function

A test function is continuous with compact support, so it is integrable against any measure which
is finite on compacts, and the integral is a linear functional on the test space.  For the finest
locally convex topology continuity of a linear functional is automatic — the seminorm `‖φ ·‖` is
itself a member of the defining family — so the integral is a continuous functional and its kernel
is a closed subspace, which is nuclear like every subspace of the test space.

* `deningerFinest_functional_bounded` : every linear functional is continuous for the finest
  locally convex topology.
* `deningerTestSpace_integrable`, `deningerTestIntegral` : the integral of a test function.
* `DeningerTestKernel`, `deningerTestKernel_isNuclearSpaceC` : the test functions of total mass
  zero form a nuclear subspace.
-/

namespace RHTower

open MeasureTheory

section FinestFunctional

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **Every linear functional is continuous for the finest locally convex topology**: the seminorm
`‖φ ·‖` is one of the defining seminorms and bounds it. -/
theorem deningerFinest_functional_bounded (φ : E →ₗ[𝕜] 𝕜) :
    ∃ p : Seminorm 𝕜 E, ∀ x, ‖φ x‖ ≤ 1 * p x :=
  ⟨(normSeminorm 𝕜 𝕜).comp φ, fun x => by rw [one_mul]; exact le_rfl⟩

end FinestFunctional

section TestIntegral

variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
variable (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]

omit [MeasurableSpace Y] [OpensMeasurableSpace Y] in
/-- The support of a locally constant function being closed, compact support in the sense of the
support and in the sense of its closure agree. -/
theorem deningerTestSpace_hasCompactSupport {f : Y → ℝ} (hf : IsLocallyConstant f)
    (hK : IsCompact (Function.support f)) : HasCompactSupport f := by
  rw [HasCompactSupport, tsupport, (deningerSupport_isClosed hf).closure_eq]
  exact hK

/-- **A test function is integrable** against any measure finite on compacts. -/
theorem deningerTestSpace_integrable (g : DeningerTestSpace Y) : Integrable (g : Y → ℝ) μ :=
  (g.2.1.continuous).integrable_of_hasCompactSupport
    (deningerTestSpace_hasCompactSupport g.2.1 g.2.2)

/-- **The integral of a test function**, as a linear functional on the test space. -/
noncomputable def deningerTestIntegral : DeningerTestSpace Y →ₗ[ℝ] ℝ where
  toFun g := ∫ y, (g : Y → ℝ) y ∂μ
  map_add' g h := integral_add (deningerTestSpace_integrable μ g) (deningerTestSpace_integrable μ h)
  map_smul' c _ := integral_smul c _

@[simp]
theorem deningerTestIntegral_apply (g : DeningerTestSpace Y) :
    deningerTestIntegral μ g = ∫ y, (g : Y → ℝ) y ∂μ := rfl

/-- **The integral is a continuous functional** on the test space with its finest locally convex
topology. -/
theorem deningerTestIntegral_bounded :
    ∃ p : Seminorm ℝ (DeningerTestSpace Y), ∀ g, ‖deningerTestIntegral μ g‖ ≤ 1 * p g :=
  deningerFinest_functional_bounded _

/-- **The test functions of total mass zero.** -/
noncomputable def DeningerTestKernel : Submodule ℝ (DeningerTestSpace Y) :=
  LinearMap.ker (deningerTestIntegral μ)

theorem deningerTestKernel_mem {g : DeningerTestSpace Y} :
    g ∈ DeningerTestKernel μ ↔ ∫ y, (g : Y → ℝ) y ∂μ = 0 := Iff.rfl

/-- **The kernel of the integral is a nuclear subspace of the test space.** -/
theorem deningerTestKernel_isNuclearSpaceC [T2Space Y] [SecondCountableTopology Y] :
    DeningerIsNuclearSpaceC (fun p : Seminorm ℝ (DeningerTestSpace Y) =>
      deningerRestrictSeminorm (DeningerTestKernel μ) p) :=
  deningerTestSubspace_isNuclearSpaceC _

/-- **A subspace of the kernel of the integral is nuclear and annihilated by the integral**, the
situation of a distinguished family of test functions of total mass zero. -/
theorem deningerTestIntegral_eq_zero_of_le_kernel [T2Space Y] [SecondCountableTopology Y]
    {F : Submodule ℝ (DeningerTestSpace Y)} (hF : F ≤ DeningerTestKernel μ)
    (g : DeningerTestSpace Y) (hg : g ∈ F) : deningerTestIntegral μ g = 0 := hF hg

end TestIntegral

end RHTower
