import GaloisForLFunctions.RHTower.DeningerTestIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# The test space inside `L²`, and the dual injection

A test function is continuous with compact support, hence square integrable, and the resulting map
of the test space into `L²` is injective as soon as the measure charges every nonempty open set:
two continuous functions agreeing almost everywhere for such a measure are equal.

Every linear map out of a space carrying its finest locally convex topology is continuous, so the
embedding is continuous with no hypothesis, and the transpose of any continuous linear map with
dense range is injective — the dual of the larger space injects into the dual of the smaller one.
Those two facts are the abstract content of a test/Hilbert scale and of the dual scale it induces.

* `deningerFinest_map_bounded` : every linear map out of a finest topology space is continuous.
* `deningerTestToL2`, `_injective` : the test space inside `L²`.
* `deningerDual_injective_of_denseRange` : the transpose of a dense range map is injective.
-/

namespace RHTower

open MeasureTheory

section FinestMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **Every linear map into a normed space is continuous for the finest locally convex
topology**: the seminorm `‖T ·‖` is one of the defining seminorms and bounds it. -/
theorem deningerFinest_map_bounded {N : Type*} [SeminormedAddCommGroup N] [NormedSpace 𝕜 N]
    (T : E →ₗ[𝕜] N) : ∃ p : Seminorm 𝕜 E, ∀ x, ‖T x‖ ≤ 1 * p x :=
  ⟨(normSeminorm 𝕜 N).comp T, fun x => by rw [one_mul]; exact le_rfl⟩

end FinestMap

section DualInjection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- **The transpose of a map with dense range is injective**: two continuous functionals agreeing
on a dense subspace agree. -/
theorem deningerDual_injective_of_denseRange {E F : Type*}
    [TopologicalSpace F] [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]
    {T : E →ₗ[𝕜] F} (hT : DenseRange T) {φ ψ : F →ₗ[𝕜] 𝕜} (hφ : Continuous φ)
    (hψ : Continuous ψ) (h : φ.comp T = ψ.comp T) : φ = ψ := by
  refine DFunLike.coe_injective (hT.equalizer hφ hψ ?_)
  funext x
  exact LinearMap.congr_fun h x

end DualInjection

section TestL2

variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
variable (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]

/-- **A test function is square integrable.** -/
theorem deningerTestSpace_memLp (g : DeningerTestSpace Y) : MemLp (g : Y → ℝ) 2 μ :=
  (g.2.1.continuous).memLp_of_hasCompactSupport
    (deningerTestSpace_hasCompactSupport g.2.1 g.2.2)

/-- **The test space inside `L²`.** -/
noncomputable def deningerTestToL2 : DeningerTestSpace Y →ₗ[ℝ] Lp ℝ 2 μ where
  toFun g := (deningerTestSpace_memLp μ g).toLp _
  map_add' _ _ := MemLp.toLp_add _ _
  map_smul' c _ := MemLp.toLp_const_smul c _

theorem deningerTestToL2_coeFn (g : DeningerTestSpace Y) :
    deningerTestToL2 μ g =ᵐ[μ] (g : Y → ℝ) :=
  MemLp.coeFn_toLp (deningerTestSpace_memLp μ g)

/-- **The test space embeds into `L²`** for a measure charging every nonempty open set: a
continuous function vanishing almost everywhere then vanishes. -/
theorem deningerTestToL2_injective [μ.IsOpenPosMeasure] :
    Function.Injective (deningerTestToL2 μ) := by
  intro g h hgh
  refine Subtype.ext ?_
  have hae : (g : Y → ℝ) =ᵐ[μ] (h : Y → ℝ) :=
    ((deningerTestToL2_coeFn μ g).symm.trans (by rw [hgh])).trans
      (deningerTestToL2_coeFn μ h)
  exact (Continuous.ae_eq_iff_eq μ g.2.1.continuous h.2.1.continuous).mp hae

/-- **The embedding into `L²` is continuous** for the finest locally convex topology of the test
space. -/
theorem deningerTestToL2_bounded :
    ∃ p : Seminorm ℝ (DeningerTestSpace Y), ∀ g, ‖deningerTestToL2 μ g‖ ≤ 1 * p g :=
  deningerFinest_map_bounded _

end TestL2

end RHTower
