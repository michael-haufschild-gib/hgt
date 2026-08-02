import GaloisForLFunctions.RHTower.DeningerTestSigma

/-!
# Operators on the test space: pullback, averaging, and the integral

The pullback of a locally constant function along a continuous map is locally constant, and its
support is the preimage of the support, so a proper map pulls test functions back to test
functions.  Pullback along a proper map is therefore an operator on the test space, automatically
continuous since every linear map is continuous for the finest locally convex topology.

Averaging the pullbacks along a finite family of proper maps — the Galois average and the
normalized field-norm projection are of this shape — is again such an operator, and if the maps
preserve the measure then the integral of a test function is unchanged, so the operators preserve
the subspace of test functions of total mass zero.

* `deningerTestPullback`, `_apply`, `_bounded` : pullback along a proper map.
* `deningerTestAverage` : a weighted average of pullbacks.
* `deningerTestIntegral_pullback` : the integral is invariant under a measure preserving proper
  map, so its kernel is preserved.
-/

namespace RHTower

open MeasureTheory

section Pullback

variable {Y Y' : Type*} [TopologicalSpace Y] [TopologicalSpace Y']

/-- The pullback of a test function along a proper map is a test function. -/
theorem deningerTestPullback_mem {f : Y → Y'} (hf : IsProperMap f) {g : Y' → ℝ}
    (hg : g ∈ DeningerTestSpace Y') : (g ∘ f) ∈ DeningerTestSpace Y := by
  refine ⟨hg.1.comp_continuous hf.continuous, ?_⟩
  have hsupp : Function.support (g ∘ f) = f ⁻¹' Function.support g := by
    ext y
    simp [Function.mem_support]
  rw [hsupp]
  exact hf.isCompact_preimage hg.2

/-- **Pullback along a proper map**, as an operator of test spaces. -/
noncomputable def deningerTestPullback {f : Y → Y'} (hf : IsProperMap f) :
    DeningerTestSpace Y' →ₗ[ℝ] DeningerTestSpace Y where
  toFun g := ⟨(g : Y' → ℝ) ∘ f, deningerTestPullback_mem hf g.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem deningerTestPullback_apply {f : Y → Y'} (hf : IsProperMap f)
    (g : DeningerTestSpace Y') (y : Y) :
    ((deningerTestPullback hf g : DeningerTestSpace Y) : Y → ℝ) y
      = (g : Y' → ℝ) (f y) := rfl

/-- **Pullback is continuous** for the finest locally convex topologies, as is every linear map. -/
theorem deningerTestPullback_bounded {f : Y → Y'} (hf : IsProperMap f)
    (p : Seminorm ℝ (DeningerTestSpace Y)) :
    ∃ q : Seminorm ℝ (DeningerTestSpace Y'), ∀ g, p (deningerTestPullback hf g) ≤ 1 * q g :=
  ⟨p.comp (deningerTestPullback hf), fun g => by rw [one_mul]; exact le_rfl⟩

/-- **A weighted average of pullbacks**, the shape of a Galois average or of a normalized
field-norm projection. -/
noncomputable def deningerTestAverage {κ : Type*} (s : Finset κ) (c : κ → ℝ) {f : κ → Y → Y}
    (hf : ∀ k, IsProperMap (f k)) : DeningerTestSpace Y →ₗ[ℝ] DeningerTestSpace Y :=
  ∑ k ∈ s, c k • deningerTestPullback (hf k)

theorem deningerTestAverage_apply {κ : Type*} (s : Finset κ) (c : κ → ℝ) {f : κ → Y → Y}
    (hf : ∀ k, IsProperMap (f k)) (g : DeningerTestSpace Y) (y : Y) :
    ((deningerTestAverage s c hf g : DeningerTestSpace Y) : Y → ℝ) y
      = ∑ k ∈ s, c k * (g : Y → ℝ) (f k y) := by
  have hval : (deningerTestAverage s c hf g : DeningerTestSpace Y)
      = ∑ k ∈ s, c k • deningerTestPullback (hf k) g := by
    show (∑ k ∈ s, c k • deningerTestPullback (hf k)) g = _
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => rfl
  rw [hval, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Submodule.coe_smul]
  simp

end Pullback

section IntegralInvariance

variable {Y Y' : Type*} [TopologicalSpace Y] [TopologicalSpace Y']
variable [MeasurableSpace Y] [OpensMeasurableSpace Y] [MeasurableSpace Y']
variable [OpensMeasurableSpace Y'] (μ : Measure Y) (ν : Measure Y')
variable [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]

/-- **The integral is invariant under pullback along a measure preserving proper map.** -/
theorem deningerTestIntegral_pullback {f : Y → Y'} (hf : IsProperMap f)
    (hmp : MeasurePreserving f μ ν) (hemb : MeasurableEmbedding f)
    (g : DeningerTestSpace Y') :
    deningerTestIntegral μ (deningerTestPullback hf g) = deningerTestIntegral ν g := by
  show ∫ y, ((deningerTestPullback hf g : DeningerTestSpace Y) : Y → ℝ) y ∂μ
    = ∫ y, (g : Y' → ℝ) y ∂ν
  have hcomp : ∫ y, (g : Y' → ℝ) (f y) ∂μ = ∫ y, (g : Y' → ℝ) y ∂ν :=
    hmp.integral_comp hemb _
  exact hcomp

/-- **Pullback along a measure preserving proper map preserves the test functions of total mass
zero.** -/
theorem deningerTestKernel_pullback {f : Y → Y'} (hf : IsProperMap f)
    (hmp : MeasurePreserving f μ ν) (hemb : MeasurableEmbedding f)
    {g : DeningerTestSpace Y'} (hg : g ∈ DeningerTestKernel ν) :
    deningerTestPullback hf g ∈ DeningerTestKernel μ := by
  have hzero : deningerTestIntegral ν g = 0 := hg
  show deningerTestIntegral μ (deningerTestPullback hf g) = 0
  rw [deningerTestIntegral_pullback μ ν hf hmp hemb g, hzero]

end IntegralInvariance

end RHTower
