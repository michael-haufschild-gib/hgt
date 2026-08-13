import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The Cauchy transform of a functional on continuous functions on a plane compact

For a compact `K ⊆ ℂ`, the element `v - z` of the Banach algebra `C(K, ℂ)` is a unit exactly when
`v ∉ K`, and its inverse is the Cauchy kernel.  The Cauchy transform of a continuous functional `A`
is the scalar function `v ↦ A((v - z)⁻¹)`.  Inversion in a Banach algebra is differentiable at
units, so the transform is holomorphic off `K`, and outside a disc containing `K` the kernel is the
norm-convergent geometric series in the coordinate, so a functional killing every power of the
coordinate has vanishing transform there.

* `GaloisForLFunctions.HTGeometry.coordMap`, `GaloisForLFunctions.HTGeometry.cauchyTransform`;
* `GaloisForLFunctions.HTGeometry.differentiableOn_cauchyTransform`;
* `GaloisForLFunctions.HTGeometry.cauchyTransform_eq_zero_of_lt`;
* `GaloisForLFunctions.HTGeometry.norm_cauchyTransform_le`.
-/

noncomputable section

open Complex Set

namespace GaloisForLFunctions.HTGeometry

variable {K : Set ℂ} [CompactSpace K]

/-- The coordinate function of a compact subset of the plane. -/
def coordMap (K : Set ℂ) : C(K, ℂ) := ⟨fun z => (z : ℂ), continuous_subtype_val⟩

omit [CompactSpace K] in
@[simp] theorem coordMap_apply (z : K) : coordMap K z = (z : ℂ) := rfl

/-- The Cauchy kernel at a point off the compact set, as a continuous function on it. -/
def kernelFun (K : Set ℂ) {v : ℂ} (hv : v ∉ K) : C(K, ℂ) :=
  ⟨fun z => (v - (z : ℂ))⁻¹, by
    refine Continuous.inv₀ (by fun_prop) ?_
    intro z
    rw [sub_ne_zero]
    intro h
    exact hv (h ▸ z.2)⟩

omit [CompactSpace K] in
@[simp] theorem kernelFun_apply {v : ℂ} (hv : v ∉ K) (z : K) :
    kernelFun K hv z = (v - (z : ℂ))⁻¹ := rfl

/-- The resolvent of the coordinate at a point off the compact set. -/
def resolventElt (K : Set ℂ) (v : ℂ) : C(K, ℂ) := v • (1 : C(K, ℂ)) - coordMap K

omit [CompactSpace K] in
@[simp] theorem resolventElt_apply (v : ℂ) (z : K) :
    resolventElt K v z = v - (z : ℂ) := by
  simp [resolventElt, coordMap]

/-- The resolvent is a unit of the Banach algebra, with the Cauchy kernel as inverse. -/
def resolventUnit (K : Set ℂ) [CompactSpace K] {v : ℂ} (hv : v ∉ K) : (C(K, ℂ))ˣ where
  val := resolventElt K v
  inv := kernelFun K hv
  val_inv := by
    ext z
    have hz : v - (z : ℂ) ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      exact hv (h ▸ z.2)
    simp [resolventElt, coordMap, kernelFun, mul_inv_cancel₀ hz]
  inv_val := by
    ext z
    have hz : v - (z : ℂ) ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      exact hv (h ▸ z.2)
    simp [resolventElt, coordMap, kernelFun, inv_mul_cancel₀ hz]

/-- The Cauchy transform of a continuous functional on `C(K, ℂ)`. -/
def cauchyTransform (A : C(K, ℂ) →L[ℂ] ℂ) (v : ℂ) : ℂ :=
  A (Ring.inverse (resolventElt K v))

theorem cauchyTransform_eq (A : C(K, ℂ) →L[ℂ] ℂ) {v : ℂ} (hv : v ∉ K) :
    cauchyTransform A v = A (kernelFun K hv) := by
  have hunit : resolventElt K v = ((resolventUnit K hv : (C(K, ℂ))ˣ) : C(K, ℂ)) := rfl
  rw [cauchyTransform, hunit, Ring.inverse_unit]
  rfl

/-! ## Holomorphy off the carrier -/

/-- The resolvent inverse, as a map into the continuous functions on the carrier. -/
def resolventInv (K : Set ℂ) [CompactSpace K] (v : ℂ) : C(K, ℂ) :=
  Ring.inverse (resolventElt K v)

theorem resolventInv_eq {v : ℂ} (hv : v ∉ K) : resolventInv K v = kernelFun K hv := by
  have hunit : resolventElt K v = ((resolventUnit K hv : (C(K, ℂ))ˣ) : C(K, ℂ)) := rfl
  rw [resolventInv, hunit, Ring.inverse_unit]
  rfl

theorem differentiableAt_resolventInv {v : ℂ} (hv : v ∉ K) :
    DifferentiableAt ℂ (resolventInv K) v := by
  have haff : DifferentiableAt ℂ (fun u : ℂ => resolventElt K u) v := by
    have : Differentiable ℂ fun u : ℂ => u • (1 : C(K, ℂ)) - coordMap K :=
      (differentiable_id.smul_const (1 : C(K, ℂ))).sub_const (coordMap K)
    exact this.differentiableAt
  have hinv : DifferentiableAt ℂ Ring.inverse (resolventElt K v) := by
    have h := hasFDerivAt_ringInverse (𝕜 := ℂ) (resolventUnit K hv)
    exact h.differentiableAt
  exact hinv.comp v haff

theorem continuousOn_resolventInv : ContinuousOn (resolventInv K) Kᶜ := fun _v hv =>
  (differentiableAt_resolventInv hv).continuousAt.continuousWithinAt

theorem cauchyTransform_eq_apply_resolventInv (A : C(K, ℂ) →L[ℂ] ℂ) (v : ℂ) :
    cauchyTransform A v = A (resolventInv K v) := rfl

theorem differentiableAt_cauchyTransform (A : C(K, ℂ) →L[ℂ] ℂ) {v : ℂ} (hv : v ∉ K) :
    DifferentiableAt ℂ (cauchyTransform A) v :=
  A.differentiableAt.comp v (differentiableAt_resolventInv hv)

theorem differentiableOn_cauchyTransform (A : C(K, ℂ) →L[ℂ] ℂ) :
    DifferentiableOn ℂ (cauchyTransform A) Kᶜ := fun _v hv =>
  (differentiableAt_cauchyTransform A hv).differentiableWithinAt

theorem analyticOnNhd_cauchyTransform (hK : IsCompact K) (A : C(K, ℂ) →L[ℂ] ℂ) :
    AnalyticOnNhd ℂ (cauchyTransform A) Kᶜ :=
  (differentiableOn_cauchyTransform A).analyticOnNhd hK.isClosed.isOpen_compl

/-! ## Size of the transform -/

theorem norm_kernelFun_le {v : ℂ} (hv : v ∉ K) {r : ℝ} (hr : 0 < r)
    (hdist : ∀ z ∈ K, r ≤ ‖v - z‖) : ‖kernelFun K hv‖ ≤ r⁻¹ := by
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun z => ?_
  rw [kernelFun_apply, norm_inv]
  simp only [← one_div]
  exact one_div_le_one_div_of_le hr (hdist z z.2)

theorem norm_cauchyTransform_le (A : C(K, ℂ) →L[ℂ] ℂ) {v : ℂ} (hv : v ∉ K) {r : ℝ} (hr : 0 < r)
    (hdist : ∀ z ∈ K, r ≤ ‖v - z‖) : ‖cauchyTransform A v‖ ≤ ‖A‖ * r⁻¹ := by
  rw [cauchyTransform_eq A hv]
  refine le_trans (A.le_opNorm _) ?_
  exact mul_le_mul_of_nonneg_left (norm_kernelFun_le hv hr hdist) (norm_nonneg A)

/-! ## Vanishing outside a disc containing the carrier -/

theorem norm_coordMap_le {r : ℝ} (hr : 0 ≤ r) (hK : ∀ z ∈ K, ‖z‖ ≤ r) : ‖coordMap K‖ ≤ r :=
  (ContinuousMap.norm_le _ hr).2 fun z => hK z z.2

theorem summable_geometricKernel {v : ℂ} {r : ℝ} (hr : 0 ≤ r) (hK : ∀ z ∈ K, ‖z‖ ≤ r)
    (hv : r < ‖v‖) :
    Summable fun m : ℕ => ((v⁻¹) ^ (m + 1)) • (coordMap K ^ m) := by
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv
    linarith
  refine Summable.of_norm ?_
  have hbound : ∀ m : ℕ, ‖((v⁻¹) ^ (m + 1)) • (coordMap K ^ m)‖
      ≤ ‖v‖⁻¹ * (r / ‖v‖) ^ m := by
    intro m
    rw [norm_smul, norm_pow, norm_inv]
    have h1 : ‖coordMap K ^ m‖ ≤ r ^ m := by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun z => ?_
      have hval : (coordMap K ^ m) z = ((z : ℂ)) ^ m := by
        simp [coordMap]
      rw [hval, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hK z z.2) m
    calc ‖v‖⁻¹ ^ (m + 1) * ‖coordMap K ^ m‖
        ≤ ‖v‖⁻¹ ^ (m + 1) * r ^ m := by
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ‖v‖⁻¹ * (r / ‖v‖) ^ m := by
          rw [div_pow, pow_succ, inv_pow, div_eq_mul_inv]
          ring
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound ?_
  refine Summable.mul_left _ (summable_geometric_of_lt_one (by positivity) ?_)
  rw [div_lt_one (by positivity)]
  exact hv

theorem tsum_kernel_pointwise {v w : ℂ} (h : ‖w‖ < ‖v‖) :
    ∑' m : ℕ, ((v⁻¹) ^ (m + 1)) * w ^ m = (v - w)⁻¹ := by
  have hv0 : v ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at h
    exact absurd h (not_lt.mpr (norm_nonneg w))
  have hratio : ‖w / v‖ < 1 := by
    rw [norm_div, div_lt_one (by positivity)]
    exact h
  have hgeo : ∑' m : ℕ, (w / v) ^ m = (1 - w / v)⁻¹ := tsum_geometric_of_norm_lt_one hratio
  have hterm : ∀ m : ℕ, ((v⁻¹) ^ (m + 1)) * w ^ m = v⁻¹ * (w / v) ^ m := by
    intro m
    rw [div_pow, pow_succ, inv_pow, div_eq_mul_inv]
    ring
  have hvw : v - w ≠ 0 := by
    intro hc
    rw [sub_eq_zero] at hc
    rw [hc] at h
    exact absurd h (lt_irrefl _)
  rw [tsum_congr hterm, tsum_mul_left, hgeo]
  field_simp

theorem tsum_geometricKernel_eq {v : ℂ} {r : ℝ} (hr : 0 ≤ r) (hKr : ∀ z ∈ K, ‖z‖ ≤ r)
    (hv : r < ‖v‖) (hvK : v ∉ K) :
    ∑' m : ℕ, ((v⁻¹) ^ (m + 1)) • (coordMap K ^ m) = kernelFun K hvK := by
  have hsum := summable_geometricKernel (K := K) hr hKr hv
  ext z
  have heval := (ContinuousMap.evalCLM ℂ z).map_tsum hsum
  change (ContinuousMap.evalCLM ℂ z) (∑' m : ℕ, ((v⁻¹) ^ (m + 1)) • (coordMap K ^ m))
    = (kernelFun K hvK) z
  rw [heval]
  have hz : ‖(z : ℂ)‖ < ‖v‖ := lt_of_le_of_lt (hKr z z.2) hv
  have hterm : ∀ m : ℕ,
      (ContinuousMap.evalCLM ℂ z) (((v⁻¹) ^ (m + 1)) • (coordMap K ^ m))
        = ((v⁻¹) ^ (m + 1)) * ((z : ℂ)) ^ m := by
    intro m
    simp [ContinuousMap.evalCLM, coordMap]
  rw [tsum_congr hterm, tsum_kernel_pointwise hz, kernelFun_apply]

/-- **A functional killing every power of the coordinate has vanishing Cauchy transform outside a
disc containing the carrier.** -/
theorem cauchyTransform_eq_zero_of_lt (A : C(K, ℂ) →L[ℂ] ℂ)
    (hA : ∀ m : ℕ, A (coordMap K ^ m) = 0)
    {v : ℂ} {r : ℝ} (hr : 0 ≤ r) (hKr : ∀ z ∈ K, ‖z‖ ≤ r) (hv : r < ‖v‖) :
    cauchyTransform A v = 0 := by
  have hvK : v ∉ K := fun hc => absurd (hKr v hc) (not_le.mpr hv)
  rw [cauchyTransform_eq A hvK, ← tsum_geometricKernel_eq hr hKr hv hvK,
    A.map_tsum (summable_geometricKernel hr hKr hv)]
  have hterm : ∀ m : ℕ, A (((v⁻¹) ^ (m + 1)) • (coordMap K ^ m)) = 0 := by
    intro m
    rw [map_smul, hA m, smul_zero]
  rw [tsum_congr hterm, tsum_zero]

end GaloisForLFunctions.HTGeometry
