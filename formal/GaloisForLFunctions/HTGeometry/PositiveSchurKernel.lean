import GaloisForLFunctions.HTGeometry.SchurKernelComposition
import Mathlib.MeasureTheory.Function.LpOrder

/-! # Real nonnegative kernels preserve the complex L² positive cone -/

noncomputable section
open MeasureTheory Complex
open scoped ComplexOrder

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

theorem SchurKernel.op_nonneg (k : SchurKernel μ)
    (hk : ∀ t a, 0 ≤ k.toFun t a) {f : Lp ℂ 2 μ} (hf : 0 ≤ f) : 0 ≤ k.op f := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [k.op_coeFn f] with t ht
  rw [ht]
  apply integral_nonneg_of_ae
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf] with a ha
  exact mul_nonneg (hk t a) ha

theorem complex_conj_nonneg_of_nonneg {z : ℂ} (hz : 0 ≤ z) : 0 ≤ (starRingEnd ℂ) z := by
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hz
  exact Complex.nonneg_iff.mpr ⟨by simpa using hre, by simp [← him]⟩

theorem SchurKernel.adjoint_op_nonneg (k : SchurKernel μ)
    (hk : ∀ t a, 0 ≤ k.toFun t a) {f : Lp ℂ 2 μ} (hf : 0 ≤ f) :
    0 ≤ ContinuousLinearMap.adjoint k.op f := by
  rw [SchurKernel.adjoint_op]
  exact k.adjoint.op_nonneg (fun t a => complex_conj_nonneg_of_nonneg (hk a t)) hf

omit [SFinite μ] in
theorem l2_inner_nonneg_of_nonneg {f g : Lp ℂ 2 μ} (hf : 0 ≤ f) (hg : 0 ≤ g) :
    0 ≤ inner ℂ f g := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf, (Lp.coeFn_nonneg g).mpr hg] with t hft hgt
  rw [RCLike.inner_apply]
  exact mul_nonneg hgt (complex_conj_nonneg_of_nonneg hft)

end GaloisForLFunctions.HTGeometry
