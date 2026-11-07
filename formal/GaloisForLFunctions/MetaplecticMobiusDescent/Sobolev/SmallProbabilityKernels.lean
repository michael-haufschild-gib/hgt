/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license; see LICENSE and NOTICE in the parent directory.
Adapted from rellich-kondrachov, Euclidean/L2Compactness/Kernels.lean.
-/
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Support

/-!
# Compact probability kernels at every scale

A smooth bump of value one at the origin has positive integral. Normalization
produces a nonnegative unit-mass kernel supported in any prescribed ball.
-/

namespace GaloisForLFunctions.MetaplecticMobiusDescent.EuclideanSobolev.L2Compactness

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance instMeasurableSpaceE_L2CompactnessKernels : MeasurableSpace E := borel E
local instance instBorelSpaceE_L2CompactnessKernels : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_L2CompactnessKernels : OpensMeasurableSpace E := by
  infer_instance

/-- For any `δ > 0`, there exists a continuous compactly supported kernel `ψ` supported in
`Metric.ball 0 δ`, with `ψ ≥ 0` and `∫ ψ = 1` (w.r.t. Lebesgue measure). -/
theorem exists_kernel_tsupport_subset_ball_integral_eq_one {δ : ℝ} (hδ : 0 < δ) :
    ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
      (∫ x, ψ x ∂(volume : Measure E) = 1) ∧ tsupport ψ ⊆ Metric.ball (0 : E) δ := by
  classical
  have hs : (Metric.ball (0 : E) δ) ∈ 𝓝 (0 : E) := Metric.ball_mem_nhds _ hδ
  rcases exists_contDiff_tsupport_subset (n := ⊤)
    (E := E) (s := Metric.ball (0 : E) δ) (x := (0 : E)) hs with
    ⟨f, hf_tsupp, hf_cs, hf_smooth, hf_range, hf0⟩
  have hf_cont : Continuous f := hf_smooth.continuous
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    have hx : f x ∈ Set.Icc (0 : ℝ) 1 := hf_range ⟨x, rfl⟩
    exact hx.1
  have hf0_ne : f (0 : E) ≠ 0 := by
    simp [hf0]
  have hIpos :
      0 < ∫ x, f x ∂(volume : Measure E) := by
    simpa using
      (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := (volume : Measure E))
        hf_cont hf_cs hf_nonneg hf0_ne)
  set I : ℝ := ∫ x, f x ∂(volume : Measure E)
  have hI0 : I ≠ 0 := ne_of_gt hIpos
  have hIpos' : 0 < I := by simpa [I] using hIpos
  let ψ : E → ℝ := fun x => I⁻¹ * f x
  have hψc : Continuous ψ := by
    exact continuous_const.mul hf_cont
  have hψcs : HasCompactSupport ψ := by
    exact
      (HasCompactSupport.smul_left (f := fun _x : E => I⁻¹) (f' := f) hf_cs)
  have hψ0 : ∀ x, 0 ≤ ψ x := by
    intro x
    have hInv : 0 ≤ I⁻¹ := by
      have : 0 ≤ I := le_of_lt hIpos'
      simpa using inv_nonneg.2 this
    simpa [ψ] using mul_nonneg hInv (hf_nonneg x)
  have hψint : ∫ x, ψ x ∂(volume : Measure E) = 1 := by
    have : (∫ x, ψ x ∂(volume : Measure E)) = I⁻¹ * I := by
      simpa [ψ, I] using
        (MeasureTheory.integral_const_mul (μ := (volume : Measure E)) (r := I⁻¹) (f := f))
    simp [this, hI0]
  have hψ_tsupp : tsupport ψ ⊆ Metric.ball (0 : E) δ := by
    have hsub : tsupport ψ ⊆ tsupport f := by
      exact (tsupport_smul_subset_right (f := fun _x : E => I⁻¹) (g := f))
    exact hsub.trans hf_tsupp
  exact ⟨ψ, hψc, hψcs, hψ0, hψint, hψ_tsupp⟩

end Volume

end
#print axioms exists_kernel_tsupport_subset_ball_integral_eq_one

end GaloisForLFunctions.MetaplecticMobiusDescent.EuclideanSobolev.L2Compactness
