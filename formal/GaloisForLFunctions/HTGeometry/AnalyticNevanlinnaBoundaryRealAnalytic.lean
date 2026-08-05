import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierBridge
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Real analyticity of the classical Nevanlinna boundary matrix

An entire complex extension agreeing with a real-valued boundary function makes that boundary
function real analytic. Applying this restriction law to all four stored extensions removes the
separate real-analyticity premises from downstream projective-label and carrier theorems.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- **Complex-to-real restriction law.** A complex-differentiable extension whose values agree
with a real function on real inputs makes that real function analytic on all of `ℝ`. -/
theorem analyticOnNhd_real_of_differentiable_extension
    {f : ℂ → ℂ} {g : ℝ → ℝ}
    (hf : Differentiable ℂ f) (hfg : ∀ x : ℝ, f x = g x) :
    AnalyticOnNhd ℝ g Set.univ := by
  have hc : AnalyticOnNhd ℂ f (Complex.ofReal '' (Set.univ : Set ℝ)) :=
    fun z hz => hf.analyticAt z
  have hr : AnalyticOnNhd ℝ (fun x : ℝ => (f x).re) Set.univ := hc.re_ofReal
  refine hr.congr isOpen_univ ?_
  intro x hx
  simpa only [Complex.ofReal_re] using congrArg Complex.re (hfg x)

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- First boundary-matrix entry is real analytic. -/
theorem analyticOnNhd_boundary_a :
    AnalyticOnNhd ℝ F.base.toBoundaryFamily.matrix.a Set.univ :=
  analyticOnNhd_real_of_differentiable_extension F.differentiable_a F.a_real

/-- Second boundary-matrix entry is real analytic. -/
theorem analyticOnNhd_boundary_b :
    AnalyticOnNhd ℝ F.base.toBoundaryFamily.matrix.b Set.univ :=
  analyticOnNhd_real_of_differentiable_extension F.differentiable_b F.b_real

/-- Denominator coefficient `c` is real analytic. -/
theorem analyticOnNhd_boundary_c :
    AnalyticOnNhd ℝ F.base.toBoundaryFamily.matrix.c Set.univ :=
  analyticOnNhd_real_of_differentiable_extension F.differentiable_c F.c_real

/-- Denominator coefficient `d` is real analytic. -/
theorem analyticOnNhd_boundary_d :
    AnalyticOnNhd ℝ F.base.toBoundaryFamily.matrix.d Set.univ :=
  analyticOnNhd_real_of_differentiable_extension F.differentiable_d F.d_real

/-- Entire carrier data supplies both analytic denominator entries simultaneously. -/
theorem analyticOnNhd_boundary_c_and_d :
    AnalyticOnNhd ℝ F.base.toBoundaryFamily.matrix.c Set.univ ∧
      AnalyticOnNhd ℝ F.base.toBoundaryFamily.matrix.d Set.univ :=
  ⟨F.analyticOnNhd_boundary_c, F.analyticOnNhd_boundary_d⟩

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
