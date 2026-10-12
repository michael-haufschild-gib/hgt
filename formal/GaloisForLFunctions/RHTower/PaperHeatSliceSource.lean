import GaloisForLFunctions.RHTower.RiemannHeatSliceTaylorPositivity
import GaloisForLFunctions.RHTower.DeBruijnHeatEquation
import GaloisForLFunctions.RHTower.XiHorizontalSlicePolyaFrequencyCriterion
import GaloisForLFunctions.HTGeometry.SliceDerivativeJointHolomorphy
import Mathlib.Analysis.Complex.Liouville

/-!
# The full Taylor source for the LA ideal-trace application

The coefficients below are the actual factorial-normalized coefficients of
`H_λ(t - iz) H_λ(t + iz)`. Their reality, continuous height dependence and uniform
Cauchy bound are derived from the native heat kernel, without a sign assumption.
-/

namespace RHTower.PaperHeatSlice
noncomputable section
open Complex MeasureTheory Filter
open RHTower.DeBruijn GaloisForLFunctions.HTGeometry
open scoped Topology ComplexOrder NNReal

abbrev Radius := {r : ℝ // 0 < r}

def source (lam : ℝ≥0) (t : ℝ) (z : ℂ) : ℂ :=
  riemannHeat lam ((t : ℂ) - I * z) * riemannHeat lam ((t : ℂ) + I * z)

def coeff (lam : ℝ≥0) (t : ℝ) (n : ℕ) : ℂ :=
  iteratedDeriv n (source lam t) 0 / (n.factorial : ℂ)

theorem differentiable_source (lam : ℝ≥0) (t : ℝ) : Differentiable ℂ (source lam t) := by
  have h := differentiable_riemannHeat lam.property
  unfold source
  exact (h.comp (by fun_prop)).mul (h.comp (by fun_prop))

theorem source_conj (lam : ℝ≥0) (t : ℝ) (z : ℂ) :
    source lam t (starRingEnd ℂ z) = starRingEnd ℂ (source lam t z) := by
  have hplus : (t : ℂ) - I * starRingEnd ℂ z = starRingEnd ℂ ((t : ℂ) + I * z) := by
    simp [sub_eq_add_neg]
  have hminus : (t : ℂ) + I * starRingEnd ℂ z = starRingEnd ℂ ((t : ℂ) - I * z) := by
    simp
  unfold source
  calc
    _ = riemannHeat lam (starRingEnd ℂ ((t : ℂ) + I * z)) *
        riemannHeat lam (starRingEnd ℂ ((t : ℂ) - I * z)) := by rw [hplus, hminus]
    _ = starRingEnd ℂ (riemannHeat lam ((t : ℂ) + I * z)) *
        starRingEnd ℂ (riemannHeat lam ((t : ℂ) - I * z)) :=
      congrArg₂ (fun a b : ℂ => a * b)
        (riemannHeat_conj lam.property ((t : ℂ) + I * z))
        (riemannHeat_conj lam.property ((t : ℂ) - I * z))
    _ = _ := by rw [map_mul, mul_comm]

theorem iteratedDeriv_im (lam : ℝ≥0) (t : ℝ) (n : ℕ) :
    (iteratedDeriv n (source lam t) 0).im = 0 := by
  have hsym : starRingEnd ℂ ∘ source lam t ∘ starRingEnd ℂ = source lam t := by
    funext z
    simp only [Function.comp_apply, source_conj, Complex.conj_conj]
  have h := congrFun (iteratedDeriv_conj_comp_conj (source lam t) n) 0
  rw [hsym] at h
  have him := congrArg Complex.im h
  simp only [Function.comp_apply, map_zero, Complex.conj_im] at him
  linarith

theorem coeff_im (lam : ℝ≥0) (t : ℝ) (n : ℕ) : (coeff lam t n).im = 0 := by
  simp [coeff, iteratedDeriv_im]

theorem continuous_coeff (lam : ℝ≥0) (n : ℕ) : Continuous fun t : ℝ => coeff lam t n := by
  have h := differentiable_riemannHeat lam.property
  have hF : Differentiable ℂ (fun p : ℂ × ℂ =>
      riemannHeat lam (p.1 - I * p.2) * riemannHeat lam (p.1 + I * p.2)) :=
    (h.comp (by fun_prop)).mul (h.comp (by fun_prop))
  have hd := (differentiable_param_iteratedDeriv hF n 0).continuous.comp
    Complex.continuous_ofReal
  exact hd.div_const _

/-- The explicit finite Fourier-kernel majorant for a horizontal strip. -/
def stripBudget (lam : ℝ≥0) (R : ℝ) : ℝ :=
  ∫ x : ℝ, ‖heatWeight lam x‖ * Real.exp (R * |x|)

theorem stripBudget_nonneg (lam : ℝ≥0) (R : ℝ) : 0 ≤ stripBudget lam R :=
  integral_nonneg fun _ => by positivity

private theorem norm_heat_le (lam : ℝ≥0) (z : ℂ) (R : ℝ) (hR : |z.im| ≤ R) :
    ‖riemannHeat lam z‖ ≤ stripBudget lam R := by
  rw [riemannHeat_eq_expTransform]
  unfold expTransform stripBudget
  apply norm_integral_le_of_norm_le (integrable_heatWeight lam.property R)
  filter_upwards with x
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (norm_exp_I_mul_le z x).trans (by gcongr)

theorem norm_source_le (lam : ℝ≥0) (t : ℝ) (z : ℂ) :
    ‖source lam t z‖ ≤ stripBudget lam ‖z‖ ^ 2 := by
  have ha : |((t : ℂ) - I * z).im| ≤ ‖z‖ := by
    simpa using Complex.abs_re_le_norm z
  have hb : |((t : ℂ) + I * z).im| ≤ ‖z‖ := by
    simpa using Complex.abs_re_le_norm z
  simpa only [source, norm_mul, pow_two] using
    mul_le_mul (norm_heat_le lam _ _ ha) (norm_heat_le lam _ _ hb)
      (norm_nonneg _) (stripBudget_nonneg lam _)

/-- A height-uniform Cauchy estimate for every actual Taylor order. -/
theorem norm_coeff_le (lam : ℝ≥0) (R : Radius) (t : ℝ) (n : ℕ) :
    ‖coeff lam t n‖ ≤ stripBudget lam R ^ 2 / (R : ℝ) ^ n := by
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) n R.property
    (differentiable_source lam t).diffContOnCl (fun z hz => by
      have hn : ‖z‖ = (R : ℝ) := by simpa using mem_sphere_iff_norm.mp hz
      simpa only [hn] using norm_source_le lam t z)
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [coeff, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hf).2
  exact hc.trans_eq (by ring)

end
end RHTower.PaperHeatSlice
