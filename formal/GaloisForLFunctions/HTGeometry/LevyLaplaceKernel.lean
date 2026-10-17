import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-! Finite-control coordinates for arbitrary positive half-line jump activity. -/

open Complex Set
open scoped NNReal
noncomputable section
namespace GaloisForLFunctions.HTGeometry

theorem norm_cexp_neg_mul_nonneg_le_one {z : ℂ} (hz : 0 ≤ z.re)
    {h : ℝ} (hh : 0 ≤ h) : ‖Complex.exp (-z * (h : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz) hh

theorem norm_one_sub_cexp_neg_mul_le_two {z : ℂ} (hz : 0 ≤ z.re)
    {h : ℝ} (hh : 0 ≤ h) : ‖1 - Complex.exp (-z * (h : ℂ))‖ ≤ 2 := by
  calc
    ‖1 - Complex.exp (-z * (h : ℂ))‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (-z * (h : ℂ))‖ :=
      norm_sub_le _ _
    _ ≤ 2 := by
      rw [norm_one]
      linarith [norm_cexp_neg_mul_nonneg_le_one hz hh]

theorem norm_one_sub_cexp_neg_mul_le_mul {z : ℂ} (hz : 0 ≤ z.re)
    {h : ℝ} (hh : 0 ≤ h) : ‖1 - Complex.exp (-z * (h : ℂ))‖ ≤ ‖z‖ * h := by
  have hd (s : ℝ) : HasDerivAt (fun u : ℝ => Complex.exp (-z * (u : ℂ)))
      (Complex.exp (-z * (s : ℂ)) * -z) s := by
    simpa using (((hasDerivAt_id s).ofReal_comp).const_mul (-z)).cexp
  have hb (s : ℝ) (hs : s ∈ Ico 0 h) :
      ‖Complex.exp (-z * (s : ℂ)) * -z‖ ≤ ‖z‖ := by
    rw [norm_mul, norm_neg]
    exact mul_le_of_le_one_left (norm_nonneg z)
      (norm_cexp_neg_mul_nonneg_le_one hz hs.1)
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s _ => (hd s).hasDerivWithinAt) hb h (right_mem_Icc.mpr hh)
  simpa only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_zero,
    norm_sub_rev] using hmv

/-- The zero jump is removed; its independent coefficient is the deterministic drift. -/
def levyLaplaceKernel (z : ℂ) (h : ℝ≥0) : ℂ :=
  if h = 0 then 0 else
    (((1 + (h : ℝ)) / (h : ℝ) : ℝ) : ℂ) *
      (1 - Complex.exp (-z * ((h : ℝ) : ℂ)))

def levyLaplaceKernelDeriv (z : ℂ) (h : ℝ≥0) : ℂ :=
  if h = 0 then 0 else
    ((1 + (h : ℝ) : ℝ) : ℂ) * Complex.exp (-z * ((h : ℝ) : ℂ))

@[simp] theorem levyLaplaceKernel_zero (z : ℂ) : levyLaplaceKernel z 0 = 0 := by
  simp [levyLaplaceKernel]

@[simp] theorem levyLaplaceKernel_at_zero (h : ℝ≥0) : levyLaplaceKernel 0 h = 0 := by
  simp [levyLaplaceKernel]

theorem measurable_levyLaplaceKernel (z : ℂ) : Measurable (levyLaplaceKernel z) := by
  unfold levyLaplaceKernel
  apply Measurable.ite (measurableSet_singleton 0) measurable_const
  fun_prop

theorem measurable_levyLaplaceKernelDeriv (z : ℂ) :
    Measurable (levyLaplaceKernelDeriv z) := by
  unfold levyLaplaceKernelDeriv
  apply Measurable.ite (measurableSet_singleton 0) measurable_const
  fun_prop

theorem levyLaplaceKernel_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) (h : ℝ≥0) :
    0 ≤ (levyLaplaceKernel z h).re := by
  by_cases hh : h = 0
  · simp [hh]
  · have hc : 0 ≤ (1 + (h : ℝ)) / (h : ℝ) := by positivity
    have he := (Complex.re_le_norm (Complex.exp (-z * ((h : ℝ) : ℂ)))).trans
      (norm_cexp_neg_mul_nonneg_le_one hz h.coe_nonneg)
    simp only [levyLaplaceKernel, if_neg hh, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re, Complex.one_re]
    exact mul_nonneg hc (sub_nonneg.mpr he)

/-- A bound independent of the jump size, including arbitrarily small jumps. -/
theorem norm_levyLaplaceKernel_le {z : ℂ} (hz : 0 ≤ z.re) (h : ℝ≥0) :
    ‖levyLaplaceKernel z h‖ ≤ 2 + ‖z‖ := by
  by_cases hh : h = 0
  · simp only [hh, levyLaplaceKernel_zero, norm_zero]
    positivity
  · have hhpos : 0 < (h : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hh)
    have hc : 0 ≤ (1 + (h : ℝ)) / (h : ℝ) := by positivity
    let D := ‖1 - Complex.exp (-z * ((h : ℝ) : ℂ))‖
    have hD : D ≤ 2 := norm_one_sub_cexp_neg_mul_le_two hz h.coe_nonneg
    have hDdiv : D / (h : ℝ) ≤ ‖z‖ :=
      (div_le_iff₀ hhpos).mpr (norm_one_sub_cexp_neg_mul_le_mul hz h.coe_nonneg)
    simp only [levyLaplaceKernel, if_neg hh, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hc]
    change (1 + (h : ℝ)) / (h : ℝ) * D ≤ _
    calc
      (1 + (h : ℝ)) / (h : ℝ) * D = D + D / (h : ℝ) := by
        field_simp
        ring
      _ ≤ 2 + ‖z‖ := add_le_add hD hDdiv

theorem hasDerivAt_levyLaplaceKernel (z : ℂ) (h : ℝ≥0) :
    HasDerivAt (fun w => levyLaplaceKernel w h) (levyLaplaceKernelDeriv z h) z := by
  by_cases hh : h = 0
  · simpa [hh, levyLaplaceKernelDeriv] using hasDerivAt_const z (0 : ℂ)
  · have hh0 : ((h : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hh
    simp only [levyLaplaceKernel, levyLaplaceKernelDeriv, if_neg hh]
    have hd := (((hasDerivAt_id z).neg).mul_const ((h : ℝ) : ℂ)).cexp
    have hc : (((1 + (h : ℝ)) / (h : ℝ) : ℝ) : ℂ) *
        (Complex.exp (-z * ((h : ℝ) : ℂ)) * ((h : ℝ) : ℂ)) =
        ((1 + (h : ℝ) : ℝ) : ℂ) * Complex.exp (-z * ((h : ℝ) : ℂ)) := by
      push_cast
      field_simp
    simpa only [id_eq, Pi.neg_apply, Pi.sub_apply, neg_one_mul, mul_neg,
      zero_sub, neg_neg, hc] using
      ((hasDerivAt_const z (1 : ℂ)).sub hd).const_mul
        ((((1 + (h : ℝ)) / (h : ℝ) : ℝ) : ℂ))

theorem norm_levyLaplaceKernelDeriv_le {δ : ℝ} (hδ : 0 < δ)
    {z : ℂ} (hz : δ ≤ z.re) (h : ℝ≥0) :
    ‖levyLaplaceKernelDeriv z h‖ ≤ 1 + 1 / δ := by
  by_cases hh : h = 0
  · simp only [levyLaplaceKernelDeriv, hh, ↓reduceIte, norm_zero]
    positivity
  · have hcoeff : 0 ≤ 1 + (h : ℝ) := by positivity
    simp only [levyLaplaceKernelDeriv, if_neg hh, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hcoeff, Complex.norm_exp, Complex.mul_re,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    have hexp : Real.exp (-z.re * (h : ℝ)) ≤ Real.exp (-(δ * (h : ℝ))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [h.coe_nonneg]
    have hE : Real.exp (-(δ * (h : ℝ))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (mul_nonneg hδ.le h.coe_nonneg)
    have hlin : (δ * (h : ℝ)) * Real.exp (-(δ * (h : ℝ))) ≤ 1 :=
      (Real.mul_exp_neg_le_exp_neg_one _).trans (by
        apply Real.exp_le_one_iff.mpr
        norm_num)
    have hsmall : (h : ℝ) * Real.exp (-(δ * (h : ℝ))) ≤ 1 / δ := by
      apply (le_div_iff₀ hδ).mpr
      nlinarith [hlin]
    calc
      (1 + (h : ℝ)) * Real.exp (-z.re * (h : ℝ)) ≤
          (1 + (h : ℝ)) * Real.exp (-(δ * (h : ℝ))) :=
        mul_le_mul_of_nonneg_left hexp hcoeff
      _ = Real.exp (-(δ * (h : ℝ))) +
          (h : ℝ) * Real.exp (-(δ * (h : ℝ))) := by ring
      _ ≤ 1 + 1 / δ := add_le_add hE hsmall

theorem levyLaplaceKernel_ofReal (x : ℝ) (h : ℝ≥0) :
    levyLaplaceKernel (x : ℂ) h =
      (((1 + (h : ℝ)) / (h : ℝ) * (1 - Real.exp (-(x * (h : ℝ)))) : ℝ) : ℂ) := by
  by_cases hh : h = 0
  · simp [hh]
  · simp only [levyLaplaceKernel, if_neg hh]
    push_cast
    simp only [neg_mul]

end GaloisForLFunctions.HTGeometry
