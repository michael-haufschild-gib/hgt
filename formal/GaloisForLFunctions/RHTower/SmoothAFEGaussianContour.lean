import GaloisForLFunctions.RHTower.SmoothAFEGaussianKernel
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Positive-line contour invariance of the Gaussian Mellin cutoff

The inverse-Mellin integral with kernel `exp(w²) / w` is independent of its abscissa while that
abscissa remains positive.  The proof closes a rectangle between two positive lines.  Gaussian
decay `exp(-T²)` kills both horizontal sides, while
`SmoothAFEGaussianKernel` supplies absolute convergence on the two vertical sides.

This is the contour-deformation component needed before shifting through the simple pole at zero
in the smooth approximate functional equation.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Set Filter Topology

theorem norm_smoothAFEMellinIntegrand_horizontal_le
    {x a b u : ℝ} (hx : 0 < x) (ha : 0 < a) (hau : a ≤ u) (hub : u ≤ b)
    (t : ℝ) :
    ‖smoothAFEMellinIntegrand x ((u : ℂ) + (t : ℂ) * I)‖
      ≤ (Real.exp (|Real.log x| * b) * (Real.exp (b ^ 2) / a)) *
          Real.exp (-(t ^ 2)) := by
  have hu : 0 < u := ha.trans_le hau
  have hb : 0 < b := hu.trans_le hub
  have hxpow : x ^ (-u) ≤ Real.exp (|Real.log x| * b) := by
    rw [Real.rpow_def_of_pos hx]
    apply Real.exp_le_exp.2
    calc
      Real.log x * -u ≤ |Real.log x * -u| := le_abs_self _
      _ = |Real.log x| * u := by
        rw [abs_mul, abs_neg, abs_of_nonneg hu.le]
      _ ≤ |Real.log x| * b :=
        mul_le_mul_of_nonneg_left hub (abs_nonneg _)
  have hexp : Real.exp (u ^ 2) ≤ Real.exp (b ^ 2) := by
    apply Real.exp_le_exp.2
    nlinarith
  have hquot : Real.exp (u ^ 2) / u ≤ Real.exp (b ^ 2) / a := by
    calc
      Real.exp (u ^ 2) / u ≤ Real.exp (b ^ 2) / u := by
        exact div_le_div_of_nonneg_right hexp hu.le
      _ ≤ Real.exp (b ^ 2) / a := by
        exact div_le_div_of_nonneg_left (by positivity) ha hau
  calc
    ‖smoothAFEMellinIntegrand x ((u : ℂ) + (t : ℂ) * I)‖
        ≤ (x ^ (-u) * (Real.exp (u ^ 2) / u)) * Real.exp (-(t ^ 2)) :=
          norm_smoothAFEMellinIntegrand_vertical_le hx hu t
    _ ≤ (Real.exp (|Real.log x| * b) * (Real.exp (b ^ 2) / a)) *
          Real.exp (-(t ^ 2)) := by
      gcongr

theorem integral_smoothAFEMellinIntegrand_eq_of_le
    {x a b : ℝ} (hx : 0 < x) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t : ℝ, smoothAFEMellinIntegrand x ((a : ℂ) + (t : ℂ) * I))
      = ∫ t : ℝ, smoothAFEMellinIntegrand x ((b : ℂ) + (t : ℂ) * I) := by
  have hb : 0 < b := ha.trans_le hab
  haveI : NeZero (x : ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
  let F : ℂ → ℂ := smoothAFEMellinIntegrand x
  have hFdiff : DifferentiableOn ℂ F {z : ℂ | a ≤ z.re} := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro hzero
      have hzpos : 0 < z.re := ha.trans_le hz
      rw [hzero] at hzpos
      simp at hzpos
    dsimp [F, smoothAFEMellinIntegrand, smoothAFEGaussianKernel]
    exact (((differentiableAt_const_cpow_of_neZero (x : ℂ) (-z)).comp z
      (differentiable_id.neg).differentiableAt).mul
        (((differentiable_exp.comp (differentiable_pow 2)).differentiableAt).div
          differentiableAt_id hz0)).differentiableWithinAt
  have hrect : ∀ T : ℝ,
      (∫ u : ℝ in a..b, F ((u : ℂ) - (T : ℂ) * I))
        - (∫ u : ℝ in a..b, F ((u : ℂ) + (T : ℂ) * I))
        + I • (∫ t : ℝ in (-T)..T, F ((b : ℂ) + (t : ℂ) * I))
        - I • (∫ t : ℝ in (-T)..T, F ((a : ℂ) + (t : ℂ) * I)) = 0 := by
    intro T
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
      ((a : ℂ) - (T : ℂ) * I) ((b : ℂ) + (T : ℂ) * I) ?_
    · simpa using! h
    · apply hFdiff.mono
      intro z hz
      rcases hz with ⟨hzre, _⟩
      have hzre' : a ≤ z.re ∧ z.re ≤ b := by
        simpa [Set.mem_uIcc, hab] using hzre
      exact hzre'.1
  have hleft : Tendsto (fun T : ℝ =>
      ∫ t : ℝ in (-T)..T, F ((a : ℂ) + (t : ℂ) * I)) atTop
      (𝓝 (∫ t : ℝ, F ((a : ℂ) + (t : ℂ) * I))) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral
      (smoothAFEMellinIntegrand_verticalIntegrable hx ha)
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hright : Tendsto (fun T : ℝ =>
      ∫ t : ℝ in (-T)..T, F ((b : ℂ) + (t : ℂ) * I)) atTop
      (𝓝 (∫ t : ℝ, F ((b : ℂ) + (t : ℂ) * I))) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral
      (smoothAFEMellinIntegrand_verticalIntegrable hx hb)
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hexp0 : Tendsto (fun T : ℝ => Real.exp (-(T ^ 2))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply Filter.tendsto_neg_atTop_atBot.comp
    exact tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hmajor : Tendsto (fun T : ℝ =>
      (Real.exp (|Real.log x| * b) * (Real.exp (b ^ 2) / a)) * |b - a| *
        Real.exp (-(T ^ 2))) atTop (𝓝 0) := by
    simpa using hexp0.const_mul
      ((Real.exp (|Real.log x| * b) * (Real.exp (b ^ 2) / a)) * |b - a|)
  have hbottom : Tendsto (fun T : ℝ =>
      ∫ u : ℝ in a..b, F ((u : ℂ) - (T : ℂ) * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hmajor
    filter_upwards with T
    have hbd : ∀ u ∈ Set.uIoc a b,
        ‖F ((u : ℂ) - (T : ℂ) * I)‖
          ≤ (Real.exp (|Real.log x| * b) * (Real.exp (b ^ 2) / a)) *
              Real.exp (-(T ^ 2)) := by
      intro u hu
      have hu' : a ≤ u ∧ u ≤ b := by
        have := (by simpa [Set.mem_uIoc, hab] using hu : a < u ∧ u ≤ b)
        exact ⟨this.1.le, this.2⟩
      have h := norm_smoothAFEMellinIntegrand_horizontal_le hx ha hu'.1 hu'.2 (-T)
      simpa [F, neg_sq] using! h
    calc
      ‖∫ u : ℝ in a..b, F ((u : ℂ) - (T : ℂ) * I)‖
          ≤ (Real.exp (|Real.log x| * b) * (Real.exp (b ^ 2) / a)) *
              Real.exp (-(T ^ 2)) * |b - a| := by
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro u hu
            simpa [sub_eq_add_neg, ofReal_neg] using hbd u hu
      _ = (Real.exp (|Real.log x| * b) * (Real.exp (b ^ 2) / a)) *
              |b - a| * Real.exp (-(T ^ 2)) := by ring
  have htop : Tendsto (fun T : ℝ =>
      ∫ u : ℝ in a..b, F ((u : ℂ) + (T : ℂ) * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hmajor
    filter_upwards with T
    have hbd : ∀ u ∈ Set.uIoc a b,
        ‖F ((u : ℂ) + (T : ℂ) * I)‖
          ≤ (Real.exp (|Real.log x| * b) * (Real.exp (b ^ 2) / a)) *
              Real.exp (-(T ^ 2)) := by
      intro u hu
      have hu' : a ≤ u ∧ u ≤ b := by
        have := (by simpa [Set.mem_uIoc, hab] using hu : a < u ∧ u ≤ b)
        exact ⟨this.1.le, this.2⟩
      exact norm_smoothAFEMellinIntegrand_horizontal_le hx ha hu'.1 hu'.2 T
    calc
      ‖∫ u : ℝ in a..b, F ((u : ℂ) + (T : ℂ) * I)‖
          ≤ (Real.exp (|Real.log x| * b) * (Real.exp (b ^ 2) / a)) *
              Real.exp (-(T ^ 2)) * |b - a| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hbd
      _ = (Real.exp (|Real.log x| * b) * (Real.exp (b ^ 2) / a)) *
              |b - a| * Real.exp (-(T ^ 2)) := by ring
  have hcomb := ((hbottom.sub htop).add (hright.const_smul I)).sub
    (hleft.const_smul I)
  rw [funext hrect] at hcomb
  have hval := tendsto_nhds_unique hcomb tendsto_const_nhds
  have hfin :
      I * (∫ t : ℝ, F ((b : ℂ) + (t : ℂ) * I))
        - I * (∫ t : ℝ, F ((a : ℂ) + (t : ℂ) * I)) = 0 := by
    simpa [smul_eq_mul] using hval
  have hi : I ≠ 0 := Complex.I_ne_zero
  rw [← mul_sub] at hfin
  have hba := (mul_eq_zero.mp hfin).resolve_left hi
  exact (sub_eq_zero.mp hba).symm

theorem integral_smoothAFEMellinIntegrand_eq
    {x σ τ : ℝ} (hx : 0 < x) (hσ : 0 < σ) (hτ : 0 < τ) :
    (∫ t : ℝ, smoothAFEMellinIntegrand x ((σ : ℂ) + (t : ℂ) * I))
      = ∫ t : ℝ, smoothAFEMellinIntegrand x ((τ : ℂ) + (t : ℂ) * I) := by
  rcases le_total σ τ with hστ | hτσ
  · exact integral_smoothAFEMellinIntegrand_eq_of_le hx hσ hστ
  · exact (integral_smoothAFEMellinIntegrand_eq_of_le hx hτ hτσ).symm

theorem smoothAFECutoffAt_eq
    {x σ τ : ℝ} (hx : 0 < x) (hσ : 0 < σ) (hτ : 0 < τ) :
    smoothAFECutoffAt σ x = smoothAFECutoffAt τ x := by
  unfold smoothAFECutoffAt mellinInv
  congr 1
  simpa only [smul_eq_mul, smoothAFEMellinIntegrand] using
    integral_smoothAFEMellinIntegrand_eq hx hσ hτ

/-- Canonical Gaussian smooth cutoff, evaluated on the line `Re w = 1`. -/
def smoothAFECutoff (x : ℝ) : ℂ :=
  smoothAFECutoffAt 1 x

theorem smoothAFECutoffAt_eq_smoothAFECutoff
    {x σ : ℝ} (hx : 0 < x) (hσ : 0 < σ) :
    smoothAFECutoffAt σ x = smoothAFECutoff x := by
  exact smoothAFECutoffAt_eq hx hσ zero_lt_one

end RHTower
