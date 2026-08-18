import Mathlib
import GaloisForLFunctions.RHTower.RectangleLocalCauchyFormula
import GaloisForLFunctions.HTGeometry.RectangleResidue

/-!
# The Cauchy representation on a closed half plane

A function analytic on the closed half plane `Re s ≥ 1` and decaying there like `‖s‖⁻²` is
reproduced at every interior point by the integral of its boundary values along the line
`Re s = 1`:

```text
∫_R  φ(1 + i y) / ((1 + i y) - s)  dy  =  -2π φ(s)        (Re s > 1).
```

The proof applies the rectangle Cauchy formula on the square `[1, R] × [-R, R]` — legitimate with
the left edge exactly on the line because `φ` is analytic *on* the closed half plane — and lets
`R → ∞`.  The three moving edges each carry a factor `‖φ‖ ≤ C/R²`, so they vanish; the left edge
converges to the line integral by dominated convergence.
-/

noncomputable section

open Complex intervalIntegral MeasureTheory Filter Set

namespace GaloisForLFunctions.HTGeometry

/-- The boundary integrand along the line `Re s = 1`. -/
def lineKernel (φ : ℂ → ℂ) (s : ℂ) (y : ℝ) : ℂ := φ (1 + (y : ℂ) * I) / ((1 + (y : ℂ) * I) - s)

theorem norm_one_add_mul_I_sq (y : ℝ) : ‖(1 : ℂ) + (y : ℂ) * I‖ ^ 2 = 1 + y ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp
  ring

theorem re_one_add_mul_I (y : ℝ) : ((1 : ℂ) + (y : ℂ) * I).re = 1 := by simp

theorem continuous_lineParam : Continuous fun y : ℝ => (1 : ℂ) + (y : ℂ) * I := by
  fun_prop

/-- The boundary integrand is dominated by an integrable envelope. -/
theorem norm_lineKernel_le {φ : ℂ → ℂ} {C : ℝ}
    (hbound : ∀ z : ℂ, 1 ≤ z.re → ‖φ z‖ ≤ C / ‖z‖ ^ 2)
    {s : ℂ} (hs : 1 < s.re) (y : ℝ) :
    ‖lineKernel φ s y‖ ≤ C / (1 + y ^ 2) / (s.re - 1) := by
  have hre : ((1 : ℂ) + (y : ℂ) * I).re = 1 := re_one_add_mul_I y
  have hnum : ‖φ ((1 : ℂ) + (y : ℂ) * I)‖ ≤ C / (1 + y ^ 2) := by
    have h := hbound _ (by rw [hre])
    rwa [norm_one_add_mul_I_sq] at h
  have hden : s.re - 1 ≤ ‖((1 : ℂ) + (y : ℂ) * I) - s‖ := by
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [Complex.sub_re, hre, abs_of_nonpos (by linarith : (1:ℝ) - s.re ≤ 0)]
    linarith
  have hdenpos : (0:ℝ) < s.re - 1 := by linarith
  have hnormpos : (0:ℝ) < ‖((1 : ℂ) + (y : ℂ) * I) - s‖ := lt_of_lt_of_le hdenpos hden
  have hCnn : 0 ≤ C / (1 + y ^ 2) := le_trans (norm_nonneg _) hnum
  rw [lineKernel, norm_div]
  calc ‖φ ((1:ℂ) + (y:ℂ) * I)‖ / ‖((1:ℂ) + (y:ℂ) * I) - s‖
      ≤ (C / (1 + y ^ 2)) / ‖((1:ℂ) + (y:ℂ) * I) - s‖ := by gcongr
    _ ≤ (C / (1 + y ^ 2)) / (s.re - 1) := by gcongr

theorem norm_mk_sq (x y : ℝ) : ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp
  ring

theorem continuousOn_of_analyticOn_halfPlane {φ : ℂ → ℂ}
    (hφ : ∀ z : ℂ, 1 ≤ z.re → AnalyticAt ℂ φ z) :
    ContinuousOn φ {z : ℂ | 1 ≤ z.re} :=
  fun z hz => ((hφ z hz).continuousAt).continuousWithinAt

theorem nonneg_of_halfPlane_bound {φ : ℂ → ℂ} {C : ℝ}
    (hbound : ∀ z : ℂ, 1 ≤ z.re → ‖φ z‖ ≤ C / ‖z‖ ^ 2) : 0 ≤ C := by
  have h := hbound 1 (by simp)
  simp only [norm_one, one_pow, div_one] at h
  exact le_trans (norm_nonneg _) h

theorem continuous_lineKernel {φ : ℂ → ℂ} (hφ : ∀ z : ℂ, 1 ≤ z.re → AnalyticAt ℂ φ z)
    {s : ℂ} (hs : 1 < s.re) : Continuous (lineKernel φ s) := by
  have hmaps : ∀ y : ℝ, (1 : ℂ) + (y : ℂ) * I ∈ {z : ℂ | 1 ≤ z.re} := by
    intro y
    simp [Set.mem_setOf_eq]
  have hnum : Continuous fun y : ℝ => φ ((1 : ℂ) + (y : ℂ) * I) :=
    (continuousOn_of_analyticOn_halfPlane hφ).comp_continuous continuous_lineParam hmaps
  have hden : Continuous fun y : ℝ => ((1 : ℂ) + (y : ℂ) * I) - s := by fun_prop
  have hne : ∀ y : ℝ, ((1 : ℂ) + (y : ℂ) * I) - s ≠ 0 := by
    intro y h
    have hre : (((1 : ℂ) + (y : ℂ) * I) - s).re = 1 - s.re := by simp
    rw [h] at hre
    simp at hre
    linarith
  exact hnum.div hden hne

theorem integrable_lineKernel {φ : ℂ → ℂ} {C : ℝ}
    (hφ : ∀ z : ℂ, 1 ≤ z.re → AnalyticAt ℂ φ z)
    (hbound : ∀ z : ℂ, 1 ≤ z.re → ‖φ z‖ ≤ C / ‖z‖ ^ 2)
    {s : ℂ} (hs : 1 < s.re) :
    Integrable (lineKernel φ s) := by
  have hdenpos : (0:ℝ) < s.re - 1 := by linarith
  have henv : Integrable fun y : ℝ => C / (1 + y ^ 2) / (s.re - 1) := by
    have h := integrable_inv_one_add_sq
    have heq : (fun y : ℝ => C / (1 + y ^ 2) / (s.re - 1))
        = fun y : ℝ => (C / (s.re - 1)) * (1 + y ^ 2)⁻¹ := by
      funext y
      field_simp
    rw [heq]
    exact h.const_mul _
  refine Integrable.mono' henv (continuous_lineKernel hφ hs).aestronglyMeasurable ?_
  filter_upwards with y
  exact norm_lineKernel_le hbound hs y

/-! ### The moving edges -/

theorem norm_horizontal_edge_le {φ : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z : ℂ, 1 ≤ z.re → ‖φ z‖ ≤ C / ‖z‖ ^ 2)
    {s : ℂ} {R c : ℝ} (hR : 1 ≤ R) (hc : c ^ 2 = R ^ 2) (hcabs : |c| = R)
    (hcs : |s.im| < R) :
    ‖∫ x in (1:ℝ)..R, φ ((x : ℂ) + (c : ℂ) * I) * (((x : ℂ) + (c : ℂ) * I) - s)⁻¹‖
      ≤ C / R ^ 2 / (R - |s.im|) * R := by
  have hRpos : (0:ℝ) < R := by linarith
  have hgap : (0:ℝ) < R - |s.im| := by linarith
  have hpt : ∀ x ∈ Set.uIoc (1:ℝ) R,
      ‖φ ((x : ℂ) + (c : ℂ) * I) * (((x : ℂ) + (c : ℂ) * I) - s)⁻¹‖
        ≤ C / R ^ 2 / (R - |s.im|) := by
    intro x hx
    rw [Set.uIoc_of_le hR] at hx
    have hx1 : (1:ℝ) ≤ x := le_of_lt hx.1
    have hre : ((x : ℂ) + (c : ℂ) * I).re = x := by simp
    have hnumsq : ‖(x : ℂ) + (c : ℂ) * I‖ ^ 2 = x ^ 2 + c ^ 2 := norm_mk_sq x c
    have hnum : ‖φ ((x : ℂ) + (c : ℂ) * I)‖ ≤ C / R ^ 2 := by
      refine le_trans (hbound _ (by rw [hre]; exact hx1)) ?_
      rw [hnumsq, hc]
      have hxsq : R ^ 2 ≤ x ^ 2 + R ^ 2 := by nlinarith
      have hRsqpos : (0:ℝ) < R ^ 2 := by positivity
      exact div_le_div_of_nonneg_left hC hRsqpos hxsq
    have hden : R - |s.im| ≤ ‖((x : ℂ) + (c : ℂ) * I) - s‖ := by
      refine le_trans ?_ (Complex.abs_im_le_norm _)
      have him : (((x : ℂ) + (c : ℂ) * I) - s).im = c - s.im := by simp
      rw [him]
      have := abs_sub_abs_le_abs_sub c s.im
      rw [hcabs] at this
      linarith
    have hdenpos : (0:ℝ) < ‖((x : ℂ) + (c : ℂ) * I) - s‖ := lt_of_lt_of_le hgap hden
    rw [norm_mul, norm_inv]
    calc ‖φ ((x : ℂ) + (c : ℂ) * I)‖ * ‖((x : ℂ) + (c : ℂ) * I) - s‖⁻¹
        ≤ (C / R ^ 2) * ‖((x : ℂ) + (c : ℂ) * I) - s‖⁻¹ := by
          gcongr
      _ ≤ (C / R ^ 2) * (R - |s.im|)⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [inv_eq_one_div, inv_eq_one_div]
          gcongr
      _ = C / R ^ 2 / (R - |s.im|) := by ring
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ R - 1)] at hle
  refine hle.trans ?_
  refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem norm_vertical_edge_le {φ : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z : ℂ, 1 ≤ z.re → ‖φ z‖ ≤ C / ‖z‖ ^ 2)
    {s : ℂ} {R : ℝ} (hR : 1 ≤ R) (hcs : s.re < R) :
    ‖∫ y in (-R:ℝ)..R, φ ((R : ℂ) + (y : ℂ) * I) * (((R : ℂ) + (y : ℂ) * I) - s)⁻¹‖
      ≤ C / R ^ 2 / (R - s.re) * (2 * R) := by
  have hRpos : (0:ℝ) < R := by linarith
  have hgap : (0:ℝ) < R - s.re := by linarith
  have hpt : ∀ y ∈ Set.uIoc (-R:ℝ) R,
      ‖φ ((R : ℂ) + (y : ℂ) * I) * (((R : ℂ) + (y : ℂ) * I) - s)⁻¹‖
        ≤ C / R ^ 2 / (R - s.re) := by
    intro y _
    have hre : ((R : ℂ) + (y : ℂ) * I).re = R := by simp
    have hnumsq : ‖(R : ℂ) + (y : ℂ) * I‖ ^ 2 = R ^ 2 + y ^ 2 := norm_mk_sq R y
    have hnum : ‖φ ((R : ℂ) + (y : ℂ) * I)‖ ≤ C / R ^ 2 := by
      refine le_trans (hbound _ (by rw [hre]; linarith)) ?_
      rw [hnumsq]
      have hxsq : R ^ 2 ≤ R ^ 2 + y ^ 2 := by nlinarith
      have hRsqpos : (0:ℝ) < R ^ 2 := by positivity
      exact div_le_div_of_nonneg_left hC hRsqpos hxsq
    have hden : R - s.re ≤ ‖((R : ℂ) + (y : ℂ) * I) - s‖ := by
      refine le_trans ?_ (le_trans (le_abs_self _) (Complex.abs_re_le_norm _))
      have hre2 : (((R : ℂ) + (y : ℂ) * I) - s).re = R - s.re := by simp
      rw [hre2]
    have hdenpos : (0:ℝ) < ‖((R : ℂ) + (y : ℂ) * I) - s‖ := lt_of_lt_of_le hgap hden
    rw [norm_mul, norm_inv]
    calc ‖φ ((R : ℂ) + (y : ℂ) * I)‖ * ‖((R : ℂ) + (y : ℂ) * I) - s‖⁻¹
        ≤ (C / R ^ 2) * ‖((R : ℂ) + (y : ℂ) * I) - s‖⁻¹ := by
          gcongr
      _ ≤ (C / R ^ 2) * (R - s.re)⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [inv_eq_one_div, inv_eq_one_div]
          gcongr
      _ = C / R ^ 2 / (R - s.re) := by ring
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ R - -R)] at hle
  refine hle.trans (le_of_eq ?_)
  ring

/-! ### The representation -/

theorem tendsto_edgeBound (C a : ℝ) (k : ℝ) :
    Tendsto (fun R : ℝ => C / R ^ 2 / (R - a) * (k * R)) atTop (nhds 0) := by
  have hmul : Tendsto (fun R : ℝ => R * (R - a)) atTop atTop :=
    Filter.tendsto_id.atTop_mul_atTop₀ (Filter.tendsto_atTop_add_const_right _ (-a) tendsto_id)
  have hzero : Tendsto (fun R : ℝ => (C * k) / (R * (R - a))) atTop (nhds 0) :=
    hmul.const_div_atTop _
  refine hzero.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ), eventually_gt_atTop a] with R hR hRa
  have hRne : R ≠ 0 := ne_of_gt hR
  have hRane : R - a ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    linarith [h ▸ hRa]
  field_simp

/-- **The Cauchy representation on the closed half plane.**  A function analytic on `Re s ≥ 1` and
decaying like `‖s‖⁻²` there is reproduced by its boundary values on the line `Re s = 1`. -/
theorem halfPlane_cauchy_representation {φ : ℂ → ℂ} {C : ℝ}
    (hφ : ∀ z : ℂ, 1 ≤ z.re → AnalyticAt ℂ φ z)
    (hbound : ∀ z : ℂ, 1 ≤ z.re → ‖φ z‖ ≤ C / ‖z‖ ^ 2)
    {s : ℂ} (hs : 1 < s.re) :
    (∫ (y : ℝ), lineKernel φ s y) = -(2 * Real.pi) * φ s := by
  have hC : 0 ≤ C := nonneg_of_halfPlane_bound hbound
  have hint : Integrable (lineKernel φ s) := integrable_lineKernel hφ hbound hs
  set g : ℂ → ℂ := fun z => φ z * (z - s)⁻¹ with hgdef
  set B : ℝ → ℂ := fun R => ∫ x in (1:ℝ)..R, g ((x : ℂ) + ((-R : ℝ) : ℂ) * I) with hBdef
  set T : ℝ → ℂ := fun R => ∫ x in (1:ℝ)..R, g ((x : ℂ) + ((R : ℝ) : ℂ) * I) with hTdef
  set Rt : ℝ → ℂ := fun R => ∫ y in (-R:ℝ)..R, g (((R : ℝ) : ℂ) + (y : ℂ) * I) with hRtdef
  set L : ℝ → ℂ := fun R => ∫ y in (-R:ℝ)..R, g ((1 : ℂ) + (y : ℂ) * I) with hLdef
  have hLeq : ∀ R : ℝ, L R = ∫ y in (-R:ℝ)..R, lineKernel φ s y := by
    intro R
    rw [hLdef]
    exact intervalIntegral.integral_congr fun y _ => by rw [hgdef, lineKernel, div_eq_mul_inv]
  -- the rectangle identity
  have hrect : ∀ R : ℝ, max (max s.re |s.im|) 1 + 1 ≤ R →
      (B R - T R) + I * Rt R - I * L R = 2 * Real.pi * I * φ s := by
    intro R hR
    have hR1 : (1:ℝ) ≤ R := by
      have := le_max_right (max s.re |s.im|) 1
      linarith
    have hRre : s.re < R := by
      have h1 := le_max_left s.re |s.im|
      have h2 := le_max_left (max s.re |s.im|) 1
      linarith
    have hRim : |s.im| < R := by
      have h1 := le_max_right s.re |s.im|
      have h2 := le_max_left (max s.re |s.im|) 1
      linarith
    have himlt : -R < s.im := by
      have := neg_abs_le s.im
      linarith
    have himgt : s.im < R := by
      have := le_abs_self s.im
      linarith
    set z₁ : ℂ := (1 : ℂ) + ((-R : ℝ) : ℂ) * I with hz₁
    set z₂ : ℂ := ((R : ℝ) : ℂ) + ((R : ℝ) : ℂ) * I with hz₂
    have hz₁re : z₁.re = 1 := by rw [hz₁]; simp
    have hz₁im : z₁.im = -R := by rw [hz₁]; simp
    have hz₂re : z₂.re = R := by rw [hz₂]; simp
    have hz₂im : z₂.im = R := by rw [hz₂]; simp
    have hana : AnalyticOnNhd ℂ φ {z : ℂ | 1 ≤ z.re} := fun z hz => hφ z hz
    have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ {z : ℂ | 1 ≤ z.re} := by
      intro w hw
      rw [Complex.mem_reProdIm] at hw
      have := hw.1
      rw [hz₁re, hz₂re, uIcc_of_le hR1] at this
      exact this.1
    have hkey := RHTower.rectIntegral_cauchyFormula_of_analyticOnNhd (g := φ) (p := s)
      (z₁ := z₁) (z₂ := z₂) hana hsub
      (by rw [hz₁re]; exact hs) (by rw [hz₂re]; exact hRre)
      (by rw [hz₁im]; exact himlt) (by rw [hz₂im]; exact himgt)
    rw [RHTower.rectIntegral, hz₁re, hz₂re, hz₁im, hz₂im] at hkey
    simp only [smul_eq_mul] at hkey
    rw [hBdef, hTdef, hRtdef, hLdef]
    simpa using hkey
  -- the moving edges vanish
  have hBlim : Tendsto B atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_edgeBound C |s.im| 1)
    filter_upwards [eventually_ge_atTop (max (max s.re |s.im|) 1 + 1)] with R hR
    have hR1 : (1:ℝ) ≤ R := by
      have := le_max_right (max s.re |s.im|) 1
      linarith
    have hRim : |s.im| < R := by
      have h1 := le_max_right s.re |s.im|
      have h2 := le_max_left (max s.re |s.im|) 1
      linarith
    have hcabs : |(-R : ℝ)| = R := by
      rw [abs_neg, abs_of_nonneg (by linarith)]
    have := norm_horizontal_edge_le hC hbound (R := R) (c := -R) hR1 (by ring) hcabs hRim
    rw [hBdef, hgdef]
    exact le_trans this (le_of_eq (by ring))
  have hTlim : Tendsto T atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_edgeBound C |s.im| 1)
    filter_upwards [eventually_ge_atTop (max (max s.re |s.im|) 1 + 1)] with R hR
    have hR1 : (1:ℝ) ≤ R := by
      have := le_max_right (max s.re |s.im|) 1
      linarith
    have hRim : |s.im| < R := by
      have h1 := le_max_right s.re |s.im|
      have h2 := le_max_left (max s.re |s.im|) 1
      linarith
    have hcabs : |(R : ℝ)| = R := abs_of_nonneg (by linarith)
    have := norm_horizontal_edge_le hC hbound (R := R) (c := R) hR1 rfl hcabs hRim
    rw [hTdef, hgdef]
    exact le_trans this (le_of_eq (by ring))
  have hRtlim : Tendsto Rt atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_edgeBound C s.re 2)
    filter_upwards [eventually_ge_atTop (max (max s.re |s.im|) 1 + 1)] with R hR
    have hR1 : (1:ℝ) ≤ R := by
      have := le_max_right (max s.re |s.im|) 1
      linarith
    have hRre : s.re < R := by
      have h1 := le_max_left s.re |s.im|
      have h2 := le_max_left (max s.re |s.im|) 1
      linarith
    have := norm_vertical_edge_le hC hbound (R := R) hR1 hRre
    rw [hRtdef, hgdef]
    exact this
  set J : ℂ := ∫ (y : ℝ), lineKernel φ s y with hJdef
  have hLlim : Tendsto L atTop (nhds J) :=
    (MeasureTheory.intervalIntegral_tendsto_integral hint Filter.tendsto_neg_atTop_atBot
      Filter.tendsto_id).congr fun R => (hLeq R).symm
  -- pass to the limit
  have hconst : Tendsto (fun R : ℝ => (B R - T R) + I * Rt R - I * L R) atTop
      (nhds (2 * Real.pi * I * φ s)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (max (max s.re |s.im|) 1 + 1)] with R hR
    exact (hrect R hR).symm
  have hlim2 : Tendsto (fun R : ℝ => (B R - T R) + I * Rt R - I * L R) atTop
      (nhds ((0 - 0) + I * 0 - I * J)) :=
    ((hBlim.sub hTlim).add (tendsto_const_nhds.mul hRtlim)).sub (tendsto_const_nhds.mul hLlim)
  have heq := tendsto_nhds_unique hconst hlim2
  have h0 : I * (J + 2 * Real.pi * φ s) = 0 := by
    linear_combination heq
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h1 : J + 2 * Real.pi * φ s = 0 := (mul_eq_zero.mp h0).resolve_left hI
  rw [hJdef] at h1
  linear_combination h1

end GaloisForLFunctions.HTGeometry

end
