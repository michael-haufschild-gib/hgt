import GaloisForLFunctions.RHTower.RectangleCauchyFormulaOn
import GaloisForLFunctions.RHTower.ZetaPoleSplit

/-!
# The Perron rectangle residue

On any axis-aligned rectangle with `0 < Re` on the left edge, `Re > 1`
on the right edge, the real axis strictly between the horizontal
edges, and no zeta zeros in the closed rectangle:

`∮ (−ζ′/ζ)(s)·x^s/s² ds = 2πi·x`.

The integrand splits as `x^s/s²·(s-1)⁻¹ − (Z′/Z)(s)·x^s/s²` with
`Z(s) = (s-1)ζ(s)` entire and zero-free on the rectangle; the first
term winds around the pole `s = 1` with residue `x`, the second is
holomorphic and vanishes by Cauchy–Goursat.
-/

noncomputable section

namespace RHTower

open Complex Set

/-- Analytic edge sections are interval integrable: horizontal form. -/
theorem intervalIntegrable_analytic_horizontal {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) {a b c : ℝ}
    (hmem : ∀ t ∈ Set.uIcc a b, ((t : ℂ) + (c : ℂ) * I) ∈ U) :
    IntervalIntegrable (fun t : ℝ => f ((t : ℂ) + (c : ℂ) * I))
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  exact (ContinuousAt.comp (f := fun t : ℝ => (t : ℂ) + (c : ℂ) * I)
    (x := t) ((hf _ (hmem t ht)).continuousAt)
    ((by fun_prop : Continuous fun t : ℝ =>
      (t : ℂ) + (c : ℂ) * I).continuousAt)).continuousWithinAt

/-- Analytic edge sections are interval integrable: vertical form. -/
theorem intervalIntegrable_analytic_vertical {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) {c a b : ℝ}
    (hmem : ∀ t ∈ Set.uIcc a b, ((c : ℂ) + (t : ℂ) * I) ∈ U) :
    IntervalIntegrable (fun t : ℝ => f ((c : ℂ) + (t : ℂ) * I))
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  exact (ContinuousAt.comp (f := fun t : ℝ => (c : ℂ) + (t : ℂ) * I)
    (x := t) ((hf _ (hmem t ht)).continuousAt)
    ((by fun_prop : Continuous fun t : ℝ =>
      (c : ℂ) + (t : ℂ) * I).continuousAt)).continuousWithinAt

/-- The Perron kernel `x^s/s²` is analytic on the right half-plane. -/
theorem analyticOnNhd_perron_kernel {x : ℝ} (hx : 0 < x) :
    AnalyticOnNhd ℂ (fun s : ℂ => (x : ℂ) ^ s / s ^ (2 : ℕ))
      {s : ℂ | 0 < s.re} := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hx)
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  apply AnalyticAt.div
  · show AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s) z
    rw [show (fun s : ℂ => (x : ℂ) ^ s)
        = fun s : ℂ => Complex.exp (Complex.log (x : ℂ) * s) from
      funext fun s => Complex.cpow_def_of_ne_zero hx0 s]
    exact (Complex.differentiable_exp.comp
      (differentiable_id.const_mul (Complex.log (x : ℂ)))).analyticAt z

  · exact (differentiable_id.pow 2).analyticAt z
  · exact pow_ne_zero 2 hz0

/-- **The Perron rectangle residue**: with no zeta zeros in the closed
rectangle and the pole `1` strictly inside,
`∮ (−ζ′/ζ)·x^s/s² = 2πi·x`. -/
theorem rectIntegral_perron_eq {x : ℝ} (hx : 0 < x) {z₁ z₂ : ℂ}
    (h1 : 0 < z₁.re) (h2 : z₁.re < 1) (h3 : 1 < z₂.re)
    (h4 : z₁.im < 0) (h5 : 0 < z₂.im)
    (hzf : ∀ s : ℂ, s.re ∈ Set.uIcc z₁.re z₂.re →
      s.im ∈ Set.uIcc z₁.im z₂.im → s ≠ 1 → riemannZeta s ≠ 0) :
    rectIntegral (fun s : ℂ =>
        - deriv riemannZeta s / riemannZeta s * ((x : ℂ) ^ s / s ^ (2 : ℕ)))
      z₁ z₂ = 2 * Real.pi * I * x := by
  have hrle : z₁.re ≤ z₂.re := by linarith
  have himle : z₁.im ≤ z₂.im := by linarith
  have hedge_re : ∀ u v : ℝ, ((u : ℂ) + (v : ℂ) * I).re = u := by
    intro u v
    simp
  have hedge_im : ∀ u v : ℝ, ((u : ℂ) + (v : ℂ) * I).im = v := by
    intro u v
    simp
  -- membership of the four edges in the closed rectangle
  have hrb : ∀ t ∈ uIcc z₁.re z₂.re, ((t : ℂ) + (z₁.im : ℂ) * I)
      ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) := by
    intro t ht
    exact Complex.mem_reProdIm.2
      ⟨by rw [hedge_re]; exact ht, by rw [hedge_im]; exact left_mem_uIcc⟩
  have hrt : ∀ t ∈ uIcc z₁.re z₂.re, ((t : ℂ) + (z₂.im : ℂ) * I)
      ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) := by
    intro t ht
    exact Complex.mem_reProdIm.2
      ⟨by rw [hedge_re]; exact ht, by rw [hedge_im]; exact right_mem_uIcc⟩
  have hrr : ∀ t ∈ uIcc z₁.im z₂.im, ((z₂.re : ℂ) + (t : ℂ) * I)
      ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) := by
    intro t ht
    exact Complex.mem_reProdIm.2
      ⟨by rw [hedge_re]; exact right_mem_uIcc, by rw [hedge_im]; exact ht⟩
  have hrl : ∀ t ∈ uIcc z₁.im z₂.im, ((z₁.re : ℂ) + (t : ℂ) * I)
      ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) := by
    intro t ht
    exact Complex.mem_reProdIm.2
      ⟨by rw [hedge_re]; exact left_mem_uIcc, by rw [hedge_im]; exact ht⟩
  -- the rectangle sits in the right half-plane
  have hsub0 : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im)
      ⊆ {s : ℂ | 0 < s.re} := by
    intro s hs
    have hs1 := (Complex.mem_reProdIm.1 hs).1
    rw [uIcc_of_le hrle] at hs1
    exact lt_of_lt_of_le h1 hs1.1
  -- the pole unit is zero-free on the rectangle
  have hsubG : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im)
      ⊆ {s : ℂ | 0 < s.re} ∩ {s : ℂ | zetaPoleUnit s ≠ 0} := by
    intro s hs
    refine ⟨hsub0 hs, ?_⟩
    rcases eq_or_ne s 1 with rfl | hs1
    · simp only [Set.mem_setOf_eq, zetaPoleUnit_one]
      exact one_ne_zero
    · exact zetaPoleUnit_ne_zero hs1
        (hzf s (Complex.mem_reProdIm.1 hs).1
          (Complex.mem_reProdIm.1 hs).2 hs1)
  -- analyticity of the two summands
  have hP : AnalyticOnNhd ℂ
      (fun s : ℂ => (x : ℂ) ^ s / s ^ (2 : ℕ) * (s - 1)⁻¹)
      ({s : ℂ | 0 < s.re} \ {1}) := by
    intro z hz
    exact (analyticOnNhd_perron_kernel hx z hz.1).mul
      (((differentiable_id.sub_const 1).analyticAt z).inv
        (sub_ne_zero.2 hz.2))
  have hG : AnalyticOnNhd ℂ
      (fun s : ℂ => - (deriv zetaPoleUnit s / zetaPoleUnit s)
        * ((x : ℂ) ^ s / s ^ (2 : ℕ)))
      ({s : ℂ | 0 < s.re} ∩ {s : ℂ | zetaPoleUnit s ≠ 0}) := by
    intro z hz
    exact (((differentiable_zetaPoleUnit.analyticAt z).deriv.div
      (differentiable_zetaPoleUnit.analyticAt z) hz.2).neg).mul
      (analyticOnNhd_perron_kernel hx z hz.1)
  -- edge membership in the punctured rectangle and in the zero-free set
  have hSb : ∀ t ∈ uIcc z₁.re z₂.re, ((t : ℂ) + (z₁.im : ℂ) * I)
      ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) \ {1} := by
    intro t ht
    refine ⟨hrb t ht, ?_⟩
    intro hone
    have him := congrArg Complex.im hone
    rw [hedge_im, Complex.one_im] at him
    linarith
  have hSt : ∀ t ∈ uIcc z₁.re z₂.re, ((t : ℂ) + (z₂.im : ℂ) * I)
      ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) \ {1} := by
    intro t ht
    refine ⟨hrt t ht, ?_⟩
    intro hone
    have him := congrArg Complex.im hone
    rw [hedge_im, Complex.one_im] at him
    linarith
  have hSr : ∀ t ∈ uIcc z₁.im z₂.im, ((z₂.re : ℂ) + (t : ℂ) * I)
      ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) \ {1} := by
    intro t ht
    refine ⟨hrr t ht, ?_⟩
    intro hone
    have hre := congrArg Complex.re hone
    rw [hedge_re, Complex.one_re] at hre
    linarith
  have hSl : ∀ t ∈ uIcc z₁.im z₂.im, ((z₁.re : ℂ) + (t : ℂ) * I)
      ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) \ {1} := by
    intro t ht
    refine ⟨hrl t ht, ?_⟩
    intro hone
    have hre := congrArg Complex.re hone
    rw [hedge_re, Complex.one_re] at hre
    linarith
  have hSP : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) \ {1}
      ⊆ {s : ℂ | 0 < s.re} \ {1} := fun s hs => ⟨hsub0 hs.1, hs.2⟩
  -- the pointwise split on the punctured rectangle
  have hpt : ∀ s ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) \ {1},
      - deriv riemannZeta s / riemannZeta s * ((x : ℂ) ^ s / s ^ (2 : ℕ))
        = (x : ℂ) ^ s / s ^ (2 : ℕ) * (s - 1)⁻¹
          + - (deriv zetaPoleUnit s / zetaPoleUnit s)
            * ((x : ℂ) ^ s / s ^ (2 : ℕ)) := by
    intro s hs
    have hs1 : s ≠ 1 := hs.2
    have hζ := hzf s (Complex.mem_reProdIm.1 hs.1).1
      (Complex.mem_reProdIm.1 hs.1).2 hs1
    calc - deriv riemannZeta s / riemannZeta s * ((x : ℂ) ^ s / s ^ (2 : ℕ))
        = - (deriv riemannZeta s / riemannZeta s)
            * ((x : ℂ) ^ s / s ^ (2 : ℕ)) := by
          rw [neg_div]
      _ = (1 / (s - 1) - deriv zetaPoleUnit s / zetaPoleUnit s)
            * ((x : ℂ) ^ s / s ^ (2 : ℕ)) := by
          rw [neg_zeta_logDeriv_eq hs1 hζ]
      _ = (x : ℂ) ^ s / s ^ (2 : ℕ) * (s - 1)⁻¹
            + - (deriv zetaPoleUnit s / zetaPoleUnit s)
              * ((x : ℂ) ^ s / s ^ (2 : ℕ)) := by
          ring
  -- split the boundary integral
  rw [rectIntegral_congr hpt hSb hSt hSr hSl]
  rw [rectIntegral_add
    (intervalIntegrable_analytic_horizontal (hP.mono hSP)
      fun t ht => hSb t ht)
    (intervalIntegrable_analytic_horizontal (hG.mono hsubG)
      fun t ht => hrb t ht)
    (intervalIntegrable_analytic_horizontal (hP.mono hSP)
      fun t ht => hSt t ht)
    (intervalIntegrable_analytic_horizontal (hG.mono hsubG)
      fun t ht => hrt t ht)
    (intervalIntegrable_analytic_vertical (hP.mono hSP)
      fun t ht => hSr t ht)
    (intervalIntegrable_analytic_vertical (hG.mono hsubG)
      fun t ht => hrr t ht)
    (intervalIntegrable_analytic_vertical (hP.mono hSP)
      fun t ht => hSl t ht)
    (intervalIntegrable_analytic_vertical (hG.mono hsubG)
      fun t ht => hrl t ht)]
  -- the regular part vanishes
  rw [rectIntegral_eq_zero_of_analyticOnNhd hsubG hG, add_zero]
  -- the pole part winds once around `1`
  have hpole := rectIntegral_cauchyFormula_analyticOnNhd
    (g := fun s : ℂ => (x : ℂ) ^ s / s ^ (2 : ℕ))
    (U := {s : ℂ | 0 < s.re}) (p := 1) hsub0
    (analyticOnNhd_perron_kernel hx)
    (by rw [Complex.one_re]; exact h2)
    (by rw [Complex.one_re]; exact h3)
    (by rw [Complex.one_im]; exact h4)
    (by rw [Complex.one_im]; exact h5)
  rw [hpole]
  simp [Complex.cpow_one]

end RHTower
