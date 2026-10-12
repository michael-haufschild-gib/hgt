import GaloisForLFunctions.RHTower.XiLineStripConvexity
import GaloisForLFunctions.RHTower.KiKimLeeRelativeBounds

/-!
# The strip terms of the one-sided Gaussian average of `ξ`, sharp form

Notation of `KiKimLeeRelativeBounds`: `α = ½ log(X/2π)`, `F(w) = ξ(½ + w + iX)`, `u = y + 2tα`,
`g_t(v) = (4πt)^{−½}e^{−v²/4t}`, `P = ‖F(u)‖e^{−tα²}`. Put `c = 2tα` (the heat depth `t log(X/2π)`).

The corpus bounds the strip `0 < w ≤ 9/2` with `g_t ≤ (4πt)^{−½}` and a polynomial strip comparison.
That forces `c ≥ 40`. Here the Gaussian factor is kept, and the strip comparison is the convexity
bound `‖F(w)‖ ≤ K X^{(½+η−w)/2}(X/2π)^{(w−u)/2}‖F(u)‖` (`exists_norm_xiLine_le_strip_convexity`).
Completing the square,

`g_t(w−y)‖F(w)‖ ≤ (4πt)^{−½} K (2π)^{(½+η)/2} · exp(B/(4t)) · P`,
`B = −(w−y)² + 2c(½+η−y) − c²`.

**The exponent** (`strip_bracket_le`): for `|y| ≤ ½`, `w ≥ 0`, `c ≥ 1`,
`B ≤ −¼ + 2c(1+η) − c²`. The worst case is `y = −½`, `w = 0`. So `B ≤ −m` as soon as
`c² − 2c(1+η) + ¼ ≥ m > 0`, i.e. `c > 1 + η + √((1+η)² − ¼)` (→ `1 + √3/2` as `η → 0`).

**Theorem** (`sharp_strip_terms_le`). Let `w₁ = ½ + η`. All three strip terms of the window estimates
(the plain strip integral, the slope-weighted strip integral, and the boundary value at `w₁`) are at
most `P · sharpStripErr`, where `sharpStripErr = (1+η)((1+η)/(2t) + α + 1)(4πt)^{−½}K(2π)^{(½+η)/2}e^{−m/4t}`.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

/-- **The strip exponent.** -/
theorem strip_bracket_le {c η y w : ℝ} (hc : 1 ≤ c) (hy : |y| ≤ 1 / 2) (hw : 0 ≤ w) :
    -(w - y) ^ 2 + 2 * c * (1 / 2 + η - y) - c ^ 2 ≤ -(1 / 4) + 2 * c * (1 + η) - c ^ 2 := by
  have hy1 := (abs_le.mp hy).1
  have hy2 := (abs_le.mp hy).2
  rcases le_or_gt y 0 with hy0 | hy0
  · -- `−(w−y)² ≤ −y²` and `−y² − 2cy ≤ −¼ + c` on `[−½, 0]`
    have h1 : y ^ 2 ≤ (w - y) ^ 2 := by nlinarith
    nlinarith
  · nlinarith [sq_nonneg (w - y)]

/-- The sharp strip error. -/
def sharpStripErr (K η m t α : ℝ) : ℝ :=
  (1 + η) * ((1 + η) / (2 * t) + α + 1) * ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * K *
    (2 * Real.pi) ^ ((1 / 2 + η) / 2) * Real.exp (-(m / (4 * t))))

/-- **The pointwise strip bound.** -/
theorem gaussDensity_mul_norm_xiLine_le_sharp {K η m t X y w : ℝ} (ht : 0 < t)
    (hK : ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + η → 1 ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤
        K * X ^ ((1 / 2 + η - w) / 2) * (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K) (hX : 16 ≤ X) (hy : |y| ≤ 1 / 2)
    (hc1 : 3 / 2 ≤ 2 * t * (horizontalSlope X).re)
    (hcX : y + 2 * t * (horizontalSlope X).re ≤ X)
    (hm : m ≤ (2 * t * (horizontalSlope X).re) ^ 2 -
      2 * (2 * t * (horizontalSlope X).re) * (1 + η) + 1 / 4)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1 / 2 + η) :
    gaussDensity t (w - y) * ‖xiLine X w‖ ≤
      (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * K * (2 * Real.pi) ^ ((1 / 2 + η) / 2) *
        Real.exp (-(m / (4 * t))) *
        (‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp (-(t * (horizontalSlope X).re ^ 2))) := by
  set α := (horizontalSlope X).re with hα
  set u := y + 2 * t * α with hu
  set c := 2 * t * α with hc
  set N := ‖xiLine X u‖ with hN
  have hX0 : 0 < X := by linarith
  have hy1 := (abs_le.mp hy).1
  have hu1 : 1 ≤ u := by rw [hu]; linarith
  have hF := hK X w u hX hw0 hw1 hu1 hcX
  -- rewrite the powers of `X` through `X = 2π e^{2α}`
  have hXe : X / (2 * Real.pi) = Real.exp (2 * α) := by
    have := height_eq hX0
    rw [← hα] at this
    rw [this]; field_simp
  have hpow1 : (X / (2 * Real.pi)) ^ ((w - u) / 2) = Real.exp (α * (w - u)) := by
    rw [hXe, ← Real.exp_mul]; congr 1; ring
  have hXsplit : X = (2 * Real.pi) * (X / (2 * Real.pi)) := by field_simp
  have hpow2 : X ^ ((1 / 2 + η - w) / 2) ≤
      (2 * Real.pi) ^ ((1 / 2 + η) / 2) * Real.exp (α * (1 / 2 + η - w)) := by
    rw [hXsplit, Real.mul_rpow (by positivity) (by positivity), hXe, ← Real.exp_mul]
    have e : 2 * α * ((1 / 2 + η - w) / 2) = α * (1 / 2 + η - w) := by ring
    rw [e]
    gcongr
    · linarith [Real.pi_gt_three]
    · linarith
  -- the Gaussian
  have hg : gaussDensity t (w - y) =
      (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-((w - y) ^ 2 / (4 * t))) := rfl
  -- the exponent
  have hcc : 1 ≤ c := by linarith
  have hB := strip_bracket_le (η := η) hcc hy hw0
  have hexp : Real.exp (-((w - y) ^ 2 / (4 * t))) * Real.exp (α * (1 / 2 + η - w)) *
      Real.exp (α * (w - u)) ≤ Real.exp (-(m / (4 * t))) * Real.exp (-(t * α ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hαt : α = c / (2 * t) := by rw [hc]; field_simp
    have huc : u = y + c := by rw [hu, hc]
    have h4t : 0 < 4 * t := by positivity
    have hL : -((w - y) ^ 2 / (4 * t)) + α * (1 / 2 + η - w) + α * (w - u) =
        (-(w - y) ^ 2 + 2 * c * (1 / 2 + η - y) - c ^ 2 - c ^ 2) / (4 * t) := by
      rw [huc, hαt]; field_simp; ring
    have hR : -(m / (4 * t)) + -(t * α ^ 2) = (-m - c ^ 2) / (4 * t) := by
      rw [hαt]; field_simp; ring
    rw [hL, hR]
    apply div_le_div_of_nonneg_right _ h4t.le
    linarith
  have hG0 : 0 ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) := by positivity
  have hN0 : 0 ≤ N := norm_nonneg _
  calc gaussDensity t (w - y) * ‖xiLine X w‖
      ≤ ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-((w - y) ^ 2 / (4 * t)))) *
          (K * ((2 * Real.pi) ^ ((1 / 2 + η) / 2) * Real.exp (α * (1 / 2 + η - w))) *
            Real.exp (α * (w - u)) * N) := by
        rw [hg]
        refine mul_le_mul_of_nonneg_left (hF.trans ?_) (by positivity)
        rw [hpow1]
        gcongr
    _ = (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * K * (2 * Real.pi) ^ ((1 / 2 + η) / 2) *
          (Real.exp (-((w - y) ^ 2 / (4 * t))) * Real.exp (α * (1 / 2 + η - w)) *
            Real.exp (α * (w - u))) * N := by ring
    _ ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * K * (2 * Real.pi) ^ ((1 / 2 + η) / 2) *
          (Real.exp (-(m / (4 * t))) * Real.exp (-(t * α ^ 2))) * N := by gcongr
    _ = _ := by ring

/-- **The three strip terms, sharp form.** -/
theorem sharp_strip_terms_le {K η m t X y : ℝ} (ht : 0 < t) (hη : 0 < η)
    (hK : ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + η → 1 ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤
        K * X ^ ((1 / 2 + η - w) / 2) * (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K) (hX : 16 ≤ X) (hy : |y| ≤ 1 / 2) (hα : 0 ≤ (horizontalSlope X).re)
    (hc1 : 3 / 2 ≤ 2 * t * (horizontalSlope X).re)
    (hcX : y + 2 * t * (horizontalSlope X).re ≤ X)
    (hm : m ≤ (2 * t * (horizontalSlope X).re) ^ 2 -
      2 * (2 * t * (horizontalSlope X).re) * (1 + η) + 1 / 4) :
    (∫ w in Ioc (0 : ℝ) (1 / 2 + η), (|(w - y) / (2 * t)| + ‖horizontalSlope X‖) *
        gaussDensity t (w - y) * ‖xiLine X w‖) ≤
      ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-(t * (horizontalSlope X).re ^ 2)) *
        sharpStripErr K η m t (horizontalSlope X).re ∧
    (∫ w in Ioc (0 : ℝ) (1 / 2 + η), gaussDensity t (w - y) * ‖xiLine X w‖) ≤
      ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-(t * (horizontalSlope X).re ^ 2)) *
        sharpStripErr K η m t (horizontalSlope X).re ∧
    gaussDensity t (1 / 2 + η - y) * ‖xiLine X (1 / 2 + η)‖ ≤
      ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-(t * (horizontalSlope X).re ^ 2)) *
        sharpStripErr K η m t (horizontalSlope X).re := by
  set α := (horizontalSlope X).re with hαdef
  set P := ‖xiLine X (y + 2 * t * α)‖ * Real.exp (-(t * α ^ 2)) with hP
  set Q := (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * K * (2 * Real.pi) ^ ((1 / 2 + η) / 2) *
    Real.exp (-(m / (4 * t))) with hQ
  set A := (1 + η) / (2 * t) + α + 1 with hA
  have hQ0 : 0 ≤ Q := by positivity
  have hP0 : 0 ≤ P := by positivity
  have hA1 : 1 ≤ A := by
    have : 0 ≤ (1 + η) / (2 * t) := by positivity
    linarith
  have hpt : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + η), gaussDensity t (w - y) * ‖xiLine X w‖ ≤ Q * P :=
    fun w hw => gaussDensity_mul_norm_xiLine_le_sharp ht hK hK0 hX hy hc1 hcX hm hw.1 hw.2
  have hslope : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + η),
      (|(w - y) / (2 * t)| + ‖horizontalSlope X‖) * gaussDensity t (w - y) * ‖xiLine X w‖ ≤
        A * (Q * P) := by
    intro w hw
    have hwt : |(w - y) / (2 * t)| ≤ (1 + η) / (2 * t) := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * t)]
      gcongr
      rw [abs_le] at hy ⊢
      constructor <;> linarith [hw.1, hw.2]
    have ha := norm_horizontalSlope_le hα
    have hAB : |(w - y) / (2 * t)| + ‖horizontalSlope X‖ ≤ A := by rw [hA]; linarith
    rw [mul_assoc]
    have hGF : 0 ≤ gaussDensity t (w - y) * ‖xiLine X w‖ :=
      mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _)
    exact mul_le_mul hAB (hpt w hw) hGF (by linarith)
  have hvol : volume.real (Ioc (0 : ℝ) (1 / 2 + η)) = 1 / 2 + η := by
    rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hint_bound : ∀ (f : ℝ → ℝ) (B : ℝ), (∀ w, 0 ≤ f w) →
      (∀ w ∈ Icc (0 : ℝ) (1 / 2 + η), f w ≤ B) →
      ∫ w in Ioc (0 : ℝ) (1 / 2 + η), f w ≤ (1 / 2 + η) * B := by
    intro f B hf0 hfB
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := f) (C := B)
      measure_Ioc_lt_top (fun w hw => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 w)]; exact hfB w (Ioc_subset_Icc_self hw))
    rw [hvol] at h
    have := le_abs_self (∫ w in Ioc (0 : ℝ) (1 / 2 + η), f w)
    rw [← Real.norm_eq_abs] at this
    linarith
  have herr : sharpStripErr K η m t α = (1 + η) * A * Q := by
    rw [sharpStripErr, hA, hQ]
  have hQP : 0 ≤ Q * P := mul_nonneg hQ0 hP0
  refine ⟨?_, ?_, ?_⟩
  · refine (hint_bound _ _ (fun w => mul_nonneg (mul_nonneg (by positivity)
      (gaussDensity_pos ht _).le) (norm_nonneg _)) hslope).trans ?_
    rw [herr]
    have hAQP : 0 ≤ A * (Q * P) := mul_nonneg (by linarith) hQP
    have h2 : (1 / 2 + η) * (A * (Q * P)) ≤ (1 + η) * (A * (Q * P)) :=
      mul_le_mul_of_nonneg_right (by linarith) hAQP
    calc (1 / 2 + η) * (A * (Q * P)) ≤ (1 + η) * (A * (Q * P)) := h2
      _ = P * ((1 + η) * A * Q) := by ring
  · refine (hint_bound _ _ (fun w => mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _))
      hpt).trans ?_
    rw [herr]
    have h1 : Q * P ≤ A * (Q * P) := le_mul_of_one_le_left hQP hA1
    nlinarith
  · have h0 := hpt (1 / 2 + η) ⟨by linarith, le_rfl⟩
    have h1 : Q * P ≤ A * (Q * P) := le_mul_of_one_le_left hQP hA1
    have h2 : A * (Q * P) ≤ (1 + η) * (A * (Q * P)) := le_mul_of_one_le_left (by positivity) (by linarith)
    rw [herr]
    calc gaussDensity t (1 / 2 + η - y) * ‖xiLine X (1 / 2 + η)‖ ≤ Q * P := h0
      _ ≤ P * ((1 + η) * A * Q) := by nlinarith

end

end RHTower.DeBruijn
