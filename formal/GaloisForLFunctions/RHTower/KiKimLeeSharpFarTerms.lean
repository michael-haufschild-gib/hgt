import GaloisForLFunctions.RHTower.KiKimLeeSharpTerms

/-!
# The far terms of the one-sided Gaussian average, with a general bound at the far end

The corpus far-region estimates (`far_integrand_le`, `far_terms_le`) obtain `‖F(W)‖` at
`W = 2tα + α²` from the log-linear model on a window starting at `9/2`. Here `‖F(W)‖` is a
hypothesis, `‖F(W)‖ ≤ e^b ‖F(u)‖ e^{(W−u)(α+1/8)}`. The conclusions are the corpus ones with
`‖F(u)‖` replaced by `e^b ‖F(u)‖`. The near-window argument supplies the hypothesis with
`b = (9/2)(1/η + 3)` through the split model (`norm_xiLine_le_split_model`), so the far-region
errors stay `kklRC`, `kklRB` up to a constant factor. The proofs are the corpus proofs with this
one change. They use only the growth of `F` beyond `W`, so they hold for any `f` with that growth
(`far_terms_le_of_growth`) and any constant `N` in place of `e^b ‖F(u)‖`.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

/-- **The far integrand**, for any `f` with the growth of `F` beyond `W`. -/
theorem far_integrand_le_of_growth {f : ℝ → ℂ} {N t X y W w : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hX : 200 ≤ X) (hy : |y| ≤ 1 / 2) (hα : 0 ≤ (horizontalSlope X).re) (hN0 : 0 ≤ N)
    (hW9 : 9 / 2 ≤ W)
    (hFWb : ‖f W‖ ≤ N *
      Real.exp ((W - (y + 2 * t * (horizontalSlope X).re)) * ((horizontalSlope X).re + 1 / 8)))
    (hFw : ‖f w‖ ≤ ‖f W‖ *
      Real.exp (((horizontalSlope X).re + 2 + (w + 1 / 2) / (2 * X)) * (w - W)))
    (hw : W < w) :
    (|(w - y) / (2 * t)| + ‖horizontalSlope X‖) * gaussDensity t (w - y) * ‖f w‖ ≤
      2 * Real.exp 1 * (1 / (2 * t) + (horizontalSlope X).re + 1) *
        (N * Real.exp ((W - (y + 2 * t * (horizontalSlope X).re)) * ((horizontalSlope X).re + 1 / 8))) *
        (gaussDensity (2 * t) (w - y) *
          Real.exp ((w - y) + (w - W) * ((horizontalSlope X).re + 2))) := by
  set α := (horizontalSlope X).re with hαdef
  set u := y + 2 * t * α with hudef
  have hy1 := (abs_le.mp hy).1
  have hy2 := (abs_le.mp hy).2
  have hwy : 0 ≤ w - y := by linarith
  -- `F` at `W` and beyond
  have hFW : ‖f W‖ ≤ N * Real.exp ((W - u) * (α + 1 / 8)) := hFWb
  have hexpo : (α + 2 + (w + 1 / 2) / (2 * X)) * (w - W) ≤
      (α + 2) * (w - W) + (w - y) ^ 2 / (8 * t) + 1 := by
    have hA : (w + 1 / 2) * (w - W) ≤ 2 * (w - y) ^ 2 + 2 := by
      nlinarith [sq_nonneg (w - y - (y + 1 / 2)), sq_nonneg (y + 1 / 2)]
    have hX0 : 0 < X := by linarith
    have h8 : 8 * t ≤ X := by linarith
    have hq : (w + 1 / 2) / (2 * X) * (w - W) ≤ ((w - y) ^ 2 + 1) / X := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hX0]
      nlinarith
    have hq2 : ((w - y) ^ 2 + 1) / X ≤ (w - y) ^ 2 / (8 * t) + 1 := by
      rw [add_div]
      have : (w - y) ^ 2 / X ≤ (w - y) ^ 2 / (8 * t) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) h8
      have : 1 / X ≤ 1 := by rw [div_le_one hX0]; linarith
      linarith
    nlinarith
  have hFw' : ‖f w‖ ≤ N * Real.exp ((W - u) * (α + 1 / 8)) *
      (Real.exp ((α + 2) * (w - W)) * Real.exp ((w - y) ^ 2 / (8 * t)) * Real.exp 1) := by
    refine hFw.trans ?_
    rw [← Real.exp_add, ← Real.exp_add]
    calc ‖f W‖ * Real.exp ((α + 2 + (w + 1 / 2) / (2 * X)) * (w - W))
        ≤ N * Real.exp ((W - u) * (α + 1 / 8)) *
            Real.exp ((α + 2) * (w - W) + (w - y) ^ 2 / (8 * t) + 1) := by
          gcongr
    _ = _ := rfl
  -- the weight
  have hweight : |(w - y) / (2 * t)| + ‖horizontalSlope X‖ ≤
      (1 / (2 * t) + α + 1) * Real.exp (w - y) := by
    have he1 : w - y ≤ Real.exp (w - y) := by linarith [Real.add_one_le_exp (w - y)]
    have he2 : 1 ≤ Real.exp (w - y) := Real.one_le_exp hwy
    have ha := norm_horizontalSlope_le hα
    rw [abs_div, abs_of_nonneg hwy, abs_of_pos (by positivity : (0 : ℝ) < 2 * t)]
    have : (w - y) / (2 * t) ≤ 1 / (2 * t) * Real.exp (w - y) := by
      rw [div_eq_mul_one_div, mul_comm]; gcongr
    nlinarith
  have hGabs := gaussDensity_mul_exp_le ht (w - y)
  have hG0 := (gaussDensity_pos ht (w - y)).le
  have hA0 : 0 ≤ |(w - y) / (2 * t)| + ‖horizontalSlope X‖ := by positivity
  calc (|(w - y) / (2 * t)| + ‖horizontalSlope X‖) * gaussDensity t (w - y) * ‖f w‖
      ≤ ((1 / (2 * t) + α + 1) * Real.exp (w - y)) * gaussDensity t (w - y) *
          (N * Real.exp ((W - u) * (α + 1 / 8)) *
            (Real.exp ((α + 2) * (w - W)) * Real.exp ((w - y) ^ 2 / (8 * t)) * Real.exp 1)) := by
        gcongr
    _ = (1 / (2 * t) + α + 1) * Real.exp 1 * (N * Real.exp ((W - u) * (α + 1 / 8))) *
          (Real.exp (w - y) * Real.exp ((α + 2) * (w - W))) *
          (gaussDensity t (w - y) * Real.exp ((w - y) ^ 2 / (8 * t))) := by ring
    _ ≤ (1 / (2 * t) + α + 1) * Real.exp 1 * (N * Real.exp ((W - u) * (α + 1 / 8))) *
          (Real.exp (w - y) * Real.exp ((α + 2) * (w - W))) *
          (2 * gaussDensity (2 * t) (w - y)) := by
        gcongr
    _ = _ := by
        rw [← Real.exp_add, show w - y + (α + 2) * (w - W) = (w - y) + (w - W) * (α + 2) by ring]
        ring

/-- **The far integrand.** -/
theorem far_integrand_le_of_bound {b t X y W w : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (hX : 200 ≤ X)
    (hy : |y| ≤ 1 / 2) (hα : 0 ≤ (horizontalSlope X).re)
    (hW9 : 9 / 2 ≤ W)
    (hFWb : ‖xiLine X W‖ ≤ (Real.exp b * ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖) *
      Real.exp ((W - (y + 2 * t * (horizontalSlope X).re)) * ((horizontalSlope X).re + 1 / 8)))
    (hw : W < w) :
    (|(w - y) / (2 * t)| + ‖horizontalSlope X‖) * gaussDensity t (w - y) * ‖xiLine X w‖ ≤
      2 * Real.exp 1 * (1 / (2 * t) + (horizontalSlope X).re + 1) *
        ((Real.exp b * ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖) *
          Real.exp ((W - (y + 2 * t * (horizontalSlope X).re)) * ((horizontalSlope X).re + 1 / 8))) *
        (gaussDensity (2 * t) (w - y) *
          Real.exp ((w - y) + (w - W) * ((horizontalSlope X).re + 2))) := by
  have hg := norm_xiLine_le_far hX hW9 hw.le
  rw [← horizontalSlope_re] at hg
  exact far_integrand_le_of_growth ht ht8 hX hy hα (by positivity) hW9 hFWb hg hw

/-- **The far terms and the boundary value at `W = 2tα + α²`**, for any `f` with the growth of `F`
beyond `W`. -/
theorem far_terms_le_of_growth {f : ℝ → ℂ} {N t X y : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hX : 200 ≤ X) (hy : |y| ≤ 1 / 2) (hα1 : 1 ≤ (horizontalSlope X).re) (hN0 : 0 ≤ N)
    (hW9 : 9 / 2 ≤ 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2)
    (hFWb : ‖f (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2)‖ ≤
      N * Real.exp ((2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 -
          (y + 2 * t * (horizontalSlope X).re)) * ((horizontalSlope X).re + 1 / 8)))
    (hgrow : ∀ w : ℝ, 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 < w →
      ‖f w‖ ≤ ‖f (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2)‖ *
        Real.exp (((horizontalSlope X).re + 2 + (w + 1 / 2) / (2 * X)) *
          (w - (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2)))) :
    (∫ w in Ioi (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2),
        (|(w - y) / (2 * t)| + ‖horizontalSlope X‖) * gaussDensity t (w - y) * ‖f w‖) ≤
      N * Real.exp (-(t * (horizontalSlope X).re ^ 2)) * kklRC t (horizontalSlope X).re ∧
    (∫ w in Ioi (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2),
        gaussDensity t (w - y) * ‖f w‖) ≤
      N * Real.exp (-(t * (horizontalSlope X).re ^ 2)) * kklRC t (horizontalSlope X).re ∧
    gaussDensity t (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 - y) *
        ‖f (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2)‖ ≤
      N * Real.exp (-(t * (horizontalSlope X).re ^ 2)) * kklRB t (horizontalSlope X).re := by
  have hα : 0 ≤ (horizontalSlope X).re := by linarith
  set α := (horizontalSlope X).re with hαdef
  set u := y + 2 * t * α with hudef
  set W := 2 * t * α + α ^ 2 with hWdef
  have hy1 := (abs_le.mp hy).1
  have hy2 := (abs_le.mp hy).2
  have hWu : u ≤ W := by rw [hudef, hWdef]; nlinarith
  set C := 2 * Real.exp 1 * (1 / (2 * t) + α + 1) * (N * Real.exp ((W - u) * (α + 1 / 8)))
    with hC
  have hC0 : 0 ≤ C := by positivity
  set m : ℝ → ℝ := fun w => C * (gaussDensity (2 * t) (w - y) *
      Real.exp ((w - y) + (w - W) * (α + 2))) with hm
  have hmsplit : ∀ w, m w = C * Real.exp (-y - W * (α + 2)) *
      (gaussDensity (2 * t) (w - y) * Real.exp (w * (α + 3))) := by
    intro w
    simp only [hm]
    rw [show (w - y) + (w - W) * (α + 2) = (-y - W * (α + 2)) + w * (α + 3) by ring, Real.exp_add]
    ring
  have h2t : (0 : ℝ) < 2 * t := by positivity
  have hm_int : Integrable m := by
    refine ((integrable_gaussDensity_sub_mul_rexp h2t y (α + 3)).const_mul
      (C * Real.exp (-y - W * (α + 2)))).congr (Eventually.of_forall fun w => ?_)
    simp only
    rw [hmsplit]
  have hm0 : ∀ w, 0 ≤ m w := fun w => by
    simp only [hm]
    have := (gaussDensity_pos h2t (w - y)).le
    positivity
  have hm_val : ∫ w, m w = C * Real.exp (-y - W * (α + 2)) *
      Real.exp (y * (α + 3) + 2 * t * (α + 3) ^ 2) := by
    simp_rw [hmsplit]
    rw [integral_const_mul, integral_gaussDensity_sub_mul_rexp h2t]
  have hm_le : ∫ w, m w ≤ N * Real.exp (-(t * α ^ 2)) * kklRC t α := by
    rw [hm_val, hC, kklRC]
    have hexp : Real.exp ((W - u) * (α + 1 / 8)) * Real.exp (-y - W * (α + 2)) *
        Real.exp (y * (α + 3) + 2 * t * (α + 3) ^ 2) ≤ Real.exp (-(t * α ^ 2)) *
        Real.exp (-(15 / 8) * α ^ 2 + t * α ^ 2 + 15 / 16 + 8 * t * α + 18 * t) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      rw [hWdef, hudef]
      nlinarith
    have hk : 0 ≤ 2 * Real.exp 1 * (1 / (2 * t) + α + 1) * N := by positivity
    calc 2 * Real.exp 1 * (1 / (2 * t) + α + 1) * (N * Real.exp ((W - u) * (α + 1 / 8))) *
          Real.exp (-y - W * (α + 2)) * Real.exp (y * (α + 3) + 2 * t * (α + 3) ^ 2)
        = (2 * Real.exp 1 * (1 / (2 * t) + α + 1) * N) *
            (Real.exp ((W - u) * (α + 1 / 8)) * Real.exp (-y - W * (α + 2)) *
              Real.exp (y * (α + 3) + 2 * t * (α + 3) ^ 2)) := by ring
      _ ≤ (2 * Real.exp 1 * (1 / (2 * t) + α + 1) * N) * (Real.exp (-(t * α ^ 2)) *
            Real.exp (-(15 / 8) * α ^ 2 + t * α ^ 2 + 15 / 16 + 8 * t * α + 18 * t)) := by
          gcongr
      _ ≤ 2 * (2 * Real.exp 1 * (1 / (2 * t) + α + 1) * N) * (Real.exp (-(t * α ^ 2)) *
            Real.exp (-(15 / 8) * α ^ 2 + t * α ^ 2 + 15 / 16 + 8 * t * α + 18 * t)) := by
          have : 0 ≤ (2 * Real.exp 1 * (1 / (2 * t) + α + 1) * N) * (Real.exp (-(t * α ^ 2)) *
            Real.exp (-(15 / 8) * α ^ 2 + t * α ^ 2 + 15 / 16 + 8 * t * α + 18 * t)) := by
            positivity
          linarith
      _ = _ := by ring
  have hpoint : ∀ w ∈ Ioi W, (|(w - y) / (2 * t)| + ‖horizontalSlope X‖) *
      gaussDensity t (w - y) * ‖f w‖ ≤ m w := fun w hw =>
    far_integrand_le_of_growth ht ht8 hX hy hα hN0 hW9 hFWb (hgrow w hw) hw
  have hone : ∀ w, 1 ≤ |(w - y) / (2 * t)| + ‖horizontalSlope X‖ := by
    intro w
    have := le_norm_horizontalSlope X
    have := abs_nonneg ((w - y) / (2 * t))
    linarith
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans ?_ ((setIntegral_le_integral (s := Ioi W) hm_int
      (Eventually.of_forall hm0)).trans hm_le)
    refine integral_mono_of_nonneg (Eventually.of_forall fun w => ?_) hm_int.integrableOn
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hpoint))
    exact mul_nonneg (mul_nonneg (by positivity) (gaussDensity_pos ht _).le) (norm_nonneg _)
  · refine le_trans ?_ ((setIntegral_le_integral (s := Ioi W) hm_int
      (Eventually.of_forall hm0)).trans hm_le)
    refine integral_mono_of_nonneg (Eventually.of_forall fun w =>
      mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _)) hm_int.integrableOn
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun w hw => ?_))
    have hGF : 0 ≤ gaussDensity t (w - y) * ‖f w‖ :=
      mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _)
    have := hpoint w hw
    have h1 := hone w
    calc gaussDensity t (w - y) * ‖f w‖
        ≤ (|(w - y) / (2 * t)| + ‖horizontalSlope X‖) * (gaussDensity t (w - y) * ‖f w‖) :=
          le_mul_of_one_le_left hGF h1
      _ = _ := by ring
      _ ≤ m w := this
  · have hFW : ‖f W‖ ≤ N * Real.exp ((W - u) * (α + 1 / 8)) := hFWb
    have hWy : α ^ 2 - 1 / 2 ≤ W - y := by rw [hWdef]; nlinarith
    have hα2 : 0 ≤ α ^ 2 - 1 / 2 := by nlinarith
    unfold gaussDensity
    rw [kklRB]
    have hc0 : 0 ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) := by positivity
    have hexp : Real.exp (-((W - y) ^ 2 / (4 * t))) * Real.exp ((W - u) * (α + 1 / 8)) ≤
        Real.exp (-(t * α ^ 2)) * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 / (4 * t)) +
          (α ^ 2 + 1 / 2) * (α + 1 / 8) + t * α ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hsq : (α ^ 2 - 1 / 2) ^ 2 / (4 * t) ≤ (W - y) ^ 2 / (4 * t) := by
        gcongr
      have hWu' : W - u ≤ α ^ 2 + 1 / 2 := by rw [hWdef, hudef]; linarith
      have : (W - u) * (α + 1 / 8) ≤ (α ^ 2 + 1 / 2) * (α + 1 / 8) := by
        gcongr
      linarith
    calc (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-((W - y) ^ 2 / (4 * t))) * ‖f W‖
        ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-((W - y) ^ 2 / (4 * t))) *
            (N * Real.exp ((W - u) * (α + 1 / 8))) := by gcongr
      _ = (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * N * (Real.exp (-((W - y) ^ 2 / (4 * t))) *
            Real.exp ((W - u) * (α + 1 / 8))) := by ring
      _ ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * N * (Real.exp (-(t * α ^ 2)) *
            Real.exp (-((α ^ 2 - 1 / 2) ^ 2 / (4 * t)) + (α ^ 2 + 1 / 2) * (α + 1 / 8) +
              t * α ^ 2)) := by gcongr
      _ = _ := by ring

/-- **The far terms and the boundary value at `W = 2tα + α²`.** -/
theorem far_terms_le_of_bound {b t X y : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (hX : 200 ≤ X) (hy : |y| ≤ 1 / 2)
    (hα1 : 1 ≤ (horizontalSlope X).re)
    (hW9 : 9 / 2 ≤ 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2)
    (hFWb : ‖xiLine X (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2)‖ ≤
      (Real.exp b * ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖) *
        Real.exp ((2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 -
          (y + 2 * t * (horizontalSlope X).re)) * ((horizontalSlope X).re + 1 / 8))) :
    (∫ w in Ioi (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2),
        (|(w - y) / (2 * t)| + ‖horizontalSlope X‖) * gaussDensity t (w - y) * ‖xiLine X w‖) ≤
      (Real.exp b * ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖) *
        Real.exp (-(t * (horizontalSlope X).re ^ 2)) * kklRC t (horizontalSlope X).re ∧
    (∫ w in Ioi (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2),
        gaussDensity t (w - y) * ‖xiLine X w‖) ≤
      (Real.exp b * ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖) *
        Real.exp (-(t * (horizontalSlope X).re ^ 2)) * kklRC t (horizontalSlope X).re ∧
    gaussDensity t (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 - y) *
        ‖xiLine X (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2)‖ ≤
      (Real.exp b * ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖) *
        Real.exp (-(t * (horizontalSlope X).re ^ 2)) * kklRB t (horizontalSlope X).re := by
  refine far_terms_le_of_growth ht ht8 hX hy hα1 (by positivity) hW9 hFWb fun w hw => ?_
  have hg := norm_xiLine_le_far hX hW9 hw.le
  rwa [← horizontalSlope_re] at hg

end

end RHTower.DeBruijn
