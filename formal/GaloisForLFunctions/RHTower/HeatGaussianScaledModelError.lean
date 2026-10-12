import GaloisForLFunctions.RHTower.HeatGaussianTiltedMoments

/-!
# The log-linear model error at the Gaussian's own scale

With `G(w) = g_t(w − y)e^{wα}` (total mass `e^{yα + tα²}`, a Gaussian of variance `2t` centred at
`u = y + 2tα`), the corpus bound
`∫ G (e^{η|w−u|} − 1) ≤ 2η e^{t(1+η)²} e^{yα+tα²}` (`integral_gaussDensity_sub_mul_rexp_mul_exp_abs_sub_one_le`)
does not tend to `0` with `t`. It compares `|x|` with `cosh x` at unit scale.

**Theorem** (`integral_gaussDensity_sub_mul_rexp_mul_exp_abs_sub_one_le_scaled`). For every scale
`s > 0`,

`∫ G (e^{η|w−u|} − 1) ≤ 2ηs e^{t(1/s+η)²} e^{yα+tα²}`.

**Proof.** Apply the pointwise bound `exp_abs_sub_one_le` with `ηs` and `x/s`, then integrate the four
exponentials by the tilted moment generating function. At `s = √t` the bound is
`2η√t e^{(1+η√t)²}`, which tends to `0` with `t` for fixed `η`.
-/

open MeasureTheory Filter Set

namespace RHTower.DeBruijn

noncomputable section

/-- **The scaled model error.** -/
theorem integral_gaussDensity_sub_mul_rexp_mul_exp_abs_sub_one_le_scaled {t : ℝ} (ht : 0 < t)
    (y α : ℝ) {η s : ℝ} (hη : 0 ≤ η) (hs : 0 < s) :
    ∫ w, gaussDensity t (w - y) * Real.exp (w * α) *
        (Real.exp (η * |w - (y + 2 * t * α)|) - 1) ≤
      2 * η * s * Real.exp (t * (1 / s + η) ^ 2) * Real.exp (y * α + t * α ^ 2) := by
  set u := y + 2 * t * α with hu
  set G : ℝ → ℝ := fun w => gaussDensity t (w - y) * Real.exp (w * α) with hG
  have hint : ∀ lam : ℝ, Integrable (fun w => G w * Real.exp (lam * (w - u))) := fun lam =>
    integrable_gaussDensity_sub_mul_rexp_mul_rexp ht y α lam u
  have hval : ∀ lam : ℝ, ∫ w, G w * Real.exp (lam * (w - u)) =
      Real.exp (y * α + t * α ^ 2) * Real.exp (t * lam ^ 2) := fun lam =>
    integral_gaussDensity_sub_mul_rexp_mul_rexp_centre ht y α lam
  have hG0 : ∀ w, 0 ≤ G w := fun w => gaussDensity_sub_mul_rexp_nonneg ht y α w
  set a := 1 / s + η with ha
  set b := 1 / s - η with hb
  have hsum : Integrable (fun w => η * s / 2 * (G w * Real.exp (a * (w - u)) +
      G w * Real.exp (b * (w - u)) + G w * Real.exp (-b * (w - u)) +
      G w * Real.exp (-a * (w - u)))) :=
    ((((hint _).add (hint _)).add (hint _)).add (hint _)).const_mul _
  have hpt : ∀ x : ℝ, Real.exp (η * |x|) - 1 ≤ η * s / 2 * (Real.exp (a * x) +
      Real.exp (b * x) + Real.exp (-b * x) + Real.exp (-a * x)) := by
    intro x
    have h := exp_abs_sub_one_le (mul_nonneg hη hs.le) (x / s)
    have e0 : η * s * |x / s| = η * |x| := by
      rw [abs_div, abs_of_pos hs]; field_simp
    have e1 : (1 + η * s) * (x / s) = a * x := by rw [ha]; field_simp
    have e2 : (1 - η * s) * (x / s) = b * x := by rw [hb]; field_simp
    have e3 : -(1 - η * s) * (x / s) = -b * x := by rw [hb]; field_simp
    have e4 : -(1 + η * s) * (x / s) = -a * x := by rw [ha]; field_simp
    rw [e0, e1, e2, e3, e4] at h
    exact h
  calc ∫ w, G w * (Real.exp (η * |w - u|) - 1)
      ≤ ∫ w, η * s / 2 * (G w * Real.exp (a * (w - u)) +
          G w * Real.exp (b * (w - u)) + G w * Real.exp (-b * (w - u)) +
          G w * Real.exp (-a * (w - u))) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun w => ?_) hsum
          (Eventually.of_forall fun w => ?_)
        · have : 1 ≤ Real.exp (η * |w - u|) := Real.one_le_exp (mul_nonneg hη (abs_nonneg _))
          exact mul_nonneg (hG0 w) (by linarith)
        · refine le_trans (mul_le_mul_of_nonneg_left (hpt (w - u)) (hG0 w)) (le_of_eq ?_)
          ring
    _ = η * s / 2 * (Real.exp (y * α + t * α ^ 2) * Real.exp (t * a ^ 2) +
          Real.exp (y * α + t * α ^ 2) * Real.exp (t * b ^ 2) +
          Real.exp (y * α + t * α ^ 2) * Real.exp (t * (-b) ^ 2) +
          Real.exp (y * α + t * α ^ 2) * Real.exp (t * (-a) ^ 2)) := by
        rw [integral_const_mul, integral_add ?_ (hint _), integral_add ?_ (hint _),
          integral_add (hint _) (hint _), hval, hval, hval, hval]
        · exact (hint _).add (hint _)
        · exact ((hint _).add (hint _)).add (hint _)
    _ ≤ 2 * η * s * Real.exp (t * a ^ 2) * Real.exp (y * α + t * α ^ 2) := by
        have hab : b ^ 2 ≤ a ^ 2 := by
          rw [ha, hb]
          have : 0 ≤ 1 / s := by positivity
          nlinarith
        have hle : Real.exp (t * b ^ 2) ≤ Real.exp (t * a ^ 2) :=
          Real.exp_le_exp.mpr (by nlinarith)
        have e1 : (-b) ^ 2 = b ^ 2 := by ring
        have e2 : (-a) ^ 2 = a ^ 2 := by ring
        rw [e1, e2]
        have hE := Real.exp_pos (y * α + t * α ^ 2)
        have hηs : 0 ≤ η * s := mul_nonneg hη hs.le
        nlinarith [mul_le_mul_of_nonneg_left hle hE.le]

end

end RHTower.DeBruijn
