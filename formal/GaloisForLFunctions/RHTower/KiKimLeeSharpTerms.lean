import GaloisForLFunctions.RHTower.XiLineStripGaussianSharp
import GaloisForLFunctions.RHTower.HeatGaussianScaledModelError

/-!
# The remaining error terms of the one-sided Gaussian average, near window

Notation of `KiKimLeeRelativeBounds`: `α = ½ log(X/2π)`, `F(w) = ξ(½ + w + iX)`, `u = y + 2tα`,
`N = ‖F(u)‖`, `P = N e^{−tα²}`, `c = 2tα`. The window starts at `w₁ = ½ + η` and carries the
model error `η₁ = 1/η + 3` (`norm_xiLine_sub_model_le_near`).

* **Lower tail** (`sharp_lowerTail_le`): `N e^{−uα} ∫_{w ≤ w₁} g_t(w−y)e^{wα} ≤ P · sharpR1`, with
  `sharpR1 = exp((α/2)(1 + η − (3/4)c))`. This is the Chernoff bound with parameter `α/2`. It is
  small once `c > (4/3)(1+η)`.
* **Model error** (`sharp_modelError_le`): `N e^{−uα} ∫ g_t(w−y)e^{wα}(e^{η₁|w−u|} − 1) ≤ P · sharpR3`,
  with `sharpR3 = 2η₁√t e^{t(1/√t + η₁)²}`. This uses the scaled Gaussian bound at scale `√t`.
* **Window mass** (`sharp_windowMass_le`): `∫_{w₁}^{W} g_t(w−y)‖F(w)‖ ≤ P(1 + sharpR3)`.
* **`F` at the far end** (`norm_xiLine_le_split_model`): for `u ≤ 9/2 ≤ W`,
  `‖F(W)‖ ≤ e^{(9/2)η₁} N e^{(W−u)(α+1/8)}`. The near model is used on `[u, 9/2]` and the corpus
  model with error `1/8` on `[9/2, W]`, so the large `η₁` costs only a constant factor.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

/-- The sharp lower-tail error. -/
def sharpR1 (η t α : ℝ) : ℝ := Real.exp (α / 2 * (1 + η - 3 / 4 * (2 * t * α)))

/-- The sharp model error. -/
def sharpR3 (η t : ℝ) : ℝ :=
  2 * (1 / η + 3) * Real.sqrt t * Real.exp (t * (1 / Real.sqrt t + (1 / η + 3)) ^ 2)

/-- **The sharp lower tail.** -/
theorem sharp_lowerTail_le {η t α y N : ℝ} (ht : 0 < t) (hy : |y| ≤ 1 / 2) (hα : 0 ≤ α)
    (hN : 0 ≤ N) :
    N * Real.exp (-((y + 2 * t * α) * α)) *
        ∫ w in Iic (1 / 2 + η : ℝ), gaussDensity t (w - y) * Real.exp (w * α) ≤
      N * Real.exp (-(t * α ^ 2)) * sharpR1 η t α := by
  have h := setIntegral_Iic_gaussDensity_sub_mul_rexp_le ht y α (1 / 2 + η) (α / 2) (by linarith)
  have hy' := neg_abs_le y
  calc N * Real.exp (-((y + 2 * t * α) * α)) *
        ∫ w in Iic (1 / 2 + η : ℝ), gaussDensity t (w - y) * Real.exp (w * α)
      ≤ N * Real.exp (-((y + 2 * t * α) * α)) *
          Real.exp (α / 2 * (1 / 2 + η) + y * (α - α / 2) + t * (α - α / 2) ^ 2) := by gcongr
    _ = N * Real.exp (-(t * α ^ 2) + α / 2 * (1 / 2 + η - y - 3 / 2 * t * α)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ N * Real.exp (-(t * α ^ 2) + α / 2 * (1 + η - 3 / 4 * (2 * t * α))) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hN
        have hy1 := (abs_le.mp hy).1
        nlinarith
    _ = _ := by rw [sharpR1, mul_assoc N, ← Real.exp_add]

/-- **The sharp model error.** -/
theorem sharp_modelError_le {η t α y N : ℝ} (ht : 0 < t) (hη : 0 < η) (hN : 0 ≤ N) :
    N * Real.exp (-((y + 2 * t * α) * α)) *
        ∫ w, gaussDensity t (w - y) * Real.exp (w * α) *
          (Real.exp ((1 / η + 3) * |w - (y + 2 * t * α)|) - 1) ≤
      N * Real.exp (-(t * α ^ 2)) * sharpR3 η t := by
  have h := integral_gaussDensity_sub_mul_rexp_mul_exp_abs_sub_one_le_scaled ht y α
    (η := 1 / η + 3) (s := Real.sqrt t) (by positivity) (Real.sqrt_pos.mpr ht)
  calc N * Real.exp (-((y + 2 * t * α) * α)) *
        ∫ w, gaussDensity t (w - y) * Real.exp (w * α) *
          (Real.exp ((1 / η + 3) * |w - (y + 2 * t * α)|) - 1)
      ≤ N * Real.exp (-((y + 2 * t * α) * α)) *
          (2 * (1 / η + 3) * Real.sqrt t *
            Real.exp (t * (1 / Real.sqrt t + (1 / η + 3)) ^ 2) *
            Real.exp (y * α + t * α ^ 2)) := by gcongr
    _ = N * (Real.exp (-((y + 2 * t * α) * α)) * Real.exp (y * α + t * α ^ 2)) *
          sharpR3 η t := by rw [sharpR3]; ring
    _ = _ := by rw [← Real.exp_add, scale_identity]

/-- **The sharp window mass.** -/
theorem sharp_windowMass_le {η t X y : ℝ} (ht : 0 < t) (hη : 0 < η) (hX : 200 ≤ X)
    (hu : y + 2 * t * (horizontalSlope X).re ∈ Icc (1 / 2 + η) (X / 32 - 1 / 2))
    {W : ℝ} (hW : W ≤ X / 32 - 1 / 2) :
    ∫ w in Ioc (1 / 2 + η) W, gaussDensity t (w - y) * ‖xiLine X w‖ ≤
      ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp (-(t * (horizontalSlope X).re ^ 2)) * (1 + sharpR3 η t) := by
  set α := (horizontalSlope X).re with hα
  set u := y + 2 * t * α with hu_def
  set N := ‖xiLine X u‖ with hN
  set η₁ := 1 / η + 3 with hη₁
  have hη₁0 : 0 ≤ η₁ := by positivity
  have hN0 : 0 ≤ N := norm_nonneg _
  have hint1 := integrable_gaussDensity_sub_mul_rexp ht y α
  have hint2 := integrable_modelError ht y α u η₁ hη₁0
  have hmaj : Integrable (fun w => N * Real.exp (-(u * α)) *
      (gaussDensity t (w - y) * Real.exp (w * α) +
        gaussDensity t (w - y) * Real.exp (w * α) * (Real.exp (η₁ * |w - u|) - 1))) :=
    (hint1.add hint2).const_mul _
  have hnonneg : ∀ w, 0 ≤ N * Real.exp (-(u * α)) *
      (gaussDensity t (w - y) * Real.exp (w * α) +
        gaussDensity t (w - y) * Real.exp (w * α) * (Real.exp (η₁ * |w - u|) - 1)) := by
    intro w
    have h1 : 1 ≤ Real.exp (η₁ * |w - u|) := Real.one_le_exp (by positivity)
    have := gaussDensity_sub_mul_rexp_nonneg ht y α w
    positivity
  calc ∫ w in Ioc (1 / 2 + η) W, gaussDensity t (w - y) * ‖xiLine X w‖
      ≤ ∫ w in Ioc (1 / 2 + η) W, N * Real.exp (-(u * α)) *
          (gaussDensity t (w - y) * Real.exp (w * α) +
            gaussDensity t (w - y) * Real.exp (w * α) * (Real.exp (η₁ * |w - u|) - 1)) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun w =>
          mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _)) hmaj.integrableOn ?_
        refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun w hw => ?_)
        have hwW : w ∈ Icc (1 / 2 + η) (X / 32 - 1 / 2) := ⟨hw.1.le, hw.2.trans hW⟩
        have hm := norm_xiLine_sub_model_le_near hX hη hu hwW
        have hn : ‖xiLine X u * Complex.exp (((w - u : ℝ) : ℂ) * horizontalSlope X)‖ =
            N * Real.exp ((w - u) * α) := by
          rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
        have htri := norm_sub_norm_le (xiLine X w)
          (xiLine X u * Complex.exp (((w - u : ℝ) : ℂ) * horizontalSlope X))
        rw [hn] at htri
        rw [← hα] at hm
        have hFw : ‖xiLine X w‖ ≤ N * Real.exp ((w - u) * α) * Real.exp (η₁ * |w - u|) := by
          nlinarith
        have hsplit : Real.exp ((w - u) * α) = Real.exp (-(u * α)) * Real.exp (w * α) := by
          rw [← Real.exp_add]; ring_nf
        rw [hsplit] at hFw
        have hG := (gaussDensity_pos ht (w - y)).le
        calc gaussDensity t (w - y) * ‖xiLine X w‖
            ≤ gaussDensity t (w - y) * (N * (Real.exp (-(u * α)) * Real.exp (w * α)) *
                Real.exp (η₁ * |w - u|)) := by gcongr
          _ = _ := by ring
    _ ≤ ∫ w, N * Real.exp (-(u * α)) *
          (gaussDensity t (w - y) * Real.exp (w * α) +
            gaussDensity t (w - y) * Real.exp (w * α) * (Real.exp (η₁ * |w - u|) - 1)) :=
        setIntegral_le_integral hmaj (Eventually.of_forall hnonneg)
    _ = N * Real.exp (-(u * α)) * (∫ w, gaussDensity t (w - y) * Real.exp (w * α)) +
          N * Real.exp (-(u * α)) * ∫ w, gaussDensity t (w - y) * Real.exp (w * α) *
            (Real.exp (η₁ * |w - u|) - 1) := by
        rw [integral_const_mul, integral_add hint1 hint2]; ring
    _ ≤ N * Real.exp (-(t * α ^ 2)) + N * Real.exp (-(t * α ^ 2)) * sharpR3 η t := by
        rw [hu_def, tiltedMass_eq ht]
        exact add_le_add le_rfl (sharp_modelError_le ht hη hN0)
    _ = _ := by ring

/-- **`F` at the far end of the window, by the split model.** -/
theorem norm_xiLine_le_split_model {η X u W : ℝ} (hX : 200 ≤ X) (hη : 0 < η)
    (hu : u ∈ Icc (1 / 2 + η) (9 / 2)) (hW : W ∈ Icc (9 / 2 : ℝ) (X / 32 - 1 / 2)) :
    ‖xiLine X W‖ ≤
      Real.exp (9 / 2 * (1 / η + 3)) * ‖xiLine X u‖ *
        Real.exp ((W - u) * ((horizontalSlope X).re + 1 / 8)) := by
  set α := (horizontalSlope X).re with hα
  have h9 : (9 / 2 : ℝ) ≤ X / 32 - 1 / 2 := hW.1.trans hW.2
  -- `[u, 9/2]` with the near model
  have hnear := norm_xiLine_sub_model_le_near hX hη ⟨hu.1, hu.2.trans h9⟩
    (w := 9 / 2) ⟨by linarith [hu.1, hu.2], h9⟩
  -- `[9/2, W]` with the corpus model
  have hfar := norm_xiLine_le_model hX ⟨le_rfl, h9⟩ hW
  have hn : ∀ A : ℂ, ∀ v : ℝ, ‖A * Complex.exp (((v : ℝ) : ℂ) * horizontalSlope X)‖ =
      ‖A‖ * Real.exp (v * α) := by
    intro A v; rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
  have htri := norm_sub_norm_le (xiLine X (9 / 2))
    (xiLine X u * Complex.exp (((9 / 2 - u : ℝ) : ℂ) * horizontalSlope X))
  rw [hn] at htri
  rw [← hα] at hnear hfar
  have hF9 : ‖xiLine X (9 / 2)‖ ≤ ‖xiLine X u‖ * Real.exp ((9 / 2 - u) * α) *
      Real.exp ((1 / η + 3) * |9 / 2 - u|) := by nlinarith
  have habs : |9 / 2 - u| ≤ 9 / 2 := by
    rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
  have habs2 : |W - 9 / 2| = W - 9 / 2 := abs_of_nonneg (by linarith [hW.1])
  rw [habs2] at hfar
  have hu0 : 0 ≤ ‖xiLine X u‖ := norm_nonneg _
  calc ‖xiLine X W‖ ≤ ‖xiLine X (9 / 2)‖ * Real.exp ((W - 9 / 2) * α) *
        Real.exp (1 / 8 * (W - 9 / 2)) := hfar
    _ ≤ (‖xiLine X u‖ * Real.exp ((9 / 2 - u) * α) * Real.exp ((1 / η + 3) * (9 / 2))) *
          Real.exp ((W - 9 / 2) * α) * Real.exp (1 / 8 * (W - u)) := by
        gcongr
        · exact hF9.trans (by gcongr)
        · linarith [hu.1, hu.2]
    _ = Real.exp (9 / 2 * (1 / η + 3)) * ‖xiLine X u‖ *
          (Real.exp ((9 / 2 - u) * α) * Real.exp ((W - 9 / 2) * α) *
            Real.exp (1 / 8 * (W - u))) := by ring
    _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2; ring

end

end RHTower.DeBruijn
