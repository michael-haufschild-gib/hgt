import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The witness of a zero persists for the reciprocal aperture

Averaged estimates bound the measure of the heights where a detecting form is negative. Such a
bound excludes an individual defect only if the defect's witness stays negative on a set larger
than the allowed exceptional set. This file computes that persistence scale.

* **Lipschitz persistence** (`neg_on_Ioo_of_lipschitz`, `ofReal_le_volume_neg_of_lipschitz`). A
  witness with height-Lipschitz constant `Λ` and value `≤ −m` at `γ` is negative on
  `(γ − m/Λ, γ + m/Λ)`; the tent `Λ|τ − γ| − m` shows the interval is exact
  (`tent_neg_iff`).
* **The zero term persists for `1/A`, at every depth** (`zeroTerm_ge`). A zero `ρ = ½ + δ + iγ`
  enters a test of aperture `A` (a nonnegative weight `g` supported in `[−A, A]`) through
  `Z(τ) = ∫ g(x) e^{δx} cos((τ − γ)x) dx`. Since `1 − cos y ≤ |y|` (`one_sub_cos_le_abs`),
  `Z(τ) ≥ (1 − A|τ − γ|) Z(γ)`. The depth `δ` enlarges the peak `Z(γ)` and the height derivative
  by the same factor, so the relative persistence scale is `1/A`, independent of `δ`.
* **Localization threshold** (`volume_neg_ge_of_zeroTerm`, `false_of_volume_lt`). If the witness is
  `−Z + R` with `|R| ≤ r < Z(γ)`, its negative set contains an interval of length
  `2(1 − r/Z(γ))/A`. A measure bound on bad heights below that length excludes the zero;
  above it, the defect can hide.

At the natural aperture `A ≍ log T` the exceptional set must therefore be smaller than a constant
multiple of `1/log T`, the mean spacing of the zeros: a density or averaged positivity theorem
becomes an individual-defect theorem only below the zero-spacing scale.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

/-! ### Lipschitz persistence -/

/-- **A Lipschitz witness stays negative for `m/Λ` on each side.** -/
theorem neg_on_Ioo_of_lipschitz {W : ℝ → ℝ} {Λ m γ : ℝ} (hΛ : 0 < Λ)
    (hlip : ∀ τ τ', |W τ - W τ'| ≤ Λ * |τ - τ'|) (hγ : W γ ≤ -m) :
    ∀ τ ∈ Ioo (γ - m / Λ) (γ + m / Λ), W τ < 0 := by
  intro τ hτ
  have hd : |τ - γ| < m / Λ := by
    rw [abs_lt]; constructor <;> linarith [hτ.1, hτ.2]
  have h1 := hlip τ γ
  have h2 : Λ * |τ - γ| < m := by
    have := mul_lt_mul_of_pos_left hd hΛ
    rwa [mul_div_cancel₀ _ hΛ.ne'] at this
  have h3 := (abs_le.mp h1).2
  linarith

/-- **The negative set of a Lipschitz witness has measure at least `2m/Λ`.** -/
theorem ofReal_le_volume_neg_of_lipschitz {W : ℝ → ℝ} {Λ m γ : ℝ} (hΛ : 0 < Λ)
    (hlip : ∀ τ τ', |W τ - W τ'| ≤ Λ * |τ - τ'|) (hγ : W γ ≤ -m) {E : Set ℝ}
    (hE : {τ | W τ < 0} ⊆ E) : ENNReal.ofReal (2 * (m / Λ)) ≤ volume E := by
  have hsub : Ioo (γ - m / Λ) (γ + m / Λ) ⊆ E := fun τ hτ =>
    hE (neg_on_Ioo_of_lipschitz hΛ hlip hγ τ hτ)
  calc ENNReal.ofReal (2 * (m / Λ)) = volume (Ioo (γ - m / Λ) (γ + m / Λ)) := by
        rw [Real.volume_Ioo]; ring_nf
    _ ≤ volume E := measure_mono hsub

/-- **The interval is exact**: the tent `Λ|τ − γ| − m` is negative exactly on it. -/
theorem tent_neg_iff {Λ m γ : ℝ} (hΛ : 0 < Λ) (τ : ℝ) :
    Λ * |τ - γ| - m < 0 ↔ τ ∈ Ioo (γ - m / Λ) (γ + m / Λ) := by
  rw [sub_neg, ← lt_div_iff₀' hΛ, abs_lt, mem_Ioo]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem tent_lipschitz {Λ m γ : ℝ} (hΛ : 0 ≤ Λ) (τ τ' : ℝ) :
    |(Λ * |τ - γ| - m) - (Λ * |τ' - γ| - m)| ≤ Λ * |τ - τ'| := by
  rw [show Λ * |τ - γ| - m - (Λ * |τ' - γ| - m) = Λ * (|τ - γ| - |τ' - γ|) by ring, abs_mul,
    abs_of_nonneg hΛ]
  exact mul_le_mul_of_nonneg_left
    ((abs_abs_sub_abs_le_abs_sub _ _).trans (le_of_eq (by ring_nf))) hΛ

/-! ### The zero term at aperture `A` -/

/-- `1 − cos y ≤ |y|`. -/
theorem one_sub_cos_le_abs (y : ℝ) : 1 - Real.cos y ≤ |y| := by
  rcases le_or_gt |y| 2 with hy | hy
  · have hc := Real.one_sub_sq_div_two_le_cos (x := y)
    have hsq : y ^ 2 / 2 ≤ |y| := by
      have : y ^ 2 = |y| * |y| := by rw [← sq_abs, sq]
      rw [this]
      nlinarith [abs_nonneg y]
    linarith
  · have := Real.neg_one_le_cos y
    linarith

/-- The contribution of a zero `½ + δ + iγ` to a test with weight `g`, read at height `τ`. -/
def zeroTerm (g : ℝ → ℝ) (δ γ τ : ℝ) : ℝ := ∫ x, g x * Real.exp (δ * x) * Real.cos ((τ - γ) * x)

theorem zeroTerm_self (g : ℝ → ℝ) (δ γ : ℝ) :
    zeroTerm g δ γ γ = ∫ x, g x * Real.exp (δ * x) := by
  simp [zeroTerm]

/-- **The zero term persists for the reciprocal aperture, at every depth.** For a nonnegative
weight supported in `[−A, A]`, `Z(τ) ≥ (1 − A|τ − γ|) Z(γ)`. -/
theorem zeroTerm_ge {g : ℝ → ℝ} {A δ γ : ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hsupp : ∀ x, A < |x| → g x = 0) (hint : Integrable fun x => g x * Real.exp (δ * x))
    (τ : ℝ) : (1 - A * |τ - γ|) * zeroTerm g δ γ γ ≤ zeroTerm g δ γ τ := by
  have hcos : Integrable fun x => g x * Real.exp (δ * x) * Real.cos ((τ - γ) * x) := by
    refine hint.mono (hint.aestronglyMeasurable.mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs (Real.cos _)]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _)
  rw [zeroTerm_self, zeroTerm, ← integral_const_mul]
  refine integral_mono (hint.const_mul _) hcos fun x => ?_
  have hw : 0 ≤ g x * Real.exp (δ * x) := mul_nonneg (hg0 x) (Real.exp_pos _).le
  by_cases hx : A < |x|
  · simp [hsupp x hx]
  · push Not at hx
    have h1 := one_sub_cos_le_abs ((τ - γ) * x)
    have h2 : |(τ - γ) * x| ≤ A * |τ - γ| := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    have h3 : 1 - A * |τ - γ| ≤ Real.cos ((τ - γ) * x) := by linarith
    calc (1 - A * |τ - γ|) * (g x * Real.exp (δ * x))
        ≤ Real.cos ((τ - γ) * x) * (g x * Real.exp (δ * x)) := mul_le_mul_of_nonneg_right h3 hw
      _ = g x * Real.exp (δ * x) * Real.cos ((τ - γ) * x) := by ring

/-! ### The localization threshold -/

/-- **A witness dominated by a zero term is negative on an interval of length
`2(1 − r/Z(γ))/A`.** -/
theorem neg_of_zeroTerm {g : ℝ → ℝ} {A δ γ r : ℝ} (hA : 0 < A) (hg0 : ∀ x, 0 ≤ g x)
    (hsupp : ∀ x, A < |x| → g x = 0) (hint : Integrable fun x => g x * Real.exp (δ * x))
    (hr : r < zeroTerm g δ γ γ) {W : ℝ → ℝ} (hW : ∀ τ, W τ ≤ -zeroTerm g δ γ τ + r) :
    ∀ τ ∈ Ioo (γ - (1 - r / zeroTerm g δ γ γ) / A) (γ + (1 - r / zeroTerm g δ γ γ) / A),
      W τ < 0 := by
  intro τ hτ
  set Z := zeroTerm g δ γ γ with hZ
  have hZ0 : 0 ≤ Z := by
    rw [hZ, zeroTerm_self]
    exact integral_nonneg fun x => mul_nonneg (hg0 x) (Real.exp_pos _).le
  have hge := zeroTerm_ge (γ := γ) hg0 hsupp hint τ
  have hkey : r < (1 - A * |τ - γ|) * Z := by
    rcases hZ0.lt_or_eq with hZpos | hZz
    · have hd : |τ - γ| < (1 - r / Z) / A := by
        rw [abs_lt]; constructor <;> linarith [hτ.1, hτ.2]
      have hAd : A * |τ - γ| < 1 - r / Z := by
        have := mul_lt_mul_of_pos_left hd hA
        rwa [mul_div_cancel₀ _ hA.ne'] at this
      have : r / Z < 1 - A * |τ - γ| := by linarith
      rwa [div_lt_iff₀ hZpos] at this
    · rw [← hZz, mul_zero]
      rw [← hZz] at hr
      exact hr
  linarith [hW τ]

/-- **The negative set of a zero's witness has measure at least `2(1 − r/Z(γ))/A`.** -/
theorem volume_neg_ge_of_zeroTerm {g : ℝ → ℝ} {A δ γ r : ℝ} (hA : 0 < A) (hg0 : ∀ x, 0 ≤ g x)
    (hsupp : ∀ x, A < |x| → g x = 0) (hint : Integrable fun x => g x * Real.exp (δ * x))
    (hr : r < zeroTerm g δ γ γ) {W : ℝ → ℝ} (hW : ∀ τ, W τ ≤ -zeroTerm g δ γ τ + r)
    {E : Set ℝ} (hE : {τ | W τ < 0} ⊆ E) :
    ENNReal.ofReal (2 * ((1 - r / zeroTerm g δ γ γ) / A)) ≤ volume E := by
  set ℓ := (1 - r / zeroTerm g δ γ γ) / A with hℓ
  have hsub : Ioo (γ - ℓ) (γ + ℓ) ⊆ E := fun τ hτ =>
    hE (neg_of_zeroTerm hA hg0 hsupp hint hr hW τ hτ)
  calc ENNReal.ofReal (2 * ℓ) = volume (Ioo (γ - ℓ) (γ + ℓ)) := by
        rw [Real.volume_Ioo]; ring_nf
    _ ≤ volume E := measure_mono hsub

/-- **The localization threshold.** If the heights where the witness may be negative have measure
below `2(1 − r/Z(γ))/A`, there is no zero of that profile at height `γ`. -/
theorem false_of_volume_lt {g : ℝ → ℝ} {A δ γ r : ℝ} (hA : 0 < A) (hg0 : ∀ x, 0 ≤ g x)
    (hsupp : ∀ x, A < |x| → g x = 0) (hint : Integrable fun x => g x * Real.exp (δ * x))
    (hr : r < zeroTerm g δ γ γ) {W : ℝ → ℝ} (hW : ∀ τ, W τ ≤ -zeroTerm g δ γ τ + r)
    {E : Set ℝ} (hE : {τ | W τ < 0} ⊆ E)
    (hsmall : volume E < ENNReal.ofReal (2 * ((1 - r / zeroTerm g δ γ γ) / A))) : False :=
  absurd (volume_neg_ge_of_zeroTerm hA hg0 hsupp hint hr hW hE) (not_le.mpr hsmall)

end GaloisForLFunctions.ArithmeticCorrelationGeometry
