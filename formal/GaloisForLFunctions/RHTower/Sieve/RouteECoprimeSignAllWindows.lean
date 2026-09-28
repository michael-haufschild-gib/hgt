import GaloisForLFunctions.RHTower.Sieve.RouteELongWindow
import GaloisForLFunctions.RHTower.Sieve.MoebiusAveragedMeanSquareAllLengths
import GaloisForLFunctions.RHTower.Sieve.MoebiusSignInWindow
import GaloisForLFunctions.RHTower.Sieve.SqrtWindowLaw

/-!
# Route E's coprime product-sign law at every admissible window

For every window law `h(x)` with `h/log log(3x) → ∞`, both coprime squarefree product-sign classes
in `[x, x + h√x]` carry at least `D²(1/2 − A) − ε` of `h√x log 2`, and consequently every
sufficiently large interval `[x, x + h(x)√x]` contains integers of both Möbius signs.  Below the
square root the Möbius input is Matomäki–Radziwiłł's short-interval mean square at every length
(`Sieve/MoebiusAveragedMeanSquareAllLengths`); above it every input is a consequence of the prime
number theorem and the square-divisor count (`Sieve/RouteELongWindow`).  The two regimes are
glued by the window laws `min(h, √x)` and `max(h, √x)`.
-/

namespace RHTower.Sieve

open Filter Topology ArithmeticFunction

noncomputable section

/-- The minimum of two window laws satisfying the growth condition satisfies it. -/
theorem tendsto_min_div_logLog {f g : ℝ → ℝ}
    (hf : Tendsto (fun x => f x / Real.log (Real.log (3 * x))) atTop atTop)
    (hg : Tendsto (fun x => g x / Real.log (Real.log (3 * x))) atTop atTop) :
    Tendsto (fun x => min (f x) (g x) / Real.log (Real.log (3 * x))) atTop atTop := by
  have hL : ∀ᶠ x : ℝ in atTop, 0 < Real.log (Real.log (3 * x)) := by
    have h3 : Tendsto (fun x : ℝ => Real.log (Real.log (3 * x))) atTop atTop :=
      Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
        (tendsto_id.const_mul_atTop (by norm_num)))
    exact h3.eventually_gt_atTop 0
  rw [tendsto_atTop]
  intro b
  filter_upwards [hf.eventually_ge_atTop b, hg.eventually_ge_atTop b, hL] with x h1 h2 hL0
  rw [le_div_iff₀ hL0] at h1 h2 ⊢
  exact le_min h1 h2

/-- **The card's Theorem `(3)` at every admissible window.**  For every window law with
`h/log log(3x) → ∞`, each coprime squarefree product-sign class carries at least
`D²(1/2 − A) − ε` of `h√x log 2`. -/
theorem route_e_sign_density_all_windows {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ (2 : ℕ) / 2
          - squarefreeDensity ^ (2 : ℕ) * RHTower.coprimeSharedPrimeDensity - ε
        ≤ coprimeSignClassCount x (hh x) s / (hh x * Real.sqrt x * Real.log 2) := by
  have hgrow₁ := tendsto_min_div_logLog hgrow tendsto_sqrt_div_logLog_atTop
  have hsmall₁ : ∀ᶠ x in atTop, min (hh x) (Real.sqrt x) ≤ Real.sqrt x :=
    Filter.Eventually.of_forall fun x => min_le_right _ _
  have hgrow₂ : Tendsto (fun x => max (hh x) (Real.sqrt x) / Real.log (Real.log (3 * x)))
      atTop atTop := by
    have hL : ∀ᶠ x : ℝ in atTop, 0 ≤ Real.log (Real.log (3 * x)) := by
      have h3 : Tendsto (fun x : ℝ => Real.log (Real.log (3 * x))) atTop atTop :=
        Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
          (tendsto_id.const_mul_atTop (by norm_num)))
      exact h3.eventually_ge_atTop 0
    refine tendsto_atTop_mono' atTop ?_ hgrow
    filter_upwards [hL] with x hx
    exact div_le_div_of_nonneg_right (le_max_left _ _) hx
  have hsmall := route_e_sign_density_of_moebius_averaged hs hgrow₁ hsmall₁
    (averagedMeanSquare_moebius_of_tendsto (tendsto_of_growth hgrow₁) hsmall₁) hε
  have hlarge := route_e_sign_density_long_windows hs hgrow₂
    (Filter.Eventually.of_forall fun x => le_max_right (hh x) (Real.sqrt x)) hε
  filter_upwards [hsmall, hlarge] with x h1 h2
  rcases le_total (hh x) (Real.sqrt x) with hle | hle
  · rwa [min_eq_left hle] at h1
  · rwa [max_eq_left hle] at h2

/-- **Both coprime product-sign classes are eventually nonempty at every admissible window.** -/
theorem route_e_signClass_nonempty_all_windows {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop) :
    ∀ᶠ x in atTop, (coprimeSignClass x (hh x) s).Nonempty := by
  have hgrow₁ := tendsto_min_div_logLog hgrow tendsto_sqrt_div_logLog_atTop
  have hsmall₁ : ∀ᶠ x in atTop, min (hh x) (Real.sqrt x) ≤ Real.sqrt x :=
    Filter.Eventually.of_forall fun x => min_le_right _ _
  have hgrow₂ : Tendsto (fun x => max (hh x) (Real.sqrt x) / Real.log (Real.log (3 * x)))
      atTop atTop := by
    have hL : ∀ᶠ x : ℝ in atTop, 0 ≤ Real.log (Real.log (3 * x)) := by
      have h3 : Tendsto (fun x : ℝ => Real.log (Real.log (3 * x))) atTop atTop :=
        Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
          (tendsto_id.const_mul_atTop (by norm_num)))
      exact h3.eventually_ge_atTop 0
    refine tendsto_atTop_mono' atTop ?_ hgrow
    filter_upwards [hL] with x hx
    exact div_le_div_of_nonneg_right (le_max_left _ _) hx
  have hsmall := route_e_signClass_nonempty_of_moebius_averaged hs hgrow₁ hsmall₁
    (averagedMeanSquare_moebius_of_tendsto (tendsto_of_growth hgrow₁) hsmall₁)
  have hlarge := route_e_signClass_nonempty_long_windows hs hgrow₂
    (Filter.Eventually.of_forall fun x => le_max_right (hh x) (Real.sqrt x))
  filter_upwards [hsmall, hlarge] with x h1 h2
  rcases le_total (hh x) (Real.sqrt x) with hle | hle
  · rwa [min_eq_left hle] at h1
  · rwa [max_eq_left hle] at h2

/-- **Both Möbius signs in every short interval `[x, x + h(x)√x]`.**  For every window law with
`h/log log(3x) → ∞`, every sufficiently large such interval contains an integer `m₊` with
`μ(m₊) = 1` and an integer `m₋` with `μ(m₋) = −1`. -/
theorem exists_moebius_pos_and_neg_all_windows {hh : ℝ → ℝ}
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop) :
    ∀ᶠ x : ℝ in atTop,
      (∃ m : ℕ, x ≤ (m : ℝ) ∧ (m : ℝ) ≤ x + hh x * Real.sqrt x ∧ moebius m = 1)
      ∧ (∃ m : ℕ, x ≤ (m : ℝ) ∧ (m : ℝ) ≤ x + hh x * Real.sqrt x ∧ moebius m = -1) := by
  filter_upwards [route_e_signClass_nonempty_all_windows (s := 1) (Or.inl rfl) hgrow,
    route_e_signClass_nonempty_all_windows (s := -1) (Or.inr rfl) hgrow] with x h1 h2
  exact ⟨exists_moebius_eq_of_signClass_nonempty h1, exists_moebius_eq_of_signClass_nonempty h2⟩

/-- The window law `(log log 3x)^{1+η}` satisfies the growth condition. -/
theorem tendsto_logLog_rpow_div_logLog {η : ℝ} (hη : 0 < η) :
    Tendsto (fun x : ℝ => Real.log (Real.log (3 * x)) ^ (1 + η) / Real.log (Real.log (3 * x)))
      atTop atTop := by
  have h3 : Tendsto (fun x : ℝ => Real.log (Real.log (3 * x))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      (tendsto_id.const_mul_atTop (by norm_num)))
  refine ((tendsto_rpow_atTop hη).comp h3).congr' ?_
  filter_upwards [h3.eventually_gt_atTop 0] with x hx
  simp only [Function.comp]
  rw [Real.rpow_add hx, Real.rpow_one]
  field_simp

/-- **Both Möbius signs at the window `√x·(log log 3x)^{1+η}`.** -/
theorem exists_moebius_pos_and_neg_logLog_window {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop,
      (∃ m : ℕ, x ≤ (m : ℝ)
          ∧ (m : ℝ) ≤ x + Real.log (Real.log (3 * x)) ^ (1 + η) * Real.sqrt x ∧ moebius m = 1)
      ∧ (∃ m : ℕ, x ≤ (m : ℝ)
          ∧ (m : ℝ) ≤ x + Real.log (Real.log (3 * x)) ^ (1 + η) * Real.sqrt x
          ∧ moebius m = -1) :=
  exists_moebius_pos_and_neg_all_windows (tendsto_logLog_rpow_div_logLog hη)

end

end RHTower.Sieve
