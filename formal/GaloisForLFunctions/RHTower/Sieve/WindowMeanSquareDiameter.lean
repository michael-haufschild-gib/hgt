import GaloisForLFunctions.RHTower.Sieve.LSeriesTranslate
import GaloisForLFunctions.RHTower.Sieve.GhsStepFour
/-!
# The mean square over the exceptional window, by the sieve at the window's own width

A set of diameter `R` is either empty or a translate of an interval of radius `R`, and on such an interval the
translated sieve estimate applies.  So for the exceptional window of the Halász dichotomy — which the corpus
proves has diameter `O(δ/log z)` — the mean square is bounded by

`2π(5R/4)·∑_n (2(n(e^{1/R} − e^{−1/R}) + 1)/log Y + E + z)·‖a_n n^{−σ}‖²`,

proportional to `R` and to the sieve mass, in place of the trivial `R·(ℓ¹ mass)²`.  The shift of the interval to
the origin is an interval-integral change of variables, and the frequency translation is absorbed by the
coefficients without changing their moduli.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set Finset

/-- A set of diameter at most `R` is either empty or contained in a ball of radius `R` about one of its points. -/
theorem subset_Icc_of_diameter {S : Set ℝ} {R : ℝ}
    (hdiam : ∀ t ∈ S, ∀ u ∈ S, |t - u| ≤ R) :
    S = ∅ ∨ ∃ t₀ : ℝ, S ⊆ Set.Icc (t₀ - R) (t₀ + R) := by
  rcases Set.eq_empty_or_nonempty S with h | ⟨t₀, ht₀⟩
  · exact Or.inl h
  · refine Or.inr ⟨t₀, fun t ht => ?_⟩
    have h := hdiam t ht t₀ ht₀
    rw [abs_le] at h
    exact Set.mem_Icc.2 ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Shifting the interval of integration to the origin. -/
theorem integral_Icc_shift (F : ℝ → ℝ) (t₀ R : ℝ) (hR : 0 ≤ R) :
    (∫ t in Set.Icc (t₀ - R) (t₀ + R), F t) = ∫ u in Set.Icc (-R) R, F (t₀ + u) := by
  have hle1 : t₀ - R ≤ t₀ + R := by linarith
  have hle2 : -R ≤ R := by linarith
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle1,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle2]
  have h := intervalIntegral.integral_comp_add_left (a := -R) (b := R) F t₀
  rw [h]
  congr 1

/-- **The mean square over the exceptional window, by the sieve at the window's own width.**  A set of diameter
`R` is a translate of an interval of radius `R`, on which the translated sieve estimate applies: the bound is
proportional to `R`, not to `R` times the square of the `ℓ¹` mass. -/
theorem integral_normSq_LSeries_le_of_diameter {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (hprime : ∀ n ∈ s, a n ≠ 0 → n.Prime) (σ : ℝ)
    {S : Set ℝ} {R : ℝ} (hR : 0 < R) (hdiam : ∀ t ∈ S, ∀ u ∈ S, |t - u| ≤ R)
    (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y) :
    (∫ t in S, ‖LSeries a ((σ : ℂ) + (t : ℝ) * I)‖ ^ 2)
      ≤ 2 * Real.pi * ((5 * R / 4) * ∑ n ∈ s,
          (2 * ((n : ℝ) * (Real.exp (1 / R) - Real.exp (-(1 / R))) + 1) / Real.log Y
            + selbergFibreError z Y + (z : ℝ))
              * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2) := by
  classical
  have hcont : Continuous fun t : ℝ => ‖LSeries a ((σ : ℂ) + (t : ℝ) * I)‖ ^ 2 :=
    (continuous_LSeries_line_of_support hs0 hsupp σ).norm.pow 2
  have hnn : (0 : ℝ) ≤ 2 * Real.pi * ((5 * R / 4) * ∑ n ∈ s,
      (2 * ((n : ℝ) * (Real.exp (1 / R) - Real.exp (-(1 / R))) + 1) / Real.log Y
        + selbergFibreError z Y + (z : ℝ))
          * ‖a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2) := by
    have herr : 0 ≤ selbergFibreError z Y := selbergFibreError_nonneg hz Y
    have hzR : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
    have hS : Real.exp (-(1 / R)) ≤ Real.exp (1 / R) := by
      refine Real.exp_le_exp.2 ?_
      have : (0 : ℝ) < 1 / R := by positivity
      linarith
    refine mul_nonneg (by positivity) (mul_nonneg (by positivity) ?_)
    refine Finset.sum_nonneg fun n _ => ?_
    have hnnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hnum : (0 : ℝ) ≤ 2 * ((n : ℝ) * (Real.exp (1 / R) - Real.exp (-(1 / R))) + 1) := by
      have : (0 : ℝ) ≤ (n : ℝ) * (Real.exp (1 / R) - Real.exp (-(1 / R))) :=
        mul_nonneg hnnn (by linarith)
      linarith
    have hcount : (0 : ℝ) ≤ 2 * ((n : ℝ) * (Real.exp (1 / R) - Real.exp (-(1 / R))) + 1)
        / Real.log Y + selbergFibreError z Y + (z : ℝ) := by
      have := div_nonneg hnum hlog.le
      linarith
    positivity
  rcases subset_Icc_of_diameter hdiam with hempty | ⟨t₀, hsub⟩
  · rw [hempty]
    simpa using hnn
  · have hmono : (∫ t in S, ‖LSeries a ((σ : ℂ) + (t : ℝ) * I)‖ ^ 2)
        ≤ ∫ t in Set.Icc (t₀ - R) (t₀ + R), ‖LSeries a ((σ : ℂ) + (t : ℝ) * I)‖ ^ 2 := by
      refine setIntegral_mono_set (hcont.integrableOn_Icc)
        (Filter.Eventually.of_forall fun t => by positivity) hsub.eventuallyLE
    refine hmono.trans ?_
    rw [integral_Icc_shift _ t₀ R hR.le]
    have hcongr : ∀ u : ℝ, ‖LSeries a ((σ : ℂ) + ((t₀ + u : ℝ) : ℝ) * I)‖ ^ 2
        = ‖LSeries a ((σ : ℂ) + ((t₀ + u : ℝ) : ℂ) * I)‖ ^ 2 := by
      intro u
      norm_num
    rw [setIntegral_congr_fun measurableSet_Icc (fun u _ => hcongr u)]
    exact integral_Icc_normSq_LSeries_translate_le_prime_sieve hs0 hsupp hprime σ t₀ hR z Y hY hYz
      hz hlog

end RHTower.Sieve
end
