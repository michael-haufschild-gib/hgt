import GaloisForLFunctions.RHTower.Sieve.RealWindowAlignment
import GaloisForLFunctions.RHTower.Sieve.PerronWindowKernelCompareAll

/-!
# Matomäki--Teräväinen Lemma 3.1: the pointwise window comparison, assembled

Three owned steps compose into one inequality, with no asymptotic notation and every error term
explicit:

* the **alignment** (`sum_realWindow_eq_perronWindowSum`) — the coefficient sum over the real window
  `(x, x+h]` *is* the natural window sum at `A = ⌊x⌋`, `H = ⌊x+h⌋ − ⌊x⌋`, with no error;
* the **two-window Perron identity** (`norm_realWindowSum_compare_sub_integral_le`) — the difference
  of the two normalised windows is one integral against `perronCompareKernel`, plus four truncated
  Perron endpoint errors;
* the **kernel domination at every height**
  (`norm_integral_perronPoly_compareKernel_le`) — that integral is bounded by the mixed-moment
  integral, which `integral_mixed_moment_windowCompare_le` estimates from the two mean squares.

The result is the pointwise form of Lemma 3.1 with the mixed-moment integral left as the only
analytic input.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The pointwise window comparison.**  The real short window differs from its normalised
reference window by the mixed-moment integral plus the four truncated-Perron endpoint errors. -/
theorem norm_realWindowSum_compare_le
    {c : ℕ → ℂ} {M : ℕ} {K T x h h₁ t₀ : ℝ}
    (hK : ∀ n, ‖c n‖ ≤ K) (hT : 0 < T) (hx : 0 ≤ x) (hh : 0 ≤ h) (hh₁ : 0 ≤ h₁)
    (hM : ⌊x + h⌋₊ ≤ M) (hM₁ : ⌊x + h₁⌋₊ ≤ M)
    (hHpos : 0 < ((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ))
    (hHle : ((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) ≤ ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ))
    (ht₀ : 0 < t₀)
    (hlow : t₀ ≤ ((⌊x⌋₊ : ℝ) + 1 / 2) / ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ)) :
    ‖(∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, c n)
        - ((((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) / ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) : ℝ) : ℂ)
          * (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h₁⌋₊, c n)‖
      ≤ (1 / (2 * Real.pi)) *
          (∫ t in (-T)..T, ‖perronPoly c M 1 t‖ *
            windowCompareKernel ((⌊x⌋₊ : ℝ) + 1 / 2) ((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ)
              ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) t₀ t)
        + (perronNearError K M ⌊x + h⌋₊ 1 T + perronNearError K M ⌊x⌋₊ 1 T
          + (((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) / ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ)) *
            (perronNearError K M ⌊x + h₁⌋₊ 1 T + perronNearError K M ⌊x⌋₊ 1 T)) := by
  classical
  set A : ℝ := (⌊x⌋₊ : ℝ) + 1 / 2 with hA
  set H : ℝ := ((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) with hH
  set H₁ : ℝ := ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) with hH₁
  have hApos : 0 < A := by
    have : (0 : ℝ) ≤ (⌊x⌋₊ : ℝ) := Nat.cast_nonneg _
    rw [hA]; linarith
  have hbase := norm_realWindowSum_compare_sub_integral_le hK hT hx hh hh₁ hM hM₁
  set S : ℂ := (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h⌋₊, c n)
      - ((H / H₁ : ℝ) : ℂ) * (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + h₁⌋₊, c n) with hS
  set I : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
      perronPoly c M 1 t * perronCompareKernel A H H₁ t with hI
  have htri : ‖S‖ ≤ ‖S - I‖ + ‖I‖ := by
    have : S = (S - I) + I := by ring
    calc ‖S‖ = ‖(S - I) + I‖ := by rw [← this]
      _ ≤ ‖S - I‖ + ‖I‖ := norm_add_le _ _
  refine htri.trans ?_
  have hInorm : ‖I‖ ≤ (1 / (2 * Real.pi)) *
      (∫ t in (-T)..T, ‖perronPoly c M 1 t‖ * windowCompareKernel A H H₁ t₀ t) := by
    rw [hI, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (2 * Real.pi))]
    exact mul_le_mul_of_nonneg_left
      (norm_integral_perronPoly_compareKernel_le c M hApos hHpos hHle ht₀ hlow hT.le)
      (by positivity)
  have hrest : ‖S - I‖ ≤ perronNearError K M ⌊x + h⌋₊ 1 T + perronNearError K M ⌊x⌋₊ 1 T
      + (H / H₁) * (perronNearError K M ⌊x + h₁⌋₊ 1 T + perronNearError K M ⌊x⌋₊ 1 T) := hbase
  linarith [hInorm, hrest]

end

end RHTower.Sieve
