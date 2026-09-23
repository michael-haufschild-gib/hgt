import GaloisForLFunctions.RHTower.BandTrialSeries

/-!
# The Kaiser–Bessel trial function and its band transform

The Kaiser–Bessel trial function of the band concentration problem is

```text
K_c(x) = sum_k (c² (1-x²)/4)^k/(k!)²      (= I_0(c sqrt(1-x²))),
```

a nonnegative weight on `[-1, 1]`, and its finite-Fourier transform is the odd-factorial series

```text
∫_(-1)^(1 : ℕ) K_c(x) cos(omega x) dx = sum_m 2 (c² - omega²)^m/(2m+1)!.
```

Inside the band every term of the right-hand series is positive, so a single term bounds the transform
from below — which is what makes the trial's in-band spectral mass exponentially large.  Outside the
band the series is `2 sin(sqrt(omega²-c²))/sqrt(omega²-c²)`, whose square is integrable with a
polynomial bound.  Together these give the upper envelope of the band leakage at the rate `e^(-2c)`.

The proof assembles the pieces: term-by-term integration in the weight exponent (dominated by the
exponential series), the moment expansion of each weight transform, the coefficient identity, and the
antidiagonal collapse.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory intervalIntegral

/-- The Kaiser–Bessel trial weight on the band. -/
def kaiserTrial (c x : ℝ) : ℝ :=
  ∑' k : ℕ, (c ^ 2 * (1 - x ^ 2) / 4) ^ k / (Nat.factorial k : ℝ) ^ 2

/-- The trial weight is even: each term depends on `x` only through `x²`. -/
theorem kaiserTrial_even (c x : ℝ) : kaiserTrial c (-x) = kaiserTrial c x := by
  rw [kaiserTrial, kaiserTrial]
  refine tsum_congr fun k => ?_
  rw [neg_sq]

/-- Squared factorials dominate factorials, so the trial series converges. -/
theorem summable_kaiserTerm (u : ℝ) :
    Summable fun k : ℕ => u ^ k / (Nat.factorial k : ℝ) ^ 2 := by
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial |u|) fun k => ?_
  have hkpos : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hk1 : (1 : ℝ) ≤ (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_pow, abs_of_pos hkpos, sq]
  rw [div_le_div_iff₀ (by positivity) hkpos]
  have hsq : (Nat.factorial k : ℝ) * 1 ≤ (Nat.factorial k : ℝ) * (Nat.factorial k : ℝ) := by
    exact mul_le_mul_of_nonneg_left hk1 (le_of_lt hkpos)
  nlinarith [pow_nonneg (abs_nonneg u) k, hkpos, hk1]

/-- **The band transform of the Kaiser–Bessel trial is the odd-factorial series.** -/
theorem integral_kaiserTrial_cos (c ω : ℝ) :
    (∫ x in (-1 : ℝ)..1, kaiserTrial c x * Real.cos (ω * x))
      = ∑' m : ℕ, 2 * (c ^ 2 - ω ^ 2) ^ m / (Nat.factorial (2 * m + 1) : ℝ) := by
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  set G : ℕ → ℝ → ℝ := fun k x =>
    (c ^ 2 / 4) ^ k / (Nat.factorial k : ℝ) ^ 2 * ((1 - x ^ 2) ^ k * Real.cos (ω * x)) with hG
  have hcont : ∀ k, Continuous (G k) := by
    intro k
    rw [hG]
    fun_prop
  have hint : ∀ k, Integrable (G k) (volume.restrict (Set.Ioc (-1 : ℝ) 1)) := fun k =>
    (hcont k).integrableOn_Ioc
  -- the pointwise bound on the band
  have hptbound : ∀ (k : ℕ), ∀ x ∈ Set.Ioc (-1 : ℝ) 1,
      ‖G k x‖ ≤ (c ^ 2 / 4) ^ k / (Nat.factorial k : ℝ) ^ 2 := by
    intro k x hx
    have hx1 : |x| ≤ 1 := by
      rw [abs_le]
      exact ⟨le_of_lt hx.1, hx.2⟩
    have hw : |1 - x ^ 2| ≤ 1 := by
      rw [abs_le]
      constructor
      · nlinarith [sq_nonneg x, abs_le.mp hx1]
      · nlinarith [sq_nonneg x]
    have hkpos : (0 : ℝ) < (Nat.factorial k : ℝ) ^ 2 := by
      have : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
      positivity
    have hcoef : (0 : ℝ) ≤ (c ^ 2 / 4) ^ k / (Nat.factorial k : ℝ) ^ 2 := by positivity
    have hcoefabs : |(c ^ 2 / 4) ^ k / (Nat.factorial k : ℝ) ^ 2|
        = (c ^ 2 / 4) ^ k / (Nat.factorial k : ℝ) ^ 2 := abs_of_nonneg hcoef
    have hnorm : ‖G k x‖
        = (c ^ 2 / 4) ^ k / (Nat.factorial k : ℝ) ^ 2 * (|1 - x ^ 2| ^ k * |Real.cos (ω * x)|) := by
      show |(c ^ 2 / 4) ^ k / (Nat.factorial k : ℝ) ^ 2 *
          ((1 - x ^ 2) ^ k * Real.cos (ω * x))| = _
      rw [abs_mul, hcoefabs, abs_mul, abs_pow]
    rw [hnorm]
    have hfac : |1 - x ^ 2| ^ k * |Real.cos (ω * x)| ≤ 1 := by
      have h1 : |1 - x ^ 2| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg _) hw
      have h2 : |Real.cos (ω * x)| ≤ 1 := Real.abs_cos_le_one _
      calc |1 - x ^ 2| ^ k * |Real.cos (ω * x)| ≤ 1 * 1 := by
            gcongr
        _ = 1 := by norm_num
    calc (c ^ 2 / 4) ^ k / (Nat.factorial k : ℝ) ^ 2 * (|1 - x ^ 2| ^ k * |Real.cos (ω * x)|)
        ≤ (c ^ 2 / 4) ^ k / (Nat.factorial k : ℝ) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hfac hcoef
      _ = (c ^ 2 / 4) ^ k / (Nat.factorial k : ℝ) ^ 2 := mul_one _
  have hnormbound : ∀ k : ℕ,
      (∫ x, ‖G k x‖ ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)))
        ≤ 2 * ((c ^ 2 / 4) ^ k / (Nat.factorial k : ℝ) ^ 2) := by
    intro k
    have hmono : (∫ x, ‖G k x‖ ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)))
        ≤ ∫ _x : ℝ, (c ^ 2 / 4) ^ k / (Nat.factorial k : ℝ) ^ 2
            ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)) :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun x => norm_nonneg _)
        (integrable_const _)
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          exact hptbound k x hx)
    refine hmono.trans ?_
    rw [MeasureTheory.integral_const, smul_eq_mul, bandMeasure_real_univ]
  have hsummable : Summable fun k : ℕ =>
      (∫ x, ‖G k x‖ ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1))) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun x => norm_nonneg _)
      hnormbound ((summable_kaiserTerm (c ^ 2 / 4)).mul_left 2)
  have hkey := MeasureTheory.integral_tsum_of_summable_integral_norm hint hsummable
  -- the series sums to the trial times the cosine
  have hsumpt : ∀ x : ℝ, (∑' k : ℕ, G k x) = kaiserTrial c x * Real.cos (ω * x) := by
    intro x
    rw [hG, kaiserTrial, ← tsum_mul_right]
    refine tsum_congr fun k => ?_
    have hpow : (c ^ 2 * (1 - x ^ 2) / 4) ^ k = (c ^ 2 / 4) ^ k * (1 - x ^ 2) ^ k := by
      rw [← mul_pow]
      congr 1
      ring
    rw [hpow]
    ring
  -- each term is the inner series of trial terms
  have hterm : ∀ k : ℕ, (∫ x, G k x ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)))
      = ∑' j : ℕ, trialTerm c ω (j, k) := by
    intro k
    have hGint : (∫ x, G k x ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)))
        = (c ^ 2 / 4) ^ k / (Nat.factorial k : ℝ) ^ 2 *
          ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ k * Real.cos (ω * x) := by
      rw [intervalIntegral.integral_of_le hle, hG]
      exact MeasureTheory.integral_const_mul _ _
    rw [hGint, integral_trialWeight_cos k ω, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [trialCoeff_eq c ω j k, trialTerm]
  -- assemble
  have hswap : (∑' k : ℕ, ∑' j : ℕ, trialTerm c ω (j, k))
      = ∑' p : ℕ × ℕ, trialTerm c ω p := by
    have hsum := summable_trialTerm c ω
    have hsumswap : Summable fun q : ℕ × ℕ => trialTerm c ω (q.2, q.1) :=
      (Equiv.prodComm ℕ ℕ).summable_iff.mpr hsum
    have hfib : ∀ k : ℕ, Summable fun j : ℕ => trialTerm c ω (j, k) := fun k =>
      hsumswap.prod_factor k
    have h1 : (∑' q : ℕ × ℕ, trialTerm c ω (q.2, q.1))
        = ∑' k : ℕ, ∑' j : ℕ, trialTerm c ω (j, k) := hsumswap.tsum_prod' hfib
    have h2 : (∑' q : ℕ × ℕ, trialTerm c ω (q.2, q.1)) = ∑' p : ℕ × ℕ, trialTerm c ω p :=
      (Equiv.prodComm ℕ ℕ).tsum_eq (trialTerm c ω)
    rw [← h1, h2]
  rw [intervalIntegral.integral_of_le hle,
    ← MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsumpt), ← hkey]
  rw [show (∑' k : ℕ, ∫ x, G k x ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)))
      = ∑' k : ℕ, ∑' j : ℕ, trialTerm c ω (j, k) from tsum_congr hterm]
  rw [hswap, tsum_trialTerm_eq]

end GaloisForLFunctions.RHTower

end
