import GaloisForLFunctions.RHTower.TrigammaVertical
import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic

/-!
# A quantitative vertical lower bound for the trigamma imaginary part

On the vertical line `σ + it` with `0 < σ ≤ 1` the trigamma series

```text
−Im ψ′(σ + it) = ∑ₙ 2(σ+n)t / ((σ+n)² + t²)²
```

has only nonnegative terms, so any partial sum is a lower bound.  Summing the first `⌈t⌉` terms —
each of which is at least `(σ+n)/(19 t³)` once `(σ+n)² + t² ≤ 7t²` — gives a bound of the exact
order `1/t`.

This is the quantitative input behind the second-derivative test on the critical line: the Hardy
phase satisfies `θ″(t) = −Im ψ′(1/4 + it/2)/4`, so the bound below makes `θ″(t) ≳ 1/t`.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- The `n`-th term of the trigamma imaginary-part series, with its sign removed. -/
def trigammaVerticalTerm (σ t : ℝ) (n : ℕ) : ℝ :=
  2 * (σ + n) * t / (((σ + n) ^ 2 + t ^ 2) ^ 2)

theorem trigammaVerticalTerm_nonneg {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (n : ℕ) :
    0 ≤ trigammaVerticalTerm σ t n := by
  rw [trigammaVerticalTerm]
  have h1 : 0 ≤ 2 * (σ + n) * t := by positivity
  positivity

theorem im_inv_sq_eq {σ t : ℝ} (n : ℕ) :
    (((((σ : ℂ) + (t : ℂ) * Complex.I) + (n : ℂ)) ^ 2)⁻¹).im
      = -trigammaVerticalTerm σ t n := by
  have hzn : ((σ : ℂ) + (t : ℂ) * Complex.I) + (n : ℂ)
      = ((σ + n : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hzn, ← inv_pow, pow_two, Complex.mul_im, Complex.inv_re, Complex.inv_im,
    Complex.normSq_add_mul_I]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    zero_add, add_zero]
  rw [trigammaVerticalTerm]
  field_simp
  ring


/-- Every partial sum of the trigamma imaginary-part series is a lower bound. -/
theorem partialSum_le_neg_im_deriv_digamma {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (N : ℕ) :
    ∑ n ∈ Finset.range N, trigammaVerticalTerm σ t n
      ≤ -(deriv Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).im := by
  set z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hz
  have hzre : 0 < z.re := by
    rw [hz]
    simpa using hσ
  have hlim := deriv_digamma_partialSum_tendsto hzre
  have hlimim : Tendsto (fun M : ℕ => (∑ n ∈ Finset.range M, ((z + (n : ℂ)) ^ 2)⁻¹).im)
      atTop (nhds (deriv Complex.digamma z).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp hlim
  have hsum : ∀ M : ℕ, (∑ n ∈ Finset.range M, ((z + (n : ℂ)) ^ 2)⁻¹).im
      = -∑ n ∈ Finset.range M, trigammaVerticalTerm σ t n := by
    intro M
    rw [Complex.im_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun n _ => by rw [hz, im_inv_sq_eq]
  have hlim' : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M, trigammaVerticalTerm σ t n)
      atTop (nhds (-(deriv Complex.digamma z).im)) := by
    have := hlimim.neg
    refine this.congr fun M => ?_
    rw [hsum M, neg_neg]
  refine Monotone.ge_of_tendsto ?_ hlim' N
  intro a b hab
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) ?_
  intro n _ _
  exact trigammaVerticalTerm_nonneg hσ ht n

/-- **The quantitative vertical trigamma bound.**  On the vertical line `σ + it` with
`0 < σ ≤ 1` and `t ≥ 2`, the imaginary part of `ψ′` is at most `−1/(22 t)`. -/
theorem neg_im_deriv_digamma_lower_bound {σ t : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (ht : 2 ≤ t) :
    1 / (50 * t) ≤ -(deriv Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).im := by
  have htpos : (0 : ℝ) < t := by linarith
  set N : ℕ := ⌈t⌉₊ with hN
  have hNge : t ≤ (N : ℝ) := Nat.le_ceil t
  have hNlt : (N : ℝ) < t + 1 := Nat.ceil_lt_add_one htpos.le
  have hlow : ∀ n ∈ Finset.range N,
      2 * (σ + n) / (25 * t ^ 3) ≤ trigammaVerticalTerm σ t n := by
    intro n hn
    have hnsucc : (n : ℝ) + 1 ≤ (N : ℝ) := by
      have hnat : n + 1 ≤ N := Finset.mem_range.mp hn
      exact_mod_cast hnat
    have hnle : (n : ℝ) ≤ t := by linarith
    have hsnpos : (0 : ℝ) < σ + n := by positivity
    have hsn : σ + n ≤ 2 * t := by linarith
    have hdpos : (0 : ℝ) < ((σ + n) ^ 2 + t ^ 2) ^ 2 := by positivity
    have hsq : (σ + n) ^ 2 ≤ 4 * t ^ 2 := by nlinarith [hsnpos, hsn, htpos]
    have hden : ((σ + n) ^ 2 + t ^ 2) ^ 2 ≤ 25 * t ^ 4 := by
      nlinarith [hsq, sq_nonneg t, htpos, sq_nonneg (σ + n)]
    have hnum : (0 : ℝ) ≤ 2 * (σ + n) * t := by positivity
    have hstep : 2 * (σ + n) * t / (25 * t ^ 4) ≤ trigammaVerticalTerm σ t n := by
      rw [trigammaVerticalTerm]
      exact div_le_div_of_nonneg_left hnum hdpos hden
    refine le_trans (le_of_eq ?_) hstep
    field_simp
  have hN2 : 2 ≤ N := by
    have : (2 : ℝ) ≤ (N : ℝ) := le_trans ht hNge
    exact_mod_cast this
  have hgauss : ∑ n ∈ Finset.range N, ((n : ℕ) : ℝ) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by
    have hnat := Finset.sum_range_id_mul_two N
    have hcast : ((∑ i ∈ Finset.range N, i : ℕ) : ℝ) * 2 = ((N * (N - 1) : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hnat
    rw [Nat.cast_sum] at hcast
    have hsub : ((N * (N - 1) : ℕ) : ℝ) = (N : ℝ) * ((N : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega)]
      norm_num
    rw [hsub] at hcast
    linarith
  have hsum : (1 : ℝ) / (50 * t) ≤ ∑ n ∈ Finset.range N, trigammaVerticalTerm σ t n := by
    refine le_trans ?_ (Finset.sum_le_sum hlow)
    have hid : ∑ n ∈ Finset.range N, (2 * (σ + n) / (25 * t ^ 3))
        = (2 / (25 * t ^ 3)) * ∑ n ∈ Finset.range N, (σ + (n : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hid]
    have hlin : ∑ n ∈ Finset.range N, ((n : ℕ) : ℝ)
        ≤ ∑ n ∈ Finset.range N, (σ + (n : ℝ)) :=
      Finset.sum_le_sum fun n _ => by linarith
    have hbig : (t : ℝ) * (t - 1) / 2 ≤ ∑ n ∈ Finset.range N, (σ + (n : ℝ)) := by
      refine le_trans ?_ hlin
      rw [hgauss]
      nlinarith [hNge, ht]
    have hcoef : (0 : ℝ) < 2 / (25 * t ^ 3) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hbig hcoef.le
    refine le_trans ?_ hmul
    have hrhs : 2 / (25 * t ^ 3) * (t * (t - 1) / 2) = (t - 1) / (25 * t ^ 2) := by
      field_simp
    rw [hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [ht, htpos]
  linarith [partialSum_le_neg_im_deriv_digamma hσ htpos N, hsum]


/-! ## The Hardy phase has second derivative of exact order `1/t` -/

/-- **The quantitative second-jet law.**  For `t ≥ 4` the Hardy phase velocity increases at least
at rate `1/(100 t)`; this is the `θ″(t) ≍ 1/(2t)` input of the second-derivative test. -/
theorem deriv_gammaHardyPhaseRate_lower_bound {t : ℝ} (ht : 4 ≤ t) :
    1 / (100 * t) ≤ deriv gammaHardyPhaseRate t := by
  have htpos : (0 : ℝ) < t := by linarith
  have harg : linePt t / 2 = ((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
    unfold linePt
    push_cast
    ring
  have hbound := neg_im_deriv_digamma_lower_bound (σ := (1 / 4 : ℝ)) (t := t / 2)
    (by norm_num) (by norm_num) (by linarith)
  rw [deriv_gammaHardyPhaseRate, harg]
  have hval : (1 : ℝ) / (50 * (t / 2)) = 1 / (25 * t) := by
    field_simp
  rw [hval] at hbound
  have h25 : (0 : ℝ) < 25 * t := by linarith
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)] at *
  nlinarith [hbound, htpos]

end RHTower
