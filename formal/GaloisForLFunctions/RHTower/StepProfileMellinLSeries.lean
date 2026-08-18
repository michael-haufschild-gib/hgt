import GaloisForLFunctions.RHTower.AbelTailLSeries
import GaloisForLFunctions.HTGeometry.StepProfileMellinTransform

/-!
# The Mellin transform of a summatory profile is its `L`-series

Combining the integral form of Abel summation with the increment-series form gives, for a real
source `b` whose partial sums are `O(N^θ)` and `Re s > max(0, θ)` inside the domain of
convergence,

```text
s ∫_1^∞ ( ∑_{m ≤ x} b m ) x^{-s-1} dx  =  ∑_{n ≥ 1} b n n^{-s} .
```
-/

noncomputable section

open MeasureTheory Set Complex

namespace RHTower

/-- **Mellin form of Abel summation.**  The Mellin transform of the summatory step profile is
`1/s` times the `L`-series of the source. -/
theorem mellin_sourcePartialSum_eq_LSeries {b : ℕ → ℝ} {C θ : ℝ} (hC : 0 ≤ C)
    (hb : ∀ N : ℕ, |sourcePartialSum b N| ≤ C * (N : ℝ) ^ θ) {s : ℂ} (hs : 0 < s.re)
    (hθs : θ < s.re) (hsum : LSeriesSummable (fun n => (b n : ℂ)) s) :
    s * (∫ x in Set.Ioi (1:ℝ), (sourcePartialSum b ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1))
      = LSeries (fun n => (b n : ℂ)) s := by
  rw [GaloisForLFunctions.HTGeometry.mellin_stepProfile_eq_tsum hC hb hs hθs]
  rw [← abelTailSeries_sourcePartialSum hC hb hs hθs hsum, abelTailSeries]

/-- The real partial sums of a complex source inherit its norm bound. -/
theorem abs_re_sourcePartialSum_le {b : ℕ → ℂ} {C θ : ℝ}
    (hb : ∀ N : ℕ, ‖∑ m ∈ Finset.Icc 1 N, b m‖ ≤ C * (N : ℝ) ^ θ) (N : ℕ) :
    |sourcePartialSum (fun n => (b n).re) N| ≤ C * (N : ℝ) ^ θ := by
  have h1 : sourcePartialSum (fun n => (b n).re) N = (∑ m ∈ Finset.Icc 1 N, b m).re := by
    rw [sourcePartialSum, Complex.re_sum]
  rw [h1]
  exact le_trans (Complex.abs_re_le_norm _) (hb N)

/-- The imaginary partial sums of a complex source inherit its norm bound. -/
theorem abs_im_sourcePartialSum_le {b : ℕ → ℂ} {C θ : ℝ}
    (hb : ∀ N : ℕ, ‖∑ m ∈ Finset.Icc 1 N, b m‖ ≤ C * (N : ℝ) ^ θ) (N : ℕ) :
    |sourcePartialSum (fun n => (b n).im) N| ≤ C * (N : ℝ) ^ θ := by
  have h1 : sourcePartialSum (fun n => (b n).im) N = (∑ m ∈ Finset.Icc 1 N, b m).im := by
    rw [sourcePartialSum, Complex.im_sum]
  rw [h1]
  exact le_trans (Complex.abs_im_le_norm _) (hb N)

/-- A complex partial sum splits into its real and imaginary partial sums. -/
theorem complexPartialSum_split (b : ℕ → ℂ) (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, b m)
      = ((sourcePartialSum (fun n => (b n).re) N : ℝ) : ℂ)
        + Complex.I * ((sourcePartialSum (fun n => (b n).im) N : ℝ) : ℂ) := by
  have h1 : ((sourcePartialSum (fun n => (b n).re) N : ℝ) : ℂ)
      = ∑ m ∈ Finset.Icc 1 N, ((b m).re : ℂ) := by
    rw [sourcePartialSum, Complex.ofReal_sum]
  have h2 : ((sourcePartialSum (fun n => (b n).im) N : ℝ) : ℂ)
      = ∑ m ∈ Finset.Icc 1 N, ((b m).im : ℂ) := by
    rw [sourcePartialSum, Complex.ofReal_sum]
  rw [h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  apply Complex.ext <;> simp

open GaloisForLFunctions.HTGeometry in
/-- The Mellin integrand of a complex summatory profile is integrable. -/
theorem integrableOn_complexPartialSum {b : ℕ → ℂ} {C θ : ℝ} (hC : 0 ≤ C)
    (hb : ∀ N : ℕ, ‖∑ m ∈ Finset.Icc 1 N, b m‖ ≤ C * (N : ℝ) ^ θ) {s : ℂ} (hs : 0 < s.re)
    (hθs : θ < s.re) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, b m) * (x : ℂ) ^ (-s - 1)) (Set.Ioi (1:ℝ)) := by
  have hintr := integrableOn_stepProfile (R := sourcePartialSum (fun n => (b n).re)) hC
    (abs_re_sourcePartialSum_le hb) hs hθs (s := s)
  have hinti := integrableOn_stepProfile (R := sourcePartialSum (fun n => (b n).im)) hC
    (abs_im_sourcePartialSum_le hb) hs hθs (s := s)
  refine (hintr.add (hinti.const_mul Complex.I)).congr ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with x _
  show ((sourcePartialSum (fun n => (b n).re) ⌊x⌋₊ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
      + Complex.I * (((sourcePartialSum (fun n => (b n).im) ⌊x⌋₊ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
    = (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, b m) * (x : ℂ) ^ (-s - 1)
  rw [complexPartialSum_split b ⌊x⌋₊]
  ring

open GaloisForLFunctions.HTGeometry in
/-- **Mellin form of Abel summation, complex coefficients.**  Splitting a complex source into its
real and imaginary parts reduces to the real statement. -/
theorem mellin_complexPartialSum_eq_LSeries {b : ℕ → ℂ} {C θ : ℝ} (hC : 0 ≤ C)
    (hb : ∀ N : ℕ, ‖∑ m ∈ Finset.Icc 1 N, b m‖ ≤ C * (N : ℝ) ^ θ) {s : ℂ} (hs : 0 < s.re)
    (hθs : θ < s.re) (hsum : LSeriesSummable b s) :
    s * (∫ x in Set.Ioi (1:ℝ), (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, b m) * (x : ℂ) ^ (-s - 1))
      = LSeries b s := by
  classical
  set br : ℕ → ℝ := fun n => (b n).re with hbr
  set bi : ℕ → ℝ := fun n => (b n).im with hbi
  have hsplitSum : ∀ N : ℕ, (∑ m ∈ Finset.Icc 1 N, b m)
      = ((sourcePartialSum br N : ℝ) : ℂ) + Complex.I * ((sourcePartialSum bi N : ℝ) : ℂ) := by
    intro N
    have h1 : ((sourcePartialSum br N : ℝ) : ℂ) = ∑ m ∈ Finset.Icc 1 N, ((b m).re : ℂ) := by
      rw [sourcePartialSum, hbr, Complex.ofReal_sum]
    have h2 : ((sourcePartialSum bi N : ℝ) : ℂ) = ∑ m ∈ Finset.Icc 1 N, ((b m).im : ℂ) := by
      rw [sourcePartialSum, hbi, Complex.ofReal_sum]
    rw [h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    apply Complex.ext <;> simp
  have hbrb : ∀ N : ℕ, |sourcePartialSum br N| ≤ C * (N : ℝ) ^ θ := by
    intro N
    have h1 : sourcePartialSum br N = (∑ m ∈ Finset.Icc 1 N, b m).re := by
      rw [sourcePartialSum, hbr, Complex.re_sum]
    rw [h1]
    exact le_trans (Complex.abs_re_le_norm _) (hb N)
  have hbib : ∀ N : ℕ, |sourcePartialSum bi N| ≤ C * (N : ℝ) ^ θ := by
    intro N
    have h1 : sourcePartialSum bi N = (∑ m ∈ Finset.Icc 1 N, b m).im := by
      rw [sourcePartialSum, hbi, Complex.im_sum]
    rw [h1]
    exact le_trans (Complex.abs_im_le_norm _) (hb N)
  have hsumr : LSeriesSummable (fun n => (br n : ℂ)) s := by
    refine Summable.of_norm_bounded (g := fun n => ‖LSeries.term b s n‖) hsum.norm ?_
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero (by omega), LSeries.term_of_ne_zero (by omega),
        norm_div, norm_div]
      gcongr
      simpa [hbr] using Complex.abs_re_le_norm (b n)
  have hsumi : LSeriesSummable (fun n => (bi n : ℂ)) s := by
    refine Summable.of_norm_bounded (g := fun n => ‖LSeries.term b s n‖) hsum.norm ?_
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero (by omega), LSeries.term_of_ne_zero (by omega),
        norm_div, norm_div]
      gcongr
      simpa [hbi] using Complex.abs_im_le_norm (b n)
  have hLsplit : LSeries b s
      = LSeries (fun n => (br n : ℂ)) s + Complex.I * LSeries (fun n => (bi n : ℂ)) s := by
    rw [LSeries, LSeries, LSeries, ← tsum_mul_left, ← Summable.tsum_add hsumr (hsumi.mul_left Complex.I)]
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero (by omega : n ≠ 0), LSeries.term_of_ne_zero (by omega : n ≠ 0),
        LSeries.term_of_ne_zero (by omega : n ≠ 0), hbr, hbi]
      rw [← mul_div_assoc, ← add_div]
      congr 1
      apply Complex.ext <;> simp
  have hintr := integrableOn_stepProfile hC hbrb hs hθs (s := s)
  have hinti := integrableOn_stepProfile hC hbib hs hθs (s := s)
  have hintegral : (∫ x in Set.Ioi (1:ℝ), (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, b m) * (x : ℂ) ^ (-s - 1))
      = (∫ x in Set.Ioi (1:ℝ), ((sourcePartialSum br ⌊x⌋₊ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
        + Complex.I *
          ∫ x in Set.Ioi (1:ℝ), ((sourcePartialSum bi ⌊x⌋₊ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add hintr (hinti.const_mul _)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro x _
    show (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, b m) * (x : ℂ) ^ (-s - 1)
      = ((sourcePartialSum br ⌊x⌋₊ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
        + Complex.I * (((sourcePartialSum bi ⌊x⌋₊ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
    rw [hsplitSum ⌊x⌋₊]
    ring
  rw [hintegral, mul_add, mellin_sourcePartialSum_eq_LSeries hC hbrb hs hθs hsumr, hLsplit]
  rw [← mul_assoc, mul_comm s Complex.I, mul_assoc,
    mellin_sourcePartialSum_eq_LSeries hC hbib hs hθs hsumi]

end RHTower

end
