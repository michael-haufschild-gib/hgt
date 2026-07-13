import GaloisForLFunctions.RHTower.DigammaAsymptotic

/-!
# The absolutely convergent Gauss series for digamma

The repository already proves Gauss's finite-limit formula for `digamma`.  This module turns that
ordered limit into the absolutely convergent reciprocal-difference series.  Absolute convergence
is the input needed for termwise Laplace/Fourier evaluation of the rectangular archimedean edge.
-/

open Complex Filter MeasureTheory Set Real
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The absolutely convergent Gauss-series summand for the digamma function. -/
def gaussDigammaSeriesTerm (s : ℂ) (n : ℕ) : ℂ :=
  1 / ((n : ℂ) + 1) - 1 / (s + n)

theorem gaussDigammaSeriesTerm_eq
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    gaussDigammaSeriesTerm s n =
      (s - 1) / (((n : ℂ) + 1) * (s + n)) := by
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (by positivity : (n : ℝ) + 1 ≠ 0)
  have hsn : s + (n : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hre
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  unfold gaussDigammaSeriesTerm
  field_simp [hn1, hsn]
  ring

/-- The Gauss-series summands are absolutely summable throughout the open right half-plane. -/
theorem summable_norm_gaussDigammaSeriesTerm
    {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ => ‖gaussDigammaSeriesTerm s n‖) := by
  let c : ℝ := min 1 s.re
  have hc : 0 < c := lt_min (by norm_num) hs
  have hbase : Summable (fun n : ℕ => 1 / (((n : ℝ) + 1) ^ 2)) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
    apply h.congr
    intro n
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    simp only [Real.rpow_two]
  apply (hbase.mul_left (‖s - 1‖ / c)).of_nonneg_of_le
  · exact fun n => norm_nonneg _
  intro n
  rw [gaussDigammaSeriesTerm_eq hs, norm_div, norm_mul]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcs : c ≤ s.re := min_le_right _ _
  have hsnre : c * ((n : ℝ) + 1) ≤ (s + (n : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    nlinarith
  have hsnorm : c * ((n : ℝ) + 1) ≤ ‖s + (n : ℂ)‖ :=
    hsnre.trans (Complex.re_le_norm _)
  have hn1pos : 0 < (n : ℝ) + 1 := by positivity
  have hn1ne : ((n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (by positivity : (n : ℝ) + 1 ≠ 0)
  have hsnne : s + (n : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hre
    linarith
  have hdenpos : 0 < ‖((n : ℂ) + 1)‖ * ‖s + (n : ℂ)‖ :=
    mul_pos (norm_pos_iff.mpr hn1ne) (norm_pos_iff.mpr hsnne)
  have hden : c * (((n : ℝ) + 1) ^ 2) ≤
      ‖((n : ℂ) + 1)‖ * ‖s + (n : ℂ)‖ := by
    have hnorm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
      rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by
        push_cast
        ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn1pos]
    rw [hnorm]
    nlinarith
  calc
    ‖s - 1‖ / (‖((n : ℂ) + 1)‖ * ‖s + (n : ℂ)‖) ≤
        ‖s - 1‖ / (c * ((n : ℝ) + 1) ^ 2) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hden
    _ = (‖s - 1‖ / c) * (1 / ((n : ℝ) + 1) ^ 2) := by
      field_simp
      <;> ring

theorem summable_gaussDigammaSeriesTerm
    {s : ℂ} (hs : 0 < s.re) :
    Summable (gaussDigammaSeriesTerm s) :=
  summable_norm_iff.mp (summable_norm_gaussDigammaSeriesTerm hs)

private theorem tendsto_harmonic_succ_sub_log_sub_euler :
    Tendsto
      (fun n : ℕ =>
        (harmonic (n + 1) : ℝ) - Real.log n -
          Real.eulerMascheroniConstant)
      atTop (nhds 0) := by
  have hmain : Tendsto
      (fun n : ℕ =>
        (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant)
      atTop (nhds 0) := by
    simpa only [sub_self] using
      Real.tendsto_harmonic_sub_log.sub_const Real.eulerMascheroniConstant
  have hinv : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹)) atTop (nhds 0) := by
    have hcast : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp hcast
  convert hmain.add hinv using 1
  · funext n
    rw [harmonic_succ]
    push_cast
    ring
  · simp

private theorem tendsto_gaussDigammaSeries_partial
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ => ∑ j ∈ Finset.range (n + 1), gaussDigammaSeriesTerm s j)
      atTop
      (nhds (Complex.digamma s + Real.eulerMascheroniConstant)) := by
  have hcorrR := tendsto_harmonic_succ_sub_log_sub_euler
  have hcorrR' : Tendsto
      (fun n : ℕ => (harmonic (n + 1) : ℝ) - Real.log n)
      atTop (nhds Real.eulerMascheroniConstant) := by
    convert hcorrR.add_const Real.eulerMascheroniConstant using 1 <;>
      simp <;> ring
  have hcorr : Tendsto
      (fun n : ℕ =>
        (((harmonic (n + 1) : ℝ) - Real.log n : ℝ) : ℂ))
      atTop (nhds (Real.eulerMascheroniConstant : ℂ)) := by
    exact (Complex.continuous_ofReal.tendsto Real.eulerMascheroniConstant).comp hcorrR'
  have hsum := (gauss_digamma hs).add hcorr
  convert hsum using 1
  funext n
  simp_rw [gaussDigammaSeriesTerm]
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  have hharm :
      (∑ j ∈ Finset.range (n + 1), (1 : ℂ) / ((j : ℂ) + 1)) =
        ((harmonic (n + 1) : ℝ) : ℂ) := by
    symm
    exact harmonic_cast_eq (n + 1)
  rw [Finset.sum_sub_distrib, hharm, hlog]
  push_cast
  ring

/-- **Gauss series for digamma.**  On `Re s > 0`, digamma is Euler's constant plus an
absolutely convergent series of reciprocal differences. -/
theorem digamma_eq_neg_euler_add_tsum_gauss
    {s : ℂ} (hs : 0 < s.re) :
    Complex.digamma s =
      -(Real.eulerMascheroniConstant : ℂ) +
        ∑' n : ℕ, gaussDigammaSeriesTerm s n := by
  have hsum := summable_gaussDigammaSeriesTerm hs
  have hpartial : Tendsto
      (fun n : ℕ => ∑ j ∈ Finset.range n, gaussDigammaSeriesTerm s j)
      atTop
      (nhds (Complex.digamma s + Real.eulerMascheroniConstant)) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [Nat.add_comm] using tendsto_gaussDigammaSeries_partial hs
  have hhas : HasSum (gaussDigammaSeriesTerm s)
      (Complex.digamma s + Real.eulerMascheroniConstant) :=
    (hsum.hasSum_iff_tendsto_nat).mpr hpartial
  rw [hhas.tsum_eq]
  ring

/-! ## Elementary Laplace realization -/

/-- The time-domain exponential difference whose Laplace integral is one Gauss-series term. -/
def gaussDigammaLaplaceTerm (s : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (-((n : ℂ) + 1) * (t : ℂ)) -
    Complex.exp (-(s + n) * (t : ℂ))

theorem integrableOn_gaussDigammaLaplaceTerm
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    IntegrableOn (gaussDigammaLaplaceTerm s n) (Ioi 0) := by
  have hn : (-((n : ℂ) + 1)).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hsn : (-(s + n)).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  exact (integrableOn_exp_mul_complex_Ioi hn 0).sub
    (integrableOn_exp_mul_complex_Ioi hsn 0)

/-- Every Gauss reciprocal difference is exactly an elementary half-line Laplace integral. -/
theorem integral_gaussDigammaLaplaceTerm
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∫ t : ℝ in Ioi 0, gaussDigammaLaplaceTerm s n t) =
      gaussDigammaSeriesTerm s n := by
  have hn : (-((n : ℂ) + 1)).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hsn : (-(s + n)).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  change (∫ t : ℝ in Ioi 0,
      Complex.exp (-((n : ℂ) + 1) * (t : ℂ)) -
        Complex.exp (-(s + n) * (t : ℂ))) = _
  rw [integral_sub
    (integrableOn_exp_mul_complex_Ioi hn 0)
    (integrableOn_exp_mul_complex_Ioi hsn 0),
    integral_exp_mul_complex_Ioi hn 0,
    integral_exp_mul_complex_Ioi hsn 0]
  unfold gaussDigammaSeriesTerm
  simp [Complex.exp_zero, div_eq_mul_inv, add_comm]
  rw [show -s + -(n : ℂ) = -(s + n) by ring,
    show -(n : ℂ) + -1 = -((n : ℂ) + 1) by ring,
    inv_neg, inv_neg]
  ring

end


end RHTower
