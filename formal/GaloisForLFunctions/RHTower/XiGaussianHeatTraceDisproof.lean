import GaloisForLFunctions.RHTower.XiThermalSourceRelativeGapBound
import GaloisForLFunctions.RHTower.TraceHankelConverse

/-!
# Gaussian heat trace on the multiplicity-exact Xi divisor

For positive heat time `t`, the Gaussian multiplier
`exp (-t * xiSpectralPoint q ^ (2 : ℕ))` is absolutely summable over every Xi zero with its exact
analytic multiplicity.  The proof is unconditional: the open critical strip and the existing
completed-source height gap make the real part of every squared centered spectral coordinate a
fixed positive fraction of its norm square, while reciprocal-square summability controls the
resulting exponential tail.

Critical-line reflection makes the full complex trace real without RH.  Under RH every summand is
positive real, hence the trace is nonnegative.  Its strict-negative contrapositive is a formal,
unconditional RH-false endpoint for the parabolic shifted-moment lane.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Every centered Xi spectral square lies in a uniform right half-plane sector.  The rough
constant `1 / 2` is enough to dominate the Gaussian heat multiplier by the already summable
reciprocal-square divisor. -/
theorem xiSpectralPoint_normSq_lt_two_mul_sq_re (q : XiZeroCopy) :
    Complex.normSq (xiSpectralPoint q) <
      2 * (xiSpectralPoint q ^ (2 : ℕ)).re := by
  have hhorizontal : ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) < 1 / 4 :=
    xi_divisor_support_centered_re_sq_lt_quarter q.1
  have hheight := xiZeroCopy_two_lt_im_sq q
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
    simp [xiSpectralPoint]
  have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by
    simp [xiSpectralPoint]
  rw [Complex.normSq_apply]
  simp only [pow_two, Complex.mul_re]
  rw [hre, him]
  nlinarith [sq_nonneg ((q.1 : ℂ).re - 1 / 2)]

/-- One Gaussian heat multiplier on the centered, multiplicity-exact Xi divisor. -/
def xiGaussianHeatTerm (t : ℝ) (q : XiZeroCopy) : ℂ :=
  Complex.exp (-(t : ℂ) * xiSpectralPoint q ^ (2 : ℕ))

/-- At every positive time, the Gaussian heat multiplier is absolutely summable over the entire
Xi divisor with analytic multiplicity. -/
theorem summable_xiGaussianHeatTerm {t : ℝ} (ht : 0 < t) :
    Summable (xiGaussianHeatTerm t) := by
  apply Summable.of_norm_bounded
    (xiSpectralPoint_inv_sq_summable.mul_left (2 / t))
  intro q
  let A : ℝ := (xiSpectralPoint q ^ (2 : ℕ)).re
  let N : ℝ := Complex.normSq (xiSpectralPoint q)
  have hgap : N < 2 * A := by
    simpa only [N, A] using xiSpectralPoint_normSq_lt_two_mul_sq_re q
  have hN : 0 < N :=
    Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)
  have hA : 0 < A := by nlinarith
  have htA : 0 < t * A := mul_pos ht hA
  have hexp : Real.exp (-(t * A)) ≤ (t * A)⁻¹ := by
    rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos (t * A)) htA]
    nlinarith [Real.add_one_le_exp (t * A)]
  have hinv : (t * A)⁻¹ ≤ (2 / t) * (1 / N) := by
    rw [← one_div]
    calc
      1 / (t * A) ≤ 2 / (t * N) := by
        rw [div_le_div_iff₀ (mul_pos ht hA) (mul_pos ht hN)]
        nlinarith
      _ = (2 / t) * (1 / N) := by
        field_simp [ne_of_gt ht, ne_of_gt hN]
  calc
    ‖xiGaussianHeatTerm t q‖ = Real.exp (-(t * A)) := by
      rw [xiGaussianHeatTerm, Complex.norm_exp]
      simp [A, Complex.mul_re]
    _ ≤ (t * A)⁻¹ := hexp
    _ ≤ (2 / t) * (1 / N) := hinv
    _ = (2 / t) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
      rw [Complex.sq_norm]

/-- The Gaussian heat trace of the full centered Xi divisor. -/
def xiGaussianHeatTrace (t : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, xiGaussianHeatTerm t q

/-- Critical-line reflection conjugates each Gaussian heat summand. -/
theorem xiGaussianHeatTerm_lineConj (t : ℝ) (q : XiZeroCopy) :
    xiGaussianHeatTerm t (xiZeroCopyLineConjEquiv q) =
      (starRingEnd ℂ) (xiGaussianHeatTerm t q) := by
  rw [xiGaussianHeatTerm, xiGaussianHeatTerm, xiSpectralPoint_lineConj]
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- The full Xi Gaussian heat trace is real unconditionally. -/
theorem star_xiGaussianHeatTrace (t : ℝ) :
    (starRingEnd ℂ) (xiGaussianHeatTrace t) = xiGaussianHeatTrace t := by
  rw [xiGaussianHeatTrace, Complex.conj_tsum]
  calc
    (∑' q : XiZeroCopy, (starRingEnd ℂ) (xiGaussianHeatTerm t q)) =
        ∑' q : XiZeroCopy,
          xiGaussianHeatTerm t (xiZeroCopyLineConjEquiv q) := by
      apply tsum_congr
      intro q
      exact (xiGaussianHeatTerm_lineConj t q).symm
    _ = ∑' q : XiZeroCopy, xiGaussianHeatTerm t q := by
      exact xiZeroCopyLineConjEquiv.tsum_eq (xiGaussianHeatTerm t)

theorem xiGaussianHeatTrace_im_eq_zero (t : ℝ) :
    (xiGaussianHeatTrace t).im = 0 :=
  Complex.conj_eq_iff_im.mp (star_xiGaussianHeatTrace t)

/-- The real scalar whose strict negativity is the heat-trace RH-disproof witness. -/
def xiGaussianHeatTraceReal (t : ℝ) : ℝ :=
  (xiGaussianHeatTrace t).re

theorem xiGaussianHeatTraceReal_eq_tsum_re {t : ℝ} (ht : 0 < t) :
    xiGaussianHeatTraceReal t =
      ∑' q : XiZeroCopy, (xiGaussianHeatTerm t q).re := by
  rw [xiGaussianHeatTraceReal, xiGaussianHeatTrace,
    Complex.re_tsum (summable_xiGaussianHeatTerm ht)]

/-- RH makes the real Xi Gaussian heat trace nonnegative at every positive time. -/
theorem xiGaussianHeatTraceReal_nonneg_of_riemannHypothesis
    (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 < t) :
    0 ≤ xiGaussianHeatTraceReal t := by
  rw [xiGaussianHeatTraceReal_eq_tsum_re ht]
  apply tsum_nonneg
  intro q
  obtain ⟨x, hcoord⟩ := xiSpectralPoint_real_of_rh hRH q
  rw [xiGaussianHeatTerm, hcoord]
  simpa [Complex.exp_re, pow_two, Complex.mul_re, Complex.mul_im] using
    (Real.exp_nonneg (-(t * (x * x))))

/-- **Formal RH-false heat endpoint.**  A single strictly negative Gaussian heat-trace value at
positive time contradicts RH. -/
theorem not_riemannHypothesis_of_xiGaussianHeatTraceReal_neg
    {t : ℝ} (ht : 0 < t) (hneg : xiGaussianHeatTraceReal t < 0) :
    ¬ RiemannHypothesis := by
  intro hRH
  exact (not_lt_of_ge
    (xiGaussianHeatTraceReal_nonneg_of_riemannHypothesis hRH ht)) hneg

/-! ## Polynomial-square Gaussian filters -/

private theorem pow_mul_exp_neg_le_factorial_div_pow
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (n : ℕ) :
    x ^ n * Real.exp (-(c * x)) ≤ (n.factorial : ℝ) / c ^ n := by
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  have hcpow : 0 < c ^ n := pow_pos hc n
  have hseries := Real.pow_div_factorial_le_exp (c * x)
    (mul_nonneg hc.le hx.le) n
  have hpow : (c * x) ^ n ≤ Real.exp (c * x) * (n.factorial : ℝ) := by
    rw [div_le_iff₀ hfac] at hseries
    exact hseries
  have hneg : 0 ≤ Real.exp (-(c * x)) := (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_right hpow hneg
  have hcancel : Real.exp (c * x) * Real.exp (-(c * x)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  apply (le_div_iff₀ hcpow).2
  calc
    (x ^ n * Real.exp (-(c * x))) * c ^ n =
        (c * x) ^ n * Real.exp (-(c * x)) := by
      rw [mul_pow]
      ring
    _ ≤ (Real.exp (c * x) * (n.factorial : ℝ)) *
          Real.exp (-(c * x)) := hmul
    _ = (n.factorial : ℝ) := by
      calc
        Real.exp (c * x) * (n.factorial : ℝ) * Real.exp (-(c * x)) =
            (n.factorial : ℝ) *
              (Real.exp (c * x) * Real.exp (-(c * x))) := by ring
        _ = (n.factorial : ℝ) := by rw [hcancel]; ring

/-- Every monomial moment of the Xi Gaussian is absolutely summable. -/
theorem summable_xiGaussianHeatMonomialTerm
    {t : ℝ} (ht : 0 < t) (j : ℕ) :
    Summable (fun q : XiZeroCopy =>
      (xiSpectralPoint q ^ (2 : ℕ)) ^ j * xiGaussianHeatTerm t q) := by
  let c : ℝ := t / 2
  let C : ℝ := ((j + 1).factorial : ℝ) / c ^ (j + 1)
  have hc : 0 < c := by dsimp [c]; linarith
  apply Summable.of_norm_bounded
    (xiSpectralPoint_inv_sq_summable.mul_left C)
  intro q
  let A : ℝ := (xiSpectralPoint q ^ (2 : ℕ)).re
  let N : ℝ := Complex.normSq (xiSpectralPoint q)
  have hgap : N < 2 * A := by
    simpa only [N, A] using xiSpectralPoint_normSq_lt_two_mul_sq_re q
  have hN : 0 < N := Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)
  have hA : 0 < A := by nlinarith
  have hdecay : Real.exp (-(t * A)) ≤ Real.exp (-(c * N)) := by
    rw [Real.exp_le_exp]
    dsimp [c]
    nlinarith
  have hpoly := pow_mul_exp_neg_le_factorial_div_pow hc hN (j + 1)
  have hweighted :
      N ^ j * Real.exp (-(c * N)) ≤ C * (1 / N) := by
    rw [one_div, ← div_eq_mul_inv]
    apply (le_div_iff₀ hN).2
    calc
      (N ^ j * Real.exp (-(c * N))) * N =
          N ^ (j + 1) * Real.exp (-(c * N)) := by
        rw [pow_succ]
        ring
      _ ≤ C := by simpa only [C] using hpoly
  calc
    ‖(xiSpectralPoint q ^ (2 : ℕ)) ^ j * xiGaussianHeatTerm t q‖ =
        N ^ j * Real.exp (-(t * A)) := by
      rw [norm_mul, norm_pow, norm_pow, xiGaussianHeatTerm,
        Complex.norm_exp, Complex.sq_norm]
      simp [A, N, Complex.mul_re]
    _ ≤ N ^ j * Real.exp (-(c * N)) :=
      mul_le_mul_of_nonneg_left hdecay (pow_nonneg hN.le j)
    _ ≤ C * (1 / N) := hweighted
    _ = C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
      rw [Complex.sq_norm]

private theorem evalRealPolynomial_eq_sum (Q : Polynomial ℝ) (z : ℂ) :
    evalRealPolynomial Q z =
      ∑ k ∈ Finset.range (Q.natDegree + 1), (Q.coeff k : ℂ) * z ^ k := by
  rw [evalRealPolynomial, Polynomial.eval_eq_sum_range]
  simp only [Polynomial.natDegree_map_eq_of_injective
      (f := algebraMap ℝ ℂ) Complex.ofReal_injective,
    Polynomial.coeff_map, coe_algebraMap]

/-- A real polynomial in the squared spectral coordinate times the Gaussian is absolutely
summable over the Xi divisor. -/
theorem summable_xiGaussianHeatPolynomialTerm
    {t : ℝ} (ht : 0 < t) (Q : Polynomial ℝ) :
    Summable (fun q : XiZeroCopy =>
      evalRealPolynomial Q (xiSpectralPoint q ^ (2 : ℕ)) *
        xiGaussianHeatTerm t q) := by
  have hsum : Summable (fun q : XiZeroCopy =>
      ∑ k ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff k : ℂ) *
          ((xiSpectralPoint q ^ (2 : ℕ)) ^ k * xiGaussianHeatTerm t q)) := by
    apply summable_sum
    intro k hk
    exact (summable_xiGaussianHeatMonomialTerm ht k).mul_left
      (Q.coeff k : ℂ)
  apply hsum.congr
  intro q
  rw [evalRealPolynomial_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Polynomial-square Gaussian filter on one multiplicity copy of the squared Xi divisor. -/
def xiPolynomialGaussianHeatTerm
    (P : Polynomial ℝ) (t : ℝ) (q : XiZeroCopy) : ℂ :=
  evalRealPolynomial P (xiSpectralPoint q ^ (2 : ℕ)) ^ (2 : ℕ) *
    xiGaussianHeatTerm t q

theorem summable_xiPolynomialGaussianHeatTerm
    {t : ℝ} (ht : 0 < t) (P : Polynomial ℝ) :
    Summable (xiPolynomialGaussianHeatTerm P t) := by
  apply (summable_xiGaussianHeatPolynomialTerm ht (P * P)).congr
  intro q
  simp [xiPolynomialGaussianHeatTerm, evalRealPolynomial_mul, pow_two]

theorem xiPolynomialGaussianHeatTerm_lineConj
    (P : Polynomial ℝ) (t : ℝ) (q : XiZeroCopy) :
    xiPolynomialGaussianHeatTerm P t (xiZeroCopyLineConjEquiv q) =
      (starRingEnd ℂ) (xiPolynomialGaussianHeatTerm P t q) := by
  rw [xiPolynomialGaussianHeatTerm, xiPolynomialGaussianHeatTerm,
    xiSpectralPoint_lineConj, ← map_pow,
    evalRealPolynomial_conj, xiGaussianHeatTerm_lineConj,
    map_mul, map_pow]

/-- Multiplicity-exact polynomial-square Gaussian trace. -/
def xiPolynomialGaussianHeatTrace (P : Polynomial ℝ) (t : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, xiPolynomialGaussianHeatTerm P t q

/-- Every polynomial-square Gaussian trace is real unconditionally. -/
theorem star_xiPolynomialGaussianHeatTrace (P : Polynomial ℝ) (t : ℝ) :
    (starRingEnd ℂ) (xiPolynomialGaussianHeatTrace P t) =
      xiPolynomialGaussianHeatTrace P t := by
  rw [xiPolynomialGaussianHeatTrace, Complex.conj_tsum]
  calc
    (∑' q : XiZeroCopy,
        (starRingEnd ℂ) (xiPolynomialGaussianHeatTerm P t q)) =
        ∑' q : XiZeroCopy,
          xiPolynomialGaussianHeatTerm P t
            (xiZeroCopyLineConjEquiv q) := by
      apply tsum_congr
      intro q
      exact (xiPolynomialGaussianHeatTerm_lineConj P t q).symm
    _ = ∑' q : XiZeroCopy, xiPolynomialGaussianHeatTerm P t q := by
      exact xiZeroCopyLineConjEquiv.tsum_eq
        (xiPolynomialGaussianHeatTerm P t)

theorem xiPolynomialGaussianHeatTrace_im_eq_zero
    (P : Polynomial ℝ) (t : ℝ) :
    (xiPolynomialGaussianHeatTrace P t).im = 0 :=
  Complex.conj_eq_iff_im.mp (star_xiPolynomialGaussianHeatTrace P t)

/-- Real value of the polynomial-square Gaussian trace. -/
def xiPolynomialGaussianHeatTraceReal (P : Polynomial ℝ) (t : ℝ) : ℝ :=
  (xiPolynomialGaussianHeatTrace P t).re

/-- RH makes every polynomial-square Gaussian trace nonnegative. -/
theorem xiPolynomialGaussianHeatTraceReal_nonneg_of_riemannHypothesis
    (hRH : RiemannHypothesis) (P : Polynomial ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ xiPolynomialGaussianHeatTraceReal P t := by
  rw [xiPolynomialGaussianHeatTraceReal,
    xiPolynomialGaussianHeatTrace,
    Complex.re_tsum (summable_xiPolynomialGaussianHeatTerm ht P)]
  apply tsum_nonneg
  intro q
  obtain ⟨x, hcoord⟩ := xiSpectralPoint_real_of_rh hRH q
  rw [xiPolynomialGaussianHeatTerm, xiGaussianHeatTerm, hcoord]
  have hsq : (x : ℂ) ^ (2 : ℕ) = ((x ^ (2 : ℕ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hsq, evalRealPolynomial_ofReal]
  simpa [Complex.exp_re, pow_two, Complex.mul_re, Complex.mul_im] using
    mul_nonneg (sq_nonneg (Polynomial.eval (x * x) P))
      (Real.exp_nonneg (-(t * (x * x))))

/-- **Filtered formal RH-false endpoint.**  One strictly negative polynomial-square Gaussian
trace at positive time contradicts RH. -/
theorem not_riemannHypothesis_of_xiPolynomialGaussianHeatTraceReal_neg
    (P : Polynomial ℝ) {t : ℝ} (ht : 0 < t)
    (hneg : xiPolynomialGaussianHeatTraceReal P t < 0) :
    ¬ RiemannHypothesis := by
  intro hRH
  exact (not_lt_of_ge
    (xiPolynomialGaussianHeatTraceReal_nonneg_of_riemannHypothesis
      hRH P ht)) hneg

end

end RHTower
