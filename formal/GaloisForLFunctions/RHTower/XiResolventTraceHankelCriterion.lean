import GaloisForLFunctions.RHTower.XiGaussianHeatTuranPairSum
import GaloisForLFunctions.RHTower.XiSquaredEulerRayFullResponse

/-!
# RH from the resolvent trace, whose moments are the Euler-ray response

The Gaussian ladder tests the squared divisor with `exp (-t w)`.  Replacing that weight by the
resolvent weight `(w + X)^(-1)` changes nothing structurally — the divisor is still tested by a
positive-measure moment condition — but it changes everything computationally: the moments of the
resolvent trace are the **derivatives of the Euler-ray response**

`sum_q (w q + x^(2 : ℕ))^(-1) = logDeriv xi (1/2 + x) / x`,

which for `x > 1/2` is an absolutely convergent prime--Gamma expression.  So the criterion below is
stated directly on data the corpus already computes from primes.

The reality conclusion is the corpus's abstract trace--Hankel converse
`traceHankel_nonnegative_on_principalIdeal_implies_real`, applied with the trivial separator: the
resolvent coordinates `lam q = (w q + X)^(-1)` are nonzero, summable, and accumulate only at the
origin, which is exactly that theorem's hypothesis shape.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## §1 The resolvent coordinate -/

/-- The resolvent coordinate of a divisor copy at spectral parameter `X`. -/
def xiResolventPoint (X : ℝ) (q : XiZeroCopy) : ℂ :=
  (xiSpectralPoint q ^ 2 + (X : ℂ))⁻¹

theorem xiSpectralSq_add_ofReal_re_pos {X : ℝ} (hX : 0 ≤ X) (q : XiZeroCopy) :
    0 < (xiSpectralPoint q ^ 2 + (X : ℂ)).re := by
  have h := xiSpectralSq_re_pos q
  simp only [Complex.add_re, Complex.ofReal_re]
  linarith

theorem xiSpectralSq_add_ofReal_ne_zero {X : ℝ} (hX : 0 ≤ X) (q : XiZeroCopy) :
    xiSpectralPoint q ^ 2 + (X : ℂ) ≠ 0 := by
  intro hzero
  have := xiSpectralSq_add_ofReal_re_pos hX q
  rw [hzero] at this
  simp at this

theorem xiResolventPoint_ne_zero {X : ℝ} (hX : 0 ≤ X) (q : XiZeroCopy) :
    xiResolventPoint X q ≠ 0 :=
  inv_ne_zero (xiSpectralSq_add_ofReal_ne_zero hX q)

/-- The resolvent coordinate is dominated by the reciprocal-square weight of the divisor. -/
theorem norm_xiResolventPoint_le {X : ℝ} (hX : 0 ≤ X) (q : XiZeroCopy) :
    ‖xiResolventPoint X q‖ ≤ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  have hgap := xiSpectralPoint_normSq_lt_two_mul_sq_re q
  have hpos : 0 < Complex.normSq (xiSpectralPoint q) :=
    Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)
  have hre : Complex.normSq (xiSpectralPoint q) / 2 ≤
      (xiSpectralPoint q ^ 2 + (X : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hnorm : Complex.normSq (xiSpectralPoint q) / 2 ≤
      ‖xiSpectralPoint q ^ 2 + (X : ℂ)‖ :=
    le_trans hre (Complex.re_le_norm _)
  have hhalf : 0 < Complex.normSq (xiSpectralPoint q) / 2 := by linarith
  rw [xiResolventPoint, norm_inv, Complex.sq_norm]
  rw [inv_le_iff_one_le_mul₀ (lt_of_lt_of_le hhalf hnorm)]
  have hNinv : Complex.normSq (xiSpectralPoint q) *
      (1 / Complex.normSq (xiSpectralPoint q)) = 1 := by field_simp
  nlinarith [hnorm, hpos, hNinv, one_div_pos.mpr hpos]

theorem summable_norm_xiResolventPoint {X : ℝ} (hX : 0 ≤ X) :
    Summable (fun q : XiZeroCopy => ‖xiResolventPoint X q‖) := by
  apply Summable.of_nonneg_of_le (fun q => norm_nonneg _) (norm_xiResolventPoint_le hX)
  exact xiSpectralPoint_inv_sq_summable.mul_left 2

theorem summable_xiResolventPoint {X : ℝ} (hX : 0 ≤ X) :
    Summable (xiResolventPoint X) :=
  summable_norm_iff.mp (summable_norm_xiResolventPoint hX)

/-- The resolvent coordinates accumulate only at the origin. -/
theorem finite_setOf_le_norm_xiResolventPoint {X : ℝ} (hX : 0 ≤ X) {r : ℝ} (hr : 0 < r) :
    {q : XiZeroCopy | r ≤ ‖xiResolventPoint X q‖}.Finite := by
  apply Set.Finite.subset (finite_xiHeatShell (1 / r))
  intro q hq
  simp only [Set.mem_setOf_eq] at hq ⊢
  have hne := xiSpectralSq_add_ofReal_ne_zero hX q
  have hnormpos : 0 < ‖xiSpectralPoint q ^ 2 + (X : ℂ)‖ := norm_pos_iff.mpr hne
  have hbound : ‖xiSpectralPoint q ^ 2 + (X : ℂ)‖ ≤ r⁻¹ := by
    rw [xiResolventPoint, norm_inv, le_inv_comm₀ hr hnormpos] at hq
    exact hq
  have hone : (1 : ℝ) / r = r⁻¹ := one_div r
  have hre : (xiSpectralPoint q ^ 2).re + X ≤ ‖xiSpectralPoint q ^ 2 + (X : ℂ)‖ := by
    have := Complex.re_le_norm (xiSpectralPoint q ^ 2 + (X : ℂ))
    simpa [Complex.add_re] using this
  linarith

/-! ## §2 The resolvent trace and the reality criterion -/

/-- The resolvent trace of the divisor tested against a real polynomial. -/
def xiResolventTrace (X : ℝ) (p : Polynomial ℝ) : ℂ :=
  ∑' q : XiZeroCopy,
    xiResolventPoint X q * evalRealPolynomial p (xiResolventPoint X q) ^ 2

/-- **Nonnegativity of every resolvent trace proves RH.**  The resolvent coordinates satisfy the
hypotheses of the abstract trace--Hankel converse with the trivial separator, so no copy can hide a
nonreal resolvent value; a real resolvent value forces a real squared spectral point, and the
height gap then forces a real spectral point. -/
theorem riemannHypothesis_of_forall_xiResolventTrace_re_nonneg {X : ℝ} (hX : 0 ≤ X)
    (h : ∀ p : Polynomial ℝ, 0 ≤ (xiResolventTrace X p).re) :
    RiemannHypothesis := by
  have hreal : ∀ q : XiZeroCopy, (xiResolventPoint X q).im = 0 := by
    refine traceHankel_nonnegative_on_principalIdeal_implies_real
      (xiResolventPoint X) (xiResolventPoint_ne_zero hX)
      (fun {r} hr => finite_setOf_le_norm_xiResolventPoint hX hr)
      (summable_xiResolventPoint hX) 1 (fun q _ => by simp) ?_
    intro p
    have hp := h p
    rw [xiResolventTrace] at hp
    simpa using hp
  by_contra hRH
  obtain ⟨q, hq⟩ := exists_spectralSq_im_pos_of_not_riemannHypothesis hRH
  have hqim : (xiResolventPoint X q).im = 0 := hreal q
  rw [xiResolventPoint, Complex.inv_im] at hqim
  have hne := xiSpectralSq_add_ofReal_ne_zero hX q
  have hnormSq : Complex.normSq (xiSpectralPoint q ^ 2 + (X : ℂ)) ≠ 0 :=
    fun hc => hne (Complex.normSq_eq_zero.mp hc)
  have hzero : (xiSpectralPoint q ^ 2 + (X : ℂ)).im = 0 := by
    rw [div_eq_zero_iff] at hqim
    rcases hqim with hnum | hden
    · linarith [neg_eq_zero.mp hnum]
    · exact absurd hden hnormSq
  simp only [Complex.add_im, Complex.ofReal_im, add_zero] at hzero
  rw [hzero] at hq
  exact lt_irrefl 0 hq

/-! ## §3 The moments are the Euler-ray response -/

/-- Moments of the resolvent trace: the `n`-th moment is `sum_q (w q + X)^(-(n+1))`. -/
def xiResolventMoment (n : ℕ) (X : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, xiResolventPoint X q ^ (n + 1)

/-- The corpus reciprocal-square resolvent term at an imaginary base point is the resolvent
coordinate at the squared parameter. -/
theorem xiReciprocalSquareResolventTerm_eq_xiResolventPoint {x : ℝ} (hx : 0 < x)
    (q : XiZeroCopy) :
    xiReciprocalSquareResolventTerm (-(x : ℂ) * I) q = xiResolventPoint (x ^ 2) q := by
  have hw : xiSpectralPoint q ^ 2 ≠ 0 := pow_ne_zero _ (xiSpectralPoint_ne_zero q)
  have hden : xiSpectralPoint q ^ 2 + ((x ^ 2 : ℝ) : ℂ) ≠ 0 :=
    xiSpectralSq_add_ofReal_ne_zero (by positivity) q
  have hz : (-(x : ℂ) * I) ^ 2 = -((x ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, neg_pow, I_sq]
    ring
  have hR : xiZeroCopyReciprocalSquare q = (xiSpectralPoint q ^ 2)⁻¹ := by
    rw [xiZeroCopyReciprocalSquare, inv_pow]
  have hden2 : (1 : ℂ) - (-((x ^ 2 : ℝ) : ℂ)) * (xiSpectralPoint q ^ 2)⁻¹ =
      (xiSpectralPoint q ^ 2 + ((x ^ 2 : ℝ) : ℂ)) * (xiSpectralPoint q ^ 2)⁻¹ := by
    rw [add_mul, mul_inv_cancel₀ hw]
    ring
  rw [xiReciprocalSquareResolventTerm, hR, hz, hden2, xiResolventPoint,
    div_eq_iff (mul_ne_zero hden (inv_ne_zero hw)), ← mul_assoc,
    inv_mul_cancel₀ hden, one_mul]

/-- **The zeroth resolvent moment is the Euler-ray response.**  For `x > 1/2` the right-hand side is
an absolutely convergent prime--Gamma expression, so the criterion of §2 is stated on prime data. -/
theorem xiResolventMoment_zero_eq_logDeriv {x : ℝ} (hx : 0 < x) :
    xiResolventMoment 0 (x ^ 2) =
      logDeriv xi ((1 / 2 : ℂ) + (x : ℂ)) / (x : ℂ) := by
  rw [logDeriv_xi_eulerRay_div_eq_tsum_xiReciprocalSquareResolventTerm hx,
    xiResolventMoment]
  exact tsum_congr fun q => by
    rw [pow_one, xiReciprocalSquareResolventTerm_eq_xiResolventPoint hx q]

end

end RHTower
