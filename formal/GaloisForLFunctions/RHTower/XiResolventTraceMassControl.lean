import GaloisForLFunctions.RHTower.XiResolventTuranDeviationControl

/-!
# Mass control of every polynomial resolvent trace

The quantitative Hamburger bound at every Hankel order.  The 45° cone law transfers from the
shifted squares to the resolvent coordinates themselves: `|Im u_q| < Re u_q`.  For a real
polynomial `p` the imaginary part of `evalRealPolynomial p` on the closed unit disc is
Lipschitz in the imaginary part of the argument with constant `L_p = Σ |coeff k| · k`, and the
cone gives the pointwise bound `Re (u · P(u)²) ≥ −2 · (Im P(u))² ≥ −2 L_p² (Im u)²`.  Summing:

`Re (xiResolventTrace X p) ≥ −2 L_p² · M`,   `M = Σ (Im u_q)²`,

for every real polynomial and every shift `X ≥ 0` — the entire possible negativity of every
polynomial trace, hence of every Hankel form, is explicitly carried by the single `ℓ²`
imaginary mass, which vanishes exactly on RH.  This subsumes the order-two Turán control with
a purely quadratic mass bound. -/

open Complex

namespace RHTower

noncomputable section

/-- The Lipschitz bound of a real polynomial on the closed unit disc. -/
def evalRealPolynomialLipBound (p : Polynomial ℝ) : ℝ :=
  ∑ k ∈ Finset.range (p.natDegree + 1), |p.coeff k| * k

theorem evalRealPolynomialLipBound_nonneg (p : Polynomial ℝ) :
    0 ≤ evalRealPolynomialLipBound p := by
  apply Finset.sum_nonneg
  intro k _
  positivity

/-- Unit-disc power differences are Lipschitz with constant the exponent. -/
theorem norm_pow_sub_pow_le_of_norm_le_one {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (k : ℕ) : ‖u ^ k - v ^ k‖ ≤ k * ‖u - v‖ := by
  induction k with
  | zero => simp
  | succ n ih =>
      have hstep : u ^ (n + 1) - v ^ (n + 1) = u ^ n * (u - v) + (u ^ n - v ^ n) * v := by
        ring
      calc ‖u ^ (n + 1) - v ^ (n + 1)‖ ≤ ‖u ^ n * (u - v)‖ + ‖(u ^ n - v ^ n) * v‖ := by
            rw [hstep]
            exact norm_add_le _ _
        _ ≤ ‖u - v‖ + n * ‖u - v‖ := by
            rw [norm_mul, norm_mul, norm_pow]
            have h1 : ‖u‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg u) hu
            nlinarith [norm_nonneg (u - v), norm_nonneg (u ^ n - v ^ n),
              mul_le_mul_of_nonneg_right ih (norm_nonneg v), norm_nonneg v,
              mul_le_mul_of_nonneg_left hv (norm_nonneg (u ^ n - v ^ n))]
        _ = (n + 1 : ℕ) * ‖u - v‖ := by push_cast; ring

/-- **The imaginary Lipschitz law**: on the closed unit disc a real polynomial's imaginary
part is bounded by its Lipschitz constant times the imaginary part of the argument. -/
theorem abs_im_evalRealPolynomial_le (p : Polynomial ℝ) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    |(evalRealPolynomial p u).im| ≤ evalRealPolynomialLipBound p * |u.im| := by
  have hconj : (starRingEnd ℂ) (evalRealPolynomial p u) =
      evalRealPolynomial p ((starRingEnd ℂ) u) := (evalRealPolynomial_conj p u).symm
  have him : |(evalRealPolynomial p u).im| =
      ‖evalRealPolynomial p u - evalRealPolynomial p ((starRingEnd ℂ) u)‖ / 2 := by
    rw [← hconj, Complex.sub_conj]
    rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one,
      abs_mul, abs_two]
    ring
  have hdiff : evalRealPolynomial p u - evalRealPolynomial p ((starRingEnd ℂ) u) =
      ∑ k ∈ Finset.range (p.natDegree + 1),
        ((p.coeff k : ℂ) * (u ^ k - ((starRingEnd ℂ) u) ^ k)) := by
    have hdeg : (p.map (algebraMap ℝ ℂ)).natDegree < p.natDegree + 1 := by
      have := Polynomial.natDegree_map_le (f := algebraMap ℝ ℂ) (p := p)
      omega
    rw [evalRealPolynomial, evalRealPolynomial,
      Polynomial.eval_eq_sum_range' hdeg, Polynomial.eval_eq_sum_range' hdeg,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.coeff_map]
    simp only [coe_algebraMap]
    ring
  have hbound : ‖evalRealPolynomial p u - evalRealPolynomial p ((starRingEnd ℂ) u)‖ ≤
      evalRealPolynomialLipBound p * ‖u - (starRingEnd ℂ) u‖ := by
    rw [hdiff]
    calc ‖∑ k ∈ Finset.range (p.natDegree + 1),
        ((p.coeff k : ℂ) * (u ^ k - ((starRingEnd ℂ) u) ^ k))‖ ≤
        ∑ k ∈ Finset.range (p.natDegree + 1),
          ‖(p.coeff k : ℂ) * (u ^ k - ((starRingEnd ℂ) u) ^ k)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (p.natDegree + 1),
          |p.coeff k| * (k * ‖u - (starRingEnd ℂ) u‖) := by
          apply Finset.sum_le_sum
          intro k _
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact norm_pow_sub_pow_le_of_norm_le_one hu (by rwa [RCLike.norm_conj]) k
      _ = evalRealPolynomialLipBound p * ‖u - (starRingEnd ℂ) u‖ := by
          rw [evalRealPolynomialLipBound, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
  have hsub : ‖u - (starRingEnd ℂ) u‖ = 2 * |u.im| := by
    rw [Complex.sub_conj, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      mul_one, abs_mul, abs_two]
  rw [him]
  rw [hsub] at hbound
  linarith [mul_nonneg (evalRealPolynomialLipBound_nonneg p) (abs_nonneg u.im)]

/-- The 45° cone law transfers to the resolvent coordinates. -/
theorem abs_im_lt_re_xiResolventPoint {X : ℝ} (hX : 0 ≤ X) (q : XiZeroCopy) :
    |(xiResolventPoint X q).im| < (xiResolventPoint X q).re := by
  have hcone := xiSpectralSq_add_abs_im_lt_re hX q
  have hne := xiSpectralSq_add_ofReal_ne_zero hX q
  have hnsq : 0 < Complex.normSq (xiSpectralPoint q ^ 2 + (X : ℂ)) :=
    Complex.normSq_pos.mpr hne
  rw [xiResolventPoint, Complex.inv_re, Complex.inv_im, abs_div, abs_neg,
    abs_of_pos hnsq, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul_of_pos_right hcone (inv_pos.mpr hnsq)

/-- **The pointwise cone bound**: a coordinate in the 45° cone with unit norm multiplies any
complex square with real part at least `−2·(Im w)²`. -/
theorem re_mul_sq_ge_of_cone {u w : ℂ} (hc : |u.im| ≤ u.re) (hb : ‖u‖ ≤ 1) :
    -(2 * w.im ^ 2) ≤ (u * w ^ 2).re := by
  have hre : (u * w ^ 2).re = u.re * (w.re ^ 2 - w.im ^ 2) - u.im * (2 * w.re * w.im) := by
    have hw2r : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by
      rw [sq, Complex.mul_re]
      ring
    have hw2i : (w ^ 2).im = 2 * w.re * w.im := by
      rw [sq, Complex.mul_im]
      ring
    rw [Complex.mul_re, hw2r, hw2i]
  have hure : |u.re| ≤ 1 := le_trans (Complex.abs_re_le_norm u) hb
  have huim : |u.im| ≤ 1 := le_trans (Complex.abs_im_le_norm u) hb
  have hcross : |u.im * (2 * w.re * w.im)| ≤ |u.im| * (w.re ^ 2 + w.im ^ 2) := by
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have h2 : |2 * w.re * w.im| = 2 * (|w.re| * |w.im|) := by
      rw [abs_mul, abs_mul, abs_two]
      ring
    rw [h2]
    nlinarith [sq_abs w.re, sq_abs w.im, sq_nonneg (|w.re| - |w.im|),
      abs_nonneg w.re, abs_nonneg w.im]
  have habs := abs_le.mp hcross
  have hrepos : 0 ≤ u.re := le_trans (abs_nonneg _) hc
  rw [hre]
  nlinarith [sq_nonneg w.re, sq_nonneg w.im, le_abs_self u.re, neg_abs_le u.im,
    le_abs_self u.im, mul_le_mul_of_nonneg_right hc (sq_nonneg w.im),
    mul_le_mul_of_nonneg_right hc (sq_nonneg w.re),
    mul_le_mul_of_nonneg_right hure (sq_nonneg w.im)]

/-- **Termwise mass bound**: every polynomial trace term is bounded below by minus twice the
squared Lipschitz constant times the squared imaginary part of the coordinate. -/
theorem re_traceTerm_ge_neg_mass {X : ℝ} (hX : 0 ≤ X) (p : Polynomial ℝ) (q : XiZeroCopy) :
    -(2 * evalRealPolynomialLipBound p ^ 2 * (xiResolventPoint X q).im ^ 2) ≤
      (xiResolventPoint X q *
        evalRealPolynomial p (xiResolventPoint X q) ^ 2).re := by
  have hb : ‖xiResolventPoint X q‖ ≤ 1 := norm_xiResolventPoint_le_one hX q
  have hc : |(xiResolventPoint X q).im| ≤ (xiResolventPoint X q).re :=
    (abs_im_lt_re_xiResolventPoint hX q).le
  have hpoint := re_mul_sq_ge_of_cone hc hb (w := evalRealPolynomial p (xiResolventPoint X q))
  have hLip := abs_im_evalRealPolynomial_le p hb
  have hsq : (evalRealPolynomial p (xiResolventPoint X q)).im ^ 2 ≤
      evalRealPolynomialLipBound p ^ 2 * (xiResolventPoint X q).im ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg _) hLip
    calc (evalRealPolynomial p (xiResolventPoint X q)).im ^ 2 =
        |(evalRealPolynomial p (xiResolventPoint X q)).im| ^ 2 := (sq_abs _).symm
      _ ≤ (evalRealPolynomialLipBound p * |(xiResolventPoint X q).im|) ^ 2 := by
          nlinarith [abs_nonneg (evalRealPolynomial p (xiResolventPoint X q)).im, hLip,
            mul_nonneg (evalRealPolynomialLipBound_nonneg p)
              (abs_nonneg (xiResolventPoint X q).im)]
      _ = evalRealPolynomialLipBound p ^ 2 * (xiResolventPoint X q).im ^ 2 := by
          rw [mul_pow, sq_abs]
  linarith

/-- **Mass control of every polynomial resolvent trace.**  The whole possible negativity of
every polynomial trace is carried by the `ℓ²` imaginary mass, with constant twice the squared
unit-disc Lipschitz bound of the polynomial. -/
theorem xiResolventTrace_re_ge_neg_mass {X : ℝ} (hX : 0 ≤ X) (p : Polynomial ℝ) :
    -(2 * evalRealPolynomialLipBound p ^ 2 * xiResolventImSqMass X) ≤
      (xiResolventTrace X p).re := by
  have hB := evalRealPolynomialNormBound_nonneg p (zero_le_one (α := ℝ))
  have hsumTrace : Summable (fun q : XiZeroCopy =>
      xiResolventPoint X q * evalRealPolynomial p (xiResolventPoint X q) ^ 2) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
      ((summable_norm_xiResolventPoint hX).mul_left
        (evalRealPolynomialNormBound p 1 ^ 2))
    rw [norm_mul, norm_pow]
    have h1 : ‖evalRealPolynomial p (xiResolventPoint X q)‖ ≤
        evalRealPolynomialNormBound p 1 :=
      norm_evalRealPolynomial_le p (norm_xiResolventPoint_le_one hX q)
    have h2 : ‖evalRealPolynomial p (xiResolventPoint X q)‖ ^ 2 ≤
        evalRealPolynomialNormBound p 1 ^ 2 := by
      nlinarith [norm_nonneg (evalRealPolynomial p (xiResolventPoint X q))]
    nlinarith [norm_nonneg (xiResolventPoint X q),
      mul_le_mul_of_nonneg_left h2 (norm_nonneg (xiResolventPoint X q))]
  rw [xiResolventTrace, Complex.re_tsum hsumTrace]
  have hsumRe : Summable (fun q : XiZeroCopy =>
      (xiResolventPoint X q * evalRealPolynomial p (xiResolventPoint X q) ^ 2).re) := by
    simpa only [Function.comp_apply] using!
      hsumTrace.map Complex.reCLM Complex.reCLM.continuous
  have hsumLow : Summable (fun q : XiZeroCopy =>
      -(2 * evalRealPolynomialLipBound p ^ 2 * (xiResolventPoint X q).im ^ 2)) :=
    ((summable_im_sq_xiResolventPoint hX).mul_left
      (2 * evalRealPolynomialLipBound p ^ 2)).neg
  have hcompare := hsumLow.tsum_le_tsum
    (fun q => re_traceTerm_ge_neg_mass hX p q) hsumRe
  calc -(2 * evalRealPolynomialLipBound p ^ 2 * xiResolventImSqMass X) =
      ∑' q : XiZeroCopy,
        -(2 * evalRealPolynomialLipBound p ^ 2 * (xiResolventPoint X q).im ^ 2) := by
        rw [tsum_neg, tsum_mul_left, xiResolventImSqMass]
    _ ≤ ∑' q : XiZeroCopy,
        (xiResolventPoint X q * evalRealPolynomial p (xiResolventPoint X q) ^ 2).re :=
        hcompare

/-- **Mass control of every Hankel form**: at every order and every coefficient vector the
possible negativity of the resolvent Hankel form is explicitly bounded by the `ℓ²` imaginary
mass. -/
theorem xiResolventHankelForm_re_ge_neg_mass {X : ℝ} (hX : 0 ≤ X) (N : ℕ) (a : ℕ → ℝ) :
    -(2 * evalRealPolynomialLipBound
        (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) ^ 2 *
          xiResolventImSqMass X) ≤
      (xiResolventHankelForm N a X).re := by
  rw [← xiResolventTrace_rangeSum hX N a]
  exact xiResolventTrace_re_ge_neg_mass hX _

end

end RHTower
