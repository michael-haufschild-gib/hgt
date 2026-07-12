import GaloisForLFunctions.RHTower.CCMRectangularWeilCompleteness

/-!
# Rectangular Weil values as screw-function curvature

The multiplicity-exact Xi divisor defines an unconditional screw profile by
an absolutely convergent reciprocal-square sum.  A fixed-width rectangular
two-edge Weil value is exactly a centered second difference of this profile.
This is the source-facing coordinate form of the rectangular carrier.
-/

open Complex

namespace RHTower

noncomputable section

/-- One reciprocal-square summand of the centered Xi screw profile. -/
def xiScrewDivisorTerm (t : ℝ) (q : XiZeroCopy) : ℂ :=
  (Complex.cosh ((t : ℂ) * (I * xiSpectralPoint q)) - 1) /
    (I * xiSpectralPoint q) ^ 2

/-- Complex `cosh` is controlled by the exponential of the absolute real
part.  This is the bound that is uniform on the centered Xi strip. -/
theorem norm_cosh_le_exp_abs_re (z : ℂ) :
    ‖Complex.cosh z‖ ≤ Real.exp |z.re| := by
  rw [Complex.cosh, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  have htri := norm_add_le (Complex.exp z) (Complex.exp (-z))
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re] at htri
  have h1 := Real.exp_le_exp.mpr (le_abs_self z.re)
  have h2 := Real.exp_le_exp.mpr (neg_le_abs z.re)
  linarith

/-- Uniform reciprocal-square domination of one screw summand. -/
theorem norm_xiScrewDivisorTerm_le (t : ℝ) (q : XiZeroCopy) :
    ‖xiScrewDivisorTerm t q‖ ≤
      (Real.exp (|t| / 2) + 1) / ‖xiSpectralPoint q‖ ^ 2 := by
  let w : ℂ := I * xiSpectralPoint q
  have hw : w ≠ 0 := mul_ne_zero I_ne_zero (xiSpectralPoint_ne_zero q)
  have hwstrip : |w.re| ≤ (1 / 2 : ℝ) := by
    exact le_of_lt (abs_re_I_mul_xiSpectralPoint_le_half q)
  have htre : |(((t : ℂ) * w).re)| ≤ |t| / 2 := by
    rw [Complex.mul_re]
    simp only [ofReal_re, ofReal_im, zero_mul, sub_zero, abs_mul]
    calc
      |t| * |w.re| ≤ |t| * (1 / 2) := by
        gcongr
      _ = |t| / 2 := by ring
  have hcosh : ‖Complex.cosh ((t : ℂ) * w)‖ ≤ Real.exp (|t| / 2) :=
    (norm_cosh_le_exp_abs_re _).trans (Real.exp_le_exp.mpr htre)
  rw [xiScrewDivisorTerm, norm_div, norm_pow, norm_mul, norm_I, one_mul]
  calc
    ‖Complex.cosh ((t : ℂ) * w) - 1‖ / ‖xiSpectralPoint q‖ ^ 2 ≤
        (‖Complex.cosh ((t : ℂ) * w)‖ + 1) /
          ‖xiSpectralPoint q‖ ^ 2 := by
      gcongr
      simpa using norm_sub_le (Complex.cosh ((t : ℂ) * w)) 1
    _ ≤ (Real.exp (|t| / 2) + 1) / ‖xiSpectralPoint q‖ ^ 2 := by
      gcongr

/-- The centered Xi screw profile is absolutely summable for every real
parameter, with analytic multiplicity retained. -/
theorem xiScrewDivisorTerm_summable (t : ℝ) :
    Summable (xiScrewDivisorTerm t) := by
  apply Summable.of_norm_bounded
    (xiSpectralPoint_inv_sq_summable.mul_left
      (Real.exp (|t| / 2) + 1))
  intro q
  calc
    ‖xiScrewDivisorTerm t q‖ ≤
        (Real.exp (|t| / 2) + 1) / ‖xiSpectralPoint q‖ ^ 2 :=
      norm_xiScrewDivisorTerm_le t q
    _ = (Real.exp (|t| / 2) + 1) *
        (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring

/-- The unconditional multiplicity-exact Xi screw profile. -/
def xiScrewDivisor (t : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, xiScrewDivisorTerm t q

/-- Schwarz conjugation of one Xi screw summand is implemented by the exact
conjugate divisor-copy equivalence. -/
theorem xiScrewDivisorTerm_copyConj (t : ℝ) (q : XiZeroCopy) :
    xiScrewDivisorTerm t (xiZeroCopyConjEquiv q) =
      (starRingEnd ℂ) (xiScrewDivisorTerm t q) := by
  have hw : I * xiSpectralPoint (xiZeroCopyConjEquiv q) =
      (starRingEnd ℂ) (I * xiSpectralPoint q) := by
    rw [xiSpectralPoint_copyConj]
    simp
  rw [xiScrewDivisorTerm, xiScrewDivisorTerm, hw]
  rw [map_div₀, map_sub, map_one, map_pow, ← Complex.cosh_conj]
  congr 3
  simp

/-- The Xi screw profile is real-valued without assuming RH. -/
theorem star_xiScrewDivisor (t : ℝ) :
    (starRingEnd ℂ) (xiScrewDivisor t) = xiScrewDivisor t := by
  rw [xiScrewDivisor, Complex.conj_tsum]
  calc
    (∑' q : XiZeroCopy, (starRingEnd ℂ) (xiScrewDivisorTerm t q)) =
        ∑' q : XiZeroCopy,
          xiScrewDivisorTerm t (xiZeroCopyConjEquiv q) := by
      apply tsum_congr
      intro q
      exact (xiScrewDivisorTerm_copyConj t q).symm
    _ = ∑' q : XiZeroCopy, xiScrewDivisorTerm t q := by
      exact xiZeroCopyConjEquiv.tsum_eq (xiScrewDivisorTerm t)

theorem xiScrewDivisor_im_eq_zero (t : ℝ) :
    (xiScrewDivisor t).im = 0 :=
  Complex.conj_eq_iff_im.mp (star_xiScrewDivisor t)

private theorem rectangularTwoEdgeTransform_eq_sinhDifference
    {L a : ℝ} {w : ℂ} (hw : w ≠ 0) :
    rectangularTwoEdgeTransform L a w =
      2 * (Complex.sinh ((a : ℂ) * w) -
        Complex.sinh ((a - L : ℂ) * w)) / w := by
  rw [rectangularTwoEdgeTransform, rectangularWindowAmplitude_eq_div hw,
    rectangularWindowAmplitude_eq_div (neg_ne_zero.mpr hw)]
  simp only [Complex.sinh]
  field_simp [hw]
  have hpos : Complex.exp ((a : ℂ) * w) *
      Complex.exp (-(w * (L : ℂ))) =
      Complex.exp (w * ((a : ℂ) - L)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hneg : Complex.exp (-((a : ℂ) * w)) *
      Complex.exp (w * (L : ℂ)) =
      Complex.exp (-(w * ((a : ℂ) - L))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [mul_sub, mul_sub, hpos, hneg]
  ring

private theorem sinhDifference_sq_identity (x y : ℂ) :
    (2 * (Complex.sinh x - Complex.sinh y)) ^ 2 =
      2 * ((Complex.cosh (2 * x) - 1) +
        (Complex.cosh (2 * y) - 1) -
        2 * (Complex.cosh (x + y) - 1) +
        2 * (Complex.cosh (x - y) - 1)) := by
  rw [Complex.cosh_two_mul, Complex.cosh_two_mul,
    Complex.cosh_add, Complex.cosh_sub]
  have hx := Complex.cosh_sq_sub_sinh_sq x
  have hy := Complex.cosh_sq_sub_sinh_sq y
  linear_combination -2 * hx - 2 * hy

/-- Pointwise hyperbolic identity behind the rectangular curvature law. -/
theorem rectangularTwoEdgeTransform_sq_eq_screwTerms
    {L a : ℝ} {w : ℂ} (hw : w ≠ 0) :
    rectangularTwoEdgeTransform L a w ^ 2 =
      2 * (((Complex.cosh ((2 * a : ℝ) * w) - 1) / w ^ 2) +
        ((Complex.cosh ((2 * a - 2 * L : ℝ) * w) - 1) / w ^ 2) -
        2 * ((Complex.cosh ((2 * a - L : ℝ) * w) - 1) / w ^ 2) +
        2 * ((Complex.cosh ((L : ℂ) * w) - 1) / w ^ 2)) := by
  rw [rectangularTwoEdgeTransform_eq_sinhDifference hw]
  rw [div_pow]
  have hid := sinhDifference_sq_identity
    ((a : ℂ) * w) ((a - L : ℂ) * w)
  have hid' :
      (2 * (Complex.sinh ((a : ℂ) * w) -
        Complex.sinh ((a - L : ℂ) * w))) ^ 2 =
        2 * ((Complex.cosh ((2 * a : ℝ) * w) - 1) +
          (Complex.cosh ((2 * a - 2 * L : ℝ) * w) - 1) -
          2 * (Complex.cosh ((2 * a - L : ℝ) * w) - 1) +
          2 * (Complex.cosh ((L : ℂ) * w) - 1)) := by
    have ha : ((2 * a : ℝ) : ℂ) * w = 2 * ((a : ℂ) * w) := by
      push_cast
      ring
    have hb : ((2 * a - 2 * L : ℝ) : ℂ) * w =
        2 * (((a - L : ℝ) : ℂ) * w) := by
      push_cast
      ring
    have hc : ((2 * a - L : ℝ) : ℂ) * w =
        (a : ℂ) * w + ((a - L : ℝ) : ℂ) * w := by
      push_cast
      ring
    have hd : (L : ℂ) * w =
        (a : ℂ) * w - ((a - L : ℝ) : ℂ) * w := by
      push_cast
      ring
    rw [ha, hb, hc, hd]
    simpa only [ofReal_sub] using hid
  rw [hid']
  field_simp [hw]

/-- Every fixed-width rectangular Weil value is the centered second
difference of the Xi screw profile, plus the fixed endpoint term. -/
theorem xiWeilPolarization_rectangular_eq_screwCurvature (L a : ℝ) :
    xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
        (xiRectangularTwoEdgeTransform L a) =
      2 * (xiScrewDivisor (2 * a) + xiScrewDivisor (2 * a - 2 * L) -
        2 * xiScrewDivisor (2 * a - L) + 2 * xiScrewDivisor L) := by
  rw [xiWeilPolarization_rectangular_eq_tsum_sq]
  have h1 := xiScrewDivisorTerm_summable (2 * a)
  have h2 := xiScrewDivisorTerm_summable (2 * a - 2 * L)
  have h3 := xiScrewDivisorTerm_summable (2 * a - L)
  have h4 := xiScrewDivisorTerm_summable L
  rw [xiScrewDivisor, xiScrewDivisor, xiScrewDivisor, xiScrewDivisor]
  let f1 := xiScrewDivisorTerm (2 * a)
  let f2 := xiScrewDivisorTerm (2 * a - 2 * L)
  let f3 := xiScrewDivisorTerm (2 * a - L)
  let f4 := xiScrewDivisorTerm L
  have hsA : Summable (fun q => f1 q + f2 q) := h1.add h2
  have hsB : Summable (fun q => 2 * f3 q - 2 * f4 q) :=
    (h3.mul_left 2).sub (h4.mul_left 2)
  calc
    ∑' q : XiZeroCopy,
        xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ 2 =
      ∑' q : XiZeroCopy,
        2 * (f1 q + f2 q - 2 * f3 q + 2 * f4 q) := by
          apply tsum_congr
          intro q
          have hw : I * xiSpectralPoint q ≠ 0 :=
            mul_ne_zero I_ne_zero (xiSpectralPoint_ne_zero q)
          rw [xiRectangularTwoEdgeTransform]
          rw [rectangularTwoEdgeTransform_sq_eq_screwTerms hw]
          simp only [f1, f2, f3, f4, xiScrewDivisorTerm]
    _ = 2 * ∑' q : XiZeroCopy,
        (f1 q + f2 q - 2 * f3 q + 2 * f4 q) := by
          rw [tsum_mul_left]
    _ = 2 *
        ((∑' q : XiZeroCopy, f1 q) + (∑' q : XiZeroCopy, f2 q) -
          2 * (∑' q : XiZeroCopy, f3 q) +
          2 * (∑' q : XiZeroCopy, f4 q)) := by
          congr 1
          calc
            (∑' q : XiZeroCopy,
                (f1 q + f2 q - 2 * f3 q + 2 * f4 q)) =
              ∑' q : XiZeroCopy,
                ((f1 q + f2 q) - (2 * f3 q - 2 * f4 q)) := by
                  apply tsum_congr
                  intro q
                  ring
            _ = (∑' q : XiZeroCopy, (f1 q + f2 q)) -
                (∑' q : XiZeroCopy, (2 * f3 q - 2 * f4 q)) := by
                  rw [hsA.tsum_sub hsB]
            _ = _ := by
                  rw [h1.tsum_add h2,
                    (h3.mul_left 2).tsum_sub (h4.mul_left 2),
                    tsum_mul_left, tsum_mul_left]
                  ring

/-- The fixed-width centered discrete curvature of the Xi screw profile. -/
def xiScrewWindowCurvature (L x : ℝ) : ℂ :=
  2 * (xiScrewDivisor x + xiScrewDivisor (x - 2 * L) -
    2 * xiScrewDivisor (x - L) + 2 * xiScrewDivisor L)

/-- The rectangular Weil value at aperture `a` is the screw curvature at
the center coordinate `2a`. -/
theorem xiWeilPolarization_rectangular_eq_xiScrewWindowCurvature (L a : ℝ) :
    xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
        (xiRectangularTwoEdgeTransform L a) =
      xiScrewWindowCurvature L (2 * a) := by
  rw [xiWeilPolarization_rectangular_eq_screwCurvature]
  unfold xiScrewWindowCurvature
  rfl

/-- At logarithmic aperture, the rectangular carrier is the screw curvature
on the exact arithmetic mesh `log n`. -/
theorem xiWeilPolarization_rectangular_logSample_eq_xiScrewWindowCurvature
    (L : ℝ) (n : ℕ) :
    xiWeilPolarization
        (xiRectangularTwoEdgeTransform L (Real.log n / 2))
        (xiRectangularTwoEdgeTransform L (Real.log n / 2)) =
      xiScrewWindowCurvature L (Real.log n) := by
  rw [xiWeilPolarization_rectangular_eq_xiScrewWindowCurvature]
  congr 2
  ring

/-- False RH forces the fixed-width screw curvature below every real level
cofinally on the logarithmic integer mesh. -/
theorem not_riemannHypothesis_implies_xiScrewWindowCurvature_logSample_cofinally_unbounded_below
    {L : ℝ} (hL : 0 < L) (hRH : ¬RiemannHypothesis) :
    ∀ B : ℝ, ∀ N0 : ℕ, ∃ n : ℕ,
      N0 ≤ n ∧ L ≤ Real.log n / 2 ∧
      (xiScrewWindowCurvature L (Real.log n)).re < B := by
  intro B N0
  obtain ⟨n, hn, hLa, hbelow⟩ :=
    not_riemannHypothesis_implies_rectangular_weil_cofinally_unbounded_below
      hL hRH B N0
  refine ⟨n, hn, hLa, ?_⟩
  simpa only [xiWeilPolarization_rectangular_logSample_eq_xiScrewWindowCurvature]
    using hbelow

/-- Exact discrete-curvature criterion: for every fixed positive width, RH
is equivalent to nonnegativity on the logarithmic integer mesh. -/
theorem riemannHypothesis_iff_xiScrewWindowCurvature_logSample_nonneg
    {L : ℝ} (hL : 0 < L) :
    RiemannHypothesis ↔
      ∀ n : ℕ, 0 ≤ (xiScrewWindowCurvature L (Real.log n)).re := by
  rw [riemannHypothesis_iff_rectangular_logSample_weil_nonneg hL]
  constructor <;> intro h n
  · simpa only [xiWeilPolarization_rectangular_logSample_eq_xiScrewWindowCurvature]
      using h n
  · simpa only [xiWeilPolarization_rectangular_logSample_eq_xiScrewWindowCurvature]
      using h n

/-- More strongly, RH is equivalent to eventual lower boundedness of the
same fixed-width screw curvature on the logarithmic integer mesh. -/
theorem riemannHypothesis_iff_xiScrewWindowCurvature_logSample_eventually_bddBelow
    {L : ℝ} (hL : 0 < L) :
    RiemannHypothesis ↔
      ∃ B : ℝ, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
        L ≤ Real.log n / 2 →
        B ≤ (xiScrewWindowCurvature L (Real.log n)).re := by
  rw [riemannHypothesis_iff_rectangular_logSample_weil_eventually_bddBelow hL]
  constructor
  · rintro ⟨B, N0, h⟩
    refine ⟨B, N0, fun n hn hLa => ?_⟩
    simpa only [xiWeilPolarization_rectangular_logSample_eq_xiScrewWindowCurvature]
      using h n hn hLa
  · rintro ⟨B, N0, h⟩
    refine ⟨B, N0, fun n hn hLa => ?_⟩
    simpa only [xiWeilPolarization_rectangular_logSample_eq_xiScrewWindowCurvature]
      using h n hn hLa

end

end RHTower
