import GaloisForLFunctions.RHTower.GaussHodgeWeilEntireDetection

/-!
# The deviation moment: what an arithmetic positivity source must control

The negative sector of the Weil form has an exact analytic normal form.  The odd part of any
test at a divisor point factors as `i * Im(alpha) * dslope F (conj alpha) alpha`: the deviation
of the point from the critical line times a symmetric divided difference of the test.  Hence
for every square-summable test

`Re W(F,F) = Σ ‖even part‖² − Σ (Im alpha_q)² · ‖dslope F (conj alpha_q) alpha_q‖²`,

and in classical coordinates `(Im alpha)² = (beta − 1/2)²`: the defect of Weil positivity is
the second moment of zero deviations weighted by divided differences of the test.  The critical
strip gives the unconditional weight bound `(Im alpha)² < 1/4`, so the diagonal Weil value is
bounded below by even energy minus a quarter of the divided-difference energy.  RH is exactly
the vanishing of the deviation-weighted divided-difference energy on all square-summable tests.

A positivity producer therefore has one job: dominate the deviation-weighted divided-difference
moment `Σ m(rho) (beta−1/2)² |ΔF|²` by the even energy — the precise inequality the arithmetic
input must supply.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## The divisor in classical coordinates -/

/-- Every divisor copy comes from an actual zero of the completed `xi`. -/
theorem xi_zeroCopy_eq_zero (q : XiZeroCopy) : xi ((q.1 : ℂ)) = 0 := by
  have h := XiC_xiSpectralPoint_eq_zero q
  rw [XiC] at h
  have harg : 1 / 2 + xiSpectralPoint q * Complex.I = ((q.1 : ℂ)) := by
    rw [xiSpectralPoint_eq_support, xiSpectralPointSupport]
    have hI : (-Complex.I) * Complex.I = 1 := by
      rw [neg_mul, Complex.I_mul_I]
      ring
    linear_combination ((q.1 : ℂ) - 1 / 2) * hI
  rwa [harg] at h

/-- The imaginary part of a centered spectral point is the deviation of the underlying zero
from the critical line. -/
theorem xiSpectralPoint_im (q : XiZeroCopy) :
    (xiSpectralPoint q).im = 1 / 2 - ((q.1 : ℂ)).re := by
  rw [xiSpectralPoint_eq_support, xiSpectralPointSupport]
  simp [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_im,
    Complex.I_re, Complex.I_im]

/-- **The strip bound on deviations**: every centered spectral point lies within distance `1/2`
of the real axis, because every `xi` zero lies in the open critical strip. -/
theorem abs_xiSpectralPoint_im_lt_half (q : XiZeroCopy) :
    |(xiSpectralPoint q).im| < 1 / 2 := by
  obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit (xi_zeroCopy_eq_zero q)
  rw [xiSpectralPoint_im, abs_lt]
  constructor <;> linarith

/-! ## The odd part is deviation times divided difference -/

/-- **The deviation factorization of the odd part.**  At every divisor point the odd part of
any test is `i` times the deviation times the symmetric divided difference across the
reflection pair.  On the critical line both sides vanish. -/
theorem xiWeilOddPart_eq_deviation_mul_dslope (F : ℂ → ℂ) (q : XiZeroCopy) :
    xiWeilOddPart F (xiSpectralPoint q) =
      Complex.I * (((xiSpectralPoint q).im : ℝ) : ℂ) *
        dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q) := by
  by_cases h : (starRingEnd ℂ) (xiSpectralPoint q) = xiSpectralPoint q
  · have him : (xiSpectralPoint q).im = 0 := by
      have hc := congrArg Complex.im h
      simp only [Complex.conj_im] at hc
      linarith
    rw [xiWeilOddPart, h, him]
    simp
  · rw [dslope_of_ne F (Ne.symm h), slope_def_field, xiWeilOddPart]
    have him : (xiSpectralPoint q).im ≠ 0 := by
      intro hc
      apply h
      have : (xiSpectralPoint q).im = -(xiSpectralPoint q).im := by rw [hc]; ring
      apply Complex.ext
      · exact Complex.conj_re _
      · rw [Complex.conj_im, hc, neg_zero]
    have hsub : xiSpectralPoint q - (starRingEnd ℂ) (xiSpectralPoint q) =
        2 * Complex.I * (((xiSpectralPoint q).im : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [Complex.sub_re, Complex.conj_re, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im]
      · simp [Complex.sub_im, Complex.conj_im, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im]
        ring
    rw [hsub]
    have him' : (((xiSpectralPoint q).im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast him
    field_simp [him', Complex.I_ne_zero]

/-- The odd-sector energy density is the squared deviation times the squared divided
difference. -/
theorem norm_sq_xiWeilOddPart_eq_deviation (F : ℂ → ℂ) (q : XiZeroCopy) :
    ‖xiWeilOddPart F (xiSpectralPoint q)‖ ^ 2 =
      (xiSpectralPoint q).im ^ 2 *
        ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2 := by
  rw [xiWeilOddPart_eq_deviation_mul_dslope, norm_mul, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]

/-! ## The deviation moment identity -/

/-- **The deviation moment identity.**  For every square-summable test the diagonal Weil value
is the even energy minus the second moment of critical-line deviations weighted by divided
differences of the test.  This is the exact analytic content of the negative Krein sector: a
positivity producer must dominate this moment by the even energy. -/
theorem xiWeilPolarization_re_eq_deviation_moment {F : ℂ → ℂ}
    (hF : XiWeilSquareSummable F) :
    (xiWeilPolarization F F).re =
      (∑' q : XiZeroCopy, ‖xiWeilEvenPart F (xiSpectralPoint q)‖ ^ 2) -
        ∑' q : XiZeroCopy, (xiSpectralPoint q).im ^ 2 *
          ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2 := by
  rw [xiWeilPolarization_self_eq_parity_energies hF, Complex.ofReal_re]
  congr 1
  exact tsum_congr fun q => norm_sq_xiWeilOddPart_eq_deviation F q

/-- The deviation-weighted divided-difference energy of a square-summable test converges. -/
theorem deviation_dslope_energy_summable {F : ℂ → ℂ} (hF : XiWeilSquareSummable F) :
    Summable (fun q : XiZeroCopy => (xiSpectralPoint q).im ^ 2 *
      ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2) := by
  refine (xiWeilOddPart_squareSummable hF).congr fun q => ?_
  exact norm_sq_xiWeilOddPart_eq_deviation F q

/-- **The unconditional strip lower bound.**  Whenever the divided-difference energy of a test
converges, the diagonal Weil value is at least the even energy minus one quarter of the
divided-difference energy — the quarter being the square of the strip half-width, the only
unconditional information about deviations. -/
theorem xiWeilPolarization_re_ge_strip_bound {F : ℂ → ℂ}
    (hF : XiWeilSquareSummable F)
    (hD : Summable (fun q : XiZeroCopy =>
      ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2)) :
    (∑' q : XiZeroCopy, ‖xiWeilEvenPart F (xiSpectralPoint q)‖ ^ 2) -
        (1 / 4) * ∑' q : XiZeroCopy,
          ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2 ≤
      (xiWeilPolarization F F).re := by
  rw [xiWeilPolarization_re_eq_deviation_moment hF]
  have hpt : ∀ q : XiZeroCopy,
      (xiSpectralPoint q).im ^ 2 *
          ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2 ≤
        (1 / 4) * ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2 := by
    intro q
    have h := abs_xiSpectralPoint_im_lt_half q
    have h2 : (xiSpectralPoint q).im ^ 2 ≤ 1 / 4 := by
      nlinarith [abs_nonneg ((xiSpectralPoint q).im), sq_abs ((xiSpectralPoint q).im)]
    exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have hmoment : (∑' q : XiZeroCopy, (xiSpectralPoint q).im ^ 2 *
        ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2) ≤
      (1 / 4) * ∑' q : XiZeroCopy,
        ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2 := by
    rw [← tsum_mul_left]
    exact (deviation_dslope_energy_summable hF).tsum_le_tsum hpt (hD.mul_left (1 / 4))
  linarith

/-! ## RH as vanishing of the deviation moment -/

/-- **RH ⟺ the deviation-weighted divided-difference energy vanishes** on every square-summable
test: the second moment of zero deviations, tested against all divided differences, is the
whole obstruction. -/
theorem riemannHypothesis_iff_deviation_moment_eq_zero :
    RiemannHypothesis ↔
      ∀ F : ℂ → ℂ, XiWeilSquareSummable F →
        (∑' q : XiZeroCopy, (xiSpectralPoint q).im ^ 2 *
          ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2) = 0 := by
  rw [riemannHypothesis_iff_forall_pairDifEnergy_eq_zero]
  have hlink : ∀ F : ℂ → ℂ, (∑' q : XiZeroCopy, ‖xiWeilPairDif F q‖ ^ 2) =
      4 * ∑' q : XiZeroCopy, (xiSpectralPoint q).im ^ 2 *
        ‖dslope F ((starRingEnd ℂ) (xiSpectralPoint q)) (xiSpectralPoint q)‖ ^ 2 := by
    intro F
    rw [← tsum_mul_left]
    apply tsum_congr
    intro q
    have hodd := xiWeilOddPart_spectral F q
    have hdif : xiWeilPairDif F q = 2 * xiWeilOddPart F (xiSpectralPoint q) := by
      rw [hodd]
      ring
    rw [hdif, norm_mul, mul_pow, ← norm_sq_xiWeilOddPart_eq_deviation]
    norm_num
  constructor
  · intro h F hF
    have hzero := h F hF
    rw [hlink F] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)
  · intro h F hF
    rw [hlink F, h F hF, mul_zero]

end

end RHTower
