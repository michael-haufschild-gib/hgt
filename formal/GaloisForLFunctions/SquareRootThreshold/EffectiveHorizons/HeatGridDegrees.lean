import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.TraceHankelDegrees
import GaloisForLFunctions.RHTower.XiGaussianHeatTwoPrimeSourceSampling
import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalLineReceiver
import GaloisForLFunctions.RHTower.XiOrderFourteenCornerSourceExclusion

/-!
# Explicit degrees for two arithmetic heat grids

The absolute ξ heat mass is at most `6/h`. The finite outer sampled spectrum
therefore gives an explicit source polynomial and degree bound detecting each
nonreal sample. Two distinct prime-log spacings remove exponential aliasing;
the detector vanishes at the omitted pole and allows every odd starting offset.
-/

open Complex Polynomial Filter Topology

noncomputable section
namespace RHTower

/-- The reciprocal-square spectral mass is bounded by the zeroth source moment. -/
theorem xiSpectralPoint_inverse_square_mass_lt_two :
    (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) < 2 := by
  have hs := sectorFactor_mul_xiShiftAbsoluteMass_le_normalizedPrimeArchMoment 0
  norm_num at hs
  have hm : xiShiftAbsoluteMass 0 < 2 := by
    linarith only [hs, normalizedPrimeArchMoment_zero_lt_one]
  simpa only [xiShiftAbsoluteMass, Nat.zero_add, pow_one, xiZeroCopyReciprocalSquare,
    norm_pow, norm_inv, inv_pow, one_div] using hm

/-- The total absolute heat mass has a numerical bound at every positive grid spacing. -/
theorem tsum_norm_xiGaussianHeatTerm_le_six_div {h : ℝ} (hh : 0 < h) :
    (∑' q : XiZeroCopy, ‖xiGaussianHeatTerm h q‖) ≤ 6 / h := by
  have hterm (q : XiZeroCopy) : ‖xiGaussianHeatTerm h q‖ ≤
      (3 / h) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
    simpa only [xiGaussianHeatTermC, xiGaussianHeatTerm, Complex.ofReal_re,
      Complex.ofReal_im] using
      norm_xiGaussianHeatTermC_le_of_abs_im_le (τ := (h : ℂ))
        (by simpa using hh) (by simpa using hh.le) q
  calc
    _ ≤ ∑' q : XiZeroCopy, (3 / h) * (1 / ‖xiSpectralPoint q‖ ^ 2) :=
      (summable_xiGaussianHeatTerm hh).norm.tsum_le_tsum hterm
        (xiSpectralPoint_inv_sq_summable.mul_left _)
    _ = (3 / h) * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := tsum_mul_left
    _ ≤ (3 / h) * 2 := mul_le_mul_of_nonneg_left
      xiSpectralPoint_inverse_square_mass_lt_two.le (by positivity)
    _ = 6 / h := by ring

/-- Zero copies whose sampled heat modulus is at least half the target modulus. -/
def xiHeatGridOuterCopies (h : ℝ) (hh : 0 < h) (q : XiZeroCopy) : Finset XiZeroCopy :=
  (finite_setOf_le_norm_xiGaussianHeatTerm hh
    (show 0 < ‖xiGaussianHeatTerm h q‖ / 2 from div_pos
      (norm_pos_iff.mpr (xiGaussianHeatTerm_ne_zero h q)) (by norm_num))).toFinset

theorem mem_xiHeatGridOuterCopies {h : ℝ} (hh : 0 < h) (q i : XiZeroCopy) :
    i ∈ xiHeatGridOuterCopies h hh q ↔
      ‖xiGaussianHeatTerm h q‖ / 2 ≤ ‖xiGaussianHeatTerm h i‖ := by
  simp only [xiHeatGridOuterCopies, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

/-- The finite sampled outer spectrum, with repeated nodes identified. -/
def xiHeatGridOuterSpectrum (h : ℝ) (hh : 0 < h) (q : XiZeroCopy) : Finset ℂ :=
  (xiHeatGridOuterCopies h hh q).image (xiGaussianHeatTerm h)

/-- The odd offset and omitted pole are encoded by one real polynomial ideal. -/
def xiHeatGridDetectionIdeal (h : ℝ) (K : ℕ) : ℝ[X] :=
  X ^ K * (X - C (xiHeatGridPole h))

/-- An explicit arithmetic-source detector on a heat sampling grid. -/
def xiHeatGridExplicitDetector (h : ℝ) (hh : 0 < h) (K : ℕ) (q : XiZeroCopy) : ℝ[X] :=
  (X - C (xiHeatGridPole h)) *
    traceHankelIdealDetector (xiHeatGridOuterSpectrum h hh q)
      (xiGaussianHeatTerm h q) (xiHeatGridDetectionIdeal h K) (6 / h)

/-- A finite-data degree bound for the actual arithmetic-source detector. -/
def xiHeatGridDetectionDegree (h : ℝ) (hh : 0 < h) (K : ℕ) (q : XiZeroCopy) : ℕ :=
  2 * ⌈2 * (6 / h) / ‖xiGaussianHeatTerm h q‖⌉₊ + 2 +
    traceHankelRadialExponent
      (traceHankelIdealMajorant (xiHeatGridOuterSpectrum h hh q)
        (xiGaussianHeatTerm h q) (xiHeatGridDetectionIdeal h K)) (6 / h)

theorem card_xiHeatGridOuterSpectrum_le (h : ℝ) (hh : 0 < h) (q : XiZeroCopy) :
    (xiHeatGridOuterSpectrum h hh q).card ≤ ⌈2 * (6 / h) / ‖xiGaussianHeatTerm h q‖⌉₊ := by
  refine (Finset.card_image_le).trans ?_
  exact card_le_ceil_of_half_norm_mass (xiGaussianHeatTerm h)
    (summable_xiGaussianHeatTerm hh) (6 / h) (tsum_norm_xiGaussianHeatTerm_le_six_div hh)
    (norm_pos_iff.mpr (xiGaussianHeatTerm_ne_zero h q)) (xiHeatGridOuterCopies h hh q)
    (fun i hi => (mem_xiHeatGridOuterCopies hh q i).mp hi)

theorem natDegree_xiHeatGridExplicitDetector_le (h : ℝ) (hh : 0 < h) (K : ℕ)
    (q : XiZeroCopy) :
    (xiHeatGridExplicitDetector h hh K q).natDegree ≤ xiHeatGridDetectionDegree h hh K q := by
  have hp := natDegree_traceHankelIdealDetector_le (xiHeatGridOuterSpectrum h hh q)
    (xiGaussianHeatTerm h q) (xiHeatGridDetectionIdeal h K) (6 / h)
  have hb : (X - C (xiHeatGridPole h) : ℝ[X]).natDegree ≤ 1 := by
    exact (natDegree_sub_le _ _).trans (by simp)
  have hmul := @natDegree_mul_le ℝ _ (X - C (xiHeatGridPole h))
    (traceHankelIdealDetector (xiHeatGridOuterSpectrum h hh q)
      (xiGaussianHeatTerm h q) (xiHeatGridDetectionIdeal h K) (6 / h))
  have hcard := card_xiHeatGridOuterSpectrum_le h hh q
  change _ ≤ 2 * ⌈2 * (6 / h) / ‖xiGaussianHeatTerm h q‖⌉₊ + 2 + _
  change ((X - C (xiHeatGridPole h)) * _).natDegree ≤ _
  omega

theorem xiHeatGridExplicitDetector_pole_zero (h : ℝ) (hh : 0 < h) (K : ℕ)
    (q : XiZeroCopy) :
    (xiHeatGridExplicitDetector h hh K q).eval (xiHeatGridPole h) = 0 := by
  simp only [xiHeatGridExplicitDetector, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul]

/-- Every nonreal sampled node is detected at the explicit finite degree, after any odd offset. -/
theorem xiPrimeArchHeatGrid_explicitDetector_negative {h : ℝ} (hh : 0 < h) (K : ℕ)
    (q : XiZeroCopy) (him : (xiGaussianHeatTerm h q).im ≠ 0) :
    HTGeometry.momentFunctional (xiPrimeArchHeatGridMoment h K)
      (xiHeatGridExplicitDetector h hh K q ^ 2) < -1 / 2 := by
  have hα : xiGaussianHeatTerm h q ≠ 0 := xiGaussianHeatTerm_ne_zero h q
  have ha : evalRealPolynomial (xiHeatGridDetectionIdeal h K) (xiGaussianHeatTerm h q) ≠ 0 := by
    rw [xiHeatGridDetectionIdeal, evalRealPolynomial_mul, evalRealPolynomial_pow]
    have hX : evalRealPolynomial X (xiGaussianHeatTerm h q) = xiGaussianHeatTerm h q := by
      simp only [evalRealPolynomial, Polynomial.map_X, Polynomial.eval_X]
    have hb : evalRealPolynomial (X - C (xiHeatGridPole h)) (xiGaussianHeatTerm h q) =
        xiGaussianHeatTerm h q - (xiHeatGridPole h : ℂ) := by simp [evalRealPolynomial]
    rw [hX, hb]
    refine mul_ne_zero (pow_ne_zero K hα) ?_
    intro he
    have hi := congrArg Complex.im he
    exact him (by simpa using hi)
  have hneg := traceHankelIdealDetector_negative (xiGaussianHeatTerm h)
    (summable_xiGaussianHeatTerm hh) (6 / h) (tsum_norm_xiGaussianHeatTerm_le_six_div hh)
    q him (xiHeatGridDetectionIdeal h K) ha (xiHeatGridOuterCopies h hh q)
    (mem_xiHeatGridOuterCopies hh q)
  rw [momentFunctional_xiPrimeArchHeatGridMoment_square_of_pole_zero hh K _
    (xiHeatGridExplicitDetector_pole_zero h hh K q), momentFunctional_xiHeatGridMoment_square hh K]
  simpa only [xiHeatGridOuterSpectrum, xiHeatGridExplicitDetector, xiHeatGridDetectionIdeal,
    mul_assoc] using hneg

/-- One of the two prime-log grids detects every nonreal squared ξ-frequency at finite degree. -/
theorem two_prime_heatGrids_explicitDetector_negative {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) (K L : ℕ) (q : XiZeroCopy)
    (hq : (xiSpectralPoint q ^ 2).im ≠ 0) :
    HTGeometry.momentFunctional (xiPrimeArchHeatGridMoment (Real.log p) K)
      (xiHeatGridExplicitDetector (Real.log p) (Real.log_pos (by exact_mod_cast hp.one_lt)) K q ^ 2)
        < -1 / 2 ∨
    HTGeometry.momentFunctional (xiPrimeArchHeatGridMoment (Real.log r) L)
      (xiHeatGridExplicitDetector (Real.log r) (Real.log_pos (by exact_mod_cast hr.one_lt)) L q ^ 2)
        < -1 / 2 := by
  have hp0 : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hr0 : 0 < Real.log r := Real.log_pos (by exact_mod_cast hr.one_lt)
  by_cases h₁ : (xiGaussianHeatTerm (Real.log p) q).im = 0
  · have h₂ : (xiGaussianHeatTerm (Real.log r) q).im ≠ 0 := by
      intro hh
      exact hq (im_eq_zero_of_two_prime_exp_real hp hr hpr (xiSpectralPoint q ^ 2) h₁ hh)
    exact Or.inr (xiPrimeArchHeatGrid_explicitDetector_negative hr0 L q h₂)
  · exact Or.inl (xiPrimeArchHeatGrid_explicitDetector_negative hp0 K q h₁)

/-- Every off-line ξ-zero yields a finite-degree negative arithmetic source test
on the `log 2` or `log 3` grid, with independently prescribed odd offsets. -/
theorem two_three_heatGrids_explicitDetector_negative_of_offLine
    (K L : ℕ) (q : XiZeroCopy) (hq : (q.1 : ℂ).re ≠ 1 / 2) :
    HTGeometry.momentFunctional (xiPrimeArchHeatGridMoment (Real.log 2) K)
      (xiHeatGridExplicitDetector (Real.log 2) (Real.log_pos (by norm_num)) K q ^ 2)
        < -1 / 2 ∨
    HTGeometry.momentFunctional (xiPrimeArchHeatGridMoment (Real.log 3) L)
      (xiHeatGridExplicitDetector (Real.log 3) (Real.log_pos (by norm_num)) L q ^ 2)
        < -1 / 2 := by
  apply two_prime_heatGrids_explicitDetector_negative Nat.prime_two Nat.prime_three
    (by norm_num) K L q
  have hspec : (xiSpectralPoint q ^ 2).im =
      -2 * (q.1 : ℂ).im * ((q.1 : ℂ).re - 1 / 2) := by
    simp only [pow_two, Complex.mul_im]
    simp [xiSpectralPoint]
    ring
  rw [hspec]
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (xiSupport_im_ne_zero q.1)) (sub_ne_zero.mpr hq)

#print axioms tsum_norm_xiGaussianHeatTerm_le_six_div
#print axioms natDegree_xiHeatGridExplicitDetector_le
#print axioms xiPrimeArchHeatGrid_explicitDetector_negative
#print axioms two_prime_heatGrids_explicitDetector_negative
#print axioms two_three_heatGrids_explicitDetector_negative_of_offLine

end RHTower
