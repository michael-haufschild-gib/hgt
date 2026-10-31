import GaloisForLFunctions.ArithmeticIncidencePositivity.GammaDilationControlsTheArchimedeanForm
import GaloisForLFunctions.ArithmeticIncidencePositivity.PoleDilationHasAnExplicitMassBound
import GaloisForLFunctions.ArithmeticIncidencePositivity.LagChebyshevAbelSummation
import GaloisForLFunctions.BiScaleUncertainty.LinearKreinSmoothingAndInverseLinearGridTail
import GaloisForLFunctions.RHTower.DigammaQuarter

/-!
# Effective dilation on the one-prime aperture

Support in the centered unit interval leaves precisely the prime two.
Low full Weil energy bounds the positive Levy energy. The logarithmic
correlation modulus then controls the moving prime sample under dilation.
-/

noncomputable section
open MeasureTheory Set
namespace GaloisForLFunctions.ArithmeticIncidencePositivity
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm
open ArithmeticCriticalityTheory RenormalizedArithmeticPotentialTheory BiScaleUncertainty

/-- The actual coefficient of the only prime visible in a centered unit support. -/
def onePrimeCoefficient : ℝ := Real.sqrt 2 * Real.log 2

theorem onePrimeCoefficient_pos : 0 < onePrimeCoefficient := by
  exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) (Real.log_pos (by norm_num))

private theorem autocorr_zero_of_unit_support {f : ℝ → ℝ}
    (hs : ∀ u, 1 / 2 < |u| → f u = 0) {t : ℝ} (ht : 1 < |t|) :
    autocorr f t = 0 := by
  change (∫ u, f u * f (u + t)) = 0
  have hzero (u : ℝ) : f u * f (u + t) = 0 := by
    by_cases hu : 1 / 2 < |u|
    · rw [hs u hu, zero_mul]
    · have hsu := abs_sub_abs_le_abs_sub t (-u)
      rw [abs_neg, sub_neg_eq_add, add_comm] at hsu
      rw [hs (u + t) (by linarith only [ht, hsu, le_of_not_gt hu]), mul_zero]
  simp only [hzero, integral_zero]

/-- The exact prime sum on a centered unit support contains only the atom at two. -/
theorem primeSum_eq_two_of_unit_support {f : ℝ → ℝ}
    (hs : ∀ u, 1 / 2 < |u| → f u = 0) :
    primeSum f = onePrimeCoefficient * autocorr f (Real.log 2) := by
  have hterm (n : ℕ) :
      (∫ u, f u * f (u - Real.log n)) + (∫ u, f u * f (u + Real.log n)) =
        2 * autocorr f (Real.log n) := by
    change autocorr f (-Real.log n) + autocorr f (Real.log n) = _
    rw [autocorr_neg]
    ring
  unfold primeSum
  simp_rw [hterm]
  rw [tsum_eq_single 2]
  · rw [vonMangoldtAtom, if_pos (by norm_num : 2 ≤ (2 : ℕ)),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    simp only [Nat.cast_ofNat, onePrimeCoefficient]
    have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · intro n hn
    by_cases hn2 : 2 ≤ n
    · have h3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
      have hlog3 : 1 < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        linarith only [Real.exp_one_lt_d9]
      have hlog : 1 < Real.log n := hlog3.trans_le
        (Real.log_le_log (by norm_num) h3)
      rw [autocorr_zero_of_unit_support hs
        (by rw [abs_of_pos (by linarith only [hlog])]; exact hlog), mul_zero, mul_zero]
    · rw [vonMangoldtAtom, if_neg hn2, zero_mul]

/-- The two physical definitions of the archimedean Levy energy agree exactly. -/
theorem levyEnergy_eq_biScaleLevyEnergy {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    levyEnergy f = biScaleLevyEnergy f := by
  unfold levyEnergy biScaleLevyEnergy
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only [archLevySinhWeight]
  rw [integral_sub_shift_sq hfc hf x, exp_half_div_sinh_eq hx]
  ring

theorem fullZeroForm_eq_arch_prime_pole {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    fullZeroForm f = archForm f - primeSum f + realPoleForm f := by
  rw [fullZeroForm_eq_markovEnergy_add_expMoments hf.continuous hfc,
    markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, realPoleForm_eq_expMoments]

/-- An explicit upper bound for Levy energy on the unit low-energy cone. -/
def onePrimeLowEnergyConstant : ℝ :=
  1 + 2 * |gammaHardyPhaseRate 0| + onePrimeCoefficient + 2 * Real.exp 2

theorem onePrimeLowEnergyConstant_pos : 0 < onePrimeLowEnergyConstant := by
  have := onePrimeCoefficient_pos
  unfold onePrimeLowEnergyConstant
  positivity

/-- Gauss's quarter value opens every constant in the low-energy bound. -/
theorem onePrimeLowEnergyConstant_closed :
    onePrimeLowEnergyConstant =
      1 + Real.log Real.pi + 3 * Real.log 2 + Real.eulerMascheroniConstant + Real.pi / 2 +
        onePrimeCoefficient + 2 * Real.exp 2 := by
  have hline : linePt 0 / 2 = (1 / 4 : ℂ) := by
    unfold linePt
    norm_num
  have hvalue : 2 * gammaHardyPhaseRate 0 =
      -GaloisForLFunctions.RHTower.archRatioCharge := by
    unfold gammaHardyPhaseRate
    rw [hline, GaloisForLFunctions.RHTower.digamma_quarter]
    simp only [Complex.neg_re, Complex.ofReal_re,
      GaloisForLFunctions.RHTower.archRatioCharge]
    ring
  have hneg : gammaHardyPhaseRate 0 ≤ 0 := by
    linarith only [hvalue, GaloisForLFunctions.RHTower.archRatioCharge_pos]
  rw [onePrimeLowEnergyConstant, abs_of_nonpos hneg]
  dsimp only [GaloisForLFunctions.RHTower.archRatioCharge] at hvalue
  linarith only [hvalue]

theorem abs_realPoleForm_le_sq_mass {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hs : ∀ u, 1 / 2 < |u| → f u = 0) :
    |realPoleForm f| ≤ 2 * Real.exp 2 * ∫ u, f u ^ 2 := by
  have hA : 0 ≤ ∫ u, |f u| := integral_nonneg fun u => abs_nonneg _
  have hp := abs_centered_exponentialMoment_le hf.continuous hfc hs
    (q := 1 / 2) (by norm_num)
  have hm := abs_centered_exponentialMoment_le hf.continuous hfc hs
    (q := -(1 / 2)) (by norm_num)
  have hmass := _root_.RHTower.SeparatedBump.sq_integral_abs_le hf
    (δ := 1) hs (by norm_num)
  rw [one_mul] at hmass
  have he : Real.exp 1 * Real.exp 1 = Real.exp 2 := by rw [← Real.exp_add]; norm_num
  rw [realPoleForm, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * (Real.exp 1 * ∫ u, |f u|) * (Real.exp 1 * ∫ u, |f u|) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num)) hm
        (abs_nonneg _) (by positivity)
    _ = 2 * Real.exp 2 * (∫ u, |f u|) ^ 2 := by rw [← he]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)

/-- Bounded full energy forces an explicit bound on the positive Levy term. -/
theorem biScaleLevyEnergy_le_of_fullZeroForm_le_mass {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hs : ∀ u, 1 / 2 < |u| → f u = 0)
    (hQ : fullZeroForm f ≤ ∫ u, f u ^ 2) :
    biScaleLevyEnergy f ≤ onePrimeLowEnergyConstant * ∫ u, f u ^ 2 := by
  have hmass0 : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hmass : autocorr f 0 = ∫ u, f u ^ 2 := by
    unfold autocorr
    simp only [add_zero, ← sq]
  have hp := abs_autocorr_le_zero hfc hf.continuous (Real.log 2)
  rw [hmass] at hp
  have hprime : onePrimeCoefficient * autocorr f (Real.log 2) ≤
      onePrimeCoefficient * ∫ u, f u ^ 2 :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans hp) onePrimeCoefficient_pos.le
  have hpolar := neg_abs_le (realPoleForm f)
  have hb := abs_realPoleForm_le_sq_mass hf hfc hs
  have hgamma := mul_le_mul_of_nonneg_right
    (neg_abs_le (gammaHardyPhaseRate 0)) hmass0
  rw [fullZeroForm_eq_arch_prime_pole hf hfc, archForm_eq_levyEnergy hf hfc,
    levyEnergy_eq_biScaleLevyEnergy hf.continuous hfc,
    primeSum_eq_two_of_unit_support hs] at hQ
  unfold onePrimeLowEnergyConstant
  nlinarith only [hQ, hprime, hpolar, hb, hgamma]

/-- The fixed numerator in the logarithmic prime-dilation modulus. -/
def onePrimeDilationCoefficient : ℝ :=
  onePrimeCoefficient * (32 * Real.exp (1 / 2) * onePrimeLowEnergyConstant + 2)

theorem onePrimeDilationCoefficient_pos : 0 < onePrimeDilationCoefficient := by
  unfold onePrimeDilationCoefficient
  exact mul_pos onePrimeCoefficient_pos (by
    have := onePrimeLowEnergyConstant_pos
    positivity)

theorem unitSupport_comp_mul {f : ℝ → ℝ}
    (hs : ∀ u, 1 / 2 < |u| → f u = 0) {r : ℝ} (hr : 1 ≤ r) :
    ∀ u, 1 / 2 < |u| → f (r * u) = 0 := by
  intro u hu
  apply hs
  rw [abs_mul, abs_of_pos (lt_of_lt_of_le zero_lt_one hr)]
  have h := mul_le_mul_of_nonneg_right hr (abs_nonneg u)
  linarith only [hu, h]

/-- Normalized dilation moves the unique prime sample and leaves its coefficient fixed. -/
theorem primeSum_normalized_dilation {f : ℝ → ℝ}
    (hs : ∀ u, 1 / 2 < |u| → f u = 0) {r : ℝ} (hr : 1 ≤ r) :
    r * primeSum (fun u => f (r * u)) - primeSum f =
      onePrimeCoefficient * (autocorr f (r * Real.log 2) - autocorr f (Real.log 2)) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [primeSum_eq_two_of_unit_support (unitSupport_comp_mul hs hr),
    primeSum_eq_two_of_unit_support hs]
  have hc : autocorr (fun u => f (r * u)) (Real.log 2) =
      r⁻¹ * autocorr f (r * Real.log 2) := by
    unfold autocorr
    have heq : (∫ u, f (r * u) * f (r * (u + Real.log 2))) =
        ∫ u, (fun v => f v * f (v + r * Real.log 2)) (r * u) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by
        change f (r * u) * f (r * (u + Real.log 2)) =
          f (r * u) * f (r * u + r * Real.log 2)
        rw [mul_add]
    rw [heq, Measure.integral_comp_mul_left
      (fun v => f v * f (v + r * Real.log 2)) r,
      abs_of_pos (inv_pos.mpr hr0), smul_eq_mul]
  rw [hc]
  field_simp

/-- The moving prime sample has an explicit logarithmic cost on the low-energy cone. -/
theorem primeSum_dilation_bound {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hs : ∀ u, 1 / 2 < |u| → f u = 0)
    (hQ : fullZeroForm f ≤ ∫ u, f u ^ 2) {r : ℝ}
    (hr : 1 < r) (hsmall : (r - 1) * Real.log 2 < 1) :
    |r * primeSum (fun u => f (r * u)) - primeSum f| ≤
      (onePrimeDilationCoefficient / (-Real.log ((r - 1) * Real.log 2))) * ∫ u, f u ^ 2 := by
  have hd0 : 0 < (r - 1) * Real.log 2 :=
    mul_pos (sub_pos.mpr hr) (Real.log_pos (by norm_num))
  have hlog : 0 < -Real.log ((r - 1) * Real.log 2) :=
    neg_pos.mpr (Real.log_neg hd0 hsmall)
  have hdist : |r * Real.log 2 - Real.log 2| = (r - 1) * Real.log 2 := by
    rw [show r * Real.log 2 - Real.log 2 = (r - 1) * Real.log 2 by ring,
      abs_of_pos hd0]
  have hmod := neg_log_mul_abs_autocorr_sub_le hf hfc
    (x := r * Real.log 2) (y := Real.log 2) (by rwa [hdist]) (by rwa [hdist])
  rw [hdist] at hmod
  have hmass : autocorr f 0 = ∫ u, f u ^ 2 := by
    unfold autocorr
    simp only [add_zero, ← sq]
  rw [hmass] at hmod
  have hlevy := biScaleLevyEnergy_le_of_fullZeroForm_le_mass hf hfc hs hQ
  have hmul := mul_le_mul_of_nonneg_left hlevy
    (show 0 ≤ 32 * Real.exp (1 / 2) by positivity)
  have hcorr : |autocorr f (r * Real.log 2) - autocorr f (Real.log 2)| ≤
      ((32 * Real.exp (1 / 2) * onePrimeLowEnergyConstant + 2) * ∫ u, f u ^ 2) /
        (-Real.log ((r - 1) * Real.log 2)) := by
    apply (le_div_iff₀ hlog).mpr
    nlinarith only [hmod, hmul]
  rw [primeSum_normalized_dilation hs hr.le, abs_mul,
    abs_of_pos onePrimeCoefficient_pos]
  exact (mul_le_mul_of_nonneg_left hcorr onePrimeCoefficient_pos.le).trans_eq (by
    unfold onePrimeDilationCoefficient
    ring)

/-- The full actual Weil form has an explicit dilation modulus on the low-energy cone. -/
theorem fullZeroForm_dilation_bound {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hs : ∀ u, 1 / 2 < |u| → f u = 0)
    (hQ : fullZeroForm f ≤ ∫ u, f u ^ 2) {r : ℝ}
    (hr : 1 < r) (hsmall : (r - 1) * Real.log 2 < 1) :
    |r * fullZeroForm (fun u => f (r * u)) - fullZeroForm f| ≤
      (10 * Real.log r + 4 * Real.exp 2 * (r - 1) +
        onePrimeDilationCoefficient / (-Real.log ((r - 1) * Real.log 2))) * ∫ u, f u ^ 2 := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hg : ContDiff ℝ 2 (fun u => f (r * u)) :=
    hf.comp (contDiff_const.mul contDiff_id)
  have hgs := unitSupport_comp_mul hs hr.le
  have hgc : HasCompactSupport (fun u => f (r * u)) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (fun u hu =>
      abs_le.mp (le_of_not_gt fun h => hu (hgs u h)))
  have harch := archForm_logarithmic_dilation_bound f hf hfc hr0
  rw [abs_of_nonneg (Real.log_nonneg hr.le)] at harch
  have hprime := primeSum_dilation_bound hf hfc hs hQ hr hsmall
  have hpole := realPoleForm_dilation_bound hf hfc hs hr.le
  rw [fullZeroForm_eq_arch_prime_pole hg hgc, fullZeroForm_eq_arch_prime_pole hf hfc]
  rw [show r * (archForm (fun u => f (r * u)) - primeSum (fun u => f (r * u)) +
        realPoleForm (fun u => f (r * u))) - (archForm f - primeSum f + realPoleForm f) =
      (r * archForm (fun u => f (r * u)) - archForm f) -
        (r * primeSum (fun u => f (r * u)) - primeSum f) +
        (r * realPoleForm (fun u => f (r * u)) - realPoleForm f) by ring]
  exact ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
    ((add_le_add (add_le_add harch hprime) hpole).trans_eq (by ring))

end GaloisForLFunctions.ArithmeticIncidencePositivity

#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.primeSum_eq_two_of_unit_support
#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.onePrimeLowEnergyConstant_closed
#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.biScaleLevyEnergy_le_of_fullZeroForm_le_mass
#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.fullZeroForm_dilation_bound
