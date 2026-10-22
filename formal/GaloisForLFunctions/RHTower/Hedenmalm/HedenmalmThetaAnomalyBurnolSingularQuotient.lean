import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPrimeRankTwoCorrectionNoGo
import GaloisForLFunctions.RHTower.BurnolPrimeDilationCoPoissonQuotient
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmTwoPrimeNormalFrame

/-!
# The theta prime anomaly has a canonical Burnol singular quotient

The Fourier transform of the normalized theta translation anomaly factors as a finite-log
multiplier times `XiC`.  Here the multiplier receives its source-canonical removable completion:
it is exactly a half-density-normalized Gamma/co-Poisson divided cell.  Thus division by `XiC` is
not an arbitrary singular rigging; it is Burnol's literal interval source.

After canonical centering, prime labels two and three form a nowhere-zero quotient frame on every
multiplicity-exact Xi divisor copy.  The raw conormal values of both anomalies vanish there, but
their co-Poisson divisor quotient has strictly positive squared energy.  This constructs the
singular source reporter demanded by anomaly cyclicity, without yet asserting the missing Ward
orientation of its energy.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile HedenmalmPrimeTranslation HedenmalmIntervalAnomaly

namespace HedenmalmThetaSource

/-- Entire Gamma/co-Poisson completion of the prime interval multiplier.  The apparent pole at
`z=0` has already been removed by `gammaCoPoissonIntervalCell`. -/
def burnolCompletedShiftMultiplier (n : ℕ) (z : ℂ) : ℂ :=
  Complex.I * thetaIntegerShiftScale n *
    gammaCoPoissonIntervalCell ((Real.log (n : ℝ) : ℝ) : ℂ)
      (1 - dirichletExponent z) (1 / 2)

/-- Off the removable point, the Gamma/co-Poisson completion is exactly the multiplier occurring
in the Fourier transform of the theta integer anomaly. -/
theorem burnolCompletedShiftMultiplier_eq_shiftMultiplier
    (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    burnolCompletedShiftMultiplier n z = shiftMultiplier n z := by
  let L : ℂ := ((Real.log (n : ℝ) : ℝ) : ℂ)
  let G : ℂ := gammaCoPoissonIntervalCell L
    (1 - dirichletExponent z) (1 / 2)
  let E : ℂ := Complex.exp (-(Complex.I * z * L))
  have hb := spectralBoundary_mul_gammaCoPoissonIntervalCell L
    (1 - dirichletExponent z) (1 / 2)
  have hparam : 1 - dirichletExponent z - (1 / 2 : ℂ) = -Complex.I * z := by
    rw [dirichletExponent]
    ring
  have hG : Complex.I * z * G = 1 - E := by
    dsimp only [G] at hb ⊢
    rw [hparam] at hb
    have hb' : -Complex.I * z * G = E - 1 := by
      calc
        -Complex.I * z * G = Complex.exp (-Complex.I * z * L) - 1 := by
          simpa only [sub_self, zero_mul, Complex.exp_zero] using hb
        _ = E - 1 := by
          dsimp only [E]
          congr 2
          ring
    linear_combination -hb'
  apply mul_left_cancel₀ hz
  calc
    z * burnolCompletedShiftMultiplier n z =
        thetaIntegerShiftScale n * (Complex.I * z * G) := by
          rw [burnolCompletedShiftMultiplier]
          dsimp only [G, L]
          ring
    _ = thetaIntegerShiftScale n * (1 - E) := by rw [hG]
    _ = z * shiftMultiplier n z := by
      rw [shiftMultiplier]
      dsimp only [E, L, thetaIntegerShiftScale]
      field_simp [hz]

/-- Exact removable value of the completed interval multiplier. -/
theorem burnolCompletedShiftMultiplier_zero (n : ℕ) :
    burnolCompletedShiftMultiplier n 0 =
      Complex.I * thetaIntegerShiftScale n *
        ((Real.log (n : ℝ) : ℝ) : ℂ) := by
  have hparam : 1 - dirichletExponent 0 = (1 / 2 : ℂ) := by
    norm_num [dirichletExponent]
  rw [burnolCompletedShiftMultiplier, hparam,
    gammaCoPoissonIntervalCell_self]
  simp

/-- Centered co-Poisson completion, in the same phase convention as the positive theta window. -/
def burnolCompletedCenteredMultiplier (n : ℕ) (z : ℂ) : ℂ :=
  -Complex.I * Complex.exp
      (Complex.I * z * ((Real.log n / 2 : ℝ) : ℂ)) *
    burnolCompletedShiftMultiplier n z

/-- Off the removable point, the centered completion is the existing centered prime multiplier. -/
theorem burnolCompletedCenteredMultiplier_eq_centeredMultiplier
    (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    burnolCompletedCenteredMultiplier n z = centeredMultiplier n z := by
  rw [burnolCompletedCenteredMultiplier,
    burnolCompletedShiftMultiplier_eq_shiftMultiplier n hz,
    centeredMultiplier_eq hz]

/-- Exact removable value of the centered completion. -/
theorem burnolCompletedCenteredMultiplier_zero (n : ℕ) :
    burnolCompletedCenteredMultiplier n 0 =
      thetaIntegerShiftScale n * ((Real.log (n : ℝ) : ℝ) : ℂ) := by
  rw [burnolCompletedCenteredMultiplier, burnolCompletedShiftMultiplier_zero]
  simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
  linear_combination
    -(thetaIntegerShiftScale n * ((Real.log (n : ℝ) : ℝ) : ℂ)) *
      Complex.I_mul_I

/-- Fourier factorization of the raw anomaly through the completed Burnol quotient. -/
theorem integral_integerAnomaly_sourceChar_eq_burnolCompleted
    {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : |z.im| < 1) (hz0 : z ≠ 0) :
    (∫ x : ℝ, integerAnomaly thetaSource n x * sourceChar z x) =
      burnolCompletedShiftMultiplier n z * XiC z := by
  rw [integral_integerAnomaly_sourceChar hn hz hz0,
    burnolCompletedShiftMultiplier_eq_shiftMultiplier n hz0]

/-- Fourier factorization of the positive centered anomaly through the same completed quotient. -/
theorem integral_centeredWindow_sourceChar_eq_burnolCompleted
    {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : |z.im| < 1) (hz0 : z ≠ 0) :
    (∫ x : ℝ, ((centeredWindow thetaSource n x : ℝ) : ℂ) * sourceChar z x) =
      burnolCompletedCenteredMultiplier n z * XiC z := by
  rw [integral_centeredWindow_sourceChar hn hz hz0,
    burnolCompletedCenteredMultiplier_eq_centeredMultiplier n hz0]

/-- Prime-two/prime-three co-Poisson anomaly quotient frame on one actual Xi divisor copy. -/
def thetaXiBurnolAnomalyQuotientFrame (q : XiZeroCopy) : ℂ × ℂ :=
  (burnolCompletedCenteredMultiplier 2 (xiSpectralPoint q),
    burnolCompletedCenteredMultiplier 3 (xiSpectralPoint q))

/-- **Faithful singular quotient reporter.**  The completed prime-two/prime-three anomaly quotient
frame never vanishes on an actual Xi divisor copy. -/
theorem thetaXiBurnolAnomalyQuotientFrame_ne_zero (q : XiZeroCopy) :
    thetaXiBurnolAnomalyQuotientFrame q ≠ (0, 0) := by
  have hz : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  intro hpair
  have h2 : burnolCompletedCenteredMultiplier 2 (xiSpectralPoint q) = 0 :=
    congrArg Prod.fst hpair
  have h3 : burnolCompletedCenteredMultiplier 3 (xiSpectralPoint q) = 0 :=
    congrArg Prod.snd hpair
  rw [burnolCompletedCenteredMultiplier_eq_centeredMultiplier 2 hz] at h2
  rw [burnolCompletedCenteredMultiplier_eq_centeredMultiplier 3 hz] at h3
  exact hz (no_common_zero_centered_two_three h2 h3)

/-- Positive scalar energy of the two-prime co-Poisson quotient reporter. -/
def thetaXiBurnolAnomalyQuotientEnergy (q : XiZeroCopy) : ℝ :=
  Complex.normSq (thetaXiBurnolAnomalyQuotientFrame q).1 +
    Complex.normSq (thetaXiBurnolAnomalyQuotientFrame q).2

theorem thetaXiBurnolAnomalyQuotientEnergy_pos (q : XiZeroCopy) :
    0 < thetaXiBurnolAnomalyQuotientEnergy q := by
  have hframe := thetaXiBurnolAnomalyQuotientFrame_ne_zero q
  have hcases :
      (thetaXiBurnolAnomalyQuotientFrame q).1 ≠ 0 ∨
        (thetaXiBurnolAnomalyQuotientFrame q).2 ≠ 0 := by
    contrapose! hframe
    exact Prod.ext hframe.1 hframe.2
  unfold thetaXiBurnolAnomalyQuotientEnergy
  rcases hcases with h1 | h2
  · have hp : 0 < Complex.normSq (thetaXiBurnolAnomalyQuotientFrame q).1 :=
      Complex.normSq_pos.mpr h1
    nlinarith [Complex.normSq_nonneg (thetaXiBurnolAnomalyQuotientFrame q).2]
  · have hp : 0 < Complex.normSq (thetaXiBurnolAnomalyQuotientFrame q).2 :=
      Complex.normSq_pos.mpr h2
    nlinarith [Complex.normSq_nonneg (thetaXiBurnolAnomalyQuotientFrame q).1]

/-- **Singular quotient separation.**  Both raw prime anomaly conormals vanish at every Xi copy,
while the source-canonical Burnol divisor quotient has strictly positive two-prime energy. -/
theorem thetaXi_rawAnomalyConormals_zero_but_burnolQuotientEnergy_pos
    (q : XiZeroCopy) :
    (∫ x : ℝ, integerAnomaly thetaSource 2 x *
        sourceChar (xiSpectralPoint q) x) = 0 ∧
      (∫ x : ℝ, integerAnomaly thetaSource 3 x *
        sourceChar (xiSpectralPoint q) x) = 0 ∧
      0 < thetaXiBurnolAnomalyQuotientEnergy q := by
  refine ⟨?_, ?_, thetaXiBurnolAnomalyQuotientEnergy_pos q⟩
  · rw [integral_integerAnomaly_sourceChar_eq_burnolCompleted
      (by norm_num) (thetaXiSpectralPoint_mem_sourceStrip q)
      (xiSpectralPoint_ne_zero q), XiC_xiSpectralPoint_eq_zero, mul_zero]
  · rw [integral_integerAnomaly_sourceChar_eq_burnolCompleted
      (by norm_num) (thetaXiSpectralPoint_mem_sourceStrip q)
      (xiSpectralPoint_ne_zero q), XiC_xiSpectralPoint_eq_zero, mul_zero]

end HedenmalmThetaSource
end
end RHTower
