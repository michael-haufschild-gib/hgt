import GaloisForLFunctions.RHTower.FrankensteinThetaPrimeTranslationPluckerLanding
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceModeNormalization
import GaloisForLFunctions.RHTower.HedenmalmThetaIntervalTransform
import GaloisForLFunctions.RHTower.HedenmalmPrimeTranslationJordanCapstone
import GaloisForLFunctions.RHTower.XiDivisorSupportedMetric

/-!
# One common prime-translation forcing vector for both Xi orientations

For every theta-source divisor mode `f_z`, the normalized integer translation satisfies the exact
inhomogeneous source equation

`(B + z⁻¹) T_n f_z = r_n`,

where `B` is the fixed theta source inverse and `r_n` is the fixed integer-translation anomaly.
The coefficient of `r_n` is literally one because the canonical divisor mode has total integral
equal to the source mass.  Hence a Xi divisor copy and its critical-line-reflected copy are not
merely exchanged by reflection: both are responses to the same nonzero, source-derived forcing
vector, with the same integer/prime label and without collapsing divisor multiplicity.

The anomaly transform also vanishes at every Xi divisor.  Thus this module identifies the exact
quotient obstruction left by common forcing: the two orientations differ only through their
resolvent parameter, while the universal forcing lies in every retained Xi conormal kernel.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile HedenmalmPrimeTranslation

namespace HedenmalmThetaSource

/-- Residual of the normalized integer translate of the canonical source mode at parameter `z`. -/
def thetaPrimeTranslatedSourceResidual (z : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  sourceInverse thetaSource (integerShift n (sourceModeF thetaSource z)) x
    - (-z⁻¹) * integerShift n (sourceModeF thetaSource z) x

/-- **Common-forcing identity.**  At a theta-source divisor, normalized integer translation turns
the homogeneous source eigen-equation into an inhomogeneous equation whose right-hand side is the
fixed integer anomaly with coefficient exactly one. -/
theorem thetaPrimeTranslatedSourceResidual_eq_integerAnomaly {z : ℂ}
    (hz : |z.im| < 1) (hzero : xiC thetaSource z = 0) (n : ℕ) (x : ℝ) :
    thetaPrimeTranslatedSourceResidual z n x = integerAnomaly thetaSource n x := by
  have hcomm := sourceInverse_integerShift thetaSource (sourceModeF thetaSource z)
    (integrable_sourceModeF_thetaSource hz hzero) n x
  rw [sourceInverse_sourceModeF_eq_smul_thetaSource hz hzero] at hcomm
  have hmass := integral_sourceModeF_thetaSource_eq_mass hz hzero
  have hmass_ne : (thetaSource.mass : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr thetaSource.mass_ne_zero
  rw [sourceFunctional, hmass, div_self hmass_ne, one_mul] at hcomm
  unfold thetaPrimeTranslatedSourceResidual
  calc
    sourceInverse thetaSource (integerShift n (sourceModeF thetaSource z)) x
          - (-z⁻¹) * integerShift n (sourceModeF thetaSource z) x =
        sourceInverse thetaSource (integerShift n (sourceModeF thetaSource z)) x
          - (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            * ((-z⁻¹) * sourceModeF thetaSource z (x + Real.log n)) := by
              rw [integerShift]
              ring
    _ = integerAnomaly thetaSource n x := hcomm

/-! ## Absorbing the anomaly into a rank-one prime connection -/

/-- Scalar half-density used by normalized integer translation. -/
def thetaIntegerShiftScale (n : ℕ) : ℂ :=
  (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

/-- Prime-dependent covariant source inverse.  Its rank-one connection subtracts exactly the
universal translation anomaly, with coefficient read from the translated source mass. -/
def thetaIntegerCovariantSourceInverse (n : ℕ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  sourceInverse thetaSource g x -
    (sourceFunctional g /
      (thetaIntegerShiftScale n * (thetaSource.mass : ℂ))) *
        integerAnomaly thetaSource n x

theorem thetaIntegerShiftScale_ne_zero {n : ℕ} (hn : 0 < n) :
    thetaIntegerShiftScale n ≠ 0 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hnR _).ne'

/-- **Exact prime covariance.**  After the universal rank-one connection is included, normalized
integer translation literally intertwines the original source inverse with the covariant one.
This holds for every integrable source vector, not only at Xi zeros. -/
theorem thetaIntegerCovariantSourceInverse_integerShift
    {n : ℕ} (hn : 0 < n) (f : ℝ → ℂ) (hf : Integrable f) :
    thetaIntegerCovariantSourceInverse n (integerShift n f) =
      integerShift n (sourceInverse thetaSource f) := by
  funext x
  have hcomm := sourceInverse_integerShift thetaSource f hf n x
  have hc : thetaIntegerShiftScale n ≠ 0 := thetaIntegerShiftScale_ne_zero hn
  have hM : (thetaSource.mass : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr thetaSource.mass_ne_zero
  have hcoef :
      (thetaIntegerShiftScale n * sourceFunctional f) /
          (thetaIntegerShiftScale n * (thetaSource.mass : ℂ)) =
        sourceFunctional f / (thetaSource.mass : ℂ) := by
    field_simp [hc, hM]
  unfold thetaIntegerCovariantSourceInverse
  rw [sourceFunctional_integerShift]
  change sourceInverse thetaSource (integerShift n f) x -
      (thetaIntegerShiftScale n * sourceFunctional f /
        (thetaIntegerShiftScale n * (thetaSource.mass : ℂ))) *
          integerAnomaly thetaSource n x = _
  rw [hcoef]
  rw [integerShift]
  linear_combination hcomm

/-- The rank-one prime connection is flat on the entire integrable translated source class:
transport by `mn` agrees with transport by `n` followed by transport by `m`. -/
theorem thetaIntegerCovariantSourceInverse_flat
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (f : ℝ → ℂ) (hf : Integrable f) :
    thetaIntegerCovariantSourceInverse (m * n) (integerShift (m * n) f) =
      integerShift m
        (thetaIntegerCovariantSourceInverse n (integerShift n f)) := by
  rw [thetaIntegerCovariantSourceInverse_integerShift (Nat.mul_pos hm hn) f hf,
    thetaIntegerCovariantSourceInverse_integerShift hn f hf]
  exact HedenmalmPrimeTranslation.integerShift_mul
    (sourceInverse thetaSource f) hm hn

/-- The common-forcing residual specialized to one multiplicity-exact Xi divisor copy. -/
def thetaXiPrimeTranslatedSourceResidual (q : XiZeroCopy) (n : ℕ) (x : ℝ) : ℂ :=
  thetaPrimeTranslatedSourceResidual (xiSpectralPoint q) n x

/-- Every Xi divisor copy has the same universal integer-translation forcing vector. -/
theorem thetaXiPrimeTranslatedSourceResidual_eq_integerAnomaly
    (q : XiZeroCopy) (n : ℕ) (x : ℝ) :
    thetaXiPrimeTranslatedSourceResidual q n x = integerAnomaly thetaSource n x := by
  exact thetaPrimeTranslatedSourceResidual_eq_integerAnomaly
    (thetaXiSpectralPoint_mem_sourceStrip q)
    (xiC_thetaSource_xiSpectralPoint_eq_zero q) n x

/-- Every translated Xi divisor mode is now a genuine homogeneous eigenmode of the same
prime-dependent covariant source inverse. -/
theorem thetaIntegerCovariantSourceInverse_thetaXi_eigen
    (q : XiZeroCopy) {n : ℕ} (hn : 0 < n) :
    thetaIntegerCovariantSourceInverse n
        (integerShift n (sourceModeF thetaSource (xiSpectralPoint q))) =
      fun x => thetaXiReciprocalEigenvalue q *
        integerShift n (sourceModeF thetaSource (xiSpectralPoint q)) x := by
  rw [thetaIntegerCovariantSourceInverse_integerShift hn
    (sourceModeF thetaSource (xiSpectralPoint q))
    (integrable_sourceModeF_thetaSource
      (thetaXiSpectralPoint_mem_sourceStrip q)
      (xiC_thetaSource_xiSpectralPoint_eq_zero q))]
  funext x
  rw [integerShift,
    sourceInverse_sourceModeF_eq_smul_thetaSource
      (thetaXiSpectralPoint_mem_sourceStrip q)
      (xiC_thetaSource_xiSpectralPoint_eq_zero q)]
  unfold thetaXiReciprocalEigenvalue integerShift
  ring

/-- The original and retained reflected copies are homogeneous eigenmodes of one literal
covariant operator, with no change of prime label or coefficient frame. -/
theorem thetaIntegerCovariantSourceInverse_thetaXi_both_eigen
    (q : XiZeroCopy) {n : ℕ} (hn : 0 < n) :
    (thetaIntegerCovariantSourceInverse n
        (integerShift n (sourceModeF thetaSource (xiSpectralPoint q))) =
      fun x => thetaXiReciprocalEigenvalue q *
        integerShift n (sourceModeF thetaSource (xiSpectralPoint q)) x) ∧
    (thetaIntegerCovariantSourceInverse n
        (integerShift n (sourceModeF thetaSource
          (xiSpectralPoint (xiZeroCopyLineConjEquiv q)))) =
      fun x => thetaXiReciprocalEigenvalue (xiZeroCopyLineConjEquiv q) *
        integerShift n (sourceModeF thetaSource
          (xiSpectralPoint (xiZeroCopyLineConjEquiv q))) x) :=
  ⟨thetaIntegerCovariantSourceInverse_thetaXi_eigen q hn,
    thetaIntegerCovariantSourceInverse_thetaXi_eigen
      (xiZeroCopyLineConjEquiv q) hn⟩

/-- The two retained cofinal orientations have literally equal residuals on the same source
carrier; reflection does not alter the forcing coefficient or the integer label. -/
theorem thetaXiPrimeTranslatedSourceResidual_lineConj
    (q : XiZeroCopy) (n : ℕ) :
    thetaXiPrimeTranslatedSourceResidual (xiZeroCopyLineConjEquiv q) n =
      thetaXiPrimeTranslatedSourceResidual q n := by
  funext x
  rw [thetaXiPrimeTranslatedSourceResidual_eq_integerAnomaly,
    thetaXiPrimeTranslatedSourceResidual_eq_integerAnomaly]

/-- Subtracting the two common-forcing equations removes the universal anomaly and leaves the
exact coefficient-faithful balance between the two source transports. -/
theorem thetaXiPrimeTranslatedSource_common_forcing_balance
    (q : XiZeroCopy) (n : ℕ) (x : ℝ) :
    sourceInverse thetaSource
          (integerShift n (sourceModeF thetaSource (xiSpectralPoint q))) x
        - sourceInverse thetaSource
          (integerShift n
            (sourceModeF thetaSource (xiSpectralPoint (xiZeroCopyLineConjEquiv q)))) x =
      thetaXiReciprocalEigenvalue q
          * integerShift n (sourceModeF thetaSource (xiSpectralPoint q)) x
        - thetaXiReciprocalEigenvalue (xiZeroCopyLineConjEquiv q)
          * integerShift n
            (sourceModeF thetaSource (xiSpectralPoint (xiZeroCopyLineConjEquiv q))) x := by
  have hq := thetaXiPrimeTranslatedSourceResidual_eq_integerAnomaly q n x
  have hr := thetaXiPrimeTranslatedSourceResidual_eq_integerAnomaly
    (xiZeroCopyLineConjEquiv q) n x
  unfold thetaXiPrimeTranslatedSourceResidual thetaPrimeTranslatedSourceResidual at hq hr
  unfold thetaXiReciprocalEigenvalue
  linear_combination hq - hr

/-- At a genuine prime label the universal forcing residual is not the zero function. -/
theorem thetaXiPrimeTranslatedSourceResidual_prime_ne_zero
    (q : XiZeroCopy) (p : Nat.Primes) :
    thetaXiPrimeTranslatedSourceResidual q (p : ℕ) ≠ 0 := by
  intro hzero
  have hanomaly : ∀ x, integerAnomaly thetaSource (p : ℕ) x = 0 := by
    intro x
    rw [← thetaXiPrimeTranslatedSourceResidual_eq_integerAnomaly q]
    exact congrFun hzero x
  have hp_one := (integerAnomaly_eq_zero_iff thetaSource p.prop.pos).mp hanomaly
  exact p.prop.ne_one hp_one

/-- **Response-identification closure bridge.**  For every positive integer translation, equality
of the two reflected source responses is equivalent to horizontal vanishing of the Xi spectral
point.  The forward implication uses common forcing and canonical source mass, not injectivity of
an abstract target transport. -/
theorem thetaXiPrimeTranslatedSourceMode_eq_lineConj_iff
    (q : XiZeroCopy) {n : ℕ} (hn : 0 < n) :
    integerShift n (sourceModeF thetaSource (xiSpectralPoint q)) =
        integerShift n
          (sourceModeF thetaSource (xiSpectralPoint (xiZeroCopyLineConjEquiv q))) ↔
      (xiSpectralPoint q).im = 0 := by
  let g : ℝ → ℂ := integerShift n (sourceModeF thetaSource (xiSpectralPoint q))
  have hmass_ne : (thetaSource.mass : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr thetaSource.mass_ne_zero
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hc_ne :
      ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hnR _).ne'
  have hg_ne : g ≠ 0 := by
    intro hg
    have hfun : sourceFunctional g =
        (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (thetaSource.mass : ℂ) := by
      dsimp only [g]
      rw [sourceFunctional_integerShift, sourceFunctional,
        integral_sourceModeF_thetaSource_eq_mass
          (thetaXiSpectralPoint_mem_sourceStrip q)
          (xiC_thetaSource_xiSpectralPoint_eq_zero q)]
    have hzero : sourceFunctional g = 0 := by
      rw [hg]
      simp [sourceFunctional]
    exact (mul_ne_zero hc_ne hmass_ne) (hfun ▸ hzero)
  constructor
  · intro hresponse
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hg_ne
    have hbalance := thetaXiPrimeTranslatedSource_common_forcing_balance q n x
    change g = _ at hresponse
    rw [← hresponse] at hbalance
    have hmul :
        (thetaXiReciprocalEigenvalue q
            - thetaXiReciprocalEigenvalue (xiZeroCopyLineConjEquiv q)) * g x = 0 := by
      linear_combination -hbalance
    have hlambda : thetaXiReciprocalEigenvalue q =
        thetaXiReciprocalEigenvalue (xiZeroCopyLineConjEquiv q) := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hx)
    unfold thetaXiReciprocalEigenvalue at hlambda
    have hinv : (xiSpectralPoint q)⁻¹ =
        (xiSpectralPoint (xiZeroCopyLineConjEquiv q))⁻¹ := neg_inj.mp hlambda
    have hz : xiSpectralPoint q =
        xiSpectralPoint (xiZeroCopyLineConjEquiv q) := inv_inj.mp hinv
    rw [xiSpectralPoint_lineConj] at hz
    have him := congrArg Complex.im hz
    rw [Complex.conj_im] at him
    linarith
  · intro him
    have hconj : (starRingEnd ℂ) (xiSpectralPoint q) = xiSpectralPoint q := by
      apply Complex.ext
      · simp
      · simp [him]
    have hz : xiSpectralPoint (xiZeroCopyLineConjEquiv q) = xiSpectralPoint q := by
      rw [xiSpectralPoint_lineConj, hconj]
    rw [hz]

/-- A source theorem identifying the two positive-integer translated responses for every retained
Xi divisor copy closes the existing unconditional RH endpoint immediately. -/
theorem riemannHypothesis_of_thetaXiPrimeTranslatedSourceMode_eq_lineConj
    {n : ℕ} (hn : 0 < n)
    (hresponse : ∀ q : XiZeroCopy,
      integerShift n (sourceModeF thetaSource (xiSpectralPoint q)) =
        integerShift n
          (sourceModeF thetaSource (xiSpectralPoint (xiZeroCopyLineConjEquiv q)))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  refine ⟨(xiSpectralPoint q).re, Complex.ext ?_ ?_⟩
  · simp
  · have him := (thetaXiPrimeTranslatedSourceMode_eq_lineConj_iff q hn).mp (hresponse q)
    simp [him]

/-- The common forcing is invisible to every retained Xi conormal character.  This is the exact
quotient obstruction: a nonzero physical source vector lies in all Xi divisor-evaluation kernels. -/
theorem integral_thetaXiPrimeTranslatedSourceResidual_mul_sourceChar_eq_zero
    (q r : XiZeroCopy) {n : ℕ} (hn : 1 ≤ n) :
    (∫ x : ℝ, thetaXiPrimeTranslatedSourceResidual q n x
      * sourceChar (xiSpectralPoint r) x) = 0 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun x => by
    rw [thetaXiPrimeTranslatedSourceResidual_eq_integerAnomaly])]
  rw [integral_integerAnomaly_sourceChar hn
    (thetaXiSpectralPoint_mem_sourceStrip r) (xiSpectralPoint_ne_zero r),
    XiC_xiSpectralPoint_eq_zero, mul_zero]

end HedenmalmThetaSource

end

end RHTower
