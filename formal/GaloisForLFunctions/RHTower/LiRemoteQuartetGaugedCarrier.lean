import GaloisForLFunctions.RHTower.LiReflectedGammaCarrier
import GaloisForLFunctions.RHTower.LiRemoteQuartetPolarExact
import GaloisForLFunctions.RHTower.LiReflectedGammaCarrierCoefficient
import GaloisForLFunctions.RHTower.HypertranscendentalQuartetWardIndex
import GaloisForLFunctions.HTGeometry.MovingCanonicalSurgeryFieldInvariance
import GaloisForLFunctions.HTGeometry.DAGaugeDivisorBlindness
import GaloisForLFunctions.HTGeometry.QuartetPolynomial
import GaloisForLFunctions.HTGeometry.DifferentialIndependentFieldUniversality

/-!
# Remote-quartet gauge of the reflected-Gamma Li carrier

This module realizes the card's normalized quartet surgery as an actual entire function.  It proves
its exact divisor, functional-equation and Schwarz symmetries, exact order one,
hypertranscendence, divisor-normalized coefficient addition, and literal equality of the complete
all-translate/all-derivative differential fields before and after surgery.
-/

open Complex Set Polynomial
open scoped Differential

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

def liRemoteQuartetNormalization (a T : ℝ) : ℝ := (a ^ 2 + T ^ 2) ^ 2

def liRemoteQuartetGauge (a T : ℝ) (s : ℂ) : ℂ :=
  centeredQuartetGauge a T s / (liRemoteQuartetNormalization a T : ℂ)

def liRemoteQuartetGaugePolynomial (a T : ℝ) : Polynomial ℂ :=
  Polynomial.C ((liRemoteQuartetNormalization a T : ℂ)⁻¹) *
    centeredQuartetPolynomial a T

theorem liRemoteQuartetGaugePolynomial_eval (a T : ℝ) (s : ℂ) :
    (liRemoteQuartetGaugePolynomial a T).eval s = liRemoteQuartetGauge a T s := by
  rw [liRemoteQuartetGaugePolynomial, eval_mul, eval_C,
    centeredQuartetPolynomial_eval, liRemoteQuartetGauge]
  ring

theorem liRemoteQuartetNormalization_pos {a T : ℝ} (hT : T ≠ 0) :
    0 < liRemoteQuartetNormalization a T := by
  unfold liRemoteQuartetNormalization
  positivity

theorem liRemoteQuartetGaugePolynomial_ne_zero {a T : ℝ} (hT : 0 < T) :
    liRemoteQuartetGaugePolynomial a T ≠ 0 := by
  apply mul_ne_zero
  · apply Polynomial.C_ne_zero.mpr
    exact inv_ne_zero (ofReal_ne_zero.mpr
      (ne_of_gt (liRemoteQuartetNormalization_pos hT.ne')))
  · exact centeredQuartetPolynomial_ne_zero hT

theorem liRemoteQuartetGauge_eq_card (a T : ℝ) (s : ℂ) :
    liRemoteQuartetGauge a T s =
      ((((s - (1 / 2 : ℂ)) ^ 2 - ((a : ℂ) + I * (T : ℂ)) ^ 2) *
        ((s - (1 / 2 : ℂ)) ^ 2 - ((a : ℂ) - I * (T : ℂ)) ^ 2)) /
          (liRemoteQuartetNormalization a T : ℂ)) := by
  unfold liRemoteQuartetGauge centeredQuartetGauge
  ring_nf
  have hI2 : I ^ 2 = (-1 : ℂ) := by rw [pow_two, I_mul_I]
  have hI4 : I ^ 4 = (1 : ℂ) := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hI2]
    norm_num
  rw [hI2, hI4]
  ring

theorem liRemoteQuartetGauge_linearFactors (a T : ℝ) (s : ℂ) :
    liRemoteQuartetGauge a T s =
      (((s - (1 / 2 : ℂ) - (a : ℂ) - I * (T : ℂ)) *
          (s - (1 / 2 : ℂ) - (a : ℂ) + I * (T : ℂ)) *
        ((s - (1 / 2 : ℂ) + (a : ℂ) - I * (T : ℂ)) *
          (s - (1 / 2 : ℂ) + (a : ℂ) + I * (T : ℂ)))) /
        (liRemoteQuartetNormalization a T : ℂ)) := by
  rw [liRemoteQuartetGauge_eq_card]
  ring

theorem liRemoteQuartetGauge_eq_zero_iff {a T : ℝ} (hT : T ≠ 0) (s : ℂ) :
    liRemoteQuartetGauge a T s = 0 ↔
      s = (1 / 2 : ℂ) + (a : ℂ) + I * (T : ℂ) ∨
      s = (1 / 2 : ℂ) + (a : ℂ) - I * (T : ℂ) ∨
      s = (1 / 2 : ℂ) - (a : ℂ) + I * (T : ℂ) ∨
      s = (1 / 2 : ℂ) - (a : ℂ) - I * (T : ℂ) := by
  rw [liRemoteQuartetGauge_linearFactors]
  have hD : (liRemoteQuartetNormalization a T : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (ne_of_gt (liRemoteQuartetNormalization_pos hT))
  simp only [div_eq_zero_iff, hD, or_false, mul_eq_zero]
  constructor
  · intro hz
    exact hz.elim
      (fun h12 => h12.elim
        (fun h => Or.inl (by linear_combination h))
        (fun h => Or.inr (Or.inl (by linear_combination h))))
      (fun h34 => h34.elim
        (fun h => Or.inr (Or.inr (Or.inl (by linear_combination h))))
        (fun h => Or.inr (Or.inr (Or.inr (by linear_combination h)))))
  · intro hs
    exact hs.elim
      (fun h => Or.inl (Or.inl (by linear_combination h)))
      (fun hs' => hs'.elim
        (fun h => Or.inl (Or.inr (by linear_combination h)))
        (fun hs'' => hs''.elim
          (fun h => Or.inr (Or.inl (by linear_combination h)))
          (fun h => Or.inr (Or.inr (by linear_combination h)))))

theorem liRemoteQuartetGauge_half {a T : ℝ} (hT : T ≠ 0) :
    liRemoteQuartetGauge a T (1 / 2 : ℂ) = 1 := by
  have hD : (liRemoteQuartetNormalization a T : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (ne_of_gt (liRemoteQuartetNormalization_pos hT))
  have hcenter : centeredQuartetGauge a T (1 / 2 : ℂ) =
      (liRemoteQuartetNormalization a T : ℂ) := by
    unfold centeredQuartetGauge liRemoteQuartetNormalization
    push_cast
    ring
  rw [liRemoteQuartetGauge, hcenter, div_self hD]

theorem liRemoteQuartetGauge_one_sub (a T : ℝ) (s : ℂ) :
    liRemoteQuartetGauge a T (1 - s) = liRemoteQuartetGauge a T s := by
  unfold liRemoteQuartetGauge
  rw [centeredQuartetGauge_one_sub]

theorem liRemoteQuartetGauge_conj (a T : ℝ) (s : ℂ) :
    liRemoteQuartetGauge a T ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (liRemoteQuartetGauge a T s) := by
  unfold liRemoteQuartetGauge
  rw [centeredQuartetGauge_conj, map_div₀, Complex.conj_ofReal]

def liRemoteQuartetGaugedCarrier (alpha a T : ℝ) (s : ℂ) : ℂ :=
  liRemoteQuartetGauge a T s * liReflectedGammaCarrier alpha s

theorem liRemoteQuartetGaugedCarrier_analyticOnNhd (alpha a T : ℝ) :
    AnalyticOnNhd ℂ (liRemoteQuartetGaugedCarrier alpha a T) Set.univ := by
  have hg : AnalyticOnNhd ℂ (liRemoteQuartetGauge a T) Set.univ := by
    have hfun : liRemoteQuartetGauge a T =
        fun s => (liRemoteQuartetGaugePolynomial a T).eval s := by
      funext s
      exact (liRemoteQuartetGaugePolynomial_eval a T s).symm
    rw [hfun]
    exact (liRemoteQuartetGaugePolynomial a T).differentiable.differentiableOn.analyticOnNhd
      isOpen_univ
  exact hg.mul (liReflectedGammaCarrier_analyticOnNhd alpha)

theorem liRemoteQuartetGaugedCarrier_one_sub (alpha a T : ℝ) (s : ℂ) :
    liRemoteQuartetGaugedCarrier alpha a T (1 - s) =
      liRemoteQuartetGaugedCarrier alpha a T s := by
  rw [liRemoteQuartetGaugedCarrier, liRemoteQuartetGaugedCarrier,
    liRemoteQuartetGauge_one_sub, liReflectedGammaCarrier_one_sub]

theorem liRemoteQuartetGaugedCarrier_conj (alpha a T : ℝ) (s : ℂ) :
    liRemoteQuartetGaugedCarrier alpha a T ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (liRemoteQuartetGaugedCarrier alpha a T s) := by
  rw [liRemoteQuartetGaugedCarrier, liRemoteQuartetGaugedCarrier,
    liRemoteQuartetGauge_conj, liReflectedGammaCarrier_conj, map_mul]

theorem liRemoteQuartetGaugedCarrier_hypertranscendental
    {alpha a T : ℝ} (hT : 0 < T)
    (hsep : ∀ k : ℤ, (2 * alpha : ℂ) ≠ (k : ℂ)) :
    Hypertranscendental (liRemoteQuartetGaugedCarrier alpha a T) := by
  have hfun : liRemoteQuartetGaugedCarrier alpha a T =
      fun s => (liRemoteQuartetGaugePolynomial a T).eval s *
        liReflectedGammaCarrier alpha s := by
    funext s
    rw [liRemoteQuartetGaugedCarrier, liRemoteQuartetGaugePolynomial_eval]
  rw [hfun]
  exact hypertranscendental_mul_polynomial
    (liReflectedGammaCarrier_analyticOnNhd alpha).contDiff
    (liRemoteQuartetGaugePolynomial_ne_zero hT)
    (liReflectedGammaCarrier_hypertranscendental hsep)

/-- Card parameter form of hypertranscendence.  Nonintegrality of `2 alpha - 1` is equivalent to
nonintegrality of `2 alpha`, because the two differ by the integer one. -/
theorem liRemoteQuartetGaugedCarrier_hypertranscendental_of_two_mul_sub_one
    {alpha a T : ℝ} (hT : 0 < T)
    (hsep : ∀ k : ℤ, (2 * alpha - 1 : ℂ) ≠ (k : ℂ)) :
    Hypertranscendental (liRemoteQuartetGaugedCarrier alpha a T) := by
  apply liRemoteQuartetGaugedCarrier_hypertranscendental hT
  intro k hk
  apply hsep (k - 1)
  push_cast
  linear_combination hk

theorem liRemoteQuartetGaugedCarrier_orderOneEnvelope (alpha a T : ℝ) :
    OrderOneEnvelope (liRemoteQuartetGaugedCarrier alpha a T) := by
  have h := (orderOneEnvelope_polyEval (liRemoteQuartetGaugePolynomial a T)).mul
    (liReflectedGammaCarrier_orderOneEnvelope alpha)
  exact h.congr fun s => by
    rw [liRemoteQuartetGaugedCarrier, liRemoteQuartetGaugePolynomial_eval]

theorem liRemoteQuartetGaugedCarrier_ne_zero_half
    {alpha a T : ℝ} (halpha : 0 < alpha) (hT : T ≠ 0) :
    liRemoteQuartetGaugedCarrier alpha a T (1 / 2 : ℂ) ≠ 0 := by
  rw [liRemoteQuartetGaugedCarrier, liRemoteQuartetGauge_half hT]
  simpa using liReflectedGammaCarrier_ne_zero_half halpha

theorem liRemoteQuartetGaugedCarrier_zero_arithmeticProgression
    (alpha a T : ℝ) (n : ℕ) :
    liRemoteQuartetGaugedCarrier alpha a T
      ((1 / 2 : ℂ) + I * (alpha : ℂ) + n • I) = 0 := by
  rw [liRemoteQuartetGaugedCarrier,
    liReflectedGammaCarrier_zero_arithmeticProgression, mul_zero]

/-- Exact divisor of the gauged carrier: the inserted off-line quartet plus the complete
reflected-Gamma critical-line arithmetic progression. -/
theorem liRemoteQuartetGaugedCarrier_eq_zero_iff
    {alpha a T : ℝ} (hT : T ≠ 0) {s : ℂ} :
    liRemoteQuartetGaugedCarrier alpha a T s = 0 ↔
      (s = (1 / 2 : ℂ) + (a : ℂ) + I * (T : ℂ) ∨
        s = (1 / 2 : ℂ) + (a : ℂ) - I * (T : ℂ) ∨
        s = (1 / 2 : ℂ) - (a : ℂ) + I * (T : ℂ) ∨
        s = (1 / 2 : ℂ) - (a : ℂ) - I * (T : ℂ)) ∨
      (∃ n : ℕ, s = (1 / 2 : ℂ) + I * ((n : ℂ) + (alpha : ℂ))) ∨
        ∃ n : ℕ, s = (1 / 2 : ℂ) - I * ((n : ℂ) + (alpha : ℂ)) := by
  rw [liRemoteQuartetGaugedCarrier, mul_eq_zero,
    liRemoteQuartetGauge_eq_zero_iff hT,
    liReflectedGammaCarrier_eq_zero_iff]

/-- The upper-left remote quartet member from the card is an actual zero of the completed
gauged carrier. -/
theorem liRemoteQuartetGaugedCarrier_remoteQuartetZero
    (alpha a : ℝ) {T : ℝ} (hT : T ≠ 0) :
    liRemoteQuartetGaugedCarrier alpha a T (liRemoteQuartetZero a T) = 0 := by
  rw [liRemoteQuartetGaugedCarrier_eq_zero_iff hT]
  left
  right
  right
  left
  unfold liRemoteQuartetZero
  push_cast
  ring

/-- Divisor-normalized Li coefficient of the completed gauged carrier.  Its two summands are the
critical-line arithmetic-progression divisor and the symmetry-complete inserted quartet. -/
def liRemoteQuartetGaugedCarrierCoefficient
    (alpha : ℝ) (n : ℕ) (a T : ℝ) : ℝ :=
  liReflectedGammaCarrierCoefficient alpha n +
    liRemoteQuartetProfile n
      (liRemoteRadialCoordinate a T) (liRemoteAngularCoordinate a T)

/-- Card equation `(17)`: adjoining the quartet adds exactly its symmetry-complete Li profile to
the reflected-Gamma carrier coefficient. -/
theorem liRemoteQuartetGaugedCarrierCoefficient_eq
    (alpha : ℝ) (n : ℕ) (a T : ℝ) :
    liRemoteQuartetGaugedCarrierCoefficient alpha n a T =
      liReflectedGammaCarrierCoefficient alpha n +
        liRemoteQuartetProfile n
          (liRemoteRadialCoordinate a T) (liRemoteAngularCoordinate a T) := rfl

/-- Complex divisor-sum form of equation `(17)`, with the quartet written as the literal polar
Möbius orbit. -/
theorem liRemoteQuartetGaugedCarrierCoefficient_eq_polarContribution
    (alpha : ℝ) (n : ℕ) {a T : ℝ}
    (ha : 0 < a) (ha' : a < 1 / 2) (hT : 1 / 2 < T) :
    (liRemoteQuartetGaugedCarrierCoefficient alpha n a T : ℂ) =
      (liReflectedGammaCarrierCoefficient alpha n : ℂ) +
        liPolarQuartetContribution n
          (liMobiusCoordinate (liRemoteQuartetZero a T)) := by
  rw [liRemoteQuartetGaugedCarrierCoefficient,
    liMobiusCoordinate_remoteQuartetZero_eq_polar ha ha' hT,
    liPolarQuartetContribution_eq_profile]
  norm_cast

theorem liRemoteQuartetGaugedCarrier_hasExactEntireOrderOne
    {alpha a T : ℝ} (halpha : 0 < alpha) (hT : T ≠ 0) :
    HasExactEntireOrderOne (liRemoteQuartetGaugedCarrier alpha a T) := by
  refine ⟨Complex.analyticOnNhd_univ_iff_differentiable.mp
      (liRemoteQuartetGaugedCarrier_analyticOnNhd alpha a T),
    liRemoteQuartetGaugedCarrier_orderOneEnvelope alpha a T, ?_⟩
  intro hmin
  exact hmin.no_arithmeticProgression_zeros
    (liRemoteQuartetGaugedCarrier_ne_zero_half halpha hT) I_ne_zero
    (liRemoteQuartetGaugedCarrier_zero_arithmeticProgression alpha a T)

def liRemoteQuartetGaugeRatFunc (a T : ℝ) : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ) (liRemoteQuartetGaugePolynomial a T)

theorem liRemoteQuartetGaugeRatFunc_ne_zero {a T : ℝ} (hT : 0 < T) :
    liRemoteQuartetGaugeRatFunc a T ≠ 0 := by
  unfold liRemoteQuartetGaugeRatFunc
  simpa only [map_zero] using
    (RatFunc.algebraMap_injective ℂ).ne
      (liRemoteQuartetGaugePolynomial_ne_zero (a := a) hT)

open scoped UpperEndDifferentialInstances

def liReflectedGammaCarrierUpperEndMero (alpha : ℝ) : upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact analyticUpperEndMero (liReflectedGammaCarrier alpha) 0
    ((liReflectedGammaCarrier_analyticOnNhd alpha).mono (Set.subset_univ _))

def liReflectedGammaCarrierTranslateFamily (alpha : ℝ) (h : ℂ) : upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact upperEndTranslationMeroEquiv h (liReflectedGammaCarrierUpperEndMero alpha)

def liRemoteQuartetGaugedUpperEndMero
    (alpha a T : ℝ) : upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact upperEndRatfuncToMero (liRemoteQuartetGaugeRatFunc a T) *
    liReflectedGammaCarrierUpperEndMero alpha

def liRemoteQuartetGaugedAnalyticUpperEndMero
    (alpha a T : ℝ) : upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact analyticUpperEndMero (liRemoteQuartetGaugedCarrier alpha a T) 0
    ((liRemoteQuartetGaugedCarrier_analyticOnNhd alpha a T).mono (Set.subset_univ _))

theorem liRemoteQuartetGaugedUpperEndMero_eq_analytic
    (alpha a T : ℝ) :
    letI := isDomain_upperEndAnalyticSubring
    liRemoteQuartetGaugedUpperEndMero alpha a T =
      liRemoteQuartetGaugedAnalyticUpperEndMero alpha a T := by
  letI := isDomain_upperEndAnalyticSubring
  rw [liRemoteQuartetGaugedUpperEndMero,
    liRemoteQuartetGaugeRatFunc,
    upperEndRatfuncToMero_algebraMap_polynomial,
    liReflectedGammaCarrierUpperEndMero,
    liRemoteQuartetGaugedAnalyticUpperEndMero,
    upperEndPolyToMero, analyticUpperEndMero, analyticUpperEndMero]
  change algebraMap upperEndAnalyticSubring upperEndMeroField
      (upperEndPolyToAnalytic (liRemoteQuartetGaugePolynomial a T)) *
    algebraMap upperEndAnalyticSubring upperEndMeroField
      (analyticUpperEndElement (liReflectedGammaCarrier alpha) 0 _) =
    algebraMap upperEndAnalyticSubring upperEndMeroField
      (analyticUpperEndElement (liRemoteQuartetGaugedCarrier alpha a T) 0 _)
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  change
    (((fun z : ℂ => (liRemoteQuartetGaugePolynomial a T).eval z) : ℂ → ℂ) :
        Filter.Germ upperEndFilter ℂ) *
      ((liReflectedGammaCarrier alpha : ℂ → ℂ) :
        Filter.Germ upperEndFilter ℂ) =
      ((liRemoteQuartetGaugedCarrier alpha a T : ℂ → ℂ) :
        Filter.Germ upperEndFilter ℂ)
  rw [← Filter.Germ.coe_mul, Filter.Germ.coe_eq]
  exact Filter.Eventually.of_forall fun z => by
    change (liRemoteQuartetGaugePolynomial a T).eval z *
      liReflectedGammaCarrier alpha z = _
    rw [liRemoteQuartetGaugedCarrier, liRemoteQuartetGaugePolynomial_eval]

def liRemoteQuartetGaugedTranslateFamily
    (alpha a T : ℝ) (h : ℂ) : upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact upperEndRatfuncToMero
      (ratFuncTranslationEquiv h (liRemoteQuartetGaugeRatFunc a T)) *
    liReflectedGammaCarrierTranslateFamily alpha h

theorem liRemoteQuartetGaugedTranslateFamily_eq_translation
    (alpha a T : ℝ) (h : ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    liRemoteQuartetGaugedTranslateFamily alpha a T h =
      upperEndTranslationMeroEquiv h
        (liRemoteQuartetGaugedUpperEndMero alpha a T) := by
  letI := isDomain_upperEndAnalyticSubring
  rw [liRemoteQuartetGaugedTranslateFamily,
    liReflectedGammaCarrierTranslateFamily,
    liRemoteQuartetGaugedUpperEndMero,
    map_mul, upperEndTranslationMeroEquiv_ratfuncToMero]

theorem liRemoteQuartetGaugedTranslateFamily_differentialAdjoin_eq
    (alpha a : ℝ) {T : ℝ} (hT : 0 < T) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := ratFuncCoordinateDifferential
    letI := upperEndMeroFieldDifferential
    letI : DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncDifferentialAlgebra
    differentialAdjoin (RatFunc ℂ)
        (Set.range (liRemoteQuartetGaugedTranslateFamily alpha a T)) =
      differentialAdjoin (RatFunc ℂ)
        (Set.range (liReflectedGammaCarrierTranslateFamily alpha)) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
  letI := upperEndMeroFieldDifferential
  letI : DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncDifferentialAlgebra
  apply differentialAdjoin_gauge_eq
    (liReflectedGammaCarrierTranslateFamily alpha)
    (fun h => ratFuncTranslationEquiv h (liRemoteQuartetGaugeRatFunc a T))
  intro h
  simpa only [map_zero] using (ratFuncTranslationEquiv h).injective.ne
    (liRemoteQuartetGaugeRatFunc_ne_zero (a := a) hT)

/-- Literal all-translate, all-derivative form of the unchanged-field law. -/
theorem liRemoteQuartetGaugedTranslateFamily_allJets_adjoin_eq
    (alpha a : ℝ) {T : ℝ} (hT : 0 < T) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := ratFuncCoordinateDifferential
    letI := upperEndMeroFieldDifferential
    letI : DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncDifferentialAlgebra
    IntermediateField.adjoin (RatFunc ℂ)
        (Set.range fun p : ℂ × ℕ => differentialJet p.2
          (liRemoteQuartetGaugedTranslateFamily alpha a T p.1)) =
      IntermediateField.adjoin (RatFunc ℂ)
        (Set.range fun p : ℂ × ℕ => differentialJet p.2
          (liReflectedGammaCarrierTranslateFamily alpha p.1)) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
  letI := upperEndMeroFieldDifferential
  letI : DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncDifferentialAlgebra
  rw [← differentialAdjoin_range_eq_adjoin_jetRange
      (RatFunc ℂ) (liRemoteQuartetGaugedTranslateFamily alpha a T),
    ← differentialAdjoin_range_eq_adjoin_jetRange
      (RatFunc ℂ) (liReflectedGammaCarrierTranslateFamily alpha)]
  exact liRemoteQuartetGaugedTranslateFamily_differentialAdjoin_eq alpha a hT

end
end RHTower
