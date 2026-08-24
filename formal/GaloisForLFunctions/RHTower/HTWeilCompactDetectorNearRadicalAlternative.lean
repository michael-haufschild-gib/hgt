import GaloisForLFunctions.HTGeometry.SchwartzArithmeticProgressionWeilForm
import GaloisForLFunctions.RHTower.LiRemoteQuartetGaugedCarrier
import GaloisForLFunctions.RHTower.L2FourierConjugation

/-!
# HT Weil compact-detector near-radical alternative

This file closes the concrete reflected-Gamma instantiation of the compact-detector engine. It
defines the literal four-zero Weil divisor sum, identifies it with the real quartet defect,
constructs the continuous nonnegative all-line form, proves compact-uniform invisibility and
eventual strict positivity, and derives the exact compact-escape/near-radical alternative for
detector sequences. The final theorem is a closed universal proposition.
-/

open Complex MeasureTheory Filter Set
open scoped ENNReal FourierTransform Topology

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Pointwise reality of a complex Schwartz representative. -/
def IsRealLogApertureTest {A : ℝ} (f : LogApertureSchwartz A) : Prop :=
  ∀ x : ℝ, (starRingEnd ℂ) (f.1 x) = f.1 x

/-- Shifted Mellin value attached to `1/2 + delta + iT`. -/
def logApertureShiftedMellinValue (A delta T : ℝ)
    (f : LogApertureSchwartz A) : ℂ :=
  logMellinHeightEvaluation
    (logMellinBoundedTilt A delta (logApertureSchwartzToL1 f)) T

theorem logApertureShiftedMellinValue_eq_integral
    (A delta T : ℝ) (f : LogApertureSchwartz A) :
    logApertureShiftedMellinValue A delta T f =
      ∫ x : ℝ, (Real.exp (delta * x) : ℂ) * f.1 x *
        Complex.exp (((T * x : ℝ) : ℂ) * Complex.I) :=
  logMellinHeightEvaluation_boundedTilt_eq_integral A delta T f

theorem conj_logApertureShiftedMellinValue
    {A : ℝ} {f : LogApertureSchwartz A} (hf : IsRealLogApertureTest f)
    (delta T : ℝ) :
    (starRingEnd ℂ) (logApertureShiftedMellinValue A delta T f) =
      logApertureShiftedMellinValue A delta (-T) f := by
  rw [logApertureShiftedMellinValue_eq_integral,
    logApertureShiftedMellinValue_eq_integral, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.conj_I, Complex.conj_ofReal, hf x]
  congr 2
  push_cast
  ring

/-- Literal four-zero sum `sum_{rho in Q} G(rho)G(1-rho)` for the inserted quartet. -/
def logApertureQuartetDivisorSum (A delta T : ℝ)
    (f : LogApertureSchwartz A) : ℂ :=
  logApertureShiftedMellinValue A delta T f *
      logApertureShiftedMellinValue A (-delta) (-T) f +
    logApertureShiftedMellinValue A (-delta) (-T) f *
      logApertureShiftedMellinValue A delta T f +
    logApertureShiftedMellinValue A delta (-T) f *
      logApertureShiftedMellinValue A (-delta) T f +
    logApertureShiftedMellinValue A (-delta) T f *
      logApertureShiftedMellinValue A delta (-T) f

theorem logApertureQuartetDivisorSum_eq_defect
    {A delta T : ℝ} {f : LogApertureSchwartz A}
    (hf : IsRealLogApertureTest f) :
    logApertureQuartetDivisorSum A delta T f =
      (logApertureSchwartzQuartetDefect A delta T f : ℂ) := by
  have hplus := conj_logApertureShiftedMellinValue hf delta T
  have hminus := conj_logApertureShiftedMellinValue hf (-delta) (-T)
  let a := logApertureShiftedMellinValue A delta T f
  let b := logApertureShiftedMellinValue A (-delta) (-T) f
  have hc : logApertureShiftedMellinValue A delta (-T) f = (starRingEnd ℂ) a :=
    hplus.symm
  have hd : logApertureShiftedMellinValue A (-delta) T f = (starRingEnd ℂ) b :=
    by simpa only [neg_neg] using hminus.symm
  rw [logApertureQuartetDivisorSum, hc, hd]
  change a * b + b * a + (starRingEnd ℂ) a * (starRingEnd ℂ) b +
      (starRingEnd ℂ) b * (starRingEnd ℂ) a =
    ((logApertureSchwartzQuartetDefect A delta T f : ℝ) : ℂ)
  rw [logApertureSchwartzQuartetDefect]
  change a * b + b * a + (starRingEnd ℂ) a * (starRingEnd ℂ) b +
      (starRingEnd ℂ) b * (starRingEnd ℂ) a = ((4 * (a * b).re : ℝ) : ℂ)
  rw [mul_comm b a, mul_comm ((starRingEnd ℂ) b) ((starRingEnd ℂ) a),
    ← map_mul]
  apply Complex.ext <;> simp <;> ring

/-- Divisor-enumerated Weil form of the gauged reflected-Gamma carrier. -/
def liRemoteQuartetGaugedCarrierWeilForm
    (alpha : ℝ) (halpha : 0 < alpha) (A delta T : ℝ)
    (f : LogApertureSchwartz A) : ℂ :=
  (logApertureReflectedGammaWeilForm alpha halpha f : ℂ) +
    logApertureQuartetDivisorSum A delta T f

theorem liRemoteQuartetGaugedCarrierWeilForm_sub_base
    {alpha : ℝ} (halpha : 0 < alpha) {A delta T : ℝ}
    {f : LogApertureSchwartz A} (hf : IsRealLogApertureTest f) :
    liRemoteQuartetGaugedCarrierWeilForm alpha halpha A delta T f -
        (logApertureReflectedGammaWeilForm alpha halpha f : ℂ) =
      (logApertureSchwartzQuartetDefect A delta T f : ℂ) := by
  rw [liRemoteQuartetGaugedCarrierWeilForm, add_sub_cancel_left,
    logApertureQuartetDivisorSum_eq_defect hf]

/-- Real form on real tests; its divisor sum is real by the quartet identity. -/
def liRemoteQuartetGaugedCarrierRealWeilForm
    (alpha : ℝ) (halpha : 0 < alpha) (A delta T : ℝ)
    (f : LogApertureSchwartz A) : ℝ :=
  logApertureReflectedGammaWeilForm alpha halpha f +
    logApertureSchwartzQuartetDefect A delta T f

theorem liRemoteQuartetGaugedCarrierWeilForm_eq_real
    {alpha : ℝ} (halpha : 0 < alpha) {A delta T : ℝ}
    {f : LogApertureSchwartz A} (hf : IsRealLogApertureTest f) :
    liRemoteQuartetGaugedCarrierWeilForm alpha halpha A delta T f =
      (liRemoteQuartetGaugedCarrierRealWeilForm alpha halpha A delta T f : ℂ) := by
  rw [liRemoteQuartetGaugedCarrierWeilForm,
    liRemoteQuartetGaugedCarrierRealWeilForm,
    logApertureQuartetDivisorSum_eq_defect hf]
  push_cast
  rfl

theorem compact_liRemoteQuartetGaugedCarrierWeilDifference_uniformVanishes
    {alpha : ℝ} (halpha : 0 < alpha) (A delta : ℝ)
    {K : Set (LogApertureSchwartz A)} (hK : IsCompact K)
    (hreal : ∀ f ∈ K, IsRealLogApertureTest f) :
    UniformlyVanishesAlong (cocompact ℝ) K
      (fun T f => liRemoteQuartetGaugedCarrierWeilForm alpha halpha A delta T f -
        (logApertureReflectedGammaWeilForm alpha halpha f : ℂ)) := by
  have hdefect := compact_logApertureSchwartz_heightQuartetDefect_uniformVanishes
    A delta hK
  intro eps heps
  filter_upwards [hdefect eps heps] with T hT
  intro f hf
  rw [liRemoteQuartetGaugedCarrierWeilForm_sub_base halpha (hreal f hf)]
  simpa using hT f hf

theorem compact_eventually_pos_liRemoteQuartetGaugedCarrierRealWeilForm
    {alpha : ℝ} (halpha : 0 < alpha) (A delta : ℝ)
    {K : Set (LogApertureSchwartz A)} (hK : IsCompact K) (hKne : K.Nonempty)
    (hstrict : ∀ f ∈ K, 0 < logApertureReflectedGammaWeilForm alpha halpha f) :
    ∀ᶠ T in cocompact ℝ, ∀ f ∈ K,
      0 < liRemoteQuartetGaugedCarrierRealWeilForm alpha halpha A delta T f := by
  exact eventually_strictPositive_of_compactMargin hK hKne
    (continuous_logApertureReflectedGammaWeilForm alpha halpha A).continuousOn
    hstrict
    (compact_logApertureSchwartz_heightQuartetDefect_uniformVanishes A delta hK)

theorem compact_eventually_pos_liRemoteQuartetGaugedCarrierWeilForm_re
    {alpha : ℝ} (halpha : 0 < alpha) (A delta : ℝ)
    {K : Set (LogApertureSchwartz A)} (hK : IsCompact K) (hKne : K.Nonempty)
    (hreal : ∀ f ∈ K, IsRealLogApertureTest f)
    (hstrict : ∀ f ∈ K, 0 < logApertureReflectedGammaWeilForm alpha halpha f) :
    ∀ᶠ T in cocompact ℝ, ∀ f ∈ K,
      0 < (liRemoteQuartetGaugedCarrierWeilForm alpha halpha A delta T f).re := by
  have hpos := compact_eventually_pos_liRemoteQuartetGaugedCarrierRealWeilForm
    halpha A delta hK hKne hstrict
  filter_upwards [hpos] with T hT
  intro f hf
  rw [liRemoteQuartetGaugedCarrierWeilForm_eq_real halpha (hreal f hf)]
  simpa using hT f hf

theorem compact_detectingSequence_tendsto_reflectedGammaRadical
    {alpha : ℝ} (halpha : 0 < alpha) (A delta : ℝ)
    {K : Set (LogApertureSchwartz A)} (hK : IsCompact K)
    {Z : Type*} [PseudoMetricSpace Z] {l : Filter Z}
    {height : Z → ℝ} (hheight : Tendsto height l (cocompact ℝ))
    {test : Z → LogApertureSchwartz A} (htest : ∀ᶠ z in l, test z ∈ K)
    (hdetect : ∀ᶠ z in l,
      liRemoteQuartetGaugedCarrierRealWeilForm alpha halpha A delta
        (height z) (test z) ≤ 0) :
    Tendsto (fun z => logApertureReflectedGammaWeilForm alpha halpha (test z))
      l (𝓝 0) := by
  exact tendsto_nearRadical_of_detecting
    (fun f _ => logApertureReflectedGammaWeilForm_nonneg alpha halpha f)
    (compact_logApertureSchwartz_heightQuartetDefect_uniformVanishes A delta hK)
    hheight htest hdetect

theorem detectingSequence_compactEscape_or_tendsto_reflectedGammaRadical
    {alpha : ℝ} (halpha : 0 < alpha) (A delta : ℝ)
    {Z : Type*} [PseudoMetricSpace Z] {l : Filter Z}
    {height : Z → ℝ} (hheight : Tendsto height l (cocompact ℝ))
    {test : Z → LogApertureSchwartz A}
    (hdetect : ∀ᶠ z in l,
      liRemoteQuartetGaugedCarrierRealWeilForm alpha halpha A delta
        (height z) (test z) ≤ 0) :
    (∀ K : Set (LogApertureSchwartz A), IsCompact K →
        ¬ ∀ᶠ z in l, test z ∈ K) ∨
      Tendsto (fun z => logApertureReflectedGammaWeilForm alpha halpha (test z))
        l (𝓝 0) := by
  exact compactEscape_or_tendsto_nearRadical
    (fun f => logApertureReflectedGammaWeilForm_nonneg alpha halpha f)
    (fun K hK =>
      compact_logApertureSchwartz_heightQuartetDefect_uniformVanishes A delta hK)
    hheight hdetect

theorem detectingSequence_gaugedCarrier_compactEscape_or_tendsto_radical
    {alpha : ℝ} (halpha : 0 < alpha) (A delta : ℝ)
    {Z : Type*} [PseudoMetricSpace Z] {l : Filter Z}
    {height : Z → ℝ} (hheight : Tendsto height l (cocompact ℝ))
    {test : Z → LogApertureSchwartz A}
    (hreal : ∀ᶠ z in l, IsRealLogApertureTest (test z))
    (hdetect : ∀ᶠ z in l,
      (liRemoteQuartetGaugedCarrierWeilForm alpha halpha A delta
        (height z) (test z)).re ≤ 0) :
    (∀ K : Set (LogApertureSchwartz A), IsCompact K →
        ¬ ∀ᶠ z in l, test z ∈ K) ∨
      Tendsto (fun z => logApertureReflectedGammaWeilForm alpha halpha (test z))
        l (𝓝 0) := by
  apply detectingSequence_compactEscape_or_tendsto_reflectedGammaRadical
    halpha A delta hheight
  filter_upwards [hreal, hdetect] with z hzreal hzdetect
  rw [liRemoteQuartetGaugedCarrierWeilForm_eq_real halpha hzreal] at hzdetect
  simpa using hzdetect

/-- Closed structural package linking the enumerated Weil form to the exact divisor of the
same order-one, symmetric, hypertranscendental carrier. -/
theorem liRemoteQuartetGaugedCarrier_structuralWeilPackage :
    ∀ (alpha A delta T : ℝ) (halpha : 0 < alpha) (_hT : 0 < T)
      (_hsep : ∀ k : ℤ, (2 * alpha - 1 : ℂ) ≠ (k : ℂ)),
      HasExactEntireOrderOne (liRemoteQuartetGaugedCarrier alpha delta T) ∧
      Hypertranscendental (liRemoteQuartetGaugedCarrier alpha delta T) ∧
      (∀ s : ℂ,
        liRemoteQuartetGaugedCarrier alpha delta T (1 - s) =
            liRemoteQuartetGaugedCarrier alpha delta T s ∧
        liRemoteQuartetGaugedCarrier alpha delta T ((starRingEnd ℂ) s) =
            (starRingEnd ℂ) (liRemoteQuartetGaugedCarrier alpha delta T s)) ∧
      (∀ s : ℂ, liRemoteQuartetGaugedCarrier alpha delta T s = 0 ↔
        (s = (1 / 2 : ℂ) + (delta : ℂ) + I * (T : ℂ) ∨
          s = (1 / 2 : ℂ) + (delta : ℂ) - I * (T : ℂ) ∨
          s = (1 / 2 : ℂ) - (delta : ℂ) + I * (T : ℂ) ∨
          s = (1 / 2 : ℂ) - (delta : ℂ) - I * (T : ℂ)) ∨
        (∃ n : ℕ, s = (1 / 2 : ℂ) + I * ((n : ℂ) + (alpha : ℂ))) ∨
          ∃ n : ℕ, s = (1 / 2 : ℂ) - I * ((n : ℂ) + (alpha : ℂ))) ∧
      (∀ f : LogApertureSchwartz A, IsRealLogApertureTest f →
        liRemoteQuartetGaugedCarrierWeilForm alpha halpha A delta T f =
          (liRemoteQuartetGaugedCarrierRealWeilForm alpha halpha A delta T f : ℂ)) := by
  intro alpha A delta T halpha hT hsep
  refine ⟨liRemoteQuartetGaugedCarrier_hasExactEntireOrderOne halpha hT.ne',
    liRemoteQuartetGaugedCarrier_hypertranscendental_of_two_mul_sub_one hT hsep,
    ?_, ?_, ?_⟩
  · intro s
    exact ⟨liRemoteQuartetGaugedCarrier_one_sub alpha delta T s,
      liRemoteQuartetGaugedCarrier_conj alpha delta T s⟩
  · intro s
    exact liRemoteQuartetGaugedCarrier_eq_zero_iff hT.ne'
  · intro f hf
    exact liRemoteQuartetGaugedCarrierWeilForm_eq_real halpha hf

/-- Closed card theorem: all paper hypotheses are universally quantified inside one proposition. -/
theorem htWeilCompactDetectorNearRadicalAlternative :
    ∀ (alpha A delta : ℝ) (halpha : 0 < alpha),
      Continuous (logApertureReflectedGammaWeilForm alpha halpha (A := A)) ∧
      (∀ f : LogApertureSchwartz A,
        0 ≤ logApertureReflectedGammaWeilForm alpha halpha f ∧
        logApertureReflectedGammaWeilForm alpha halpha f =
          2 * ∑' n : ℕ,
            ‖logMellinHeightEvaluation (logApertureSchwartzToL1 f) (alpha + n)‖ ^ 2) ∧
      (∀ (T : ℝ) (f : LogApertureSchwartz A), IsRealLogApertureTest f →
        liRemoteQuartetGaugedCarrierWeilForm alpha halpha A delta T f =
          (liRemoteQuartetGaugedCarrierRealWeilForm alpha halpha A delta T f : ℂ)) ∧
      (∀ K : Set (LogApertureSchwartz A), IsCompact K →
        (∀ f ∈ K, IsRealLogApertureTest f) →
        UniformlyVanishesAlong (cocompact ℝ) K
          (fun T f => liRemoteQuartetGaugedCarrierWeilForm alpha halpha A delta T f -
            (logApertureReflectedGammaWeilForm alpha halpha f : ℂ)) ∧
        (K.Nonempty →
          (∀ f ∈ K, 0 < logApertureReflectedGammaWeilForm alpha halpha f) →
          ∀ᶠ T in cocompact ℝ, ∀ f ∈ K,
            0 < (liRemoteQuartetGaugedCarrierWeilForm alpha halpha A delta T f).re)) ∧
      (∀ (Z : Type) [PseudoMetricSpace Z] (l : Filter Z)
          (height : Z → ℝ), Tendsto height l (cocompact ℝ) →
        ∀ test : Z → LogApertureSchwartz A,
          (∀ᶠ z in l, IsRealLogApertureTest (test z)) →
          (∀ᶠ z in l,
            (liRemoteQuartetGaugedCarrierWeilForm alpha halpha A delta
              (height z) (test z)).re ≤ 0) →
          (∀ K : Set (LogApertureSchwartz A), IsCompact K →
              ¬ ∀ᶠ z in l, test z ∈ K) ∨
            Tendsto (fun z => logApertureReflectedGammaWeilForm alpha halpha (test z))
              l (𝓝 0)) := by
  intro alpha A delta halpha
  refine ⟨continuous_logApertureReflectedGammaWeilForm alpha halpha A, ?_, ?_, ?_, ?_⟩
  · intro f
    exact ⟨logApertureReflectedGammaWeilForm_nonneg alpha halpha f,
      logApertureReflectedGammaWeilForm_eq_tsum alpha halpha f⟩
  · intro T f hf
    exact liRemoteQuartetGaugedCarrierWeilForm_eq_real halpha hf
  · intro K hK hreal
    refine ⟨compact_liRemoteQuartetGaugedCarrierWeilDifference_uniformVanishes
      halpha A delta hK hreal, ?_⟩
    intro hKne hstrict
    exact compact_eventually_pos_liRemoteQuartetGaugedCarrierWeilForm_re
      halpha A delta hK hKne hreal hstrict
  · intro Z inst l height hheight test hreal hdetect
    exact detectingSequence_gaugedCarrier_compactEscape_or_tendsto_radical
      halpha A delta hheight hreal hdetect

end

end RHTower
