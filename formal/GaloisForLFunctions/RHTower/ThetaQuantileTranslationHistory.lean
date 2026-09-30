import GaloisForLFunctions.RHTower.ThetaWeightedTranslationDomain
import GaloisForLFunctions.RHTower.HedenmalmThetaDerivativeHistoryQuotient
import GaloisForLFunctions.HTGeometry.L2MeasureCongruence

/-!
# Literal real-translation history in the original quantile carrier

The equality of the reciprocal power weight and the actual source measure
gives a canonical unitary into the original quantile space. It preserves the
literal derivative and translation vectors. Bounded-dual separation then
identifies the original closed derivative history with the closed span of all
genuinely admitted real translates. Every nonzero finite signed prime word is
excluded from the original source carrier by its largest nonzero coefficient.
-/

open MeasureTheory Set Topology

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry HedenmalmQuantile

noncomputable section

attribute [local instance 2000] Real.measurableSpace
attribute [local instance 2000] NormedSpace.complexToReal

private abbrev H := Lp ℂ 2 unitIntervalMeasure
private abbrev HS := SourceSpace thetaSource
private abbrev μS := volume.withDensity (realDensity (sourceWeight thetaSource))

private theorem isometry_mem_closedSpan_image
    {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (U : E ≃ₗᵢ[ℂ] F)
    (v : I → E) (x : E)
    (hx : x ∈ (Submodule.span ℂ (range v)).topologicalClosure) :
    U x ∈ (Submodule.span ℂ (range fun i => U (v i))).topologicalClosure := by
  let S := Submodule.span ℂ (range fun i => U (v i))
  have hspan : Submodule.span ℂ (range v) ≤
      S.topologicalClosure.comap U.toLinearEquiv.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change U (v i) ∈ S.topologicalClosure
    exact S.le_topologicalClosure (Submodule.subset_span ⟨i, rfl⟩)
  have hclosed : IsClosed
      (S.topologicalClosure.comap U.toLinearEquiv.toLinearMap : Set E) :=
    S.isClosed_topologicalClosure.preimage U.continuous
  exact (Submodule.span ℂ (range v)).topologicalClosure_minimal hspan hclosed hx

/-- The literal source vector of an intrinsically admitted real shift. -/
def thetaSourceRealTranslationVector (a : ThetaAdmittedRealShift 1) : HS :=
  l2MeasureCongruence thetaPowerWeightedMeasure_reciprocal_eq_sourceMeasure
    (thetaWeightedTranslationClass 1 ((a : ℝ) : ℂ))

/-- This canonical class is exactly the original literal source `toLp` vector. -/
theorem thetaSourceRealTranslationVector_eq_toLp (a : ThetaAdmittedRealShift 1) :
    thetaSourceRealTranslationVector a =
  ((thetaRealShiftSource_ofReal_memLp_source_iff a).mpr (by
    simpa only [div_one] using
      (thetaRealShiftSource_threshold_iff 1 a (by norm_num)).mp a.property)).toLp
    (fun x : ℝ => (thetaRealShiftSource a x : ℂ)) := by
  let hw := thetaRealShiftSource_ofReal_memLp 1 a (by norm_num) a.property
  exact (congrArg
    (l2MeasureCongruence thetaPowerWeightedMeasure_reciprocal_eq_sourceMeasure)
    (thetaWeightedTranslationClass_eq_toLp 1 a hw)).trans
      (l2MeasureCongruence_toLp thetaPowerWeightedMeasure_reciprocal_eq_sourceMeasure
        (fun x : ℝ => (thetaRealShiftSource a x : ℂ)) hw
        ((thetaRealShiftSource_ofReal_memLp_source_iff a).mpr (by
          simpa only [div_one] using
            (thetaRealShiftSource_threshold_iff 1 a (by norm_num)).mp a.property)))

/-- Actual quantile transport of the admitted literal source translate. -/
def thetaQuantileRealTranslationVector (a : ThetaAdmittedRealShift 1) : H :=
  quantileUnitary thetaSource (thetaSourceRealTranslationVector a)

/-- The closed span of every genuinely admitted real translate in quantile coordinates. -/
def thetaQuantileRealTranslationHistory : Submodule ℂ H :=
  (Submodule.span ℂ (range thetaQuantileRealTranslationVector)).topologicalClosure

theorem thetaSourceRealTranslationVector_coe (a : ThetaAdmittedRealShift 1) :
    (thetaSourceRealTranslationVector a : ℝ → ℂ) =ᵐ[volume]
      (fun x : ℝ => (thetaRealShiftSource a x : ℂ)) := by
  rw [thetaSourceRealTranslationVector_eq_toLp]
  apply (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
    (sourceWeight_pos thetaSource)).mp
  exact ((thetaRealShiftSource_ofReal_memLp_source_iff a).mpr (by
    simpa only [div_one] using
      (thetaRealShiftSource_threshold_iff 1 a (by norm_num)).mp a.property)).coeFn_toLp

/-- Equality of measures preserves the original literal derivative class. -/
theorem thetaReciprocalMeasureCongruence_derivative (n : ℕ) :
    l2MeasureCongruence thetaPowerWeightedMeasure_reciprocal_eq_sourceMeasure
      (thetaWeightedDerivativeVector 1 n) = thetaSourceDerivativeVector n := by
  apply Lp.ext
  have hw := l2MeasureCongruence_coe_ae
    thetaPowerWeightedMeasure_reciprocal_eq_sourceMeasure
    (thetaWeightedDerivativeVector 1 n)
    (fun x => ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ))
    (thetaWeightedDerivativeVector_coe 1 (by norm_num) (by norm_num) n)
  have hs : (thetaSourceDerivativeVector n : ℝ → ℂ) =ᵐ[μS]
      thetaSourceDerivativeFunction n :=
    (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
      (sourceWeight_pos thetaSource)).mpr (thetaSourceDerivativeVector_coe n)
  exact hw.trans hs.symm

theorem thetaQuantileDerivativeVector_eq_reciprocalTransport (n : ℕ) :
    quantileUnitary thetaSource
      (l2MeasureCongruence thetaPowerWeightedMeasure_reciprocal_eq_sourceMeasure
        (thetaWeightedDerivativeVector 1 n)) = thetaQuantileDerivativeVector n := by
  rw [thetaReciprocalMeasureCongruence_derivative]
  rfl

/-- Equality of measures preserves the literal admitted translation class. -/
theorem thetaReciprocalMeasureCongruence_translation (a : ThetaAdmittedRealShift 1) :
    l2MeasureCongruence thetaPowerWeightedMeasure_reciprocal_eq_sourceMeasure
      (thetaWeightedTranslationClass 1 ((a : ℝ) : ℂ)) =
      thetaSourceRealTranslationVector a := rfl

theorem thetaQuantileRealTranslationVector_eq_reciprocalTransport
    (a : ThetaAdmittedRealShift 1) :
    quantileUnitary thetaSource
      (l2MeasureCongruence thetaPowerWeightedMeasure_reciprocal_eq_sourceMeasure
        (thetaWeightedTranslationClass 1 ((a : ℝ) : ℂ))) =
      thetaQuantileRealTranslationVector a := by
  rw [thetaReciprocalMeasureCongruence_translation]
  rfl

private theorem sourceDerivative_transportFamily :
    (fun n => l2MeasureCongruence thetaPowerWeightedMeasure_reciprocal_eq_sourceMeasure
      (thetaWeightedDerivativeVector 1 n)) = thetaSourceDerivativeVector := by
  funext n
  exact thetaReciprocalMeasureCongruence_derivative n

private theorem sourceTranslation_transportFamily :
    (fun a : ThetaAdmittedRealShift 1 =>
      l2MeasureCongruence thetaPowerWeightedMeasure_reciprocal_eq_sourceMeasure
        (thetaWeightedTranslationClass 1 ((a : ℝ) : ℂ))) =
      thetaSourceRealTranslationVector := by
  funext a
  exact thetaReciprocalMeasureCongruence_translation a

private theorem quantileDerivative_transportFamily :
    (fun n => quantileUnitary thetaSource (thetaSourceDerivativeVector n)) =
      thetaQuantileDerivativeVector := by
  funext n
  rfl

private theorem quantileTranslation_transportFamily :
    (fun a => quantileUnitary thetaSource (thetaSourceRealTranslationVector a)) =
      thetaQuantileRealTranslationVector := by
  funext a
  rfl

/-- The original physical source history contains every admitted literal translate. -/
theorem thetaSourceRealTranslationVector_mem_derivativeHistory
    (a : ThetaAdmittedRealShift 1) :
    thetaSourceRealTranslationVector a ∈
      (Submodule.span ℂ (range thetaSourceDerivativeVector)).topologicalClosure := by
  have h := isometry_mem_closedSpan_image
    (l2MeasureCongruence thetaPowerWeightedMeasure_reciprocal_eq_sourceMeasure)
    (thetaWeightedDerivativeVector 1) (thetaWeightedTranslationClass 1 ((a : ℝ) : ℂ))
    (thetaWeightedTranslationClass_mem_derivativeHistory_of_abs 1 a (by norm_num) a.property)
  rw [sourceDerivative_transportFamily, thetaReciprocalMeasureCongruence_translation] at h
  exact h

private theorem sourceRealTranslation_closureTransport
    (f : Lp ℂ 2 (thetaPowerWeightedMeasure 1))
    (hf : f ∈ thetaWeightedRealTranslationHistory 1) :
    l2MeasureCongruence thetaPowerWeightedMeasure_reciprocal_eq_sourceMeasure f ∈
      (Submodule.span ℂ (range thetaSourceRealTranslationVector)).topologicalClosure := by
  exact l2MeasureCongruence_mem_closedSpan_of_familyEq
    thetaPowerWeightedMeasure_reciprocal_eq_sourceMeasure
    (fun a : ThetaAdmittedRealShift 1 => thetaWeightedTranslationClass 1 ((a : ℝ) : ℂ))
    thetaSourceRealTranslationVector sourceTranslation_transportFamily f hf

/-- Every literal physical derivative belongs to the source real-orbit closure. -/
theorem thetaSourceDerivativeVector_mem_realTranslationHistory (n : ℕ) :
    thetaSourceDerivativeVector n ∈
      (Submodule.span ℂ (range thetaSourceRealTranslationVector)).topologicalClosure := by
  have h := sourceRealTranslation_closureTransport (thetaWeightedDerivativeVector 1 n)
    (thetaWeightedDerivativeVector_mem_realTranslationHistory 1 (by norm_num) (by norm_num) n)
  rw [thetaReciprocalMeasureCongruence_derivative] at h
  exact h

/-- Original quantile history contains every admitted real translation. -/
theorem thetaQuantileRealTranslationVector_mem_derivativeHistory
    (a : ThetaAdmittedRealShift 1) :
    thetaQuantileRealTranslationVector a ∈ thetaQuantileDerivativeHistory := by
  have h := isometry_mem_closedSpan_image (quantileUnitary thetaSource) thetaSourceDerivativeVector
    (thetaSourceRealTranslationVector a) (thetaSourceRealTranslationVector_mem_derivativeHistory a)
  rw [quantileDerivative_transportFamily] at h
  exact h

/-- Analytic uniqueness transports every original derivative into the real-orbit closure. -/
theorem thetaQuantileDerivativeVector_mem_realTranslationHistory (n : ℕ) :
    thetaQuantileDerivativeVector n ∈ thetaQuantileRealTranslationHistory := by
  have h := isometry_mem_closedSpan_image (quantileUnitary thetaSource) thetaSourceRealTranslationVector
    (thetaSourceDerivativeVector n) (thetaSourceDerivativeVector_mem_realTranslationHistory n)
  rw [quantileTranslation_transportFamily] at h
  exact h

theorem thetaQuantileRealTranslationHistory_le_derivativeHistory :
    thetaQuantileRealTranslationHistory ≤ thetaQuantileDerivativeHistory := by
  apply (Submodule.span ℂ (range thetaQuantileRealTranslationVector)).topologicalClosure_minimal
    (Submodule.span_le.mpr ?_) (Submodule.isClosed_topologicalClosure _)
  rintro _ ⟨a, rfl⟩
  exact thetaQuantileRealTranslationVector_mem_derivativeHistory a

theorem thetaQuantileDerivativeHistory_le_realTranslationHistory :
    thetaQuantileDerivativeHistory ≤ thetaQuantileRealTranslationHistory := by
  apply (Submodule.span ℂ (range thetaQuantileDerivativeVector)).topologicalClosure_minimal
    (Submodule.span_le.mpr ?_) (Submodule.isClosed_topologicalClosure _)
  rintro _ ⟨n, rfl⟩
  exact thetaQuantileDerivativeVector_mem_realTranslationHistory n

/-- The paper's exact equality in its original, actual quantile carrier. -/
theorem thetaQuantileDerivativeHistory_eq_realTranslationHistory :
    thetaQuantileDerivativeHistory = thetaQuantileRealTranslationHistory :=
  le_antisymm thetaQuantileDerivativeHistory_le_realTranslationHistory
    thetaQuantileRealTranslationHistory_le_derivativeHistory

/-- Every genuinely admitted local translation is killed by the actual history quotient. -/
theorem thetaDerivativeHistoryQuotientProjection_realTranslation
    (a : ThetaAdmittedRealShift 1) :
    thetaDerivativeHistoryQuotientProjection (thetaQuantileRealTranslationVector a) = 0 :=
  (thetaDerivativeHistoryQuotientProjection_eq_zero_iff _).mpr
    (thetaQuantileRealTranslationVector_mem_derivativeHistory a)

/-- All nonzero finite signed prime words fail original source-space admission. -/
theorem finitePrimeThetaShift_ofReal_not_memLp_source
    (D : Finset ℕ) (c : ℕ → ℝ) (hprime : ∀ d ∈ D, Nat.Prime d)
    (hnonzero : ∃ d ∈ D, c d ≠ 0) :
    ¬ MemLp (fun x => (finiteArithmeticThetaShift D c x : ℂ)) 2 μS := by
  classical
  let E := D.filter fun d => c d ≠ 0
  have hE : E.Nonempty := by
    obtain ⟨d, hd, hc⟩ := hnonzero
    exact ⟨d, Finset.mem_filter.mpr ⟨hd, hc⟩⟩
  let b := E.max' hE
  have hb : b ∈ E := Finset.max'_mem E hE
  have hcb : c b ≠ 0 := (Finset.mem_filter.mp hb).2
  have hbprime : Nat.Prime b := hprime b (Finset.mem_filter.mp hb).1
  have hpositive : ∀ d ∈ E, 0 < d := by
    intro d hd
    exact (hprime d (Finset.mem_filter.mp hd).1).pos
  have hmax : ∀ d ∈ E, d ≤ b := fun d hd => Finset.le_max' E d hd
  have heq : finiteArithmeticThetaShift D c = finiteArithmeticThetaShift E c := by
    funext x
    simp only [finiteArithmeticThetaShift, E, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hc : c d = 0 <;> simp [hc]
  intro hm
  have hmE : MemLp (fun x => (finiteArithmeticThetaShift E c x : ℂ)) 2
      (thetaPowerWeightedMeasure 1) := by
    rw [thetaPowerWeightedMeasure_reciprocal_eq_sourceMeasure, ← heq]
    exact hm
  have ht : (1 : ℝ) < 2 / (b : ℝ) ^ 2 :=
    (finiteArithmeticThetaShift_ofReal_memLp_iff E c b hb hpositive hmax hcb 1
      (by norm_num)).mp hmE
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hbprime.two_le
  have hupper : 2 / (b : ℝ) ^ 2 ≤ (1 : ℝ) :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  exact (not_lt_of_ge hupper) ht

theorem primeThetaRealShift_ofReal_not_memLp_source (p : ℕ) (hp : Nat.Prime p) :
    ¬ MemLp (fun x : ℝ => (thetaRealShiftSource (Real.log p) x : ℂ)) 2 μS := by
  have hprime : ∀ d ∈ ({p} : Finset ℕ), Nat.Prime d := by
    intro d hd
    simp only [Finset.mem_singleton] at hd
    subst d
    exact hp
  have hnonzero : ∃ d ∈ ({p} : Finset ℕ), (fun _ : ℕ => (1 : ℝ)) d ≠ 0 := by
    exact ⟨p, by simp, by norm_num⟩
  simpa [finiteArithmeticThetaShift, thetaRealShiftSource] using
    finitePrimeThetaShift_ofReal_not_memLp_source {p} (fun _ => 1) hprime hnonzero

/-- Literal finite prime/arithmetic translate word with arbitrary complex coefficients. -/
def finiteComplexArithmeticThetaShift (D : Finset ℕ) (c : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ d ∈ D, c d * (thetaCuspFullSource (x + Real.log d) : ℂ)

theorem finiteComplexArithmeticThetaShift_re (D : Finset ℕ) (c : ℕ → ℂ) :
    (fun x => (finiteComplexArithmeticThetaShift D c x).re) =
      finiteArithmeticThetaShift D (fun d => (c d).re) := by
  funext x
  simp [finiteComplexArithmeticThetaShift, finiteArithmeticThetaShift, Complex.mul_re]

theorem finiteComplexArithmeticThetaShift_im (D : Finset ℕ) (c : ℕ → ℂ) :
    (fun x => (finiteComplexArithmeticThetaShift D c x).im) =
      finiteArithmeticThetaShift D (fun d => (c d).im) := by
  funext x
  simp [finiteComplexArithmeticThetaShift, finiteArithmeticThetaShift, Complex.mul_im]

/-- The full complex Hilbert-carrier exclusion, including arbitrary cancellation and zeros. -/
theorem finiteComplexPrimeThetaShift_not_memLp_source
    (D : Finset ℕ) (c : ℕ → ℂ) (hprime : ∀ d ∈ D, Nat.Prime d)
    (hnonzero : ∃ d ∈ D, c d ≠ 0) :
    ¬ MemLp (finiteComplexArithmeticThetaShift D c) 2 μS := by
  obtain ⟨d, hd, hc⟩ := hnonzero
  intro hm
  by_cases hr : (c d).re = 0
  · have hi : (c d).im ≠ 0 := by
      intro hi
      apply hc
      apply Complex.ext <;> simp [hr, hi]
    have him := hm.im
    change MemLp (fun x => (finiteComplexArithmeticThetaShift D c x).im) 2 μS at him
    rw [finiteComplexArithmeticThetaShift_im] at him
    exact finitePrimeThetaShift_ofReal_not_memLp_source D (fun d => (c d).im) hprime
      ⟨d, hd, hi⟩ him.ofReal
  · have hre := hm.re
    change MemLp (fun x => (finiteComplexArithmeticThetaShift D c x).re) 2 μS at hre
    rw [finiteComplexArithmeticThetaShift_re] at hre
    exact finitePrimeThetaShift_ofReal_not_memLp_source D (fun d => (c d).re) hprime
      ⟨d, hd, hr⟩ hre.ofReal

end

end RHTower.HedenmalmThetaSource
