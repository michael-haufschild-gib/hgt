import GaloisForLFunctions.RHTower.WeilPaperArithmeticProductPenalties

/-!
# Recovering completed spectral laws from phase covariances

Rational phase moments determine every real probability law. For actual
observed spectral completions, all integer-phase means vanish, so two real
covariances per pair recover those complex moments. The covariance map is a
closed embedding of the compact completion, with continuous inverse on its
image. Coordinatewise covariance convergence is exactly weak convergence.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- All rational phase moments using labels at least two. -/
def paperRationalMomentData (μ : ProbabilityMeasure ℝ) : LogIndex × LogIndex → ℂ :=
  fun p => phaseMoment (paperPrimeSpectralPushforward μ) p.1.1 p.2.1

theorem paperRationalMomentData_eq_integral (μ : ProbabilityMeasure ℝ) (n m : LogIndex) :
    paperRationalMomentData μ (n, m) =
      ∫ ξ, paperRationalPhaseObservable n m ξ ∂(μ : Measure ℝ) :=
  (integral_paperRationalPhaseObservable μ n m).symm

/-- Rational moments with labels at least two determine an arbitrary real spectral law. -/
theorem paperRationalMomentData_injective : Function.Injective paperRationalMomentData := by
  intro μ ν h
  have hm (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
      phaseMoment (paperPrimeSpectralPushforward μ) a b =
        phaseMoment (paperPrimeSpectralPushforward ν) a b := by
    let n : LogIndex := ⟨2 * a, by omega⟩
    let m : LogIndex := ⟨2 * b, by omega⟩
    have hp := congrFun h (n, m)
    change phaseMoment (paperPrimeSpectralPushforward μ) (2 * a) (2 * b) =
      phaseMoment (paperPrimeSpectralPushforward ν) (2 * a) (2 * b) at hp
    have hnm : a * (2 * b) = b * (2 * a) := by ring
    rw [phaseMoment_rational_fibre _ ha hb (by omega : 2 * a ≠ 0)
      (by omega : 2 * b ≠ 0) hnm,
      phaseMoment_rational_fibre _ ha hb (by omega : 2 * a ≠ 0)
      (by omega : 2 * b ≠ 0) hnm] at hp
    exact hp
  have hk : (fun y : ℝ => charFun (μ : Measure ℝ) (2 * Real.pi * y)) =
      fun y : ℝ => charFun (ν : Measure ℝ) (2 * Real.pi * y) := by
    apply Continuous.ext_on dense_log_nat_ratios
      (continuous_charFun.comp (continuous_const.mul continuous_id))
      (continuous_charFun.comp (continuous_const.mul continuous_id))
    rintro y ⟨a, b, ha, hb, rfl⟩
    simpa only [phaseMoment_paperPrimeSpectralPushforward _ ha hb,
      Function.comp_def, Pi.mul_apply, id_eq] using hm a b ha hb
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  have ht : 2 * Real.pi * (t / (2 * Real.pi)) = t := by
    field_simp [Real.pi_ne_zero]
  simpa only [ht] using congrFun hk (t / (2 * Real.pi))

/-- Equality of the rational moment data is exactly equality of real probability laws. -/
theorem paperRationalMomentData_eq_iff (μ ν : ProbabilityMeasure ℝ) :
    paperRationalMomentData μ = paperRationalMomentData ν ↔ μ = ν :=
  paperRationalMomentData_injective.eq_iff

/-- The cosine-cosine and negative-sine-cosine probes for an integer frequency pair. -/
def paperPhaseCovarianceProbe (k : LogIndex × LogIndex × Bool) : ℝ →ᵇ ℝ :=
  paperSingleArithmeticPenalty k.1 (if k.2.2 then Complex.I else 1) *
    paperSingleArithmeticPenalty k.2.1 1

variable {ι : Type*}

/-- Actual centered phase covariances on the observed spectral completion. -/
def paperObservedPhaseCovariances (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    C(PaperObservedSpectralCompletion c F, (LogIndex × LogIndex × Bool) → ℝ) :=
  ⟨fun μ k => ∫ ξ, paperPhaseCovarianceProbe k ξ ∂(μ.1 : Measure ℝ), by
    apply continuous_pi
    intro k
    exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (paperPhaseCovarianceProbe k)).comp continuous_subtype_val⟩

/-- The first covariance channel reads half the real rational moment. -/
theorem paperObservedPhaseCovariances_false
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) (n m : LogIndex) :
    paperObservedPhaseCovariances c F μ (n, m, false) =
      (1 / 2 : ℝ) * (phaseMoment (paperPrimeSpectralPushforward μ.1) n.1 m.1).re := by
  change (∫ ξ, paperSingleArithmeticPenalty n 1 ξ * paperSingleArithmeticPenalty m 1 ξ
    ∂(μ.1 : Measure ℝ)) = _
  rw [integral_paperSingleArithmeticPenalty_mul c F μ]
  simp only [map_one, mul_one, one_mul]

/-- The second covariance channel reads minus half the imaginary rational moment. -/
theorem paperObservedPhaseCovariances_true
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) (n m : LogIndex) :
    paperObservedPhaseCovariances c F μ (n, m, true) =
      -(1 / 2 : ℝ) * (phaseMoment (paperPrimeSpectralPushforward μ.1) n.1 m.1).im := by
  change (∫ ξ, paperSingleArithmeticPenalty n Complex.I ξ * paperSingleArithmeticPenalty m 1 ξ
    ∂(μ.1 : Measure ℝ)) = _
  rw [integral_paperSingleArithmeticPenalty_mul c F μ]
  simp only [map_one, mul_one, Complex.I_mul_re]
  ring

/-- Every single frequency has universal variance one half and zero quadrature covariance. -/
theorem paperObservedPhaseCovariances_diagonal
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) (n : LogIndex) :
    paperObservedPhaseCovariances c F μ (n, n, false) = 1 / 2 ∧
      paperObservedPhaseCovariances c F μ (n, n, true) = 0 := by
  rw [paperObservedPhaseCovariances_false, paperObservedPhaseCovariances_true, phaseMoment_self]
  simp

/-- Off-diagonal covariance data recover the entire completed spectral law. -/
theorem paperObservedPhaseCovariances_injective
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    Function.Injective (paperObservedPhaseCovariances c F) := by
  intro μ ν h
  apply Subtype.ext
  apply paperRationalMomentData_injective
  funext p
  apply Complex.ext
  · have hr := congrFun h (p.1, p.2, false)
    rw [paperObservedPhaseCovariances_false, paperObservedPhaseCovariances_false] at hr
    change (phaseMoment (paperPrimeSpectralPushforward μ.1) p.1.1 p.2.1).re =
      (phaseMoment (paperPrimeSpectralPushforward ν.1) p.1.1 p.2.1).re
    linarith
  · have hi := congrFun h (p.1, p.2, true)
    rw [paperObservedPhaseCovariances_true, paperObservedPhaseCovariances_true] at hi
    change (phaseMoment (paperPrimeSpectralPushforward μ.1) p.1.1 p.2.1).im =
      (phaseMoment (paperPrimeSpectralPushforward ν.1) p.1.1 p.2.1).im
    linarith

/-- The universal diagonal can be discarded: off-diagonal covariances already determine the law. -/
theorem paperObservedSpectralLaw_eq_iff_offDiagonal_covariances
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ ν : PaperObservedSpectralCompletion c F) :
    μ = ν ↔ ∀ n m : LogIndex, n ≠ m → ∀ b : Bool,
      paperObservedPhaseCovariances c F μ (n, m, b) =
        paperObservedPhaseCovariances c F ν (n, m, b) := by
  constructor
  · rintro rfl n m _ b
    rfl
  · intro h
    apply paperObservedPhaseCovariances_injective c F
    funext k
    rcases k with ⟨n, m, b⟩
    by_cases hnm : n = m
    · subst m
      cases b
      · exact (paperObservedPhaseCovariances_diagonal c F μ n).1.trans
          (paperObservedPhaseCovariances_diagonal c F ν n).1.symm
      · exact (paperObservedPhaseCovariances_diagonal c F μ n).2.trans
          (paperObservedPhaseCovariances_diagonal c F ν n).2.symm
    · exact h n m hnm b

/-- The covariance representation is a closed embedding on each actual compact completion. -/
theorem isClosedEmbedding_paperObservedPhaseCovariances
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    IsClosedEmbedding (paperObservedPhaseCovariances c F) :=
  (paperObservedPhaseCovariances c F).continuous.isClosedEmbedding
    (paperObservedPhaseCovariances_injective c F)

theorem isCompact_paperObservedPhaseCovariances_range
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    IsCompact (Set.range (paperObservedPhaseCovariances c F)) := by
  simpa only [Set.image_univ] using
    isCompact_univ.image (paperObservedPhaseCovariances c F).continuous

/-- Covariance data and completed spectral laws carry exactly the same topology. -/
def paperPhaseCovarianceRecoveryHomeomorph
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    PaperObservedSpectralCompletion c F ≃ₜ Set.range (paperObservedPhaseCovariances c F) :=
  (isClosedEmbedding_paperObservedPhaseCovariances c F).isEmbedding.toHomeomorph

/-- Continuous recovery of a completed real spectral law from admissible covariance data. -/
def paperPhaseCovarianceRecovery (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) :
    C(Set.range (paperObservedPhaseCovariances c F), PaperObservedSpectralCompletion c F) :=
  ⟨(paperPhaseCovarianceRecoveryHomeomorph c F).symm,
    (paperPhaseCovarianceRecoveryHomeomorph c F).symm.continuous⟩

@[simp] theorem paperPhaseCovarianceRecovery_roundtrip
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (μ : PaperObservedSpectralCompletion c F) :
    paperPhaseCovarianceRecovery c F (paperPhaseCovarianceRecoveryHomeomorph c F μ) = μ :=
  (paperPhaseCovarianceRecoveryHomeomorph c F).symm_apply_apply μ

@[simp] theorem paperObservedPhaseCovariances_recovery
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (q : Set.range (paperObservedPhaseCovariances c F)) :
    paperObservedPhaseCovariances c F (paperPhaseCovarianceRecovery c F q) = q.1 :=
  congrArg Subtype.val ((paperPhaseCovarianceRecoveryHomeomorph c F).apply_symm_apply q)

/-- Coordinatewise covariance convergence is exactly weak convergence within the compact completion. -/
theorem tendsto_paperObservedPhaseCovariances_iff
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    {α : Type*} {l : Filter α} {μ : α → PaperObservedSpectralCompletion c F}
    {μ₀ : PaperObservedSpectralCompletion c F} :
    Tendsto μ l (𝓝 μ₀) ↔ ∀ k : LogIndex × LogIndex × Bool,
      Tendsto (fun i => paperObservedPhaseCovariances c F (μ i) k) l
        (𝓝 (paperObservedPhaseCovariances c F μ₀ k)) :=
  (isClosedEmbedding_paperObservedPhaseCovariances c F).tendsto_nhds_iff.trans tendsto_pi_nhds

end RHTower.WeilWorkPBAP
