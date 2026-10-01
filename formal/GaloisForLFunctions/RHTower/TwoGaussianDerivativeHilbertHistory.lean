import GaloisForLFunctions.RHTower.TwoGaussianDerivativeFunctionHistory

/-!
# Original Hilbert realizations of the literal two-Gaussian derivative history

The source carrier is actual reciprocal-weight `L²`; the quantile carrier is
the original pinned Hilbert space. All inverse operators here act on the
algebraic history of actual derivatives. No global compactness premise occurs.
-/

noncomputable section
open MeasureTheory GaloisForLFunctions.HTGeometry RHTower RHTower.HedenmalmQuantile
open scoped ENNReal

namespace RHTower.TwoGaussianComparison

attribute [local instance] Real.measurableSpace NormedSpace.complexToReal

private def μS : Measure ℝ := volume.withDensity (realDensity (sourceWeight source))

/-- Realization of actual admitted functions in the ORIGINAL weighted source carrier. -/
def sourceHistoryRealization : functionDerivativeHistory →ₗ[ℂ] SourceSpace source where
  toFun f := (functionDerivativeHistory_admission f.property).2.2.toLp f.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sourceHistoryRealization_coe (f : functionDerivativeHistory) :
    (sourceHistoryRealization f : ℝ → ℂ) =ᵐ[μS] f.val :=
  (functionDerivativeHistory_admission f.property).2.2.coeFn_toLp

theorem sourceHistoryRealization_ae_volume (f : functionDerivativeHistory) :
    (sourceHistoryRealization f : ℝ → ℂ) =ᵐ[volume] f.val :=
  (withDensity_realDensity_ae_eq (measurable_sourceWeight source)
    (sourceWeight_pos source)).mp (sourceHistoryRealization_coe f)

theorem sourceHistoryRealization_injective : Function.Injective sourceHistoryRealization := by
  intro f g hfg
  apply Subtype.ext
  have hg := sourceHistoryRealization_ae_volume g
  rw [← hfg] at hg
  have h : f.val =ᵐ[volume] g.val :=
    (sourceHistoryRealization_ae_volume f).symm.trans hg
  exact MeasureTheory.Measure.eq_of_ae_eq h
    (functionDerivativeHistory_admission f.property).1
    (functionDerivativeHistory_admission g.property).1

theorem sourceHistoryRealization_derivative (n : ℕ) :
    sourceHistoryRealization (functionHistoryDerivativeVector n) = sourceDerivativeVector n := rfl

theorem linearIndependent_sourceDerivativeVector :
    LinearIndependent ℂ sourceDerivativeVector := by
  have h := linearIndependent_functionHistoryDerivativeVector.map' sourceHistoryRealization
    (LinearMap.ker_eq_bot.mpr sourceHistoryRealization_injective)
  convert h using 1 <;> rfl

/-- Actual source history, as a subspace of original reciprocal-weight `L²`. -/
def sourceDerivativeHistory : Submodule ℂ (SourceSpace source) := sourceHistoryRealization.range

theorem sourceDerivativeHistory_eq_span :
    sourceDerivativeHistory = Submodule.span ℂ (Set.range sourceDerivativeVector) := by
  apply le_antisymm
  · intro f hf
    obtain ⟨g, rfl⟩ := hf
    refine Submodule.span_induction
      (p := fun f hf => sourceHistoryRealization ⟨f, hf⟩ ∈
        Submodule.span ℂ (Set.range sourceDerivativeVector)) ?_ ?_ ?_ ?_ g.property
    · rintro f ⟨n, rfl⟩
      change sourceHistoryRealization (functionHistoryDerivativeVector n) ∈ _
      rw [sourceHistoryRealization_derivative]
      exact Submodule.subset_span ⟨n, rfl⟩
    · change sourceHistoryRealization 0 ∈ _
      rw [map_zero]
      exact Submodule.zero_mem _
    · intro f g hf hg hfi hgi
      change sourceHistoryRealization (⟨f,hf⟩ + ⟨g,hg⟩) ∈ _
      rw [map_add]
      exact Submodule.add_mem _ hfi hgi
    · intro c f hf hfi
      change sourceHistoryRealization (c • ⟨f,hf⟩) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ c hfi
  · apply Submodule.span_le.mpr
    rintro f ⟨n, rfl⟩
    exact ⟨functionHistoryDerivativeVector n, sourceHistoryRealization_derivative n⟩

def sourceHistoryEquiv : functionDerivativeHistory ≃ₗ[ℂ] sourceDerivativeHistory :=
  LinearEquiv.ofInjective sourceHistoryRealization sourceHistoryRealization_injective

/-- Transport of the actual integral restriction to original source history. -/
def sourceHistoryInverse : sourceDerivativeHistory →ₗ[ℂ] sourceDerivativeHistory :=
  sourceHistoryEquiv.toLinearMap.comp
    (functionHistoryInverse.comp sourceHistoryEquiv.symm.toLinearMap)

theorem sourceHistoryInverse_realization (f : functionDerivativeHistory) :
    sourceHistoryInverse (sourceHistoryEquiv f) = sourceHistoryEquiv (functionHistoryInverse f) := by
  change sourceHistoryEquiv
    (functionHistoryInverse (sourceHistoryEquiv.symm (sourceHistoryEquiv f))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem sourceHistoryInverse_literal (f : functionDerivativeHistory) :
    ((sourceHistoryInverse (sourceHistoryEquiv f) : sourceDerivativeHistory) : ℝ → ℂ)
      =ᵐ[μS] sourceInverse source f.val :=
  by
    rw [sourceHistoryInverse_realization]
    exact sourceHistoryRealization_coe (functionHistoryInverse f)

def sourceHistoryDerivativeVector (n : ℕ) : sourceDerivativeHistory :=
  sourceHistoryEquiv (functionHistoryDerivativeVector n)

theorem sourceHistoryDerivativeVector_coe (n : ℕ) :
    (sourceHistoryDerivativeVector n : SourceSpace source) = sourceDerivativeVector n :=
  sourceHistoryRealization_derivative n

theorem sourceHistoryInverse_derivative_zero :
    sourceHistoryInverse (sourceHistoryDerivativeVector 0) = 0 := by
  simp only [sourceHistoryDerivativeVector, sourceHistoryInverse_realization,
    functionHistoryInverse_derivative_zero, map_zero]

theorem sourceHistoryInverse_derivative_succ (n : ℕ) :
    sourceHistoryInverse (sourceHistoryDerivativeVector (n+1)) =
      Complex.I • sourceHistoryDerivativeVector n := by
  simp only [sourceHistoryDerivativeVector, sourceHistoryInverse_realization,
    functionHistoryInverse_derivative_succ, map_smul]

theorem linearIndependent_sourceHistoryDerivativeVector :
    LinearIndependent ℂ sourceHistoryDerivativeVector :=
  linearIndependent_functionHistoryDerivativeVector.map' sourceHistoryEquiv.toLinearMap
    (LinearMap.ker_eq_bot.mpr sourceHistoryEquiv.injective)

theorem sourceHistoryInverse_pow_realization (n : ℕ) (f : functionDerivativeHistory) :
    (sourceHistoryInverse^n) (sourceHistoryEquiv f) =
      sourceHistoryEquiv ((functionHistoryInverse^n) f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ]
    change (sourceHistoryInverse^n) (sourceHistoryInverse (sourceHistoryEquiv f)) =
      sourceHistoryEquiv ((functionHistoryInverse^n) (functionHistoryInverse f))
    rw [sourceHistoryInverse_realization, ih]

theorem sourceHistoryInverse_pow_derivative_self (n : ℕ) :
    (sourceHistoryInverse^n) (sourceHistoryDerivativeVector n) =
      Complex.I^n • sourceHistoryDerivativeVector 0 := by
  rw [sourceHistoryDerivativeVector, sourceHistoryInverse_pow_realization,
    functionHistoryInverse_pow_derivative_self, map_smul]
  rfl

theorem sourceHistoryInverse_pow_derivative_eq_zero (n k : ℕ) (h : n < k) :
    (sourceHistoryInverse^k) (sourceHistoryDerivativeVector n) = 0 := by
  rw [sourceHistoryDerivativeVector, sourceHistoryInverse_pow_realization,
    functionHistoryInverse_pow_derivative_eq_zero n k h, map_zero]

theorem sourceHistoryDerivativeVector_zero_ne_zero : sourceHistoryDerivativeVector 0 ≠ 0 := by
  intro h
  apply functionHistoryDerivativeVector_zero_ne_zero
  apply sourceHistoryEquiv.injective
  simpa only [sourceHistoryDerivativeVector, map_zero] using h

theorem sourceHistoryDerivativeVector_ne_zero (n : ℕ) : sourceHistoryDerivativeVector n ≠ 0 := by
  intro h
  have hp := congrArg (fun f => (sourceHistoryInverse^n) f) h
  rw [sourceHistoryInverse_pow_derivative_self, map_zero] at hp
  exact smul_ne_zero (pow_ne_zero n Complex.I_ne_zero) sourceHistoryDerivativeVector_zero_ne_zero hp

theorem sourceHistory_infinite_zero_chain :
    LinearIndependent ℂ sourceHistoryDerivativeVector ∧
      (∀ n, sourceHistoryDerivativeVector n ≠ 0) ∧
      (∀ n, (sourceHistoryInverse^n) (sourceHistoryDerivativeVector n) =
        Complex.I^n • sourceHistoryDerivativeVector 0) ∧
      (∀ n k, n < k → (sourceHistoryInverse^k) (sourceHistoryDerivativeVector n) = 0) :=
  ⟨linearIndependent_sourceHistoryDerivativeVector, sourceHistoryDerivativeVector_ne_zero,
    sourceHistoryInverse_pow_derivative_self, sourceHistoryInverse_pow_derivative_eq_zero⟩

/-- The original quantile unitary applied to actual weighted source representatives. -/
def quantileHistoryRealization : functionDerivativeHistory →ₗ[ℂ] H :=
  (quantileUnitary source).toLinearEquiv.toLinearMap.comp sourceHistoryRealization

theorem quantileHistoryRealization_injective : Function.Injective quantileHistoryRealization := by
  intro f g h
  apply sourceHistoryRealization_injective
  exact (quantileUnitary source).toLinearEquiv.injective h

theorem quantileHistoryRealization_ae (f : functionDerivativeHistory) :
    (quantileHistoryRealization f : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
      fun t => (Real.sqrt source.mass : ℂ) * f.val (source.quantileFun t) /
        (source.k (source.quantileFun t) : ℂ) := by
  have hq := source.measurePreserving_quantileFun.quasiMeasurePreserving.ae_eq_comp
    (source.law_ae_eq.mpr (sourceHistoryRealization_ae_volume f))
  rw [← unitIntervalMeasure_eq] at hq
  filter_upwards [quantileUnitary_ae source (sourceHistoryRealization f), hq] with t ht hft
  change (quantileUnitary source (sourceHistoryRealization f) : ℝ → ℂ) t = _
  rw [ht]
  change (sourceHistoryRealization f : ℝ → ℂ) (source.quantileFun t) = _ at hft
  rw [hft]
  rfl

theorem pinnedMean_quantileHistoryRealization (f : functionDerivativeHistory) :
    pinnedMean (quantileHistoryRealization f) =
      (∫ x, f.val x) / (Real.sqrt source.mass : ℂ) := by
  have hmeas : AEStronglyMeasurable (sourceHistoryRealization f : ℝ → ℂ) volume :=
    (functionDerivativeHistory_admission f.property).1.aestronglyMeasurable.congr
      (sourceHistoryRealization_ae_volume f).symm
  change pinnedMean (quantileUnitary source (sourceHistoryRealization f)) = _
  rw [pinnedMean_quantileUnitary, integral_quantileTransform source hmeas,
    integral_congr_ae (sourceHistoryRealization_ae_volume f)]

def quantileDerivativeVector (n : ℕ) : H := quantileUnitary source (sourceDerivativeVector n)

theorem quantileHistoryRealization_derivative (n : ℕ) :
    quantileHistoryRealization (functionHistoryDerivativeVector n) = quantileDerivativeVector n := by
  change quantileUnitary source (sourceHistoryRealization (functionHistoryDerivativeVector n)) = _
  rw [sourceHistoryRealization_derivative]
  rfl

theorem quantileDerivativeVector_zero :
    quantileDerivativeVector 0 = (Real.sqrt source.mass : ℂ) • pinnedOne := by
  apply Lp.ext
  filter_upwards [quantileHistoryRealization_ae (functionHistoryDerivativeVector 0),
    Lp.coeFn_smul (Real.sqrt source.mass : ℂ) pinnedOne, pinnedOne_coeFn] with t ht hs ho
  rw [quantileHistoryRealization_derivative] at ht
  rw [ht, hs, Pi.smul_apply, ho, smul_eq_mul]
  change (Real.sqrt source.mass : ℂ) * derivativeFunction 0 (source.quantileFun t) /
    (source.k (source.quantileFun t) : ℂ) = _
  rw [derivativeFunction_zero]
  have hne : (source.k (source.quantileFun t) : ℂ) ≠ 0 := by
    exact_mod_cast (source.pos_k (source.quantileFun t)).ne'
  field_simp [hne]

theorem pinnedMean_quantileDerivativeVector_succ (n : ℕ) :
    pinnedMean (quantileDerivativeVector (n+1)) = 0 := by
  rw [← quantileHistoryRealization_derivative, pinnedMean_quantileHistoryRealization]
  change (∫ x, derivativeFunction (n+1) x) / (Real.sqrt source.mass : ℂ) = 0
  rw [integral_derivativeFunction_succ, zero_div]

theorem linearIndependent_quantileDerivativeVector : LinearIndependent ℂ quantileDerivativeVector := by
  have h := linearIndependent_functionHistoryDerivativeVector.map' quantileHistoryRealization
    (LinearMap.ker_eq_bot.mpr quantileHistoryRealization_injective)
  convert h using 1 <;> rfl

/-- Actual quantile history inside the ORIGINAL pinned Hilbert space. -/
def quantileDerivativeHistory : Submodule ℂ H := quantileHistoryRealization.range

theorem quantileDerivativeHistory_eq_span :
    quantileDerivativeHistory = Submodule.span ℂ (Set.range quantileDerivativeVector) := by
  have hrange : quantileDerivativeHistory = sourceDerivativeHistory.map
      (quantileUnitary source).toLinearEquiv.toLinearMap := by
    ext f
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨sourceHistoryRealization g, ⟨g,rfl⟩,rfl⟩
    · rintro ⟨g,⟨h,rfl⟩,rfl⟩
      exact ⟨h,rfl⟩
  rw [hrange, sourceDerivativeHistory_eq_span, Submodule.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨g,⟨n,rfl⟩,rfl⟩
    exact ⟨n,rfl⟩
  · rintro ⟨n,rfl⟩
    exact ⟨sourceDerivativeVector n,⟨n,rfl⟩,rfl⟩

def quantileHistoryEquiv : functionDerivativeHistory ≃ₗ[ℂ] quantileDerivativeHistory :=
  LinearEquiv.ofInjective quantileHistoryRealization quantileHistoryRealization_injective

def quantileHistoryInverse : quantileDerivativeHistory →ₗ[ℂ] quantileDerivativeHistory :=
  quantileHistoryEquiv.toLinearMap.comp
    (functionHistoryInverse.comp quantileHistoryEquiv.symm.toLinearMap)

theorem quantileHistoryInverse_realization (f : functionDerivativeHistory) :
    quantileHistoryInverse (quantileHistoryEquiv f) =
      quantileHistoryEquiv (functionHistoryInverse f) := by
  change quantileHistoryEquiv
    (functionHistoryInverse (quantileHistoryEquiv.symm (quantileHistoryEquiv f))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem quantileHistoryInverse_literal (f : functionDerivativeHistory) :
    ((quantileHistoryInverse (quantileHistoryEquiv f) : quantileDerivativeHistory) : ℝ → ℂ)
      =ᵐ[unitIntervalMeasure]
      fun t => (Real.sqrt source.mass : ℂ) * sourceInverse source f.val (source.quantileFun t) /
        (source.k (source.quantileFun t) : ℂ) := by
  rw [quantileHistoryInverse_realization]
  exact quantileHistoryRealization_ae (functionHistoryInverse f)

def quantileHistoryDerivativeVector (n : ℕ) : quantileDerivativeHistory :=
  quantileHistoryEquiv (functionHistoryDerivativeVector n)

theorem quantileHistoryDerivativeVector_coe (n : ℕ) :
    (quantileHistoryDerivativeVector n : H) = quantileDerivativeVector n :=
  quantileHistoryRealization_derivative n

theorem quantileHistoryInverse_derivative_zero :
    quantileHistoryInverse (quantileHistoryDerivativeVector 0) = 0 := by
  simp only [quantileHistoryDerivativeVector, quantileHistoryInverse_realization,
    functionHistoryInverse_derivative_zero, map_zero]

theorem quantileHistoryInverse_derivative_succ (n : ℕ) :
    quantileHistoryInverse (quantileHistoryDerivativeVector (n+1)) =
      Complex.I • quantileHistoryDerivativeVector n := by
  simp only [quantileHistoryDerivativeVector, quantileHistoryInverse_realization,
    functionHistoryInverse_derivative_succ, map_smul]

theorem linearIndependent_quantileHistoryDerivativeVector :
    LinearIndependent ℂ quantileHistoryDerivativeVector :=
  linearIndependent_functionHistoryDerivativeVector.map' quantileHistoryEquiv.toLinearMap
    (LinearMap.ker_eq_bot.mpr quantileHistoryEquiv.injective)

theorem quantileHistoryInverse_pow_realization (n : ℕ) (f : functionDerivativeHistory) :
    (quantileHistoryInverse^n) (quantileHistoryEquiv f) =
      quantileHistoryEquiv ((functionHistoryInverse^n) f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ]
    change (quantileHistoryInverse^n) (quantileHistoryInverse (quantileHistoryEquiv f)) =
      quantileHistoryEquiv ((functionHistoryInverse^n) (functionHistoryInverse f))
    rw [quantileHistoryInverse_realization, ih]

theorem quantileHistoryInverse_pow_derivative_self (n : ℕ) :
    (quantileHistoryInverse^n) (quantileHistoryDerivativeVector n) =
      Complex.I^n • quantileHistoryDerivativeVector 0 := by
  rw [quantileHistoryDerivativeVector, quantileHistoryInverse_pow_realization,
    functionHistoryInverse_pow_derivative_self, map_smul]
  rfl

theorem quantileHistoryInverse_pow_derivative_eq_zero (n k : ℕ) (h : n < k) :
    (quantileHistoryInverse^k) (quantileHistoryDerivativeVector n) = 0 := by
  rw [quantileHistoryDerivativeVector, quantileHistoryInverse_pow_realization,
    functionHistoryInverse_pow_derivative_eq_zero n k h, map_zero]

theorem quantileHistoryDerivativeVector_zero_ne_zero : quantileHistoryDerivativeVector 0 ≠ 0 := by
  intro h
  apply functionHistoryDerivativeVector_zero_ne_zero
  apply quantileHistoryEquiv.injective
  simpa only [quantileHistoryDerivativeVector, map_zero] using h

theorem quantileHistoryDerivativeVector_ne_zero (n : ℕ) : quantileHistoryDerivativeVector n ≠ 0 := by
  intro h
  have hp := congrArg (fun f => (quantileHistoryInverse^n) f) h
  rw [quantileHistoryInverse_pow_derivative_self, map_zero] at hp
  exact smul_ne_zero (pow_ne_zero n Complex.I_ne_zero) quantileHistoryDerivativeVector_zero_ne_zero hp

theorem quantileHistory_infinite_zero_chain :
    LinearIndependent ℂ quantileHistoryDerivativeVector ∧
      (∀ n, quantileHistoryDerivativeVector n ≠ 0) ∧
      (∀ n, (quantileHistoryInverse^n) (quantileHistoryDerivativeVector n) =
        Complex.I^n • quantileHistoryDerivativeVector 0) ∧
      (∀ n k, n < k → (quantileHistoryInverse^k) (quantileHistoryDerivativeVector n) = 0) :=
  ⟨linearIndependent_quantileHistoryDerivativeVector, quantileHistoryDerivativeVector_ne_zero,
    quantileHistoryInverse_pow_derivative_self, quantileHistoryInverse_pow_derivative_eq_zero⟩

end RHTower.TwoGaussianComparison
