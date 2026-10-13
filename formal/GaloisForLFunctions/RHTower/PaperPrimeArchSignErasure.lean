import GaloisForLFunctions.RHTower.PaperPrimeArchAbsoluteCurrent

/-! # The exact cost of erasing the signed source

The literal correction is multiplication by `|current| - current`, hence is
positive. Its compactness and zero ideal cost retain exactly source passivity.
-/

namespace RHTower.PaperPrimeArch
noncomputable section
open Classical MeasureTheory GaloisForLFunctions.HTGeometry
open scoped ENNReal

theorem norm_signErasureSymbol_le (a : Height) (t : ℝ) :
    ‖((|current a t| - current a t : ℝ) : ℂ)‖ ≤ decayBudget + decayBudget := by
  rw [Complex.ofReal_sub]
  exact (norm_sub_le _ _).trans (add_le_add (norm_absoluteCurrent_le a t) (norm_current_le a t))

def signErasureDefect (a : Height) : Space →L[ℂ] Space :=
  lpBoundedMulCLM
    (Complex.continuous_ofReal.comp ((continuous_current a).abs.sub (continuous_current a))).measurable
    (add_nonneg decayBudget_nonneg decayBudget_nonneg) (norm_signErasureSymbol_le a)

theorem signErasureDefect_apply_ae (a : Height) (f : Space) :
    (signErasureDefect a f : ℝ → ℂ) =ᵐ[volume]
      fun t => ((|current a t| - current a t : ℝ) : ℂ) * f t :=
  lpBoundedMulCLM_coeFn _ _ _ f

theorem signErasureDefect_eq_sub (a : Height) :
    signErasureDefect a = absoluteOperator a - operator a := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [signErasureDefect_apply_ae a f, absoluteOperator_apply_ae a f,
    operator_apply_ae a f, Lp.coeFn_sub (absoluteOperator a f) (operator a f)] with t hD hA hT hsub
  change signErasureDefect a f t = (absoluteOperator a f - operator a f : Space) t
  rw [hD, hsub, Pi.sub_apply, hA, hT, Complex.ofReal_sub, sub_mul]

theorem signErasureDefect_positive (a : Height) : (signErasureDefect a).IsPositive :=
  (lpBoundedRealMul_positive_iff ((continuous_current a).abs.sub (continuous_current a))
    (add_nonneg decayBudget_nonneg decayBudget_nonneg) (norm_signErasureSymbol_le a)).mpr
      (fun _ => sub_nonneg.mpr (le_abs_self _))

def signErasureCommutant (a : Height) : paperModulationCommutant :=
  ⟨signErasureDefect a, mem_paperModulationCommutant_of_mul _ _ (signErasureDefect_apply_ae a)⟩

theorem signErasureDefect_compactIdealDistance (a : Height) :
    compactIdealDistance (signErasureDefect a) = ‖signErasureDefect a‖ :=
  paperModulationCommutant_compactIdealDistance (signErasureCommutant a)

theorem signErasureDefect_eq_zero_iff (a : Height) :
    signErasureDefect a = 0 ↔ ∀ t, 0 ≤ current a t := by
  constructor
  · intro h t
    have hb := norm_symbol_le_of_ae_mul_continuous
      (Complex.continuous_ofReal.comp ((continuous_current a).abs.sub (continuous_current a)))
      (signErasureDefect_apply_ae a) t
    rw [h, norm_zero] at hb
    have hz : ((|current a t| - current a t : ℝ) : ℂ) = 0 :=
      norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
    have hr := Complex.ofReal_eq_zero.mp hz
    linarith [abs_nonneg (current a t)]
  · intro h
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [signErasureDefect_apply_ae a f] with t ht
    simpa [abs_of_nonneg (h t)] using ht

theorem signErasureDefect_compact_iff_zero (a : Height) :
    IsCompactOperator (signErasureDefect a) ↔ signErasureDefect a = 0 := by
  constructor
  · intro h
    exact congrArg Subtype.val ((paperModulationCommutant_compact_iff_zero (signErasureCommutant a)).mp h)
  · intro h
    rw [h]
    exact isCompactOperator_zero

theorem signErasureDefect_compact_iff (a : Height) :
    IsCompactOperator (signErasureDefect a) ↔ ∀ t, 0 ≤ current a t := by
  rw [signErasureDefect_compact_iff_zero, signErasureDefect_eq_zero_iff]

theorem signErasureDefect_traceCost (a : Height) :
    compactOperatorTraceCost Space (signErasureDefect a) =
      if ∀ t, 0 ≤ current a t then 0 else ∞ := by
  rw [compactOperatorTraceCost_eq, signErasureDefect_compact_iff]

theorem absoluteOperator_eq_operator_iff (a : Height) :
    absoluteOperator a = operator a ↔ ∀ t, 0 ≤ current a t := by
  rw [← sub_eq_zero, ← signErasureDefect_eq_sub, signErasureDefect_eq_zero_iff]

theorem forall_absoluteOperator_eq_operator_iff_rh :
    (∀ a : Height, absoluteOperator a = operator a) ↔ RiemannHypothesis := by
  simp_rw [absoluteOperator_eq_operator_iff]
  exact forall_current_nonneg_iff_rh

theorem forall_signErasureDefect_compact_iff_rh :
    (∀ a : Height, IsCompactOperator (signErasureDefect a)) ↔ RiemannHypothesis := by
  simp_rw [signErasureDefect_compact_iff]
  exact forall_current_nonneg_iff_rh

theorem forall_signErasureDefect_zero_cost_iff_rh :
    (∀ a : Height, compactOperatorTraceCost Space (signErasureDefect a) = 0) ↔ RiemannHypothesis := by
  simp_rw [compactOperatorTraceCost_eq_zero_iff]
  exact forall_signErasureDefect_compact_iff_rh

theorem operator_physicalObservation_le_iff (a b : Height) :
    (∀ x, l2PhysicalObservation (operator a) x ≤ l2PhysicalObservation (operator b) x) ↔
      ∀ t, |current a t| ≤ |current b t| := by
  simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using
    forall_l2PhysicalObservation_le_iff (Complex.continuous_ofReal.comp (continuous_current a))
      (Complex.continuous_ofReal.comp (continuous_current b)) (operator_apply_ae a) (operator_apply_ae b)

theorem operator_physicalObservation_eq_iff (a b : Height) :
    (∀ x, l2PhysicalObservation (operator a) x = l2PhysicalObservation (operator b) x) ↔
      ∀ t, |current a t| = |current b t| := by
  simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using
    forall_l2PhysicalObservation_eq_iff (Complex.continuous_ofReal.comp (continuous_current a))
      (Complex.continuous_ofReal.comp (continuous_current b)) (operator_apply_ae a) (operator_apply_ae b)

end
end RHTower.PaperPrimeArch
