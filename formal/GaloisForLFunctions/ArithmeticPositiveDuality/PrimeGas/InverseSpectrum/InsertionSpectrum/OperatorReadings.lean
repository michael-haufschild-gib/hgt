import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InsertionSpectrum.ThreeTraces
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.ExtremalSpectra

/-! # Pointwise reconstruction from three ordinary traces -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap

/-- Every real relative moment detects an actual exterior omission. -/
theorem physical_moment_pos (v : MissingWave) (q : GibbsExponent) : 0 < momentLoss q (missingSpectrum v) := by
  apply lt_of_le_of_ne (momentLoss_nonneg q _)
  intro h
  have he := (relativeReading_zero_iff (powerResponse q) (missingSpectrum v)).mp h.symm
  let two : GibbsExponent := ⟨2,by norm_num⟩
  have hz := (relativeReading_zero_iff (powerResponse two) (missingSpectrum v)).mpr he
  have hc := relativePartition_real (missingSpectrum v) two
  rw [hz,Complex.ofReal_zero] at hc
  exact omissionPartition_two_ne v hc

/-- Trace of the surviving fractional-power operator on the original occupation Hilbert space. -/
def survivingOperatorTrace (v : MissingWave) (q : TraceTemperature) := opTrace (momentOperator (omitLine v.val) q.val)

theorem survivingOperatorTrace_eq (v : MissingWave) (q : TraceTemperature) :
    survivingOperatorTrace v q = survivingTrace v (q.val:ℂ) := by
  have hd : MissingDimension (omitLine v.val) 1 := (missingDimension_one_iff _).mpr ⟨_,missingWave_ne_zero v,rfl⟩
  have hc := ((nonzero_line_conserves_iff _).mpr v.property).2
  rw [survivingOperatorTrace,momentOperator_trace _ hd hc (realTraceOrder q) q.property,
    survivingTrace,survivingPartition_eq_tsum _ (z := (q.val:ℂ)) q.property,Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  exact Complex.ofReal_cpow (band_pos (missingSpectrum v) n).le q.val

private theorem real_curvature_ne (a : ℕ+) (v : MissingWave) (ha : 1 < a.val) (q : TraceTemperature) :
    traceCurvature a v (q.val:ℂ) ≠ 0 := by
  have hp := (realTraceOrder q).property
  have he : 0 < energy a := Real.log_pos (by exact_mod_cast ha)
  have hh : ‖heat (q.val:ℂ) a‖ < 1 := by
    rw [norm_heat,Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hp) he
  have h1 : 1-heat (q.val:ℂ) a ≠ 0 := by
    intro h
    rw [← sub_eq_zero.mp h,norm_one] at hh
    exact lt_irrefl _ hh
  rw [traceCurvature_eq a v (z := (q.val:ℂ)) hp]
  apply mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 h1))
  change relativePartition (missingSpectrum v) (q.val:ℂ) ≠ 0
  rw [relativePartition_real _ (realTraceOrder q)]
  exact Complex.ofReal_ne_zero.mpr (physical_moment_pos v _).ne'

/-- At every real trace temperature the determinant quotient recovers zeta directly from three genuine operator traces. -/
theorem zeta_from_three_operator_traces (a : ℕ+) (v : MissingWave) (ha : 1 < a.val) (q : TraceTemperature) :
    let t₀ := survivingOperatorTrace v q
    let t₁ := survivingOperatorTrace (insertMissing a v) q
    let t₂ := survivingOperatorTrace (insertMissing a (insertMissing a v)) q
    (t₂-t₁)-(t₁-t₀) ≠ 0 ∧ (t₀*t₂-t₁^2)/((t₂-t₁)-(t₁-t₀)) = riemannZeta (q.val:ℂ) := by
  dsimp only
  simp only [survivingOperatorTrace_eq]
  change traceCurvature a v (q.val:ℂ) ≠ 0 ∧ traceDeterminant a v (q.val:ℂ)/traceCurvature a v (q.val:ℂ) = _
  have hn := real_curvature_ne a v ha q
  refine ⟨hn,?_⟩
  rw [traceDeterminant_eq a v (z := (q.val:ℂ)) (realTraceOrder q).property,mul_div_cancel_right₀ _ hn]

#print axioms physical_moment_pos
#print axioms survivingOperatorTrace_eq
#print axioms zeta_from_three_operator_traces

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
