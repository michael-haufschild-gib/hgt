import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InsertionSpectrum.Observable

/-! # The trace of an inserted occupation sector -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap GaloisForLFunctions.HTGeometry _root_.RHTower.PrimeCoShift

private theorem surviving_moment_mem (q : TraceTemperature) (v : MissingWave) :
    momentOperator (omitLine v.val) q.val ∈ hsTraceIdeal Gas := by
  have hd : MissingDimension (omitLine v.val) 1 := (missingDimension_one_iff _).mpr ⟨_,missingWave_ne_zero v,rfl⟩
  have hc := ((nonzero_line_conserves_iff _).mpr v.property).2
  obtain ⟨A,B,hA,hB,h⟩ := (momentOperator_traceClass_iff _ hd hc (realTraceOrder q)).mpr q.property
  change momentOperator (omitLine v.val) q.val = A ∘L B at h
  rw [h]
  exact comp_mem_hsTraceIdeal hA hB

theorem lostMoment_mem (q : TraceTemperature) (v : MissingWave) : lostMoment q v ∈ hsTraceIdeal Gas :=
  (hsTraceIdeal Gas).sub_mem (gibbs_mem_traceIdeal _) (surviving_moment_mem q v)

theorem momentLoss_as_relative_trace (q : TraceTemperature) (v : MissingWave) :
    momentLoss (realTraceOrder q) (missingSpectrum v) = (opTrace (lostMoment q v)).re := by
  have hd : MissingDimension (omitLine v.val) 1 := (missingDimension_one_iff _).mpr ⟨_,missingWave_ne_zero v,rfl⟩
  have hc := ((nonzero_line_conserves_iff _).mpr v.property).2
  rw [lostMoment,opTrace_sub_of_mem (gibbs_mem_traceIdeal _) (surviving_moment_mem q v),partition_eq_zeta,Complex.sub_re]
  exact momentLoss_eq_fractional_trace _ hd hc (realTraceOrder q) q.property

/-- Cyclicity removes the conjugating shift from the ordinary relative trace. -/
theorem lostMoment_trace_insert (a : ℕ+) (v : MissingWave) (q : TraceTemperature) :
    opTrace (lostMoment q (insertMissing a v)) = heat (q.val:ℂ) a*opTrace (lostMoment q v) := by
  have hc : primeCoShift a ∘L (insertWave a).toContinuousLinearMap = ContinuousLinearMap.id ℂ Gas :=
    ContinuousLinearMap.ext (remove_insert a)
  rw [lostMoment_insert,opTrace_smul',opTrace_comp_comm_of_mem (hsTraceIdeal_comp_right (lostMoment_mem q v) _) _,
    comp_assoc,hc,comp_id]

/-- Scaling of every real spectral moment in the half-plane of absolute traces. -/
theorem inserted_real_moment (a : ℕ+) (v : MissingWave) (q : TraceTemperature) :
    momentLoss (realTraceOrder q) (missingSpectrum (insertMissing a v)) =
      sectorWeight a^q.val*momentLoss (realTraceOrder q) (missingSpectrum v) := by
  rw [momentLoss_as_relative_trace,momentLoss_as_relative_trace,lostMoment_trace_insert,
    ← sectorWeight_power_heat,Complex.re_ofReal_mul]

#print axioms lostMoment_mem
#print axioms momentLoss_as_relative_trace
#print axioms lostMoment_trace_insert
#print axioms inserted_real_moment

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
