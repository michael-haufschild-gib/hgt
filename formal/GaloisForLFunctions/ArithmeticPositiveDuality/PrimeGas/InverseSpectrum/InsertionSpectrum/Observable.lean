import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InsertionSpectrum.Powers
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DilationGibbsState

/-! # The trace-class difference under occupation insertion -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap GaloisForLFunctions.HTGeometry _root_.RHTower.PrimeCoShift

abbrev realGibbsPoint (q : TraceTemperature) : {z : ℂ // 1 < z.re} := ⟨(q.val:ℂ),q.property⟩
abbrev realTraceOrder (q : TraceTemperature) : GibbsExponent := ⟨q.val,zero_lt_one.trans q.property⟩

/-- Native Gibbs heat minus the fractional moment of the surviving propagator. -/
def lostMoment (q : TraceTemperature) (v : MissingWave) : GasOp :=
  gibbsOperator (realGibbsPoint q)-momentOperator (omitLine v.val) q.val

private theorem gibbs_insert_on (s : {z : ℂ // 1 < z.re}) (a : ℕ+) (x : Gas) :
    gibbsOperator s (insertWave a x) = heat s.val a • insertWave a (gibbsOperator s x) := by
  apply lp.ext
  funext n
  change gibbsOperator s (insertWave a x) n = heat s.val a*insertWave a (gibbsOperator s x) n
  rw [gibbsOperator_apply]
  by_cases hn : n ∈ Set.range (insertLabels a)
  · obtain ⟨k,rfl⟩ := hn
    change heat s.val (a*k)*insertWave a x (a*k) = heat s.val a*insertWave a (gibbsOperator s x) (a*k)
    rw [insertWave_at,insertWave_at,gibbsOperator_apply,heat_mul,mul_assoc]
  · rw [insertWave_off _ _ _ hn,insertWave_off _ _ _ hn,mul_zero,mul_zero]

private theorem gibbs_mode (s : {z : ℂ // 1 < z.re}) (n : ℕ+) :
    gibbsOperator s (modeWave n) = heat s.val n • modeWave n := by
  apply lp.ext
  funext k
  change gibbsOperator s (modeWave n) k = heat s.val n*modeWave n k
  rw [gibbsOperator_apply]
  rcases eq_or_ne k n with rfl | hk
  · rfl
  · simp only [modeWave,lp.single_apply,Pi.single_eq_of_ne hk,mul_zero]

theorem lostMoment_on (a : ℕ+) (v : MissingWave) (q : TraceTemperature) (x : Gas) :
    lostMoment q (insertMissing a v) (insertWave a x) =
      heat (q.val:ℂ) a • insertWave a (lostMoment q v x) := by
  simp only [lostMoment,sub_apply,gibbs_insert_on,inserted_moment_on a v (realTraceOrder q).property.le,
    map_sub,smul_sub,realGibbsPoint]

theorem lostMoment_off (a : ℕ+) (v : MissingWave) (q : TraceTemperature) (n : ℕ+) (hn : n ∉ Set.range (insertLabels a)) :
    lostMoment q (insertMissing a v) (modeWave n) = 0 := by
  change gibbsOperator (realGibbsPoint q) (modeWave n)-momentOperator (omitLine (insertWave a v.val)) q.val (modeWave n) = 0
  rw [gibbs_mode,inserted_moment_off a _ n hn (realTraceOrder q).property.le,sub_self]

/-- On the original Hilbert space, insertion conjugates the difference by the shift and multiplies by its heat amplitude. -/
theorem lostMoment_insert (a : ℕ+) (v : MissingWave) (q : TraceTemperature) :
    lostMoment q (insertMissing a v) =
      heat (q.val:ℂ) a • ((insertWave a).toContinuousLinearMap ∘L (lostMoment q v ∘L primeCoShift a)) := by
  apply ContinuousLinearMap.ext_on (s := Set.range (HilbertSchmidt.lpBasis ℕ+))
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr (HilbertSchmidt.lpBasis ℕ+).dense_span)
  rintro _ ⟨n,rfl⟩
  rw [HilbertSchmidt.lpBasis_apply]
  change lostMoment q (insertMissing a v) (modeWave n) = heat (q.val:ℂ) a • insertWave a (lostMoment q v (primeCoShift a (modeWave n)))
  by_cases hn : n ∈ Set.range (insertLabels a)
  · obtain ⟨k,rfl⟩ := hn
    change lostMoment q (insertMissing a v) (modeWave (a*k)) =
      heat (q.val:ℂ) a • insertWave a (lostMoment q v (primeCoShift a (modeWave (a*k))))
    rw [← insert_mode,remove_insert,lostMoment_on]
  · rw [lostMoment_off a v q n hn,remove_mode_off a n hn,map_zero,map_zero,smul_zero]

#print axioms lostMoment_on
#print axioms lostMoment_off
#print axioms lostMoment_insert

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
