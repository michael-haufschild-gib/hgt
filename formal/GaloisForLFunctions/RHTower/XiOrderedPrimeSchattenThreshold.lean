import GaloisForLFunctions.RHTower.XiOrderedPrimeApproximationAsymptotics
import GaloisForLFunctions.RHTower.TraceNormLimit
import GaloisForLFunctions.HTGeometry.SchattenApproximationAdditivity

/-!
# Exact Schatten threshold of the ordered Xi reciprocal operator

The smooth RVM diagonal lies in every `S_q`, `q > 1`, but not in `S₁`.  Actual reciprocal Xi
ordinates change it by an `S₁` operator, so the same sharp threshold survives relocation.
-/

namespace RHTower

noncomputable section

private theorem xiOrderedSignedPrimeOperator_eq_model_add_correction :
    xiOrderedSignedPrimeOperator =
      routeKSignedPrimeRVMOperator + xiOrderedSignedPrimeRVMCorrection := by
  calc
    xiOrderedSignedPrimeOperator =
        (xiOrderedSignedPrimeOperator - routeKSignedPrimeRVMOperator) +
          routeKSignedPrimeRVMOperator := by abel
    _ = xiOrderedSignedPrimeRVMCorrection +
        routeKSignedPrimeRVMOperator := by
      rw [xiOrderedSignedPrimeOperator_sub_routeKSignedPrimeRVMOperator]
    _ = _ := add_comm _ _

/-- The actual reciprocal-Xi diagonal lies in every Schatten class above exponent one. -/
theorem xiOrderedSignedPrimeOperator_memSchattenClass
    {q : ℝ} (hq : 1 < q) :
    MemSchattenClass q xiOrderedSignedPrimeOperator := by
  have hcorrection : MemSchattenClass q xiOrderedSignedPrimeRVMCorrection :=
    xiOrderedSignedPrimeRVMCorrection_memSchattenClass_one.mono
      one_pos hq.le
  rw [xiOrderedSignedPrimeOperator_eq_model_add_correction]
  exact GaloisForLFunctions.HTGeometry.memSchattenClass_add
    (one_pos.trans hq) (routeKSignedPrimeRVMOperator_memSchattenClass hq)
    hcorrection

/-- The logarithmic endpoint remains outside trace class. -/
theorem xiOrderedSignedPrimeOperator_not_memSchattenClass_one :
    ¬ MemSchattenClass 1 xiOrderedSignedPrimeOperator := by
  intro hactual
  have hroute : MemSchattenClass 1
      (xiOrderedSignedPrimeOperator - xiOrderedSignedPrimeRVMCorrection) :=
    hactual.one_sub xiOrderedSignedPrimeRVMCorrection_memSchattenClass_one
  apply routeKSignedPrimeRVMOperator_not_memSchattenClass_one
  convert hroute using 1
  rw [xiOrderedSignedPrimeOperator_eq_model_add_correction]
  abel

theorem xiOrderedSignedPrimeOperator_memSchattenClass_two :
    MemSchattenClass 2 xiOrderedSignedPrimeOperator :=
  xiOrderedSignedPrimeOperator_memSchattenClass (by norm_num)

end

end RHTower
