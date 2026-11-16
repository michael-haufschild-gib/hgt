import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianKummerFields
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.SquareRelativeTraceKernels

/-!
# Parameters of the Hermitian trace covering group

For the trace cover with relative exponent length dividing the full
Frobenius length, the trace-zero translations and radical scalings
have exactly the product cardinality predicted by the covering degree.
The scalar roots are fixed by the short Frobenius.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d r m : ℕ)

/-- The Hermitian cover index is also the square-field index for the short Frobenius period. -/
theorem hermitianKummerCoverIndex_eq_traceIndex :
    hermitianKummerCoverIndex d r m =
      kummerSquareIndex ((d + 1) * (r + 1) - 1) m := by
  apply Nat.succ.inj
  change hermitianKummerCoverIndex d r m + 1 =
    kummerSquareIndex ((d + 1) * (r + 1) - 1) m + 1
  rw [hermitianKummerCoverIndex_succ, kummerSquareIndex_succ,
    Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos d) (Nat.succ_pos r))]

/-- The actual trace-zero translation parameters in the Hermitian constant field. -/
abbrev HermitianCoverTraceKernel :=
  {a : SquareConstantField p (hermitianKummerCoverIndex d r m) //
    frobeniusTraceSum p ((d + 1) * (r + 1)) (m + 1) a = 0}

/-- Every allowed covering translation is fixed by the full middle Frobenius. -/
theorem hermitianCoverTraceKernel_fixed (a : HermitianCoverTraceKernel p d r m) :
    a.val ∈ squareFrobeniusFixedField p (hermitianKummerCoverIndex d r m) := by
  change a.val ^ p ^ (hermitianKummerCoverIndex d r m + 1) = a.val
  have he : (d + 1) * (r + 1) - 1 + 1 = (d + 1) * (r + 1) :=
    Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos d) (Nat.succ_pos r))
  have h := frobeniusTraceSum_zero_fixed p ((d + 1) * (r + 1) - 1) m
    (x := a.val) (by simpa only [he] using a.property)
  exact (congrArg (fun N : ℕ => a.val ^ p ^ N)
    (hermitianKummerCoverIndex_succ d r m)).trans (by simpa only [he] using h)

/-- The translation family has exactly `q^((r+1)m)` elements. -/
theorem hermitianCoverTraceKernel_card :
    Nat.card (HermitianCoverTraceKernel p d r m) = p ^ ((d + 1) * (r + 1) * m) := by
  have he : (d + 1) * (r + 1) - 1 + 1 = (d + 1) * (r + 1) :=
    Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos d) (Nat.succ_pos r))
  have hpair : (hermitianKummerCoverIndex d r m, (d + 1) * (r + 1)) =
      (kummerSquareIndex ((d + 1) * (r + 1) - 1) m, (d + 1) * (r + 1) - 1 + 1) :=
    Prod.ext (hermitianKummerCoverIndex_eq_traceIndex d r m) he.symm
  have hc := congrArg (fun t : ℕ × ℕ =>
    Nat.card {a : SquareConstantField p t.1 // frobeniusTraceSum p t.2 (m + 1) a = 0}) hpair
  exact hc.trans
    ((squareRelativeTraceKernel_card p ((d + 1) * (r + 1) - 1) m).trans
      (congrArg (fun N : ℕ => p ^ (N * m)) he))

private theorem covering_scalar_exponent :
    kummerExponent (p ^ (d + 1)) (r + 1) * (p ^ (d + 1) - 1) + 1 =
      p ^ ((d + 1) * (r + 1)) := by
  have hq : 1 ≤ p ^ (d + 1) := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  simpa only [Nat.sub_add_cancel hq, ← pow_mul] using
    kummerExponent_mul_add (p ^ (d + 1) - 1) (r + 1)

/-- All radical-scaling roots are fixed by the short Frobenius. -/
theorem hermitianCoverScalar_fixed
    (ζ : rootsOfUnity (kummerExponent (p ^ (d + 1)) (r + 1))
      (SquareConstantField p (hermitianKummerCoverIndex d r m))) :
    (ζ.val : SquareConstantField p (hermitianKummerCoverIndex d r m)) ^
      p ^ ((d + 1) * (r + 1)) = ζ.val := by
  have hz : (ζ.val : SquareConstantField p (hermitianKummerCoverIndex d r m)) ^
      kummerExponent (p ^ (d + 1)) (r + 1) = 1 :=
    congrArg Units.val ζ.property
  rw [← covering_scalar_exponent p d r, pow_succ, pow_mul, hz, one_pow, one_mul]

/-- The radical-scaling family has exactly the geometric-exponent number of elements. -/
theorem hermitianCoverScalar_card :
    Nat.card (rootsOfUnity (kummerExponent (p ^ (d + 1)) (r + 1))
      (SquareConstantField p (hermitianKummerCoverIndex d r m))) =
      kummerExponent (p ^ (d + 1)) (r + 1) := by
  have hdiv : kummerExponent (p ^ (d + 1)) (r + 1) ∣
      p ^ ((d + 1) * (r + 1)) - 1 := by
    refine ⟨p ^ (d + 1) - 1, ?_⟩
    have h := covering_scalar_exponent p d r
    omega
  have hperiod : p ^ (2 * (hermitianKummerCoverIndex d r m + 1)) =
      (p ^ ((d + 1) * (r + 1))) ^ (2 * (m + 1)) := by
    rw [hermitianKummerCoverIndex_succ, ← pow_mul]
    congr 1
    ring
  rw [finiteField_rootsOfUnity_card, squareConstantField_card, hperiod]
  exact Nat.gcd_eq_right (hdiv.trans (Nat.sub_one_dvd_pow_sub_one _ _))

/-- Translation and scaling parameters have the exact degree of the Hermitian trace cover. -/
theorem hermitianCoverParameters_card :
    Nat.card (rootsOfUnity (kummerExponent (p ^ (d + 1)) (r + 1))
      (SquareConstantField p (hermitianKummerCoverIndex d r m)) ×
        HermitianCoverTraceKernel p d r m) =
      p ^ ((d + 1) * (r + 1) * m) * kummerExponent (p ^ (d + 1)) (r + 1) := by
  rw [Nat.card_prod, hermitianCoverScalar_card, hermitianCoverTraceKernel_card, Nat.mul_comm]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
