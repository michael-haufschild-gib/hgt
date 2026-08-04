/-
Ordinary operator trace on the project's approximation-number Schatten-1 class.

`opTrace` is defined on every bounded operator, with a junk value when its canonical diagonal is
not summable.  The Horn majorization theorem in `TraceNorm` now applies to arbitrarily indexed
finite orthonormal families.  Specializing it to the canonical Hilbert basis proves absolute
diagonal convergence, the trace-norm bound, and linearity on every genuine Schatten-1 operator.
-/
import GaloisForLFunctions.RHTower.TraceNorm
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Schatten-1 membership is ordinary summability of approximation numbers. -/
theorem MemSchattenClass.one_summable_approxNumber {T : H →L[ℂ] H}
    (hT : MemSchattenClass 1 T) :
    Summable (fun n => approxNumber T n) :=
  hT.congr fun _ => Real.rpow_one _

/-- Every Schatten-1 operator has an absolutely summable diagonal in any Hilbert basis. -/
theorem MemSchattenClass.one_summable_inner_diag_basis
    {ι : Type*} {T : H →L[ℂ] H}
    (hT : MemSchattenClass 1 T) (b : HilbertBasis ι ℂ H) :
    Summable (fun i => inner ℂ (b i) (T (b i))) := by
  have hcpt : IsCompactOperator T := hT.isCompactOperator one_pos
  have hbNorm : ∀ i, b i = 0 ∨ ‖b i‖ = 1 := by
    intro i
    exact Or.inr (b.orthonormal.1 i)
  have hbOrth : ∀ i j, i ≠ j → inner ℂ (b i) (b j) = 0 := by
    intro i j hij
    exact b.orthonormal.2 hij
  apply Summable.of_norm
  exact summable_of_sum_le (fun i => norm_nonneg _)
    (sum_norm_inner_le_traceNorm hcpt hT.one_summable_approxNumber
      hbNorm hbOrth hbNorm hbOrth)

/-- Every Schatten-1 operator has an absolutely summable canonical diagonal. -/
theorem MemSchattenClass.one_summable_inner_diag {T : H →L[ℂ] H}
    (hT : MemSchattenClass 1 T) :
    Summable (fun i => inner ℂ (hsBasis ℂ H i) (T (hsBasis ℂ H i))) :=
  hT.one_summable_inner_diag_basis (hsBasis ℂ H)

/-- Ordinary operator trace is bounded by the approximation-number trace norm. -/
theorem norm_opTrace_le_traceNorm {T : H →L[ℂ] H}
    (hT : MemSchattenClass 1 T) :
    ‖opTrace T‖ ≤ traceNorm H T := by
  let b := hsBasis ℂ H
  have hcpt : IsCompactOperator T := hT.isCompactOperator one_pos
  have hbNorm : ∀ n, b n = 0 ∨ ‖b n‖ = 1 := fun n =>
    Or.inr (b.orthonormal.1 n)
  have hbOrth : ∀ m n, m ≠ n → inner ℂ (b m) (b n) = 0 := fun m n hmn =>
    b.orthonormal.2 hmn
  have hdiag := hT.one_summable_inner_diag
  unfold opTrace
  calc
    ‖∑' i, inner ℂ (b i) (T (b i))‖ ≤
        ∑' i, ‖inner ℂ (b i) (T (b i))‖ :=
      norm_tsum_le_tsum_norm hdiag.norm
    _ ≤ traceNorm H T := Real.tsum_le_of_sum_le (fun i => norm_nonneg _)
      (sum_norm_inner_le_traceNorm hcpt hT.one_summable_approxNumber
        hbNorm hbOrth hbNorm hbOrth)

@[simp] theorem opTrace_zero :
    opTrace (0 : H →L[ℂ] H) = 0 := by
  simp [opTrace]

/-- Operator trace is additive on Schatten-1 operators. -/
theorem opTrace_add_of_memSchattenClass_one {S T : H →L[ℂ] H}
    (hS : MemSchattenClass 1 S) (hT : MemSchattenClass 1 T) :
    opTrace (S + T) = opTrace S + opTrace T := by
  unfold opTrace
  simp_rw [add_apply, inner_add_right]
  exact hS.one_summable_inner_diag.tsum_add hT.one_summable_inner_diag

/-- Operator trace respects subtraction on Schatten-1 operators. -/
theorem opTrace_sub_of_memSchattenClass_one {S T : H →L[ℂ] H}
    (hS : MemSchattenClass 1 S) (hT : MemSchattenClass 1 T) :
    opTrace (S - T) = opTrace S - opTrace T := by
  unfold opTrace
  simp_rw [sub_apply, inner_sub_right]
  exact hS.one_summable_inner_diag.tsum_sub hT.one_summable_inner_diag

/-- Scalar multiplication passes through ordinary operator trace. -/
theorem opTrace_smul (c : ℂ) (T : H →L[ℂ] H) :
    opTrace (c • T) = c * opTrace T := by
  unfold opTrace
  simp_rw [smul_apply, inner_smul_right]
  exact tsum_mul_left

@[simp] theorem opTrace_neg (T : H →L[ℂ] H) :
    opTrace (-T) = -opTrace T := by
  simpa using opTrace_smul (-1) T

end RHTower
