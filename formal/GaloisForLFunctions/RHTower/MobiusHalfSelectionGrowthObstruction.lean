import GaloisForLFunctions.RHTower.SquareRootAbelDirichletTransfer
import GaloisForLFunctions.RHTower.MobiusHalfSelectionPoleObstruction
import GaloisForLFunctions.RHTower.MobiusDivisorAbelQuadraticDiagonal

/-!
# Unbounded actual half-selection mean and averaged energy

The exact twice-Abel transfer turns any linear bound on the actual mean into
the holomorphic extension forbidden by the source pole obstruction. Finite
prefix absorption and the existing variance and quadratic-diagonal bounds
exclude every eventual constant averaged-energy budget. These unconditional
theorems refute independent half-probability averaging, not adaptive ordering
or the final signed-source estimate.
-/

noncomputable section
open Filter Topology Finset
namespace RHTower

/-- The generic weighted prefix is exactly the literal arithmetic mean. -/
theorem squareRootAbelPrefix_halfSelectionDivisorConvolution (N : ℕ) :
    squareRootAbelPrefix halfSelectionDivisorConvolution N =
      (mobiusDivisorHalfSelectionHead (N+1):ℂ) := by
  symm
  simpa only [squareRootAbelPrefix,Nat.add_sub_cancel_right,Nat.cast_add,Nat.cast_one] using
    mobiusDivisorHalfSelectionHead_eq_convolution_abel (N+1)

/-- Unconditional failure of every all-cutoff linear bound on the actual mean. -/
theorem not_exists_mobiusDivisorHalfSelectionHead_linear_bound :
    ¬ ∃ C : ℝ, ∀ M : ℕ, |mobiusDivisorHalfSelectionHead M| ≤ C*(M:ℝ) := by
  rintro ⟨C,hC⟩
  have hA : ∀ n, ‖squareRootAbelPrefix halfSelectionDivisorConvolution n‖ ≤ |C| *((n:ℝ)+1) := by
    intro n
    rw [squareRootAbelPrefix_halfSelectionDivisorConvolution,Complex.norm_real,Real.norm_eq_abs]
    have h := (hC (n+1)).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    simpa only [Nat.cast_add,Nat.cast_one] using h
  apply not_exists_analytic_halfSelectionDivisor_extension
  refine ⟨squareRootAbelDirichletSum (squareRootAbelPrefix halfSelectionDivisorConvolution),
    analyticOnNhd_squareRootAbelDirichletSum (abs_nonneg C) hA, ?_⟩
  intro s hs
  exact squareRootAbelDirichletSum_eq_LSeries (abs_nonneg C) hA (by linarith)
    (LSeriesSummable_halfSelectionDivisorConvolution (by linarith))

/-- The magnitude of the actual mean exceeds every proposed linear envelope. -/
theorem exists_mobiusDivisorHalfSelectionHead_gt_linear (C : ℝ) :
    ∃ M : ℕ, C*(M:ℝ) < |mobiusDivisorHalfSelectionHead M| := by
  by_contra h
  push Not at h
  exact not_exists_mobiusDivisorHalfSelectionHead_linear_bound ⟨C,h⟩

/-- The normalized mean is unbounded after deletion of any finite prefix. -/
theorem exists_mobiusDivisorHalfSelectionHead_gt_linear_after (C : ℝ) (M₀ : ℕ) :
    ∃ M : ℕ, M₀ ≤ M ∧ C*(M:ℝ) < |mobiusDivisorHalfSelectionHead M| := by
  let D : ℝ := ∑ m ∈ range M₀, |mobiusDivisorHalfSelectionHead m|
  have hD : 0 ≤ D := sum_nonneg (fun _ _ => abs_nonneg _)
  obtain ⟨M,hM⟩ := exists_mobiusDivisorHalfSelectionHead_gt_linear (|C|+D)
  have hMpos : 0 < M := by
    by_contra h
    have he : M=0 := by omega
    simp [he,mobiusDivisorHalfSelectionHead] at hM
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hMpos
  have hMtail : M₀ ≤ M := by
    by_contra h
    have hin : M ∈ range M₀ := mem_range.mpr (by omega)
    have hle : |mobiusDivisorHalfSelectionHead M| ≤ D :=
      single_le_sum (f := fun m => |mobiusDivisorHalfSelectionHead m|) (fun _ _ => abs_nonneg _) hin
    have hscale : D ≤ (|C|+D)*(M:ℝ) := by
      nlinarith [abs_nonneg C,mul_nonneg (abs_nonneg C) (Nat.cast_nonneg (α := ℝ) M)]
    linarith
  refine ⟨M,hMtail,lt_of_le_of_lt ?_ hM⟩
  exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (Nat.cast_nonneg (α := ℝ) M)

/-- Every fixed diagonal budget fails arbitrarily far out for the actual averaged energy. -/
theorem exists_mobiusDivisorHalfSelectionEnergy_gt_diagonal_multiple (K : ℝ) (M₀ : ℕ) :
    ∃ M : ℕ, M₀ ≤ M ∧
      K*(∑ d ∈ Icc 1 M,mobiusDivisorDilationChannel M d^2) < mobiusDivisorHalfSelectionEnergy M := by
  let C : ℝ := Real.sqrt (722*|K|)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hCsq : C^2=722*|K| := Real.sq_sqrt (by positivity)
  obtain ⟨M,hM,hhead⟩ := exists_mobiusDivisorHalfSelectionHead_gt_linear_after C M₀
  refine ⟨M,hM,?_⟩
  have hCM : 0 ≤ C*(M:ℝ) := mul_nonneg hC (Nat.cast_nonneg (α := ℝ) M)
  have hsquare : (C*(M:ℝ))^2 < (mobiusDivisorHalfSelectionHead M)^2 := by
    nlinarith [sq_abs (mobiusDivisorHalfSelectionHead M)]
  rw [mul_pow,hCsq] at hsquare
  have hQ : 0 ≤ ∑ d ∈ Icc 1 M,mobiusDivisorDilationChannel M d^2 :=
    sum_nonneg (fun _ _ => sq_nonneg _)
  have hbudget : K*(∑ d ∈ Icc 1 M,mobiusDivisorDilationChannel M d^2) ≤ 722*|K| *(M:ℝ)^2 := by
    calc
      _ ≤ |K| *(∑ d ∈ Icc 1 M,mobiusDivisorDilationChannel M d^2) :=
        mul_le_mul_of_nonneg_right (le_abs_self K) hQ
      _ ≤ |K| *(722*(M:ℝ)^2) := mul_le_mul_of_nonneg_left
        (sum_mobiusDivisorDilationChannel_sq_le_quadratic M) (abs_nonneg K)
      _ = _ := by ring
  exact lt_of_le_of_lt hbudget (hsquare.trans_le (mobiusDivisorHalfSelectionHead_sq_le_energy M))

/-- No fixed multiplicative budget and finite cutoff repair the averaged-energy bound. -/
theorem not_exists_eventual_mobiusDivisorHalfSelectionEnergy_diagonal_budget :
    ¬ ∃ (K : ℝ) (M₀ : ℕ), ∀ M : ℕ, M₀ ≤ M →
      mobiusDivisorHalfSelectionEnergy M ≤ K*(∑ d ∈ Icc 1 M,mobiusDivisorDilationChannel M d^2) := by
  rintro ⟨K,M₀,h⟩
  obtain ⟨M,hM,hgt⟩ := exists_mobiusDivisorHalfSelectionEnergy_gt_diagonal_multiple K M₀
  exact (not_lt_of_ge (h M hM)) hgt

/-- The half-probability case alone refutes the independent-average ceiling. -/
theorem not_forall_mobiusDivisorHalfSelectionEnergy_le_initial :
    ¬ ∀ M : ℕ, mobiusDivisorHalfSelectionEnergy M ≤ mobiusDivisorSelectionEnergy M ∅ := by
  intro h
  apply not_exists_eventual_mobiusDivisorHalfSelectionEnergy_diagonal_budget
  refine ⟨1,0,?_⟩
  intro M hM
  simpa only [one_mul,mobiusDivisorSelectionEnergy_empty] using h M

end RHTower
