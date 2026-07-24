import GaloisForLFunctions.RHTower.DirichletSummatorySwap
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The second-moment logarithm summatory

Two-sided integral bounds for `T₂(N) = ∑_{m ≤ N} (log m)²`:

`A(N) ≤ T₂(N) ≤ A(N+1)`,  where  `A(y) = y·log²y − 2y·log y + 2y − 2`

is the antiderivative value `∫₁^y log²t dt`.  Both bounds follow from
left/right Riemann comparison of the increasing integrand on `[1, ∞)`
(`MonotoneOn.sum_le_integral_Ico` / `integral_le_sum_Ico`); the *signed*
sandwich is kept rather than the absolute-error packaging of
`HTGeometry.abs_sum_sub_integral_le_of_monotoneOn`
(`HTGeometry/MonotoneRiemannSum.lean`), which wraps the same mechanism.
This pins `T₂` to its main term within `O(log² N)`, the precision consumed
by the μ-weighted hyperbola assembly of Selberg's symmetry formula.
-/

noncomputable section

namespace RHTower

open Finset intervalIntegral

/-- The antiderivative of `log²`. -/
def logSqAntideriv (y : ℝ) : ℝ :=
  y * Real.log y ^ 2 - 2 * y * Real.log y + 2 * y - 2

theorem hasDerivAt_logSqAntideriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun u => u * Real.log u ^ 2 - 2 * (u * Real.log u) + 2 * u + -2)
      (Real.log t ^ 2) t := by
  have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht.ne'
  have hsq : HasDerivAt (fun u : ℝ => Real.log u ^ 2)
      (2 * Real.log t * t⁻¹) t := by
    have := hlog.pow 2
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  have h1 := (hasDerivAt_id' t).mul hsq
  have h2 := ((hasDerivAt_id' t).mul hlog).const_mul (2:ℝ)
  have h3 := (hasDerivAt_id' t).const_mul (2:ℝ)
  have h := ((h1.sub h2).add h3).add_const (-2:ℝ)
  have hval : 1 * Real.log t ^ 2 + t * (2 * Real.log t * t⁻¹)
      - 2 * (1 * Real.log t + t * t⁻¹) + 2 * 1 = Real.log t ^ 2 := by
    field_simp
    ring
  rw [hval] at h
  exact h

/-- `∫₁^y log²t dt = A(y)` for `y ≥ 1`. -/
theorem integral_log_sq {y : ℝ} (hy : 1 ≤ y) :
    ∫ t in (1:ℝ)..y, Real.log t ^ 2 = logSqAntideriv y := by
  have hderiv : ∀ t ∈ Set.uIcc (1:ℝ) y,
      HasDerivAt (fun u => u * Real.log u ^ 2 - 2 * (u * Real.log u)
        + 2 * u + -2) (Real.log t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hy] at ht
    exact hasDerivAt_logSqAntideriv (lt_of_lt_of_le one_pos ht.1)
  have hcont : IntervalIntegrable (fun t => Real.log t ^ 2)
      MeasureTheory.volume 1 y := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.pow
    apply Real.continuousOn_log.mono
    rw [Set.uIcc_of_le hy]
    intro t ht
    have : (0:ℝ) < t := lt_of_lt_of_le one_pos ht.1
    simp [this.ne']
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont
  rw [h, Real.log_one]
  unfold logSqAntideriv
  ring

/-- Monotonicity of `log²` on `[1, ∞)`. -/
theorem monotoneOn_log_sq {a b : ℝ} (ha : 1 ≤ a) :
    MonotoneOn (fun t : ℝ => Real.log t ^ 2) (Set.Icc a b) := by
  intro s hs t ht hst
  have hs1 : (1:ℝ) ≤ s := le_trans ha hs.1
  have ht1 : (1:ℝ) ≤ t := le_trans ha ht.1
  have hlogs : 0 ≤ Real.log s := Real.log_nonneg hs1
  have hle : Real.log s ≤ Real.log t :=
    Real.log_le_log (by linarith) hst
  exact pow_le_pow_left₀ hlogs hle 2

/-- **Upper bound**: `T₂(N) ≤ A(N+1)`. -/
theorem sum_log_sq_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ m ∈ Finset.Icc 1 N, Real.log m ^ 2
      ≤ logSqAntideriv ((N:ℝ) + 1) := by
  have hmono : MonotoneOn (fun t : ℝ => Real.log t ^ 2)
      (Set.Icc ((1:ℕ):ℝ) ((N + 1 : ℕ):ℝ)) := by
    apply monotoneOn_log_sq
    norm_num
  have h := MonotoneOn.sum_le_integral_Ico
    (a := 1) (b := N + 1) (by omega) hmono
  have hsum : ∑ x ∈ Finset.Ico 1 (N + 1), Real.log x ^ 2
      = ∑ m ∈ Finset.Icc 1 N, Real.log m ^ 2 := by
    rw [Finset.Ico_add_one_right_eq_Icc]
  have hint : (∫ x in ((1:ℕ):ℝ)..((N + 1 : ℕ):ℝ), Real.log x ^ 2)
      = logSqAntideriv ((N:ℝ) + 1) := by
    have h1N : (1:ℝ) ≤ (N:ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
    have hval := integral_log_sq h1N
    rw [show (((1:ℕ)):ℝ) = (1:ℝ) from by norm_num,
      show (((N + 1 : ℕ)):ℝ) = ((N:ℝ) + 1) from by push_cast; ring]
    exact hval
  rw [hsum, hint] at h
  exact h

/-- **Lower bound**: `A(N) ≤ T₂(N)`. -/
theorem le_sum_log_sq (N : ℕ) (hN : 1 ≤ N) :
    logSqAntideriv (N:ℝ) ≤ ∑ m ∈ Finset.Icc 1 N, Real.log m ^ 2 := by
  have hmono : MonotoneOn (fun t : ℝ => Real.log t ^ 2)
      (Set.Icc ((1:ℕ):ℝ) ((N:ℕ):ℝ)) := by
    apply monotoneOn_log_sq
    norm_num
  have h := MonotoneOn.integral_le_sum_Ico
    (a := 1) (b := N) hN hmono
  have hint : (∫ x in ((1:ℕ):ℝ)..((N:ℕ):ℝ), Real.log x ^ 2)
      = logSqAntideriv (N:ℝ) := by
    push_cast
    exact integral_log_sq (by exact_mod_cast hN)
  rw [hint] at h
  refine le_trans h ?_
  calc (∑ i ∈ Finset.Ico 1 N, Real.log ((i + 1 : ℕ) : ℝ) ^ 2)
      = ∑ m ∈ Finset.Icc 2 N, Real.log (m : ℝ) ^ 2 := by
        apply Finset.sum_nbij' (i := fun i => i + 1) (j := fun m => m - 1)
        · intro i hi
          rw [Finset.mem_Ico] at hi
          rw [Finset.mem_Icc]
          omega
        · intro m hm
          rw [Finset.mem_Icc] at hm
          rw [Finset.mem_Ico]
          omega
        · intro i _
          omega
        · intro m hm
          rw [Finset.mem_Icc] at hm
          omega
        · intro i _
          rfl
    _ ≤ ∑ m ∈ Finset.Icc 1 N, Real.log (m : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc (by omega) le_rfl)
          (fun m _ _ => sq_nonneg _)

end RHTower
