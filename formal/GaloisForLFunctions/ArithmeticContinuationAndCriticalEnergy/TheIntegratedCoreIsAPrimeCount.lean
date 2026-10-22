import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheFreeAnchorAtZeroDamping
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheCoreDominanceCriterion
import GaloisForLFunctions.RHTower.ChebyshevPsiLogSummatory

/-!
# The integrated core is a prime count

Integrating the core of the signed work over a damping interval replaces each prime weight
`Λ(j) j^{-x}` by its exact primitive:

`∫_η^ε Λ(j) j^{-x} dx = Λ(j) (j^{-η} − j^{-ε})/log j`,

and `Λ(j)/log j` is the *prime-counting* density — `1/k` at `j = p^k`.  So the integrated core is a
weighted prime count, not a weighted prime mass:

`∫_η^ε core_x(T) dx = Σ_{n ≤ T} (1/(n(n+1))) Σ_{j ≤ n} Λ(j)(j^{-η} − j^{-ε})/log j`
(`integral_workCore_eq`),

and bounding each scale below by the largest one gives

`∫_η^ε core_x(T) dx ≥ (1 − 2^{-(ε−η)}) Σ_{n ≤ T} n^{-η} ψ(n)/(log n · n(n+1))`
(`integral_workCore_ge`),

with `ψ` Chebyshev's function.  Since `ψ(n)` grows linearly, the summand is of order
`1/(n log n)`: the integrated core is *large*, and it is positive.

That reverses its role.  At the free anchor the continuation demands an **upper** bound on the
integrated work, so the explicit positive core is a debt: admission forces the deviation terms to
cancel it (`integral_workDeviation_le_of_bddAbove`).  Every proof attempt that estimates the
deviation terms crudely and hopes the core's positivity carries the day is therefore doomed — the
core's own size is the thing that has to be matched.
-/

open Set Filter Finset MeasureTheory RHTower

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The exact primitive of a prime weight -/

/-- Continuity of a damped scale weight in the damping. -/
theorem continuousOn_rpow_neg_natCast {j : ℕ} (hj : 1 ≤ j) (s : Set ℝ) :
    ContinuousOn (fun x : ℝ => (j : ℝ) ^ (-x)) s := by
  have hj0 : (j : ℝ) ≠ 0 := by
    have : (0 : ℝ) < j := by exact_mod_cast hj
    linarith
  exact ((Real.continuous_const_rpow hj0).comp continuous_neg).continuousOn

/-- The primitive of `x ↦ j^{-x}`. -/
theorem integral_rpow_neg_eq {j : ℕ} (hj : 2 ≤ j) (η ε : ℝ) :
    (∫ x in η..ε, (j : ℝ) ^ (-x)) =
      ((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j := by
  have hj1 : (1 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hL : 0 < Real.log j := Real.log_pos hj1
  have hj0 : (0 : ℝ) < (j : ℝ) := by linarith
  have hexp : ∀ x : ℝ, (j : ℝ) ^ (-x) = Real.exp (-Real.log j * x) := by
    intro x
    rw [Real.rpow_def_of_pos hj0]
    congr 1
    ring
  have hderiv : ∀ x ∈ Set.uIcc η ε,
      HasDerivAt (fun y : ℝ => Real.exp (-Real.log j * y) * (-1 / Real.log j))
        ((j : ℝ) ^ (-x)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => -Real.log (j : ℝ) * y) (-Real.log (j : ℝ)) x := by
      simpa using (hasDerivAt_id x).const_mul (-Real.log (j : ℝ))
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-Real.log (j : ℝ) * y))
        (Real.exp (-Real.log (j : ℝ) * x) * -Real.log (j : ℝ)) x := h1.exp
    have h3 := h2.mul_const (-1 / Real.log (j : ℝ))
    have hval : Real.exp (-Real.log (j : ℝ) * x) * -Real.log (j : ℝ) *
        (-1 / Real.log (j : ℝ)) = (j : ℝ) ^ (-x) := by
      rw [hexp x]
      field_simp
    rw [← hval]
    exact h3
  have hint : IntervalIntegrable (fun x : ℝ => (j : ℝ) ^ (-x)) volume η ε :=
    ContinuousOn.intervalIntegrable (continuousOn_rpow_neg_natCast (by omega) _)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, ← hexp, ← hexp]
  ring

/-! ## §2. The integrated core -/

theorem intervalIntegrable_dampedPrimeWeight {j : ℕ} (hj : 1 ≤ j) (η ε : ℝ) :
    IntervalIntegrable (fun x => dampedPrimeWeight x j) volume η ε :=
  ContinuousOn.intervalIntegrable
    (continuousOn_const.mul (continuousOn_rpow_neg_natCast hj _))

/-- The integrated prime prefix is the prime-counting prefix. -/
theorem integral_dampedPrimePrefix_eq (η ε : ℝ) (n : ℕ) :
    (∫ x in η..ε, dampedPrimePrefix x n) =
      ∑ j ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt j *
        (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j) := by
  rw [show (fun x : ℝ => dampedPrimePrefix x n) =
      (fun x : ℝ => ∑ j ∈ Finset.Icc 1 n, dampedPrimeWeight x j) from rfl,
    intervalIntegral.integral_finsetSum (fun j hj =>
      intervalIntegrable_dampedPrimeWeight (Finset.mem_Icc.mp hj).1 η ε)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  rcases eq_or_lt_of_le hj1 with hj1' | hj2
  · have hju : j = 1 := hj1'.symm
    subst hju
    simp [dampedPrimeWeight, ArithmeticFunction.vonMangoldt_apply_one]
  · rw [show (fun x : ℝ => dampedPrimeWeight x j) =
        (fun x : ℝ => ArithmeticFunction.vonMangoldt j * (j : ℝ) ^ (-x)) from rfl,
      intervalIntegral.integral_const_mul, integral_rpow_neg_eq hj2]

/-- **The integrated core.** -/
theorem integral_workCore_eq (η ε : ℝ) (T : ℕ) :
    (∫ x in η..ε, workCore x T) =
      ∑ n ∈ Finset.Icc 1 T, (∑ j ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt j *
        (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j)) /
          ((n : ℝ) * ((n : ℝ) + 1)) := by
  have hcell : ∀ n ∈ Finset.Icc 1 T, IntervalIntegrable
      (fun x => dampedPrimePrefix x n / ((n : ℝ) * ((n : ℝ) + 1))) volume η ε := by
    intro n _
    refine ContinuousOn.intervalIntegrable (ContinuousOn.div_const ?_ _)
    rw [show (fun x : ℝ => dampedPrimePrefix x n) =
        (fun x : ℝ => ∑ j ∈ Finset.Icc 1 n, dampedPrimeWeight x j) from rfl]
    exact continuousOn_finsetSum _ fun j hj =>
      continuousOn_const.mul (continuousOn_rpow_neg_natCast (Finset.mem_Icc.mp hj).1 _)
  rw [show (fun x : ℝ => workCore x T) =
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 T, dampedPrimePrefix x n /
        ((n : ℝ) * ((n : ℝ) + 1))) from rfl,
    intervalIntegral.integral_finsetSum hcell]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_div, integral_dampedPrimePrefix_eq]

/-! ## §3. The Chebyshev lower bound -/

/-- **The integrated core is at least a Chebyshev prefix.** -/
theorem integral_workCore_ge {η ε : ℝ} (hη : 0 ≤ η) (hηε : η ≤ ε) (T : ℕ) :
    (1 - (2 : ℝ) ^ (-(ε - η))) *
      ∑ n ∈ Finset.Icc 1 T, (n : ℝ) ^ (-η) * chebyshevPsi n /
        (Real.log n * ((n : ℝ) * ((n : ℝ) + 1))) ≤
      ∫ x in η..ε, workCore x T := by
  rw [integral_workCore_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hw : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
  rcases eq_or_lt_of_le hn1 with hn1' | hn2
  · -- the unit horizon carries no prime mass
    have hnu : n = 1 := hn1'.symm
    subst hnu
    have hI : (Finset.Icc 1 1 : Finset ℕ) = {1} := by
      ext m
      rw [Finset.mem_Icc, Finset.mem_singleton]
      omega
    rw [hI, Finset.sum_singleton, chebyshevPsi, hI, Finset.sum_singleton,
      ArithmeticFunction.vonMangoldt_apply_one]
    norm_num
  · have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
    have hdiff : 0 ≤ ε - η := by linarith
    have hpow2 : (0 : ℝ) < (2 : ℝ) ^ (-(ε - η)) := Real.rpow_pos_of_pos (by norm_num) _
    have hpow2le : (2 : ℝ) ^ (-(ε - η)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    -- each scale is bounded below by the top scale
    have hcell : ∀ j ∈ Finset.Icc 1 n,
        ArithmeticFunction.vonMangoldt j *
            ((1 - (2 : ℝ) ^ (-(ε - η))) * ((n : ℝ) ^ (-η) / Real.log n)) ≤
          ArithmeticFunction.vonMangoldt j *
            (((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j) := by
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
      rcases eq_or_lt_of_le hj1 with hj1' | hj2
      · have hju : j = 1 := hj1'.symm
        subst hju
        rw [ArithmeticFunction.vonMangoldt_apply_one]
        norm_num
      · have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
        have hlogj : 0 < Real.log j := Real.log_pos (by exact_mod_cast hj2)
        have hlogle : Real.log j ≤ Real.log n := Real.log_le_log hj0 (by exact_mod_cast hjn)
        -- the damped scale factor
        have hfac : (n : ℝ) ^ (-η) ≤ (j : ℝ) ^ (-η) :=
          Real.rpow_le_rpow_of_nonpos hj0 (by exact_mod_cast hjn) (by linarith)
        have hgap : (j : ℝ) ^ (-(ε - η)) ≤ (2 : ℝ) ^ (-(ε - η)) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hj2) (by linarith)
        have hnum : (1 - (2 : ℝ) ^ (-(ε - η))) * (n : ℝ) ^ (-η) ≤
            (j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε) := by
          have hsplit : (j : ℝ) ^ (-ε) = (j : ℝ) ^ (-η) * (j : ℝ) ^ (-(ε - η)) := by
            rw [← Real.rpow_add hj0]
            congr 1
            ring
          have hjη : (0 : ℝ) < (j : ℝ) ^ (-η) := Real.rpow_pos_of_pos hj0 _
          rw [hsplit]
          have h1 : (1 - (2 : ℝ) ^ (-(ε - η))) * (n : ℝ) ^ (-η) ≤
              (1 - (2 : ℝ) ^ (-(ε - η))) * (j : ℝ) ^ (-η) :=
            mul_le_mul_of_nonneg_left hfac (by linarith)
          nlinarith [hgap, hjη]
        have hnumneg : 0 ≤ (j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε) := by
          have h0 : (0 : ℝ) ≤ (1 - (2 : ℝ) ^ (-(ε - η))) * (n : ℝ) ^ (-η) := by
            have : (0 : ℝ) ≤ (n : ℝ) ^ (-η) := Real.rpow_nonneg hn0.le _
            nlinarith
          linarith
        have hdiv : (1 - (2 : ℝ) ^ (-(ε - η))) * ((n : ℝ) ^ (-η) / Real.log n) ≤
            ((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j := by
          calc (1 - (2 : ℝ) ^ (-(ε - η))) * ((n : ℝ) ^ (-η) / Real.log n)
              = ((1 - (2 : ℝ) ^ (-(ε - η))) * (n : ℝ) ^ (-η)) / Real.log n := by ring
            _ ≤ ((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log n :=
                div_le_div_of_nonneg_right hnum hlogn.le
            _ ≤ ((j : ℝ) ^ (-η) - (j : ℝ) ^ (-ε)) / Real.log j := by
                gcongr
        exact mul_le_mul_of_nonneg_left hdiv ArithmeticFunction.vonMangoldt_nonneg
    have hsum := Finset.sum_le_sum hcell
    rw [← Finset.sum_mul] at hsum
    have hpsi : (∑ j ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt j) = chebyshevPsi n := rfl
    rw [hpsi] at hsum
    have hrw : (1 - (2 : ℝ) ^ (-(ε - η))) *
        ((n : ℝ) ^ (-η) * chebyshevPsi n / (Real.log n * ((n : ℝ) * ((n : ℝ) + 1)))) =
          (chebyshevPsi n * ((1 - (2 : ℝ) ^ (-(ε - η))) * ((n : ℝ) ^ (-η) / Real.log n))) /
            ((n : ℝ) * ((n : ℝ) + 1)) := by
      field_simp
    rw [hrw]
    exact div_le_div_of_nonneg_right hsum hw.le

/-! ## §4. The core is a debt -/

/-- The deviation part of the signed work: everything except the explicit core. -/
def workDeviation (ε : ℝ) (T : ℕ) : ℝ :=
  workLinearWindow ε T + workLinearPrefix ε T + workQuadratic ε T +
    polarDilationCorrection ε T

theorem signedDampingWork_eq_core_add_deviation (ε : ℝ) (T : ℕ) :
    signedDampingWork ε T = workCore ε T + workDeviation ε T := by
  rw [workDeviation, signedDampingWork_eq_core_add]
  ring

/-- **Admission forces the deviation terms to pay for the core.** -/
theorem integral_workDeviation_le_of_bddAbove {ε B : ℝ} {η : ℝ} (hη : 0 < η) (hηε : η ≤ ε)
    (hB : ∀ T : ℕ, dampedMobiusEnergy ε T ≤ B) (T : ℕ) :
    (∫ x in η..ε, 2 * workDeviation x T) ≤
      B - 2 * ((1 - (2 : ℝ) ^ (-(ε - η))) *
        ∑ n ∈ Finset.Icc 1 T, (n : ℝ) ^ (-η) * chebyshevPsi n /
          (Real.log n * ((n : ℝ) * ((n : ℝ) + 1)))) := by
  have hwork := work_integral_le_of_bddAbove hB T hη hηε
  have hcore := integral_workCore_ge hη.le hηε T
  have hintW : IntervalIntegrable (fun x => 2 * signedDampingWork x T) volume η ε :=
    intervalIntegrable_signedDampingWork hη hηε T
  have hintC : IntervalIntegrable (fun x => 2 * workCore x T) volume η ε := by
    refine ContinuousOn.intervalIntegrable (continuousOn_const.mul ?_)
    rw [show (fun x : ℝ => workCore x T) =
        (fun x : ℝ => ∑ n ∈ Finset.Icc 1 T, dampedPrimePrefix x n /
          ((n : ℝ) * ((n : ℝ) + 1))) from rfl]
    refine continuousOn_finsetSum _ fun n _ => ContinuousOn.div_const ?_ _
    rw [show (fun x : ℝ => dampedPrimePrefix x n) =
        (fun x : ℝ => ∑ j ∈ Finset.Icc 1 n, dampedPrimeWeight x j) from rfl]
    exact continuousOn_finsetSum _ fun j hj =>
      continuousOn_const.mul (continuousOn_rpow_neg_natCast (Finset.mem_Icc.mp hj).1 _)
  have hsplit : (∫ x in η..ε, 2 * workDeviation x T) =
      (∫ x in η..ε, 2 * signedDampingWork x T) - ∫ x in η..ε, 2 * workCore x T := by
    rw [← intervalIntegral.integral_sub hintW hintC]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [signedDampingWork_eq_core_add_deviation]
    ring
  have hcore2 : 2 * ((1 - (2 : ℝ) ^ (-(ε - η))) *
      ∑ n ∈ Finset.Icc 1 T, (n : ℝ) ^ (-η) * chebyshevPsi n /
        (Real.log n * ((n : ℝ) * ((n : ℝ) + 1)))) ≤
      ∫ x in η..ε, 2 * workCore x T := by
    rw [intervalIntegral.integral_const_mul]
    linarith
  rw [hsplit]
  linarith

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
