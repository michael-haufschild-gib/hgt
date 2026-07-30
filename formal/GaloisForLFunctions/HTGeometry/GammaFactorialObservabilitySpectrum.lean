import GaloisForLFunctions.HTGeometry.GammaPeriodicConstraintCorona
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact
import GaloisForLFunctions.HTGeometry.SourceGaugeObservabilitySpectrum

/-!
# Gamma factorial observability spectrum

The unit-shift source produces the Taylor conormal coefficients `1 / (n + 1)!`.  On the canonical
square-summable clock completion, use those source coefficients as a diagonal reporter.  The
resulting operator is Hilbert--Schmidt, compact, and injective, but its range is not closed: the
unit clock modes have exactly factorially decaying observation norm.

This is a natural analytic realization of the approximate-blind phase of the source-gauge
observability trichotomy.  All finite clock coordinates are nonzero, so algebraic reconstruction
holds, while no uniform observability gap survives at the infinite boundary.
-/

open Filter Topology
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The diagonal kernel carrying the source-normalized Gamma Taylor conormal coefficients. -/
def gammaFactorialObservabilityKernel : ℕ × ℕ → ℂ := fun p ↦
  if p.1 = p.2 then gammaPeriodicConormalCoefficient p.1 else 0

/-- The squared Gamma conormal coefficients are summable. -/
theorem summable_normSq_gammaPeriodicConormalCoefficient :
    Summable (fun n : ℕ ↦ ‖gammaPeriodicConormalCoefficient n‖ ^ 2) := by
  have hbase : Summable (fun n : ℕ ↦ (1 : ℝ) / (n.factorial : ℝ)) := by
    simpa using Real.summable_pow_div_factorial 1
  have htail : Summable (fun n : ℕ ↦ (1 : ℝ) / ((n + 1).factorial : ℝ)) := by
    simpa [Nat.succ_eq_add_one] using! hbase.comp_injective Nat.succ_injective
  apply Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) htail
  rw [gammaPeriodicConormalCoefficient, norm_div, norm_one, Complex.norm_natCast]
  have hfac : (1 : ℝ) ≤ ((n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n + 1)
  have hnonneg : 0 ≤ (1 : ℝ) / ((n + 1).factorial : ℝ) := by positivity
  have hle : (1 : ℝ) / ((n + 1).factorial : ℝ) ≤ 1 :=
    (div_le_one (by positivity)).2 hfac
  nlinarith

/-- The Gamma factorial diagonal is a Hilbert--Schmidt kernel. -/
theorem gammaFactorialObservabilityKernel_isHS :
    HilbertSchmidt.IsHS gammaFactorialObservabilityKernel := by
  rw [HilbertSchmidt.IsHS, summable_prod_of_nonneg (fun p ↦ by positivity)]
  refine ⟨?_, ?_⟩
  · intro i
    apply summable_of_ne_finset_zero (s := {i})
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [gammaFactorialObservabilityKernel, hji.symm]
  · convert summable_normSq_gammaPeriodicConormalCoefficient using 1
    funext i
    rw [tsum_eq_single i]
    · simp [gammaFactorialObservabilityKernel]
    · intro j hji
      simp [gammaFactorialObservabilityKernel, hji.symm]

/-- The source-normalized Gamma factorial reporter on the square-summable clock completion. -/
def gammaFactorialObservabilityOperator :
    lp (fun _ : ℕ ↦ ℂ) 2 →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2 :=
  HilbertSchmidt.toOperator gammaFactorialObservabilityKernel_isHS

/-- The canonical clock basis diagonalizes the Gamma factorial reporter. -/
theorem gammaFactorialObservabilityOperator_single (n j : ℕ) :
    gammaFactorialObservabilityOperator (lp.single 2 n 1) j =
      if j = n then gammaPeriodicConormalCoefficient n else 0 := by
  rw [gammaFactorialObservabilityOperator,
    HilbertSchmidt.toOperator_single gammaFactorialObservabilityKernel_isHS]
  by_cases h : j = n
  · subst j
    simp [gammaFactorialObservabilityKernel]
  · simp [gammaFactorialObservabilityKernel, h]

/-- The Gamma factorial reporter is compact. -/
theorem gammaFactorialObservabilityOperator_isCompact :
    IsCompactOperator gammaFactorialObservabilityOperator :=
  (HilbertSchmidt.isHilbertSchmidt_toOperator
    gammaFactorialObservabilityKernel_isHS).isCompactOperator

theorem gammaPeriodicConormalCoefficient_ne_zero (n : ℕ) :
    gammaPeriodicConormalCoefficient n ≠ 0 := by
  simp [gammaPeriodicConormalCoefficient, Nat.factorial_ne_zero]

/-- Coordinatewise, the reporter is multiplication by the Gamma source conormal. -/
theorem gammaFactorialObservabilityOperator_apply
    (x : lp (fun _ : ℕ ↦ ℂ) 2) (n : ℕ) :
    gammaFactorialObservabilityOperator x n =
      gammaPeriodicConormalCoefficient n * x n := by
  rw [gammaFactorialObservabilityOperator,
    HilbertSchmidt.toOperator_apply gammaFactorialObservabilityKernel_isHS,
    tsum_eq_single n]
  · simp [gammaFactorialObservabilityKernel]
  · intro j hjn
    simp [gammaFactorialObservabilityKernel, hjn.symm]

/-- Every clock coordinate is nonzero, so the complete factorial reporter is algebraically
injective. -/
theorem gammaFactorialObservabilityOperator_injective :
    Function.Injective gammaFactorialObservabilityOperator := by
  intro x y hxy
  apply lp.ext
  funext n
  have hn := congrArg
    (fun z : lp (fun _ : ℕ ↦ ℂ) 2 ↦ z n) hxy
  change gammaFactorialObservabilityOperator x n =
    gammaFactorialObservabilityOperator y n at hn
  rw [gammaFactorialObservabilityOperator_apply,
    gammaFactorialObservabilityOperator_apply] at hn
  exact mul_left_cancel₀ (gammaPeriodicConormalCoefficient_ne_zero n) hn

/-- The exact observation norm of the `n`-th unit clock is `1 / (n + 1)!`. -/
theorem norm_gammaFactorialObservabilityOperator_single (n : ℕ) :
    ‖gammaFactorialObservabilityOperator (lp.single 2 n 1)‖ =
      ‖gammaPeriodicConormalCoefficient n‖ := by
  have heq : gammaFactorialObservabilityOperator (lp.single 2 n 1) =
      gammaPeriodicConormalCoefficient n • lp.single 2 n 1 := by
    apply lp.ext
    funext j
    rw [gammaFactorialObservabilityOperator_apply]
    by_cases h : j = n
    · subst j
      simp
    · change gammaPeriodicConormalCoefficient j *
          (Pi.single n (1 : ℂ) : ℕ → ℂ) j =
        gammaPeriodicConormalCoefficient n *
          (Pi.single n (1 : ℂ) : ℕ → ℂ) j
      rw [Pi.single_eq_of_ne h]
      simp
  rw [heq, norm_smul, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  norm_num

/-- The source-normalized factorial observation scales tend to zero. -/
theorem tendsto_norm_gammaPeriodicConormalCoefficient_zero :
    Tendsto (fun n ↦ ‖gammaPeriodicConormalCoefficient n‖) atTop (nhds 0) := by
  have hbase : Summable (fun n : ℕ ↦ (1 : ℝ) / (n.factorial : ℝ)) := by
    simpa using Real.summable_pow_div_factorial 1
  have htailSum : Summable
      (fun n : ℕ ↦ (1 : ℝ) / ((n + 1).factorial : ℝ)) := by
    simpa [Nat.succ_eq_add_one] using! hbase.comp_injective Nat.succ_injective
  have htail : Tendsto
      (fun n : ℕ ↦ (1 : ℝ) / ((n + 1).factorial : ℝ)) atTop (nhds 0) :=
    htailSum.tendsto_atTop_zero
  convert htail using 1
  funext n
  rw [gammaPeriodicConormalCoefficient, norm_div, norm_one, Complex.norm_natCast]

/-- The clock basis is an explicit normalized approximate-null sequence. -/
theorem gammaFactorialObservabilityOperator_hasApproximateUnitKernel :
    HasApproximateUnitKernel gammaFactorialObservabilityOperator := by
  refine ⟨fun n ↦ lp.single 2 n (1 : ℂ), ?_, ?_⟩
  · intro n
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    norm_num
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    convert tendsto_norm_gammaPeriodicConormalCoefficient_zero using 1
    funext n
    rw [norm_gammaFactorialObservabilityOperator_single]

/-- The complete Gamma factorial reporter has nonclosed range despite being injective. -/
theorem gammaFactorialObservabilityOperator_not_isClosed_range :
    ¬ IsClosed (Set.range gammaFactorialObservabilityOperator) :=
  (hasApproximateUnitKernel_iff_not_isClosed_range
    gammaFactorialObservabilityOperator
    gammaFactorialObservabilityOperator_injective).mp
      gammaFactorialObservabilityOperator_hasApproximateUnitKernel

/-- Gamma's source-normalized factorial reporter is algebraically conservative but not stably
conservative. -/
theorem gammaFactorialObservabilityOperator_not_stablyConservative :
    ¬ ∃ K, AntilipschitzWith K gammaFactorialObservabilityOperator := by
  intro hstable
  exact gammaFactorialObservabilityOperator_not_isClosed_range
    ((gammaFactorialObservabilityOperator.isClosed_range_iff_antilipschitz_of_injective
      gammaFactorialObservabilityOperator_injective).mpr hstable)

end

end GaloisForLFunctions.HTGeometry
