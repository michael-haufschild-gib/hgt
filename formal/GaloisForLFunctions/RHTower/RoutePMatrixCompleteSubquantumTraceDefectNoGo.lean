import GaloisForLFunctions.RHTower.FrankensteinMatrixCompleteBoundaryRestriction

/-!
# Route P matrix-complete subquantum trace-defect no-go

The exact Route-P matrix restriction asks a primitive Burnol-window Gram to Loewner-dominate every
finite strict-right Xi conormal Gram. This file classifies its strongest asymptotic approximation
with an additive matrix error.

If RH fails, repeat one strict-right Xi copy through an arbitrary finite target packet. Each target
copy costs at least the exact two-unit Cauchy-cube quantum, whereas injectivity keeps the complete
primitive source trace below one two-unit quantum in total. Loewner trace monotonicity therefore
forces every additive error budget `D` to obey

`2 * N <= routePPrimitiveBaseCauchyCubicTraceBudget + D N`.

Consequently no error whose eventual trace density is strictly below `2` can repair the matrix
restriction off the critical line. Existence of any such approximate restriction is exactly RH.
No positivity, Hermiticity, rank, norm, or entrywise condition is imposed on the error matrix; only
its real trace is charged.
-/

open Complex Matrix
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Matrix-complete Route-P boundary restriction with an arbitrary additive matrix error whose real
trace is charged to `D N`. -/
def RoutePMatrixCompleteBoundaryRestrictionWithTraceDefect
    (D : ℕ → ℝ) : Prop :=
  ∀ {N : ℕ} (q : Fin N → XiRightZeroCopy),
    ∃ (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ)
        (E : Matrix (Fin N) (Fin N) ℂ),
      Function.Injective pe ∧
      E.trace.re ≤ D N ∧
      frankensteinMatrixLoewnerLE
        (routePStrictRightZeroBaseCauchyCubicKernelMatrix q)
        (routePPrimitiveBurnolWindowGramMatrix pe kappa + E)

/-- The aggregate trace error eventually costs strictly less than one two-unit target quantum per
copy. -/
def RoutePEventuallySubquantumTraceDefect (D : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, c < 2 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    D N ≤ c * (N : ℝ)

/-- Existence of a matrix-complete approximate restriction with eventual error density below the
strict-right Cauchy-cube quantum. -/
def RoutePSubquantumTraceDefectBoundaryRestriction : Prop :=
  ∃ D : ℕ → ℝ,
    RoutePEventuallySubquantumTraceDefect D ∧
    RoutePMatrixCompleteBoundaryRestrictionWithTraceDefect D

/-- **Exact defect-density survivor.** If RH fails, every approximate matrix-complete restriction
pays at least `2 * N` through the fixed primitive source budget plus its error trace, on every
packet size. -/
theorem two_mul_natCast_le_routePBudget_add_traceDefect_of_not_rh
    {D : ℕ → ℝ}
    (htransport : RoutePMatrixCompleteBoundaryRestrictionWithTraceDefect D)
    (hRH : ¬ RiemannHypothesis) (N : ℕ) :
    2 * (N : ℝ) ≤ routePPrimitiveBaseCauchyCubicTraceBudget + D N := by
  obtain ⟨q⟩ := nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
  let packet : Fin N → XiRightZeroCopy := fun _ => q
  obtain ⟨pe, kappa, E, hpe, hE, hdom⟩ := htransport packet
  have htarget :
      2 * (N : ℝ) ≤
        (routePStrictRightZeroBaseCauchyCubicKernelMatrix packet).trace.re := by
    rw [re_trace_routePStrictRightZeroBaseCauchyCubicKernelMatrix]
    calc
      2 * (N : ℝ) = ∑ _i : Fin N, (2 : ℝ) := by simp [mul_comm]
      _ ≤ ∑ i : Fin N,
          1 / (4 * (xiRightCenteredZero (packet i)).re ^ 3) := by
            exact Finset.sum_le_sum fun i _ =>
              routePStrictRightZeroBaseCauchyCubicCharge_ge_two (packet i)
  have hsource :=
    re_trace_routePPrimitiveBurnolWindowGramMatrix_le_budget pe hpe kappa
  have htrace := matrix_re_trace_mono_of_frankensteinLoewnerLE hdom
  rw [Matrix.trace_add, Complex.add_re] at htrace
  linarith

/-- **Route-P approximate matrix-completion kill.** A matrix-complete boundary restriction with
eventual additive trace-defect density below the two-unit zero quantum exists exactly under RH. -/
theorem routePSubquantumTraceDefectBoundaryRestriction_iff_riemannHypothesis :
    RoutePSubquantumTraceDefectBoundaryRestriction ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨D, ⟨c, hc, N0, hD⟩, htransport⟩
    by_contra hRH
    have hgap : 0 < 2 - c := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt
      (max (routePPrimitiveBaseCauchyCubicTraceBudget / (2 - c)) (N0 : ℝ))
    have hN0R : (N0 : ℝ) < (N : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hN
    have hN0 : N0 ≤ N := by exact_mod_cast (le_of_lt hN0R)
    have hratio :
        routePPrimitiveBaseCauchyCubicTraceBudget / (2 - c) < (N : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) hN
    have hbudget :
        routePPrimitiveBaseCauchyCubicTraceBudget < (N : ℝ) * (2 - c) :=
      (div_lt_iff₀ hgap).mp hratio
    have hdefect := hD N hN0
    have hquantum :=
      two_mul_natCast_le_routePBudget_add_traceDefect_of_not_rh
        htransport hRH N
    linarith
  · intro hRH
    refine ⟨fun _ => 0, ?_, ?_⟩
    · exact ⟨1, by norm_num, 0, by intro N _; simp⟩
    · intro N q
      obtain ⟨pe, kappa, hpe, hdom⟩ :=
        matrixCompleteBoundaryRestriction_of_riemannHypothesis hRH q
      refine ⟨pe, kappa, 0, hpe, ?_, ?_⟩
      · simp
      · simpa using hdom

end

end RHTower
