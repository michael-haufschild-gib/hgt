import GaloisForLFunctions.RHTower.RoutePPrimitiveJointDepthGammaJuliaLogKreinMatrixCompletion
import GaloisForLFunctions.RHTower.BurnolPrimeLogSummability

/-!
# Route P primitive Gamma--Julia raw cofinal trace obstruction

P-G105F converts the P-G186 reciprocal-promotion source Gram `G` to primitive coordinates by the
prime-log congruence `L G L`.  The two prime logarithms in this congruence cancel exactly the
`(log p)^{-2}` regularizer in the cubic source weight.  The resulting diagonal trace density is

```text
(1/4) p^{-(e+1)} (e+1)^{-3}.
```

In particular, the depth-zero density is exactly `1/(4p)`.  Euler's divergent prime harmonic
series therefore occurs as a literal principal slice of the actual finite matrix traces.  The raw
all-cell log-conjugated source cannot be trace class, and its positive finite-packet traces have no
uniform upper bound.

This falsifies naive trace-class cofinalization of P-G105F.  Its positive survivor is sharper than
the no-go: the obstruction has exact Euler-pole coefficient `1/4`, identifying the counterterm
which a source-derived polar/Stokes completion must cancel.  Finite signed bivariate stability from
P-G105G remains intact; this file does not construct the required renormalized cofinal determinant
or identify it with Xi.
-/

open Complex Matrix

namespace RHTower

noncomputable section

/-- Diagonal trace density after literal prime-log congruence of the P-G186 source Gram. -/
def routePPrimitiveGammaJuliaLogCofinalTraceWeight (pe : Nat.Primes × ℕ) : ℝ :=
  Real.log (pe.1 : ℝ) ^ (2 : ℕ) * routePPrimitiveBaseCauchyCubicWeight pe

/-- Exact cancellation of both source logarithmic regularizers. -/
theorem routePPrimitiveGammaJuliaLogCofinalTraceWeight_eq
    (pe : Nat.Primes × ℕ) :
    routePPrimitiveGammaJuliaLogCofinalTraceWeight pe =
      (1 / 4 : ℝ) * ((pe.1 : ℝ)⁻¹) ^ (pe.2 + 1) *
        (((pe.2 : ℝ) + 1) ^ (3 : ℕ))⁻¹ := by
  rw [routePPrimitiveGammaJuliaLogCofinalTraceWeight,
    routePPrimitiveBaseCauchyCubicWeight,
    xiGammaEulerPrimitiveCubicLogMomentWeight, invNatLogSq]
  have hp : (0 : ℝ) < pe.1 := by exact_mod_cast pe.1.property.pos
  have hlog : Real.log (pe.1 : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast pe.1.property.one_lt)).ne'
  field_simp [hp.ne', hlog]
  rw [pow_succ]
  field_simp [hp.ne']
  ring

/-- The depth-zero survivor is exactly one quarter of the prime harmonic density. -/
theorem routePPrimitiveGammaJuliaLogCofinalTraceWeight_prime_zero
    (p : Nat.Primes) :
    routePPrimitiveGammaJuliaLogCofinalTraceWeight (p, 0) =
      (1 / 4 : ℝ) * (1 / (p : ℝ)) := by
  rw [routePPrimitiveGammaJuliaLogCofinalTraceWeight_eq]
  norm_num

/-- Every cell contributes nonnegative raw trace density. -/
theorem routePPrimitiveGammaJuliaLogCofinalTraceWeight_nonneg
    (pe : Nat.Primes × ℕ) :
    0 ≤ routePPrimitiveGammaJuliaLogCofinalTraceWeight pe := by
  rw [routePPrimitiveGammaJuliaLogCofinalTraceWeight_eq]
  positivity

/-- Exact finite Euler-residue normalization on every set of depth-zero prime cells. -/
theorem routePPrimitiveGammaJuliaLogCofinalTraceWeight_finitePrimeResidue
    (s : Finset Nat.Primes) :
    4 * ∑ p ∈ s, routePPrimitiveGammaJuliaLogCofinalTraceWeight (p, 0) =
      ∑ p ∈ s, 1 / (p : ℝ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [routePPrimitiveGammaJuliaLogCofinalTraceWeight_prime_zero]
  ring

/-- Actual P-G186 finite log-conjugated Gram traces are sums of the exact cofinal density. -/
theorem routePPrimitiveGammaJuliaLogConjugate_trace {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    (routePPrimitiveJointDepthPrimeLogConjugate pe
      (routePPrimitiveBurnolWindowGramMatrix pe kappa)).trace.re =
      ∑ i, routePPrimitiveGammaJuliaLogCofinalTraceWeight (pe i) := by
  rw [Matrix.trace, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Matrix.diag_apply,
    routePPrimitiveJointDepthPrimeLogConjugate_apply,
    routePPrimitiveBurnolWindowGramMatrix_eq_baseCauchy,
    routePPrimitiveBaseCauchyCubicKernelMatrix_diagonal (by norm_num),
    routePPrimitiveGammaJuliaLogCofinalTraceWeight]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  ring

/-- The exact cofinal trace density is not summable on prime-depth cells. -/
theorem routePPrimitiveGammaJuliaLogCofinalTraceWeight_not_summable :
    ¬ Summable routePPrimitiveGammaJuliaLogCofinalTraceWeight := by
  intro hsum
  have hslice : Summable (fun p : Nat.Primes =>
      routePPrimitiveGammaJuliaLogCofinalTraceWeight (p, 0)) :=
    hsum.comp_injective (fun _ _ h => Prod.mk.inj h |>.1)
  have hharm : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) := by
    have hscaled : Summable (fun p : Nat.Primes =>
        (4 : ℝ) * routePPrimitiveGammaJuliaLogCofinalTraceWeight (p, 0)) :=
      hslice.mul_left 4
    exact hscaled.congr fun p => by
      rw [routePPrimitiveGammaJuliaLogCofinalTraceWeight_prime_zero]
      ring
  exact burnolNotSummable_prime_one_div hharm

/-- Positive finite-packet trace densities have no uniform upper bound. -/
theorem routePPrimitiveGammaJuliaLogCofinalTraceWeight_finsetSum_unbounded :
    ¬ ∃ C : ℝ, ∀ s : Finset (Nat.Primes × ℕ),
      ∑ pe ∈ s, routePPrimitiveGammaJuliaLogCofinalTraceWeight pe ≤ C := by
  intro hbound
  apply routePPrimitiveGammaJuliaLogCofinalTraceWeight_not_summable
  rcases hbound with ⟨C, hC⟩
  exact summable_of_sum_le
    routePPrimitiveGammaJuliaLogCofinalTraceWeight_nonneg hC

/-- **P-G105H capstone.** The actual finite traces have exact Euler-pole density; its depth-zero
slice has coefficient `1/4`, the all-cell density is not summable, and positive finite sums are
unbounded.  No source, packet, or asymptotic premise is assumed. -/
theorem routePPrimitive_GammaJulia_logCofinalTraceNoGo :
    (∀ (N : ℕ) (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ),
      (routePPrimitiveJointDepthPrimeLogConjugate pe
        (routePPrimitiveBurnolWindowGramMatrix pe kappa)).trace.re =
        ∑ i, routePPrimitiveGammaJuliaLogCofinalTraceWeight (pe i)) ∧
    (∀ p : Nat.Primes,
      routePPrimitiveGammaJuliaLogCofinalTraceWeight (p, 0) =
        (1 / 4 : ℝ) * (1 / (p : ℝ))) ∧
    (¬ Summable routePPrimitiveGammaJuliaLogCofinalTraceWeight) ∧
    (¬ ∃ C : ℝ, ∀ s : Finset (Nat.Primes × ℕ),
      ∑ pe ∈ s, routePPrimitiveGammaJuliaLogCofinalTraceWeight pe ≤ C) := by
  exact ⟨fun _ pe kappa => routePPrimitiveGammaJuliaLogConjugate_trace pe kappa,
    routePPrimitiveGammaJuliaLogCofinalTraceWeight_prime_zero,
    routePPrimitiveGammaJuliaLogCofinalTraceWeight_not_summable,
    routePPrimitiveGammaJuliaLogCofinalTraceWeight_finsetSum_unbounded⟩

end

end RHTower
