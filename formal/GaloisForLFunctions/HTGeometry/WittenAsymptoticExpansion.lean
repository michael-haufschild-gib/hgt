import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Basic

/-!
# Exact finite phase-polynomial asymptotics

A finite stationary-phase formula has one unit complex phase for every contributing critical
component and a polynomial amplitude in the integral level.  This file proves two consequences of
that exact formula: the remainder is zero to every inverse-power order, and the resulting sequence
has polynomial growth.  These are the analytic conclusions required of the exact phase-polynomial
cases of Witten's asymptotic-expansion conjecture.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- A finite Chern--Simons phase packet with polynomial level amplitudes. -/
def finitePhasePolynomial {ι : Type*} (s : Finset ι) (phase : ι → ℂ)
    (coefficient : ι → ℕ → ℂ) (degree : ℕ) (n : ℕ) : ℂ :=
  ∑ i ∈ s, phase i ^ n *
    ∑ j ∈ Finset.range (degree + 1), coefficient i j * (n : ℂ) ^ j

/-- Exact phase-polynomial representation of a level-indexed quantum invariant. -/
def HasExactFinitePhasePolynomialExpansion {ι : Type*} (Z : ℕ → ℂ)
    (s : Finset ι) (phase : ι → ℂ) (coefficient : ι → ℕ → ℂ)
    (degree : ℕ) : Prop :=
  Z = finitePhasePolynomial s phase coefficient degree

/-- The polynomial phase model approximates the invariant to every inverse-power order. -/
def HasAllOrdersFinitePhasePolynomialRemainder {ι : Type*} (Z : ℕ → ℂ)
    (s : Finset ι) (phase : ι → ℂ) (coefficient : ι → ℕ → ℂ)
    (degree : ℕ) : Prop :=
  ∀ N : ℕ,
    (fun n : ℕ => Z n - finitePhasePolynomial s phase coefficient degree n) =O[atTop]
      fun n : ℕ => ((n : ℂ) ^ N)⁻¹

/-- Every exact finite phase-polynomial formula has identically zero remainder, hence is an
all-orders asymptotic expansion along integral levels. -/
theorem HasExactFinitePhasePolynomialExpansion.hasAllOrdersRemainder
    {ι : Type*} {Z : ℕ → ℂ} {s : Finset ι} {phase : ι → ℂ}
    {coefficient : ι → ℕ → ℂ} {degree : ℕ}
    (hZ : HasExactFinitePhasePolynomialExpansion Z s phase coefficient degree) :
    HasAllOrdersFinitePhasePolynomialRemainder Z s phase coefficient degree := by
  intro N
  have hzero : (fun n : ℕ => Z n - finitePhasePolynomial s phase coefficient degree n)
      = fun _ : ℕ => (0 : ℂ) := by
    funext n
    rw [hZ]
    ring
  rw [hzero]
  exact Asymptotics.isBigO_zero _ _

/-- An exact finite unit-phase polynomial formula grows at most polynomially in its level. -/
theorem finitePhasePolynomial_isBigO {ι : Type*} (s : Finset ι) (phase : ι → ℂ)
    (coefficient : ι → ℕ → ℂ) (degree : ℕ)
    (hphase : ∀ i ∈ s, ‖phase i‖ = 1) :
    finitePhasePolynomial s phase coefficient degree =O[atTop]
      fun n : ℕ => (n : ℂ) ^ degree := by
  refine Asymptotics.IsBigO.of_bound
    (∑ i ∈ s, ∑ j ∈ Finset.range (degree + 1), ‖coefficient i j‖) ?_
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hnorm : 1 ≤ ‖(n : ℂ)‖ := by
    rw [Complex.norm_natCast]
    exact_mod_cast hn
  calc
    ‖finitePhasePolynomial s phase coefficient degree n‖
        ≤ ∑ i ∈ s, ‖phase i ^ n *
            ∑ j ∈ Finset.range (degree + 1), coefficient i j * (n : ℂ) ^ j‖ :=
          norm_sum_le _ _
    _ = ∑ i ∈ s, ‖∑ j ∈ Finset.range (degree + 1),
            coefficient i j * (n : ℂ) ^ j‖ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [norm_mul, norm_pow, hphase i hi, one_pow, one_mul]
    _ ≤ ∑ i ∈ s, ∑ j ∈ Finset.range (degree + 1),
          ‖coefficient i j‖ * ‖(n : ℂ) ^ degree‖ := by
          apply Finset.sum_le_sum
          intro i hi
          refine le_trans (norm_sum_le _ _) ?_
          apply Finset.sum_le_sum
          intro j hj
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [norm_pow, norm_pow]
          exact pow_le_pow_right₀ hnorm (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    _ = (∑ i ∈ s, ∑ j ∈ Finset.range (degree + 1), ‖coefficient i j‖) *
          ‖(n : ℂ) ^ degree‖ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]

/-- An exact phase-polynomial formula supplies the polynomial bound predicted by Witten's
asymptotic-expansion conjecture. -/
theorem HasExactFinitePhasePolynomialExpansion.isBigO {ι : Type*} {Z : ℕ → ℂ}
    {s : Finset ι} {phase : ι → ℂ} {coefficient : ι → ℕ → ℂ} {degree : ℕ}
    (hZ : HasExactFinitePhasePolynomialExpansion Z s phase coefficient degree)
    (hphase : ∀ i ∈ s, ‖phase i‖ = 1) :
    Z =O[atTop] fun n : ℕ => (n : ℂ) ^ degree := by
  rw [hZ]
  exact finitePhasePolynomial_isBigO s phase coefficient degree hphase

end GaloisForLFunctions.HTGeometry
