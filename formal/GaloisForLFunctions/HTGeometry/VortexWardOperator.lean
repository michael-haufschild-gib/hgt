import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
# Degree-diagonal Ward operators and singular coefficient recurrences

The recurrence-to-operator mechanism of arXiv:2609.09298, equations (2.120)–(2.123),
requires both the degree-zero boundary and singular denominators to be retained.
For explicit products of step ratios, the residual is exactly the constant boundary minus
terms supported at zero denominator symbols. A second denominator factor kills every such
term; the Euler operator removes the remaining constant. All identities include singular
parameters and use formal power series, so no analytic convergence assumption is required.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open PowerSeries

def vortexDiagonal (a : ℕ → ℂ) (F : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => a n * coeff n F

def vortexWard (a b : ℕ → ℂ) (F : PowerSeries ℂ) : PowerSeries ℂ :=
  vortexDiagonal a F - X * vortexDiagonal b F

@[simp] theorem coeff_vortexDiagonal (a : ℕ → ℂ) (F : PowerSeries ℂ) (n : ℕ) :
    coeff n (vortexDiagonal a F) = a n * coeff n F := coeff_mk _ _

@[simp] theorem constantCoeff_vortexDiagonal (a : ℕ → ℂ) (F : PowerSeries ℂ) :
    constantCoeff (vortexDiagonal a F) = a 0 * constantCoeff F := by
  simpa only [coeff_zero_eq_constantCoeff] using coeff_vortexDiagonal a F 0

theorem vortexDiagonal_comp (a b : ℕ → ℂ) (F : PowerSeries ℂ) :
    vortexDiagonal a (vortexDiagonal b F) = vortexDiagonal (fun n => a n * b n) F := by
  ext n
  simp [mul_assoc]

theorem vortexDiagonal_X (a : ℕ → ℂ) (F : PowerSeries ℂ) :
    vortexDiagonal a (X * F) = X * vortexDiagonal (fun n => a (n + 1)) F := by
  ext n
  cases n <;> simp [coeff_succ_X_mul]

theorem vortexDiagonal_rescale (q : ℂ) (F : PowerSeries ℂ) :
    vortexDiagonal (fun n => q ^ n) F = rescale q F := by
  ext n
  simp [coeff_rescale]

theorem vortexDiagonal_euler (F : PowerSeries ℂ) :
    vortexDiagonal (fun n => (n : ℂ)) F = X * derivative ℂ F := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp [coeff_succ_X_mul, coeff_derivative, mul_comm]

theorem vortexWard_constant_iff (a b : ℕ → ℂ) (F : PowerSeries ℂ) :
    vortexWard a b F = C (a 0 * coeff 0 F) ↔
      ∀ n, a (n + 1) * coeff (n + 1) F = b n * coeff n F := by
  constructor
  · intro h n
    have hn := congrArg (coeff (n + 1)) h
    simpa [vortexWard, coeff_succ_X_mul, sub_eq_zero] using hn
  · intro h
    ext n
    cases n with
    | zero => simp [vortexWard]
    | succ n => simp [vortexWard, coeff_succ_X_mul, h n]

theorem vortexWard_zero_iff (a b : ℕ → ℂ) (F : PowerSeries ℂ) :
    vortexWard a b F = 0 ↔
      a 0 * coeff 0 F = 0 ∧
      ∀ n, a (n + 1) * coeff (n + 1) F = b n * coeff n F := by
  constructor
  · intro h
    constructor
    · have hn := congrArg (coeff 0) h
      simpa [vortexWard] using hn
    · intro n
      have hn := congrArg (coeff (n + 1)) h
      simpa [vortexWard, coeff_succ_X_mul, sub_eq_zero] using hn
  · rintro ⟨h0, hs⟩
    rw [(vortexWard_constant_iff a b F).2 hs, h0, map_zero]

def vortexProductSeries (r : ℕ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => ∏ k ∈ Finset.range n, r k

def vortexFactorialSeries (r : ℕ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => (∏ k ∈ Finset.range n, r k) / (n.factorial : ℂ)

theorem vortexProductSeries_ward (r : ℕ → ℂ) :
    vortexWard (fun _ => 1) r (vortexProductSeries r) = 1 := by
  have h := (vortexWard_constant_iff (fun _ => 1) r (vortexProductSeries r)).2
    (fun n => by simp [vortexProductSeries, Finset.prod_range_succ, mul_comm])
  simpa [vortexProductSeries] using h

theorem vortexFactorialSeries_recurrence (r : ℕ → ℂ) (n : ℕ) :
    (n + 1 : ℂ) * coeff (n + 1) (vortexFactorialSeries r) =
      r n * coeff n (vortexFactorialSeries r) := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [vortexFactorialSeries, coeff_mk, Finset.prod_range_succ, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

theorem vortexFactorialSeries_ward (r : ℕ → ℂ) :
    vortexWard (fun n => (n : ℂ)) r (vortexFactorialSeries r) = 0 := by
  apply (vortexWard_zero_iff _ _ _).2
  exact ⟨by simp, fun n => by simpa using vortexFactorialSeries_recurrence r n⟩

theorem vortexFactorialSeries_derivative (r : ℕ → ℂ) :
    derivative ℂ (vortexFactorialSeries r) = vortexDiagonal r (vortexFactorialSeries r) := by
  ext n
  simpa [coeff_derivative, mul_comm] using vortexFactorialSeries_recurrence r n

theorem vortexWard_rescale (a b : ℕ → ℂ) (q : ℂ) (F : PowerSeries ℂ) :
    vortexWard a (fun n => q * b n) (rescale q F) = rescale q (vortexWard a b F) := by
  ext n
  cases n with
  | zero => simp only [vortexWard, coeff_rescale, map_sub, coeff_vortexDiagonal,
      coeff_zero_X_mul, pow_zero, one_mul, mul_zero, sub_zero]
  | succ n =>
    simp only [vortexWard, coeff_rescale, map_sub, coeff_vortexDiagonal,
      coeff_succ_X_mul, pow_succ]
    ring

/-- Product of the degree-by-degree numerator/denominator ratios, with Lean's total inverse. -/
def vortexRatioSeries (a b : ℕ → ℂ) : PowerSeries ℂ :=
  vortexProductSeries (fun n => b n / a (n + 1))

/-- The precise correction at singular denominators. -/
def vortexResonanceSeries (a b : ℕ → ℂ) : PowerSeries ℂ :=
  X * PowerSeries.mk (fun n =>
    if a (n + 1) = 0 then b n * coeff n (vortexRatioSeries a b) else 0)

theorem vortexRatioSeries_recurrence (a b : ℕ → ℂ) (n : ℕ) :
    coeff (n + 1) (vortexRatioSeries a b) =
      b n / a (n + 1) * coeff n (vortexRatioSeries a b) := by
  simp only [vortexRatioSeries, vortexProductSeries, coeff_mk, Finset.prod_range_succ]
  exact mul_comm _ _

/-- The Ward residual consists exactly of the degree-zero term and resonant-degree defects. -/
theorem vortexRatioSeries_exact_residual (a b : ℕ → ℂ) :
    vortexWard a b (vortexRatioSeries a b) = C (a 0) - vortexResonanceSeries a b := by
  ext n
  cases n with
  | zero => simp [vortexWard, vortexRatioSeries, vortexProductSeries, vortexResonanceSeries]
  | succ n =>
    simp only [vortexWard, map_sub, coeff_vortexDiagonal, vortexResonanceSeries,
      coeff_succ_X_mul, coeff_mk, coeff_C, Nat.succ_ne_zero, if_false, zero_sub,
      vortexRatioSeries_recurrence]
    by_cases h : a (n + 1) = 0
    · simp [h]
    · rw [if_neg h]
      field_simp
      ring

/-- Multiplication by the denominator symbol removes every resonant-degree defect. -/
theorem vortexDiagonal_resonance (a b : ℕ → ℂ) :
    vortexDiagonal a (vortexResonanceSeries a b) = 0 := by
  ext n
  cases n with
  | zero => simp [vortexResonanceSeries]
  | succ n =>
    simp only [coeff_vortexDiagonal, vortexResonanceSeries, coeff_succ_X_mul,
      coeff_mk, map_zero]
    split_ifs with h <;> simp [h]

/-- A second denominator factor yields a closed Ward identity even at singular parameters. -/
theorem vortexRatioSeries_regularized_ward (a b : ℕ → ℂ) :
    vortexDiagonal a (vortexWard a b (vortexRatioSeries a b)) = C (a 0 ^ (2 : ℕ)) := by
  rw [vortexRatioSeries_exact_residual]
  ext n
  rw [coeff_vortexDiagonal, map_sub, coeff_C, coeff_C]
  cases n with
  | zero => simp [vortexResonanceSeries, pow_two]
  | succ n =>
    have h := congrArg (coeff (n + 1)) (vortexDiagonal_resonance a b)
    simp only [coeff_vortexDiagonal, map_zero] at h
    simpa only [Nat.succ_ne_zero, if_false, zero_sub, mul_neg] using neg_eq_zero.mpr h

/-- The Euler operator also kills the remaining degree-zero boundary term. -/
theorem vortexRatioSeries_closed_annihilator (a b : ℕ → ℂ) :
    vortexDiagonal (fun n => (n : ℂ))
      (vortexDiagonal a (vortexWard a b (vortexRatioSeries a b))) = 0 := by
  rw [vortexRatioSeries_regularized_ward]
  ext n
  rw [coeff_vortexDiagonal, coeff_C, map_zero]
  cases n <;> simp

end
end GaloisForLFunctions.HTGeometry
