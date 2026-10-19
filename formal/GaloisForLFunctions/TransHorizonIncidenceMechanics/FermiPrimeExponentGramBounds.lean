import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Classical prime-exponent Gram bounds for Fermi observability

The kernel `r ^ |i-j|` has dimension-independent lower and upper bounds
`(1-r)/(1+r)` and `(1+r)/(1-r)`. This is a classical ingredient, not a new
THIM contribution. The native use is `r = 1/p` in the odd-prime GCD Gram
factorization for dyadic-antichain coefficients.

Finite induction retains the squared weighted head as a potential. The lower
and upper induction defects are respectively
`r*(1-r)*(x₀+(1+r)*H)^2` and `r*(1+r)*(x₀-(1-r)*H)^2`.
-/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

/-- Classical geometric Gram form on one prime-exponent coordinate. -/
def primeExponentGramEnergy (r : ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, r ^ ((i.val - j.val) + (j.val - i.val)) * x i * x j

private def gramHead (r : ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, r ^ i.val * x i

private theorem gramHead_succ (r : ℝ) {n : ℕ} (x : Fin (n+1) → ℝ) :
    gramHead r x = x 0 + r * gramHead r (fun i => x i.succ) := by
  simp only [gramHead, Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_mul,
    Fin.val_succ, pow_succ, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem gramEnergy_succ (r : ℝ) {n : ℕ} (x : Fin (n+1) → ℝ) :
    primeExponentGramEnergy r x = (x 0)^2 +
      2*r*x 0*gramHead r (fun i => x i.succ) +
      primeExponentGramEnergy r (fun i => x i.succ) := by
  have hleft : (∑ i : Fin n, r ^ (i.val+1) * x 0 * x i.succ) =
      r*x 0*gramHead r (fun i => x i.succ) := by
    simp only [gramHead, Finset.mul_sum, pow_succ]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hright : (∑ i : Fin n, r ^ (i.val+1) * x i.succ * x 0) =
      r*x 0*gramHead r (fun i => x i.succ) := by
    simp only [gramHead, Finset.mul_sum, pow_succ]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [primeExponentGramEnergy, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Nat.zero_sub, Nat.sub_zero, Nat.zero_add, Nat.add_zero,
    Nat.succ_sub_succ_eq_sub, pow_zero, one_mul, Finset.sum_add_distrib] at *
  rw [hleft, hright]
  ring

private theorem gramEnergy_certificates (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {n : ℕ} (x : Fin n → ℝ) :
    (1-r)*(∑ i, (x i)^2) + r*(1+r)*(gramHead r x)^2 ≤
        (1+r)*primeExponentGramEnergy r x ∧
    (1-r)*primeExponentGramEnergy r x + r*(1-r)*(gramHead r x)^2 ≤
        (1+r)*(∑ i, (x i)^2) := by
  induction n with
  | zero => simp [primeExponentGramEnergy, gramHead]
  | succ n ih =>
    obtain ⟨hl, hu⟩ := ih (fun i => x i.succ)
    rw [gramHead_succ, gramEnergy_succ, Fin.sum_univ_succ]
    have hlow : 0 ≤ r*(1-r)*(x 0+(1+r)*gramHead r (fun i => x i.succ))^2 :=
      mul_nonneg (mul_nonneg hr (sub_nonneg.mpr hr1)) (sq_nonneg _)
    have hupp : 0 ≤ r*(1+r)*(x 0-(1-r)*gramHead r (fun i => x i.succ))^2 :=
      mul_nonneg (mul_nonneg hr (by linarith)) (sq_nonneg _)
    constructor <;> nlinarith

/-- Classical two-sided geometric Gram bound, uniform in exponent depth. -/
theorem primeExponentGramEnergy_bounds (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    {n : ℕ} (x : Fin n → ℝ) :
    (1-r)/(1+r)*(∑ i, (x i)^2) ≤ primeExponentGramEnergy r x ∧
      primeExponentGramEnergy r x ≤ (1+r)/(1-r)*(∑ i, (x i)^2) := by
  obtain ⟨hl, hu⟩ := gramEnergy_certificates r hr hr1.le x
  have hplus : 0 < 1+r := by linarith
  have hminus : 0 < 1-r := by linarith
  have hlow : 0 ≤ r*(1+r)*(gramHead r x)^2 := by positivity
  have hupp : 0 ≤ r*(1-r)*(gramHead r x)^2 := by positivity
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ hplus]
    nlinarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ hminus]
    nlinarith

end GaloisForLFunctions.TransHorizonIncidenceMechanics
