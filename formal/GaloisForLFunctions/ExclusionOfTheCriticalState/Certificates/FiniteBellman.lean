import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Residual certificates for finite descending chains

A chain with edge costs `c n` has value `∑ j < n, c j`. Its stopped Bellman
operator resets the endpoint to zero. Endpoint error and edge residuals give an
exact reconstruction, a sharp absolute error certificate, and finite recovery.
Costs may have either sign, as required for finite probe energies.

This is the finite-chain mechanism of Theorem 5 and Proposition 6 of
H. Nick Zinat Matin, *A Derivative-Free Bellman Equation for Dynamic
Time-to-Collision*, arXiv:2611.16663.
-/

open scoped BigOperators

namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FiniteBellman

noncomputable section

/-- Accumulated edge cost from a node down to the absorbing endpoint. -/
def value (c : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, c j

/-- A stopped step resets the endpoint, irrespective of the candidate there. -/
def step (c W : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => c n + W n

/-- Signed edge defect, excluding the separately recorded endpoint error. -/
def residual (c W : ℕ → ℝ) (n : ℕ) : ℝ := W (n + 1) - c n - W n

/-- Absolute endpoint error plus the variation of the residual along the chain. -/
def certificate (c W : ℕ → ℝ) (n : ℕ) : ℝ :=
  |W 0| + ∑ j ∈ Finset.range n, |residual c W j|

@[simp] theorem value_zero (c : ℕ → ℝ) : value c 0 = 0 := by simp [value]

@[simp] theorem value_succ (c : ℕ → ℝ) (n : ℕ) :
    value c (n + 1) = value c n + c n := Finset.sum_range_succ _ _

/-- Error is exactly endpoint error plus signed residual accumulation. -/
theorem error_eq (c W : ℕ → ℝ) (n : ℕ) :
    W n - value c n = W 0 + ∑ j ∈ Finset.range n, residual c W j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [value_succ, Finset.sum_range_succ]
    unfold residual
    linarith only [ih]

/-- Residual control is local to the complete chain and needs no global bound. -/
theorem abs_error_le_certificate (c W : ℕ → ℝ) (n : ℕ) :
    |W n - value c n| ≤ certificate c W n := by
  rw [error_eq]
  exact (abs_add_le _ _).trans
    (add_le_add_left (Finset.abs_sum_le_sum_abs _ _) _)

/-- Both signs of the value are certified from the same residual variation. -/
theorem value_mem_certificate_interval (c W : ℕ → ℝ) (n : ℕ) :
    W n - certificate c W n ≤ value c n ∧
      value c n ≤ W n + certificate c W n := by
  have h := abs_le.mp (abs_error_le_certificate c W n)
  constructor <;> linarith only [h.1, h.2]

/-- Residual and endpoint data recover every candidate uniquely. -/
theorem reconstruction (c W : ℕ → ℝ) (n : ℕ) :
    W n = W 0 + value (fun j => c j + residual c W j) n := by
  have h := error_eq c W n
  simp only [value, Finset.sum_add_distrib]
  unfold value at h
  linarith only [h]

/-- Arbitrary prescribed edge defects have an explicit realization. -/
theorem residual_reconstruction (c r : ℕ → ℝ) (b : ℝ) :
    residual c (fun n => b + value (fun j => c j + r j) n) = r := by
  funext n
  simp only [residual, value_succ]
  ring

/-- Endpoint and residual coordinates form an affine bijection on all sequences. -/
def residualEquiv (c : ℕ → ℝ) : (ℕ → ℝ) ≃ (ℝ × (ℕ → ℝ)) where
  toFun W := (W 0, residual c W)
  invFun p n := p.1 + value (fun j => c j + p.2 j) n
  left_inv W := funext fun n => (reconstruction c W n).symm
  right_inv p := by
    rcases p with ⟨b, r⟩
    simp only [value_zero, add_zero, residual_reconstruction]

/-- The stopped operator has exactly one fixed point, even for signed costs. -/
theorem fixed_iff (c W : ℕ → ℝ) : step c W = W ↔ W = value c := by
  constructor
  · intro h
    have h0 : W 0 = 0 := (congrFun h 0).symm
    have hr : residual c W = 0 := by
      funext n
      have hn := congrFun h (n + 1)
      change c n + W n = W (n + 1) at hn
      simp only [residual, Pi.zero_apply]
      linarith only [hn]
    funext n
    have he := error_eq c W n
    rw [h0, hr] at he
    simpa using he
  · rintro rfl
    funext n
    cases n with
    | zero => simp [step]
    | succ n => simp only [step, value_succ, add_comm]

/-- Before absorption, iteration transports the initial candidate from the last node. -/
theorem iterate_before_endpoint (c W : ℕ → ℝ) (k n : ℕ) :
    (step c)^[k] W (n + k) = value c (n + k) - value c n + W n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change c (n + k) + (step c)^[k] W (n + k) = _
    rw [ih, show n + (k + 1) = (n + k) + 1 by omega, value_succ]
    ring

/-- Exactly at the chain length, the initial endpoint error is still present. -/
theorem iterate_at_endpoint (c W : ℕ → ℝ) (n : ℕ) :
    (step c)^[n] W n = value c n + W 0 := by
  simpa using iterate_before_endpoint c W n 0

/-- One extra sweep erases arbitrary endpoint data and gives exact recovery. -/
theorem iterate_exact (c W : ℕ → ℝ) (n : ℕ) :
    (step c)^[n + 1] W n = value c n := by
  rw [Function.iterate_succ_apply, iterate_at_endpoint]
  simp only [step, add_zero]

/-- The extra sweep is necessary exactly when endpoint data violate absorption. -/
theorem iterate_exact_at_length_iff (c W : ℕ → ℝ) (n : ℕ) :
    (step c)^[n] W n = value c n ↔ W 0 = 0 := by
  rw [iterate_at_endpoint, add_eq_left]

/-- No coefficient in the endpoint-plus-residual certificate can be reduced. -/
theorem certificate_sharp (c : ℕ → ℝ) (b δ : ℝ) (n : ℕ) :
    let W := fun j => |b| + value (fun i => c i + |δ|) j
    |W n - value c n| = certificate c W n ∧
      certificate c W n = |b| + (n : ℝ) * |δ| := by
  dsimp
  have hr := residual_reconstruction c (fun _ => |δ|) |b|
  have he := error_eq c (fun j => |b| + value (fun i => c i + |δ|) j) n
  simp only [value_zero, add_zero, hr, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at he
  have hc : certificate c (fun j => |b| + value (fun i => c i + |δ|) j) n =
      |b| + (n : ℝ) * |δ| := by
    simp only [certificate, value_zero, add_zero, abs_abs, hr, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  exact ⟨by rw [he, hc, abs_of_nonneg (by positivity)], hc⟩

#print axioms error_eq
#print axioms abs_error_le_certificate
#print axioms residualEquiv
#print axioms fixed_iff
#print axioms iterate_exact
#print axioms certificate_sharp

end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FiniteBellman
