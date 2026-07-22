/-
Finite-transverse reflection rigidity: the polynomial shift core.

For a two-generator one-sided flank spectrum, finite support in the transverse generator gives a
finite characteristic polynomial for the exact period shift of the first generator. Reflection
reverses that shift and supplies the reciprocal characteristic polynomial. After their common
fixed root `X - 1` is removed, coprimality of the residual polynomials forces the carrier to be
fixed by the shift.

This module formalizes the reusable algebraic core without hiding the remaining analytic inputs:

* `polyShiftOp` evaluates a scalar polynomial at a linear shift operator;
* `eq_zero_of_coprime_polyShiftOp` is Bézout spectral exclusion;
* `fixed_of_coprime_reflected_shift_annihilators` says that two annihilators whose only common
  characteristic root is the fixed root force exact shift invariance.

The analytic consumer will construct the forward and reflected phase polynomials from the finite
transverse flank expansion, prove their residual coprimality from irrationality, and then invoke
`periodic_spectrum_rigidity`.  No growth hypothesis occurs in this core.
-/
import Mathlib

open Polynomial

noncomputable section

namespace RHTower

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Evaluation of a scalar polynomial at a linear endomorphism.  This is the finite characteristic
operator attached to a shift. -/
def polyShiftOp (S : Module.End K V) (p : Polynomial K) : Module.End K V :=
  p.eval₂ (algebraMap K (Module.End K V)) S

@[simp] theorem polyShiftOp_zero (S : Module.End K V) :
    polyShiftOp S (0 : Polynomial K) = 0 := by
  simp [polyShiftOp]

@[simp] theorem polyShiftOp_one (S : Module.End K V) :
    polyShiftOp S (1 : Polynomial K) = 1 := by
  simp [polyShiftOp]

theorem polyShiftOp_add (S : Module.End K V) (p q : Polynomial K) :
    polyShiftOp S (p + q) = polyShiftOp S p + polyShiftOp S q := by
  exact Polynomial.eval₂_add _ _

theorem polyShiftOp_mul (S : Module.End K V) (p q : Polynomial K) :
    polyShiftOp S (p * q) = polyShiftOp S p * polyShiftOp S q := by
  apply Polynomial.eval₂_mul_noncomm
  intro k
  exact Algebra.commutes _ _

@[simp] theorem polyShiftOp_X (S : Module.End K V) :
    polyShiftOp S Polynomial.X = S := by
  simp [polyShiftOp]

@[simp] theorem polyShiftOp_C (S : Module.End K V) (c : K) :
    polyShiftOp S (Polynomial.C c) = algebraMap K (Module.End K V) c := by
  simp [polyShiftOp]

theorem polyShiftOp_X_sub_one_apply (S : Module.End K V) (v : V) :
    polyShiftOp S (Polynomial.X - 1) v = S v - v := by
  rw [show Polynomial.X - (1 : Polynomial K) = Polynomial.X + (-1) by ring]
  rw [polyShiftOp_add]
  rw [show (-1 : Polynomial K) = Polynomial.C (-1 : K) by simp, polyShiftOp_C]
  simp [sub_eq_add_neg]

/-- **Bézout spectral exclusion.** Two coprime polynomial constraints on the same shift have no
common nonzero vector. -/
theorem eq_zero_of_coprime_polyShiftOp {S : Module.End K V} {p q : Polynomial K} {v : V}
    (hcop : IsCoprime p q) (hp : polyShiftOp S p v = 0) (hq : polyShiftOp S q v = 0) :
    v = 0 := by
  rcases hcop with ⟨a, b, hab⟩
  calc
    v = polyShiftOp S 1 v := by simp
    _ = polyShiftOp S (a * p + b * q) v := by rw [hab]
    _ = (polyShiftOp S (a * p) + polyShiftOp S (b * q)) v := by
      rw [polyShiftOp_add]
    _ = polyShiftOp S (a * p) v + polyShiftOp S (b * q) v := rfl
    _ = polyShiftOp S a (polyShiftOp S p v) +
        polyShiftOp S b (polyShiftOp S q v) := by
      rw [polyShiftOp_mul, polyShiftOp_mul, Module.End.mul_apply, Module.End.mul_apply]
    _ = 0 := by rw [hp, hq]; simp

/-- **Coprime reflected-shift rigidity.** If two shift annihilators have only the fixed root in
common, the carrier is fixed by the shift.  The coprime polynomials `p,q` are the residual factors
after removing `X - 1` from the forward and reflection-reversed characteristic polynomials. -/
theorem fixed_of_coprime_reflected_shift_annihilators {S : Module.End K V}
    {p q : Polynomial K} {v : V} (hcop : IsCoprime p q)
    (hp : polyShiftOp S ((Polynomial.X - 1) * p) v = 0)
    (hq : polyShiftOp S ((Polynomial.X - 1) * q) v = 0) :
    S v = v := by
  have hp' : polyShiftOp S p (S v - v) = 0 := by
    rw [mul_comm, polyShiftOp_mul, Module.End.mul_apply,
      polyShiftOp_X_sub_one_apply] at hp
    exact hp
  have hq' : polyShiftOp S q (S v - v) = 0 := by
    rw [mul_comm, polyShiftOp_mul, Module.End.mul_apply,
      polyShiftOp_X_sub_one_apply] at hq
    exact hq
  exact sub_eq_zero.mp (eq_zero_of_coprime_polyShiftOp hcop hp' hq')

/-- Distinct scalar phases give coprime linear characteristic factors. -/
theorem isCoprime_X_sub_C_X_sub_C_of_ne {a b : K} (hab : a ≠ b) :
    IsCoprime (Polynomial.X - Polynomial.C a) (Polynomial.X - Polynomial.C b) := by
  refine ⟨Polynomial.C (b - a)⁻¹, -Polynomial.C (b - a)⁻¹, ?_⟩
  calc
    Polynomial.C (b - a)⁻¹ * (Polynomial.X - Polynomial.C a) +
        -Polynomial.C (b - a)⁻¹ * (Polynomial.X - Polynomial.C b) =
      Polynomial.C (b - a)⁻¹ * (Polynomial.C b - Polynomial.C a) := by ring
    _ = Polynomial.C (b - a)⁻¹ * Polynomial.C (b - a) := by
      rw [Polynomial.C_sub]
    _ = Polynomial.C ((b - a)⁻¹ * (b - a)) := by rw [Polynomial.C_mul]
    _ = 1 := by rw [inv_mul_cancel₀ (sub_ne_zero.mpr hab.symm)]; simp

/-- The forward finite phase polynomial after removing the fixed phase `1`. -/
def forwardPhaseResidual (ω : ℂ) (s : Finset ℕ) : Polynomial ℂ :=
  ∏ n ∈ s.filter (· ≠ 0), (Polynomial.X - Polynomial.C (ω ^ n))

/-- The reflection-reversed finite phase polynomial after removing the fixed phase `1`. -/
def reflectedPhaseResidual (ω : ℂ) (s : Finset ℕ) : Polynomial ℂ :=
  ∏ n ∈ s.filter (· ≠ 0),
    (Polynomial.X - Polynomial.C ((ω ^ n)⁻¹))

/-- A positive power of a phase of infinite multiplicative order never equals the inverse of any
nonnegative power.  This is the exact algebraic use of irrationality in the two-base application. -/
theorem phase_ne_inverse_phase_of_infinite_order {ω : ℂ} (hω0 : ω ≠ 0)
    (hω : ∀ k : ℕ, 0 < k → ω ^ k ≠ 1) {m n : ℕ} (hm : 0 < m) :
    ω ^ m ≠ (ω ^ n)⁻¹ := by
  intro h
  have hn0 : ω ^ n ≠ 0 := pow_ne_zero n hω0
  have hprod : ω ^ m * ω ^ n = 1 := by rw [h, inv_mul_cancel₀ hn0]
  rw [← pow_add] at hprod
  exact hω (m + n) (Nat.add_pos_left hm n) hprod

/-- **Finite transverse phase separation.** For a phase of infinite order, the forward and
reflection-reversed finite characteristic polynomials are coprime once the fixed factor is removed.
Together with `fixed_of_coprime_reflected_shift_annihilators`, this is the positive algebraic core
of finite-transverse leaf-reflection rigidity. -/
theorem forward_reflected_phase_residual_isCoprime {ω : ℂ} (hω0 : ω ≠ 0)
    (hω : ∀ k : ℕ, 0 < k → ω ^ k ≠ 1) (s : Finset ℕ) :
    IsCoprime (forwardPhaseResidual ω s) (reflectedPhaseResidual ω s) := by
  rw [forwardPhaseResidual, reflectedPhaseResidual]
  apply IsCoprime.prod_left
  intro m hm
  apply IsCoprime.prod_right
  intro n hn
  have hm0 : m ≠ 0 := (Finset.mem_filter.mp hm).2
  exact isCoprime_X_sub_C_X_sub_C_of_ne
    (phase_ne_inverse_phase_of_infinite_order hω0 hω
      (Nat.pos_of_ne_zero hm0))

end RHTower
