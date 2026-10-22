import GaloisForLFunctions.HTGeometry.StieltjesMomentProblem
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Chebyshev traces of a moment sequence

For a real sequence `s` with moment functional `L_s(Σ a_k X^k) = Σ a_k s_k`, this module defines the
Chebyshev trace `L_s(X T_n(1 - 2X))` and the shifted trace `L_s(T_n(1 - 2X))`, where `T_n` is the
first-kind Chebyshev polynomial transported to the node interval `[0, 1]`. It records the three-term
recurrence of the trace polynomials, the first values of the traces, and their evaluation on finitely
atomic moment sequences `s_k = Σ_i w_i x_i^k`, where the traces become `Σ_i w_i x_i T_n(1 - 2 x_i)` and
`Σ_i w_i T_n(1 - 2 x_i)`.

## Main results

- `chebyshevTracePolynomial_add_two`: `P_(n+2) = 2(1 - 2X) P_(n+1) - P_n` for `P_n = X T_n(1 - 2X)`.
- `chebyshevMomentTrace_zero`, `chebyshevMomentTrace_one`: the traces at `n = 0, 1` are `s_1` and
  `s_1 - 2 s_2`.
- `momentFunctional_finset_atoms`: on an atomic moment sequence, `L_s(p) = Σ_i w_i p(x_i)`.
- `chebyshevMomentTrace_finset_atoms`: the Chebyshev trace of an atomic sequence is
  `Σ_i w_i x_i T_n(1 - 2 x_i)`.
- `chebyshevShiftedMomentTrace_finset_atoms`: the shifted trace of an atomic sequence is
  `Σ_i w_i T_n(1 - 2 x_i)`.

## Hypotheses

Unconditional algebraic identities for arbitrary real sequences, weights and atoms.
-/

open Polynomial
open scoped BigOperators

namespace HTGeometry

/-- The shifted Chebyshev kernel `T_n(1 - 2X)`, the first-kind Chebyshev polynomial moved to `[0, 1]`. -/
noncomputable def chebyshevTraceKernelPolynomial (n : ℕ) : Polynomial ℝ :=
  (Chebyshev.T ℝ (n : ℤ)).comp (1 - 2 * X)

/-- The Chebyshev trace polynomial `X · T_n(1 - 2X)`. -/
noncomputable def chebyshevTracePolynomial (n : ℕ) : Polynomial ℝ :=
  X * chebyshevTraceKernelPolynomial n

/-- The Chebyshev trace `L_s(X T_n(1 - 2X))` of a moment sequence `s`. -/
noncomputable def chebyshevMomentTrace (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  momentFunctional s (chebyshevTracePolynomial n)

/-- The shifted Chebyshev trace `L_s(T_n(1 - 2X))` of a moment sequence `s`. -/
noncomputable def chebyshevShiftedMomentTrace (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  momentFunctional s (chebyshevTraceKernelPolynomial n)

theorem chebyshevTraceKernelPolynomial_zero :
    chebyshevTraceKernelPolynomial 0 = 1 := by
  simp [chebyshevTraceKernelPolynomial]

theorem chebyshevShiftedMomentTrace_zero (s : ℕ → ℝ) :
    chebyshevShiftedMomentTrace s 0 = s 0 := by
  simpa [chebyshevShiftedMomentTrace, chebyshevTraceKernelPolynomial_zero] using
    momentFunctional_X_pow s 0

theorem chebyshevTracePolynomial_zero : chebyshevTracePolynomial 0 = X := by
  simp [chebyshevTracePolynomial, chebyshevTraceKernelPolynomial]

theorem chebyshevTracePolynomial_one :
    chebyshevTracePolynomial 1 = X - 2 * X ^ 2 := by
  simp [chebyshevTracePolynomial, chebyshevTraceKernelPolynomial, Chebyshev.T_one]
  ring_nf

/-- Three-term recurrence of the trace polynomials: `P_(n+2) = 2(1 - 2X) P_(n+1) - P_n`. -/
theorem chebyshevTracePolynomial_add_two (n : ℕ) :
    chebyshevTracePolynomial (n + 2) =
      2 * (1 - 2 * X) * chebyshevTracePolynomial (n + 1) -
        chebyshevTracePolynomial n := by
  simp only [chebyshevTracePolynomial, chebyshevTraceKernelPolynomial,
    Nat.cast_add, Nat.cast_ofNat,
    Chebyshev.T_add_two, sub_comp, mul_comp, X_comp, ofNat_comp]
  ring_nf

theorem chebyshevTracePolynomial_eval (n : ℕ) (x : ℝ) :
    (chebyshevTracePolynomial n).eval x =
      x * (Chebyshev.T ℝ (n : ℤ)).eval (1 - 2 * x) := by
  simp [chebyshevTracePolynomial, chebyshevTraceKernelPolynomial]

theorem chebyshevTraceKernelPolynomial_eval (n : ℕ) (x : ℝ) :
    (chebyshevTraceKernelPolynomial n).eval x =
      (Chebyshev.T ℝ (n : ℤ)).eval (1 - 2 * x) := by
  simp [chebyshevTraceKernelPolynomial]

/-- The zeroth Chebyshev trace is the first moment: `L_s(X) = s_1`. -/
theorem chebyshevMomentTrace_zero (s : ℕ → ℝ) :
    chebyshevMomentTrace s 0 = s 1 := by
  simpa [chebyshevMomentTrace, chebyshevTracePolynomial_zero] using
    momentFunctional_X_pow s 1

/-- The first Chebyshev trace is `L_s(X - 2X^2) = s_1 - 2 s_2`. -/
theorem chebyshevMomentTrace_one (s : ℕ → ℝ) :
    chebyshevMomentTrace s 1 = s 1 - 2 * s 2 := by
  rw [chebyshevMomentTrace, chebyshevTracePolynomial_one, momentFunctional_sub]
  have hsmul : (2 : Polynomial ℝ) * X ^ 2 = (2 : ℝ) • X ^ 2 := by
    simp only [smul_eq_C_mul, C_ofNat]
  rw [hsmul, momentFunctional_smul]
  rw [show momentFunctional s X = s 1 from by
    simpa only [pow_one] using momentFunctional_X_pow s 1,
    momentFunctional_X_pow]

/-- For a finitely atomic moment sequence `s_k = Σ_i w_i x_i^k`, the moment functional is integration
against the atoms: `L_s(p) = Σ_i w_i p(x_i)`. -/
theorem momentFunctional_finset_atoms {ι : Type*}
    (S : Finset ι) (w x : ι → ℝ) (p : Polynomial ℝ) :
    momentFunctional (fun k => ∑ i ∈ S, w i * x i ^ k) p =
      ∑ i ∈ S, w i * p.eval (x i) := by
  classical
  rw [momentFunctional_eq_support_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Chebyshev trace of an atomic sequence: `Σ_i w_i x_i T_n(1 - 2 x_i)`. -/
theorem chebyshevMomentTrace_finset_atoms {ι : Type*}
    (S : Finset ι) (w x : ι → ℝ) (n : ℕ) :
    chebyshevMomentTrace (fun k => ∑ i ∈ S, w i * x i ^ k) n =
      ∑ i ∈ S, w i * x i * (Chebyshev.T ℝ (n : ℤ)).eval (1 - 2 * x i) := by
  classical
  rw [chebyshevMomentTrace, momentFunctional_finset_atoms]
  apply Finset.sum_congr rfl
  intro i hi
  rw [chebyshevTracePolynomial_eval]
  ring

/-- Shifted Chebyshev trace of an atomic sequence: `Σ_i w_i T_n(1 - 2 x_i)`. -/
theorem chebyshevShiftedMomentTrace_finset_atoms {ι : Type*}
    (S : Finset ι) (w x : ι → ℝ) (n : ℕ) :
    chebyshevShiftedMomentTrace (fun k => ∑ i ∈ S, w i * x i ^ k) n =
      ∑ i ∈ S, w i * (Chebyshev.T ℝ (n : ℤ)).eval (1 - 2 * x i) := by
  classical
  rw [chebyshevShiftedMomentTrace, momentFunctional_finset_atoms]
  apply Finset.sum_congr rfl
  intro i hi
  rw [chebyshevTraceKernelPolynomial_eval]

end HTGeometry
