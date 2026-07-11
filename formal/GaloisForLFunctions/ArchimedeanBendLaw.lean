import Mathlib.Analysis.Complex.Basic

/-!
# The Archimedean tropical bend law

The Taylor-magnitude hypertranscendence cards (log-superlacunary, stretched-exponential,
rough-subleading, polynomial, …) all force `HT` through one purely archimedean inequality: an
**integer** zero-sum `∑ c_ν a^ν = 0` (the `z^N`-coefficient identity of a hypothetical
integer-normalized algebraic differential equation, via Mahler) cannot have a single atom whose
modulus exceeds the sum of the moduli of all the others.  Equivalently, in any zero-sum the modulus
of a distinguished integer-weighted term is bounded by the sum of the others, so a strictly dominant
term makes the sum nonzero.

This file isolates that mechanism as a self-contained normed-field fact: the analytic
coefficient-asymptotics of each card enter only to verify the strict-dominance hypothesis.
-/

open Finset

namespace GaloisForLFunctions

variable {ι : Type*} [DecidableEq ι]

/-- In an integer-weighted zero-sum over a finite set, the modulus of any one term is bounded by the
sum of the moduli of the others: `‖c_{i₀}·x_{i₀}‖ ≤ ∑_{i ≠ i₀} ‖c_i·x_i‖`. -/
theorem norm_term_le_of_sum_eq_zero (s : Finset ι) (c : ι → ℤ) (x : ι → ℂ) {i₀ : ι}
    (hi₀ : i₀ ∈ s) (hsum : ∑ i ∈ s, (c i : ℂ) * x i = 0) :
    ‖(c i₀ : ℂ) * x i₀‖ ≤ ∑ i ∈ s.erase i₀, ‖(c i : ℂ) * x i‖ := by
  have hiso : (c i₀ : ℂ) * x i₀ = -∑ i ∈ s.erase i₀, (c i : ℂ) * x i :=
    eq_neg_of_add_eq_zero_left (by
      rw [Finset.add_sum_erase s (fun i => (c i : ℂ) * x i) hi₀]; exact hsum)
  rw [hiso, norm_neg]
  exact norm_sum_le _ _

/-- **Archimedean tropical bend law.**  If a distinguished term of an integer-weighted sum strictly
dominates the sum of the moduli of the other terms — `∑_{i ≠ i₀} ‖c_i·x_i‖ < ‖x_{i₀}‖` with
`c_{i₀} ≠ 0` — then the sum is nonzero.  (The integer weight satisfies `‖c_{i₀}‖ ≥ 1`, so the
distinguished term already has modulus `≥ ‖x_{i₀}‖`.)  This is the exact contradiction the
Taylor-magnitude cards derive when the log-magnitudes are superlacunary/dominant. -/
theorem sum_ne_zero_of_dominant (s : Finset ι) (c : ι → ℤ) (x : ι → ℂ) {i₀ : ι}
    (hi₀ : i₀ ∈ s) (hc : c i₀ ≠ 0)
    (hdom : ∑ i ∈ s.erase i₀, ‖(c i : ℂ) * x i‖ < ‖x i₀‖) :
    ∑ i ∈ s, (c i : ℂ) * x i ≠ 0 := by
  intro hsum
  have hle := norm_term_le_of_sum_eq_zero s c x hi₀ hsum
  have hc1 : (1 : ℝ) ≤ ‖(c i₀ : ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hc
  have hge : ‖x i₀‖ ≤ ‖(c i₀ : ℂ) * x i₀‖ := by
    rw [norm_mul]
    nlinarith [norm_nonneg (x i₀), hc1]
  linarith

end GaloisForLFunctions
