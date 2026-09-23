import GaloisForLFunctions.RHTower.Sieve.LogPolyTranslation
import GaloisForLFunctions.HTGeometry.CellMaxProductIntegral

/-!
# The envelope enters as an aggregate over cells, not as a global supremum

A vertical integral of an envelope against the square of a prime-supported Dirichlet polynomial is
usually estimated by

```text
(sup of the envelope) × (length of the range) × (mean square per unit length) ,
```

which charges the envelope's largest value to the whole range.  Cutting the range into cells of the
admissible Gallagher length instead charges it cell by cell:

```text
∫ E(w)·‖P(w)‖² dw  ≤  (∑_k E(v_k)) · (mean square of P on one cell) ,
```

with `v_k` a maximiser of `E` on the `k`-th cell.  The mean square of `P` is the same on every cell
because a translation only twists the coefficients by unimodular factors, and it carries the sharp
prime near-diagonal weight `q/log q`.

The aggregate `∑_k E(v_k)` is the quantity that decides the strength of a Halász-type bound: with
the Perron envelope `E(w) = ‖F‖²/‖σ + it‖²` the cells far from the origin are damped by the kernel,
so the sum converges even though the range is long — whereas `sup E × length` grows with the range.
-/

noncomputable section

namespace RHTower.Sieve

open Finset MeasureTheory GaloisForLFunctions.HTGeometry

/-- The mean square of a prime-supported Dirichlet polynomial on one Gallagher cell, with the sharp
near-diagonal weight. -/
def primeCellMass (c : ℕ → ℂ) (s : Finset ℕ) : ℝ :=
  (5 / 4) * ∑ q ∈ s, (700 * ((q : ℝ) / Real.log q) + 1) * ‖c q‖ ^ (2 : ℕ)

theorem primeCellMass_nonneg (c : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ m ∈ s, m.Prime) :
    0 ≤ primeCellMass c s := by
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun q hq => ?_)
  have hq2 : 2 ≤ q := (hs q hq).two_le
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hlogq : (0 : ℝ) < Real.log q := Real.log_pos (by linarith)
  have hquot : (0 : ℝ) ≤ (q : ℝ) / Real.log q := div_nonneg (by linarith) hlogq.le
  positivity

/-- **The mean square on one Gallagher cell.**  Every cell of length `1/π` carries the same bound. -/
theorem integral_cell_normSq_logPoly_le (c : ℕ → ℂ) (s : Finset ℕ) (hs : ∀ m ∈ s, m.Prime)
    (a : ℝ) (k : ℕ) :
    (∫ w in (a + (k : ℝ) * (1 / Real.pi))..(a + ((k : ℝ) + 1) * (1 / Real.pi)),
        ‖logPoly c s w‖ ^ (2 : ℕ))
      ≤ primeCellMass c s := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set P : ℝ := 1 / Real.pi with hP
  have hP0 : (0 : ℝ) < P := by rw [hP]; positivity
  set u : ℝ := a + ((k : ℝ) + 1 / 2) * P with hu
  have hlo : a + (k : ℝ) * P = u - P / 2 := by rw [hu]; ring
  have hhi : a + ((k : ℝ) + 1) * P = u + P / 2 := by rw [hu]; ring
  have hle : a + (k : ℝ) * P ≤ a + ((k : ℝ) + 1) * P := by nlinarith [hP0]
  have hW : 2 * Real.pi * 1 * (P / 2) ≤ 1 := by
    rw [hP]
    field_simp
    norm_num
  have hconv : (∫ w in (a + (k : ℝ) * P)..(a + ((k : ℝ) + 1) * P), ‖logPoly c s w‖ ^ (2 : ℕ))
      = ∫ w in Set.Icc (u - P / 2) (u + P / 2), ‖logPoly c s w‖ ^ (2 : ℕ) := by
    rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Icc_eq_integral_Ioc, hlo, hhi]
  rw [hconv]
  exact integral_Icc_normSq_logPoly_shift_le_prime_sharp c s hs u (by linarith) hW

/-- **The envelope enters as an aggregate over cells.**  The maximisers are produced by the
statement, so any bound on `∑_k E(v_k)` can consume them. -/
theorem exists_cell_aggregate_normSq_logPoly_le {c : ℕ → ℂ} {s : Finset ℕ}
    (hs : ∀ m ∈ s, m.Prime) {E : ℝ → ℝ} (hE : Continuous E) (hE0 : ∀ t, 0 ≤ E t)
    (a : ℝ) (m : ℕ) :
    ∃ v : ℕ → ℝ,
      (∀ k, k < m →
        v k ∈ Set.Icc (a + (k : ℝ) * (1 / Real.pi)) (a + ((k : ℝ) + 1) * (1 / Real.pi)))
      ∧ (∫ w in a..(a + (m : ℝ) * (1 / Real.pi)), E w * ‖logPoly c s w‖ ^ (2 : ℕ))
          ≤ (∑ k ∈ Finset.range m, E (v k)) * primeCellMass c s := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hP0 : (0 : ℝ) < 1 / Real.pi := by positivity
  have hH : Continuous fun w : ℝ => ‖logPoly c s w‖ ^ (2 : ℕ) :=
    ((continuous_logPoly c s).norm).pow 2
  have hH0 : ∀ t : ℝ, 0 ≤ ‖logPoly c s t‖ ^ (2 : ℕ) := fun t => by positivity
  obtain ⟨v, hvmem, hvle⟩ :=
    exists_cell_max_mul_integral_le hE hH hH0 a (1 / Real.pi) hP0 m
  refine ⟨v, hvmem, le_trans hvle ?_⟩
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  exact mul_le_mul_of_nonneg_left (integral_cell_normSq_logPoly_le c s hs a k) (hE0 (v k))

end RHTower.Sieve

end
