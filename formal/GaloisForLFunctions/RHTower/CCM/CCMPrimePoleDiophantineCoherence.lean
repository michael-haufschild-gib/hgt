import GaloisForLFunctions.RHTower.CCM.CCMPrimePoleHilbert
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Quantitative cross-place coherence for CCM prime-pole vectors

The exact Cauchy covariance law turns Dirichlet approximation into a quantitative
Hilbert-space theorem.  At any two positive scales and every positive cutoff
there are indexed normalized pole vectors with squared distance of order
`N^(-2)`.  This is a positive carrier law: distinct local-factor Hardy spaces
have cofinally coherent unit directions.
-/

open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower

theorem norm_sub_sq_ccmNormalizedPrimePoleVector_le_frequency_defect
    {Lp Lq : ℝ} (hp : 0 < Lp) (hq : 0 < Lq) (n r : ℤ) :
    ‖ccmNormalizedPrimePoleVector Lq hq r -
        ccmNormalizedPrimePoleVector Lp hp n‖ ^ 2 ≤
      2 * (2 * Real.pi * ((r : ℝ) / Lq - (n : ℝ) / Lp)) ^ 2 := by
  rw [norm_sub_sq_ccmNormalizedPrimePoleVector hp hq n r]
  let a : ℝ := 2 * Real.pi * ((r : ℝ) / Lq - (n : ℝ) / Lp)
  change 2 * a ^ 2 / (1 + a ^ 2) ≤ 2 * a ^ 2
  have hden : 0 < 1 + a ^ 2 := by positivity
  rw [div_le_iff₀ hden]
  nlinarith [sq_nonneg a]

theorem exists_ccmPrimePoleVector_dirichlet_coherence
    {Lp Lq : ℝ} (hp : 0 < Lp) (hq : 0 < Lq)
    {N : ℕ} (hN : 0 < N) :
    ∃ r n : ℤ, 0 < n ∧ n ≤ N ∧
      ‖ccmNormalizedPrimePoleVector Lq hq r -
          ccmNormalizedPrimePoleVector Lp hp n‖ ^ 2 ≤
        2 * (2 * Real.pi / (Lq * (N + 1))) ^ 2 := by
  obtain ⟨r, n, hn0, hnN, happrox⟩ :=
    Real.exists_int_int_abs_mul_sub_le (Lq / Lp) hN
  refine ⟨r, n, hn0, hnN, ?_⟩
  apply (norm_sub_sq_ccmNormalizedPrimePoleVector_le_frequency_defect hp hq n r).trans
  have hgap :
      |(r : ℝ) / Lq - (n : ℝ) / Lp| ≤ 1 / ((N : ℝ) + 1) / Lq := by
    have heq :
        (r : ℝ) / Lq - (n : ℝ) / Lp =
          -(((n : ℝ) * (Lq / Lp) - r) / Lq) := by
      field_simp [hp.ne', hq.ne']
      ring
    rw [heq, abs_neg, abs_div, abs_of_pos hq]
    exact div_le_div_of_nonneg_right happrox hq.le
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hscaled :
      |2 * Real.pi * ((r : ℝ) / Lq - (n : ℝ) / Lp)| ≤
        2 * Real.pi / (Lq * ((N : ℝ) + 1)) := by
    rw [abs_mul, abs_of_nonneg hpi]
    calc
      2 * Real.pi * |(r : ℝ) / Lq - (n : ℝ) / Lp| ≤
          2 * Real.pi * (1 / ((N : ℝ) + 1) / Lq) :=
        mul_le_mul_of_nonneg_left hgap hpi
      _ = 2 * Real.pi / (Lq * ((N : ℝ) + 1)) := by
        field_simp [hq.ne']
  have hright : 0 ≤ 2 * Real.pi / (Lq * ((N : ℝ) + 1)) := by positivity
  have hsq := (sq_le_sq₀ (abs_nonneg _) hright).2 hscaled
  rw [sq_abs] at hsq
  simpa only [Nat.cast_add, Nat.cast_one] using
    (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2))

end RHTower

