import GaloisForLFunctions.HTGeometry.AbeDerivativeDampingNoGo

/-!
# Gaussian lattice decay does not by itself cure derivative small divisors

The value-level Poincaré-tail argument is protected by a Gaussian summable
majorant.  For a differentiated damping factor, a Gaussian index weight alone
still cannot give a parameter-independent envelope if the phase deficit is
allowed to be super-Gaussianly small in the index.  This module records that
exact obstruction with a fully specified model deficit `exp (-n^(3 : ℕ))`.

It is a boundary theorem for a proposed proof route, not a counterexample to
jet interpolation: a successful period-matrix construction could use further
arithmetic information or a different seed family.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **A Gaussian lattice factor cannot uniformly absorb a super-Gaussian phase
deficit after one damping derivative.**  At index `n` and parameter
`B = exp (n^(3 : ℕ))`, the displayed term equals `exp (n^(3 : ℕ) - n^(2 : ℕ) - 1)`, hence is
unbounded.  Thus strict pointwise damping plus an unspecified Gaussian lattice
weight does not imply a derivative-stable summable majorant. -/
theorem not_exists_gaussian_small_divisor_uniform_damping_bound :
    ¬ ∃ C : ℝ, ∀ B : ℝ, ∀ n : ℕ, 0 ≤ B →
      B * Real.exp (-((n : ℝ) ^ (2 : ℕ))) *
        Real.exp (-B * Real.exp (-((n : ℝ) ^ (3 : ℕ)))) ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max C 1)
  let x : ℝ := n
  have hxC : C < x := by
    exact lt_of_le_of_lt (le_max_left _ _) hn
  have hx2 : (2 : ℝ) ≤ x := by
    have hx1 : (1 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
    have hn1 : 1 < n := by
      exact_mod_cast hx1
    have hn2 : 2 ≤ n := by omega
    change (2 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn2
  let B : ℝ := Real.exp (x ^ (3 : ℕ))
  have hB : 0 ≤ B := (Real.exp_pos _).le
  have h := hC B n hB
  have hphase : -B * Real.exp (-(x ^ (3 : ℕ))) = -1 := by
    dsimp [B]
    calc
      -Real.exp (x ^ (3 : ℕ)) * Real.exp (-(x ^ (3 : ℕ)))
          = -(Real.exp (x ^ (3 : ℕ)) * Real.exp (-(x ^ (3 : ℕ)))) := by ring
      _ = -Real.exp (x ^ (3 : ℕ) + -(x ^ (3 : ℕ))) := by rw [← Real.exp_add]
      _ = -1 := by norm_num
  have hvalue : B * Real.exp (-(x ^ (2 : ℕ))) * Real.exp (-B * Real.exp (-(x ^ (3 : ℕ))))
      = Real.exp (x ^ (3 : ℕ) - x ^ (2 : ℕ) - 1) := by
    rw [hphase]
    dsimp [B]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
  change B * Real.exp (-(x ^ (2 : ℕ))) * Real.exp (-B * Real.exp (-(x ^ (3 : ℕ)))) ≤ C at h
  rw [hvalue] at h
  have hsq : x + 1 ≤ x ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (x - 1)]
  have hcube : x ^ (2 : ℕ) + x ^ (2 : ℕ) ≤ x ^ (3 : ℕ) := by
    nlinarith [mul_nonneg (sq_nonneg x) (by linarith : 0 ≤ x - 2)]
  have hexponent : x ≤ x ^ (3 : ℕ) - x ^ (2 : ℕ) - 1 := by
    linarith
  have hxexp : x < Real.exp x := by
    linarith [Real.add_one_le_exp x]
  have hlarge : C < Real.exp (x ^ (3 : ℕ) - x ^ (2 : ℕ) - 1) :=
    (hxC.trans hxexp).trans_le (Real.exp_le_exp.mpr hexponent)
  exact (not_lt_of_ge h) hlarge

/-- **Local multiplier normalization still leaves a first-jet small-divisor
obstruction.**  Normalizing by the multiplier at a packet point replaces a
phase loss `δ` by a derivative factor `B * δ` and the value damping by
`exp (-B * δ^(2 : ℕ))`.  A Gaussian lattice weight cannot dominate this uniformly
when `δ = exp (-n^(3 : ℕ))`: at `B = exp (2 n^(3 : ℕ))` the displayed term is
`exp (n^(3 : ℕ) - n^(2 : ℕ) - 1)`. -/
theorem not_exists_gaussian_normalized_small_divisor_uniform_damping_bound :
    ¬ ∃ C : ℝ, ∀ B : ℝ, ∀ n : ℕ, 0 ≤ B →
      B * Real.exp (-((n : ℝ) ^ (2 : ℕ))) * Real.exp (-((n : ℝ) ^ (3 : ℕ))) *
        Real.exp (-B * Real.exp (-(2 * (n : ℝ) ^ (3 : ℕ)))) ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max C 1)
  let x : ℝ := n
  have hxC : C < x := by
    exact lt_of_le_of_lt (le_max_left _ _) hn
  have hx2 : (2 : ℝ) ≤ x := by
    have hx1 : (1 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
    have hn1 : 1 < n := by
      exact_mod_cast hx1
    have hn2 : 2 ≤ n := by omega
    change (2 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn2
  let B : ℝ := Real.exp (2 * x ^ (3 : ℕ))
  have hB : 0 ≤ B := (Real.exp_pos _).le
  have h := hC B n hB
  have hphase : -B * Real.exp (-(2 * x ^ (3 : ℕ))) = -1 := by
    dsimp [B]
    calc
      -Real.exp (2 * x ^ (3 : ℕ)) * Real.exp (-(2 * x ^ (3 : ℕ)))
          = -(Real.exp (2 * x ^ (3 : ℕ)) * Real.exp (-(2 * x ^ (3 : ℕ)))) := by ring
      _ = -Real.exp (2 * x ^ (3 : ℕ) + -(2 * x ^ (3 : ℕ))) := by rw [← Real.exp_add]
      _ = -1 := by norm_num
  have hvalue : B * Real.exp (-(x ^ (2 : ℕ))) * Real.exp (-(x ^ (3 : ℕ))) *
      Real.exp (-B * Real.exp (-(2 * x ^ (3 : ℕ)))) =
        Real.exp (x ^ (3 : ℕ) - x ^ (2 : ℕ) - 1) := by
    rw [hphase]
    dsimp [B]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  change B * Real.exp (-(x ^ (2 : ℕ))) * Real.exp (-(x ^ (3 : ℕ))) *
      Real.exp (-B * Real.exp (-(2 * x ^ (3 : ℕ)))) ≤ C at h
  rw [hvalue] at h
  have hsq : x + 1 ≤ x ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (x - 1)]
  have hcube : x ^ (2 : ℕ) + x ^ (2 : ℕ) ≤ x ^ (3 : ℕ) := by
    nlinarith [mul_nonneg (sq_nonneg x) (by linarith : 0 ≤ x - 2)]
  have hexponent : x ≤ x ^ (3 : ℕ) - x ^ (2 : ℕ) - 1 := by
    linarith
  have hxexp : x < Real.exp x := by
    linarith [Real.add_one_le_exp x]
  have hlarge : C < Real.exp (x ^ (3 : ℕ) - x ^ (2 : ℕ) - 1) :=
    (hxC.trans hxexp).trans_le (Real.exp_le_exp.mpr hexponent)
  exact (not_lt_of_ge h) hlarge

end GaloisForLFunctions.HTGeometry
