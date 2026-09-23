/-
# The dichotomy witness: at `b = 3` the filled Julia set avoids the closed unit disk

Counterpart to `U0WindowObstruction`: at `b = −3` the filled Julia set meets the closed unit
disk (`filledJulia_meets_unit_disk`), while at `b = +3` — the SAME modulus `3 ∈ (2, 2+√2)` —
it avoids it.  Window viability at a fixed modulus in the ring `2 < ‖b‖ ≤ 2+√2` is therefore
a direction-dependent property of `arg b`, not a property of `‖b‖` alone.

The escape chain for `‖z‖ ≤ 1` under `f_3(z) = z² + 3`:

  step 1: `z² + 3` lies in the disk `D(3,1)`;
  step 2: the second iterate `z⁴ + 6z² + 12` has real part `≥ 12 − 6 − 1 = 5`;
  step 3: modulus `≥ 5` is inside the escape regime (`not_mem_filledJulia`), and escape of an
          iterate forces escape of the point (`filledJulia_forward`, contrapositive).
-/
import GaloisForLFunctions.Bottcher.Dynamics
import GaloisForLFunctions.U0.U0WindowObstruction

open Complex Set Bottcher

namespace U0DichotomyWitness

/-- **`K_3` avoids the closed unit disk**: every point of modulus `≤ 1` escapes under
`z ↦ z² + 3`. -/
theorem unitDisk_avoids_filledJulia_three {z : ℂ} (hz : ‖z‖ ≤ 1) :
    z ∉ filledJulia (3 : ℂ) := by
  intro hmem
  -- the second iterate, expanded
  have hit2 : (quadratic (3 : ℂ))^[2] z = z ^ (4 : ℕ) + 6 * z ^ (2 : ℕ) + 12 := by
    have h : (quadratic (3 : ℂ))^[2] z = quadratic 3 (quadratic 3 z) := rfl
    rw [h, quadratic_apply, quadratic_apply]
    ring
  -- |Re| bounds on the two power terms
  have h2 : |(z ^ (2 : ℕ)).re| ≤ 1 := by
    refine le_trans (Complex.abs_re_le_norm _) ?_
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg z) hz
  have h4 : |(z ^ (4 : ℕ)).re| ≤ 1 := by
    refine le_trans (Complex.abs_re_le_norm _) ?_
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg z) hz
  -- real part of the second iterate is ≥ 5
  have hre : (5 : ℝ) ≤ ((quadratic (3 : ℂ))^[2] z).re := by
    rw [hit2]
    have hsplit : (z ^ (4 : ℕ) + 6 * z ^ (2 : ℕ) + 12).re = (z ^ (4 : ℕ)).re + 6 * (z ^ (2 : ℕ)).re + 12 := by
      simp [Complex.add_re, Complex.mul_re]
    rw [hsplit]
    linarith [(abs_le.mp h2).1, (abs_le.mp h4).1]
  have hnorm : (5 : ℝ) ≤ ‖(quadratic (3 : ℂ))^[2] z‖ :=
    le_trans hre (Complex.re_le_norm _)
  -- the second iterate is inside the escape regime, so the point cannot be in `K_3`
  have hesc : (quadratic (3 : ℂ))^[2] z ∉ filledJulia (3 : ℂ) := by
    refine not_mem_filledJulia ?_ ?_
    · rw [Complex.norm_ofNat]; linarith
    · linarith
  exact hesc (filledJulia_forward hmem 2)

end U0DichotomyWitness

namespace U0DichotomyWitness

/-- **The dichotomy at modulus `3`**: window viability is a directional property.  At the SAME
modulus — `‖3‖ = ‖−3‖ = 3 ∈ (2, 2+√2)` — the filled Julia set of `b = 3` avoids the closed unit
disk (window geometry available), while the filled Julia set of `b = −3` meets it (window route
void, `U0WindowObstruction`).  No threshold in `‖b‖` alone can separate the two. -/
theorem window_dichotomy_modulus_three :
    (∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia (3 : ℂ)) ∧
    (∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia (((-3 : ℝ) : ℂ))) := by
  constructor
  · exact fun _ hz => unitDisk_avoids_filledJulia_three hz
  · refine U0WindowObstruction.filledJulia_meets_unit_disk (by norm_num) ?_
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

/-- The two dichotomy parameters have the same modulus. -/
theorem dichotomy_parameters_same_modulus :
    ‖(3 : ℂ)‖ = 3 ∧ ‖(((-3 : ℝ) : ℂ))‖ = 3 := by
  constructor
  · exact Complex.norm_ofNat 3
  · rw [Complex.norm_real, Real.norm_eq_abs]
    norm_num

end U0DichotomyWitness
