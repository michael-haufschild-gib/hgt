import GaloisForLFunctions.RHTower.Heat.AClusterHidesAnOffLineZeroFromHeat
import GaloisForLFunctions.RHTower.Heat.AWeylBumpKeepsANonrealHeatZero

/-!
# An off-line pair survives the heat flow up to heat `δ/L`

Let `F(z) = (z² + δ²) cos(Lz/2)` (`pairModel`): real zeros spaced `2π/L` (the zero density of `Ξ` at
height `X` when `L = log X`) and one off-line pair `±iδ`, at depth `δ`.  Its flow is the Gaussian
average of variance `2t` in the imaginary direction (`pairModelHeat`),

  `H_t(z) = ∫ g_t(u) F(z + iu) du`,

which for `F = ∫ cos(zu) dμ` is `∫ e^{tu²} cos(zu) dμ`, the de Bruijn deformation.

* **Size** (`norm_pairModel_le`): `‖F(x + iy)‖ ≤ (x² + y² + δ²) cosh(Ly/2)`: no centre bump, the size
  of a slice under Lindelöf-size bounds.
* **On the imaginary axis** (`pairModelHeat_mul_I`): `H_t(iy)` is real and equals
  `(e^{tL²/4}/2)(e^{Ly/2}(δ² − 2t − (y + Lt)²) + e^{−Ly/2}(δ² − 2t − (y − Lt)²))`.
* **The pair survives** (`exists_pos_pairModelHeat_mul_I_eq_zero`): if `(Lt)² + 2t < δ²` and
  `δ ≤ 2`, then `H_t(iy) = 0` for some `y > 0`: `H_t(0) > 0` and `H_t(i(δ + 1)) < 0`.

In `κ = tL`, the pair keeps a nonreal zero for `κ² + 2κ/L < δ²`, i.e. up to `κ → δ`.  With `δ` up to
`½`, size bounds at the Lindelöf level cannot place the reality horizon below `κ = ½`, the value of
the corpus method with `E ≡ 0` (`KiKimLeeTwoThirdsHorizon`: `(c − w)² > 4cE(w)` on `[0, ½]`).  The
Weyl bump (`AWeylBumpKeepsANonrealHeatZero`) gives the floor `4μ(½) = 2/3` at the current exponent.
-/

open Complex Polynomial MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

/-- The pair model `F(z) = (z² + δ²) cos(Lz/2)`. -/
def pairModel (L δ : ℝ) (z : ℂ) : ℂ := (z ^ 2 + δ ^ 2) * Complex.cos (L * z / 2)

/-- Its heat flow: the Gaussian average of variance `2t` in the imaginary direction. -/
def pairModelHeat (L δ t : ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, (gaussDensity t u : ℂ) * pairModel L δ (z + u * I)

/-- `‖F(x + iy)‖ ≤ (x² + y² + δ²) cosh(Ly/2)`. -/
theorem norm_pairModel_le (L δ x y : ℝ) :
    ‖pairModel L δ (x + y * I)‖ ≤ (x ^ 2 + y ^ 2 + δ ^ 2) * Real.cosh (L * y / 2) := by
  unfold pairModel
  rw [norm_mul]
  refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
  · refine (norm_add_le _ _).trans ?_
    rw [norm_pow, show ((δ : ℂ) ^ 2) = ((δ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg δ)]
    have : ‖(x : ℂ) + y * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    rw [this]
  · have h := norm_cos_le_cosh_im ((L : ℂ) * (x + y * I) / 2)
    have him : ((L : ℂ) * (x + y * I) / 2).im = L * y / 2 := by simp
    rwa [him] at h

/-- `e^{(λ/2)D²}(δ² − X²) = (δ² − λ) − X²`. -/
theorem forwardPolyHeat_C_sub_X_sq (s δ : ℝ) :
    forwardPolyHeat s (C (δ ^ 2) - X ^ 2) = C (δ ^ 2 - 2 * s) - X ^ 2 := by
  rw [forwardPolyHeat_eq_sum (N := 2) (by
    have : (C (δ ^ 2) - X ^ 2 : ℝ[X]).natDegree ≤ 2 := by
      refine (natDegree_sub_le _ _).trans ?_
      simp
    omega)]
  have h1 : derivative (C (δ ^ 2) - X ^ 2 : ℝ[X]) = -(C 2 * X) := by
    rw [derivative_sub, derivative_C, derivative_X_sq, zero_sub]
  have h2 : derivative (-(C 2 * X) : ℝ[X]) = -C 2 := by
    rw [derivative_neg, derivative_C_mul_X]
  have hd : (⇑derivative)^[2] (C (δ ^ 2) - X ^ 2 : ℝ[X]) = -C 2 := by
    rw [Function.iterate_succ_apply', Function.iterate_one, h1, h2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, map_one, one_mul, mul_zero, Function.iterate_zero, id, pow_one,
    Nat.factorial_one, mul_one]
  rw [hd, map_sub, map_mul]
  ring

/-- **The flow on the imaginary axis is real**:
`H_t(iy) = (e^{tL²/4}/2)(e^{Ly/2}(δ² − 2t − (y + Lt)²) + e^{−Ly/2}(δ² − 2t − (y − Lt)²))`. -/
theorem pairModelHeat_mul_I {L δ t : ℝ} (ht : 0 < t) (y : ℝ) :
    pairModelHeat L δ t (y * I) =
      ((Real.exp (t * L ^ 2 / 4) / 2 * (Real.exp (L * y / 2) * (δ ^ 2 - 2 * t - (y + L * t) ^ 2)
        + Real.exp (-(L * y / 2)) * (δ ^ 2 - 2 * t - (y - L * t) ^ 2)) : ℝ) : ℂ) := by
  have hpt : ∀ u : ℝ, (gaussDensity t u : ℂ) * pairModel L δ (y * I + u * I)
      = ((Real.exp (L * y / 2) / 2 * (gaussDensity t u * (Real.exp (L / 2 * u)
          * (C (δ ^ 2) - X ^ 2 : ℝ[X]).eval (y + u)))
        + Real.exp (-(L * y / 2)) / 2 * (gaussDensity t u * (Real.exp (-(L / 2) * u)
          * (C (δ ^ 2) - X ^ 2 : ℝ[X]).eval (y + u))) : ℝ) : ℂ) := by
    intro u
    unfold pairModel
    have hz : (y : ℂ) * I + u * I = ((y + u : ℝ) : ℂ) * I := by push_cast; ring
    have hcos : Complex.cos ((L : ℂ) * (((y + u : ℝ) : ℂ) * I) / 2)
        = ((Real.cosh (L * (y + u) / 2) : ℝ) : ℂ) := by
      rw [show (L : ℂ) * (((y + u : ℝ) : ℂ) * I) / 2 = ((L * (y + u) / 2 : ℝ) : ℂ) * I by
        push_cast; ring, Complex.cos_mul_I, Complex.ofReal_cosh]
    rw [hz, hcos]
    have hsq : (((y + u : ℝ) : ℂ) * I) ^ 2 + (δ : ℂ) ^ 2 = (((δ ^ 2 - (y + u) ^ 2) : ℝ) : ℂ) := by
      push_cast; rw [mul_pow, Complex.I_sq]; ring
    rw [hsq, Real.cosh_eq]
    simp only [eval_sub, eval_C, eval_pow, eval_X]
    have e1 : Real.exp (L * (y + u) / 2) = Real.exp (L * y / 2) * Real.exp (L / 2 * u) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(L * (y + u) / 2)) = Real.exp (-(L * y / 2)) * Real.exp (-(L / 2) * u) := by
      rw [← Real.exp_add]; ring_nf
    rw [e1, e2]
    push_cast; ring
  have h2t : 0 < 2 * t := by positivity
  obtain ⟨i1, v1⟩ := integrable_and_integral_gaussDensity_tilt_poly h2t (C (δ ^ 2) - X ^ 2) (L / 2) y
  obtain ⟨i2, v2⟩ := integrable_and_integral_gaussDensity_tilt_poly h2t (C (δ ^ 2) - X ^ 2)
    (-(L / 2)) y
  rw [show 2 * t / 2 = t by ring] at i1 v1 i2 v2
  unfold pairModelHeat
  rw [show (fun u : ℝ => (gaussDensity t u : ℂ) * pairModel L δ (y * I + u * I)) = fun u =>
      ((Real.exp (L * y / 2) / 2 * (gaussDensity t u * (Real.exp (L / 2 * u)
          * (C (δ ^ 2) - X ^ 2 : ℝ[X]).eval (y + u)))
        + Real.exp (-(L * y / 2)) / 2 * (gaussDensity t u * (Real.exp (-(L / 2) * u)
          * (C (δ ^ 2) - X ^ 2 : ℝ[X]).eval (y + u))) : ℝ) : ℂ) from funext hpt,
    integral_complex_ofReal, integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
    integral_const_mul, v1, v2, forwardPolyHeat_C_sub_X_sq]
  congr 1
  simp only [eval_sub, eval_C, eval_pow, eval_X]
  have e1 : 2 * t * (L / 2) ^ 2 / 2 = t * L ^ 2 / 4 := by ring
  have e2 : 2 * t * (-(L / 2)) ^ 2 / 2 = t * L ^ 2 / 4 := by ring
  rw [e1, e2]
  ring

/-- **The off-line pair survives the flow.**  If `t > 0`, `0 ≤ L`, `0 < δ ≤ 2` and
`(Lt)² + 2t < δ²`, then `H_t(iy) = 0` for some `y > 0`. -/
theorem exists_pos_pairModelHeat_mul_I_eq_zero {L δ t : ℝ} (ht : 0 < t) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hδ2 : δ ≤ 2) (hκ : (L * t) ^ 2 + 2 * t < δ ^ 2) :
    ∃ y : ℝ, 0 < y ∧ pairModelHeat L δ t (y * I) = 0 := by
  set R : ℝ → ℝ := fun y => Real.exp (t * L ^ 2 / 4) / 2 * (Real.exp (L * y / 2)
      * (δ ^ 2 - 2 * t - (y + L * t) ^ 2) + Real.exp (-(L * y / 2)) * (δ ^ 2 - 2 * t - (y - L * t) ^ 2))
    with hR
  have hRc : Continuous R := by rw [hR]; fun_prop
  have hE := Real.exp_pos (t * L ^ 2 / 4)
  have hR0 : 0 < R 0 := by
    have e : R 0 = Real.exp (t * L ^ 2 / 4) * (δ ^ 2 - 2 * t - (L * t) ^ 2) := by
      rw [hR]
      simp only [mul_zero, zero_div, neg_zero, Real.exp_zero, one_mul, zero_add, zero_sub, neg_sq]
      ring
    rw [e]
    exact mul_pos hE (by linarith)
  have hR1 : R (δ + 1) < 0 := by
    simp only [hR]
    have hy : 0 ≤ δ + 1 + L * t := by positivity
    have hLt : 0 ≤ L * t := mul_nonneg hL ht.le
    have h1 : δ ^ 2 - 2 * t - (δ + 1 + L * t) ^ 2 ≤ -(2 * δ + 1) := by
      nlinarith [sq_nonneg (L * t), mul_nonneg (by linarith : (0 : ℝ) ≤ δ + 1) hLt]
    have h2 : δ ^ 2 - 2 * t - (δ + 1 - L * t) ^ 2 ≤ δ ^ 2 := by nlinarith [sq_nonneg (δ + 1 - L * t)]
    have hA := Real.exp_pos (L * (δ + 1) / 2)
    have hB := Real.exp_pos (-(L * (δ + 1) / 2))
    have hAB : Real.exp (-(L * (δ + 1) / 2)) ≤ Real.exp (L * (δ + 1) / 2) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hδsq : δ ^ 2 < 2 * δ + 1 := by nlinarith
    have : Real.exp (L * (δ + 1) / 2) * (δ ^ 2 - 2 * t - (δ + 1 + L * t) ^ 2)
        + Real.exp (-(L * (δ + 1) / 2)) * (δ ^ 2 - 2 * t - (δ + 1 - L * t) ^ 2) < 0 := by
      have i1 := mul_le_mul_of_nonneg_left h1 hA.le
      have i2 := mul_le_mul_of_nonneg_left h2 hB.le
      have i3 := mul_le_mul_of_nonneg_right hAB (sq_nonneg δ)
      nlinarith
    exact mul_neg_of_pos_of_neg (by positivity) this
  obtain ⟨y, hy, hRy⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ δ + 1 by linarith)
    hRc.continuousOn ⟨hR1.le, hR0.le⟩
  have hy0 : y ≠ 0 := by rintro rfl; exact absurd hRy hR0.ne'
  refine ⟨y, lt_of_le_of_ne hy.1 (Ne.symm hy0), ?_⟩
  rw [pairModelHeat_mul_I ht y]
  have : R y = Real.exp (t * L ^ 2 / 4) / 2 * (Real.exp (L * y / 2)
      * (δ ^ 2 - 2 * t - (y + L * t) ^ 2) + Real.exp (-(L * y / 2)) * (δ ^ 2 - 2 * t - (y - L * t) ^ 2))
    := rfl
  rw [← this, hRy, Complex.ofReal_zero]

end

end RHTower.DeBruijn
