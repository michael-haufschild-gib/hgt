import GaloisForLFunctions.RHTower.DirichletLStripBounds

/-!
# The Archimedean ratio across the functional equation

The functional equation relates `Λ(χ, w)` at `Re w = -2` to `Λ(χ⁻¹, s)` at `Re s = 3`, where
`s = 1 - w`.  Its Archimedean factors are `Gammaℝ(s + δ)` and `Gammaℝ(w + δ)` with the *same* shift
`δ ∈ {0,1}`, and the two `Γ` arguments

```
(s + δ)/2 = (3+δ)/2 - (t/2) i,        (w + δ)/2 = (-2+δ)/2 + (t/2) i
```

have imaginary parts of equal modulus `|t|/2`.  The factor `e^{-π|t|/4}` therefore cancels between
numerator and denominator, and only the polynomial factors of the vertical bounds survive.

Both parities are needed: for `δ = 0` the arguments sit at `Re = 3/2` and `Re = -1`, one step right
of the half-integer base line and two steps left of the integer one; for `δ = 1` at `Re = 2` and
`Re = -1/2`, one step right of the integer base line and one step left of the half-integer one.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- **Exponential cancellation.**  An upper bound `X ≤ U E` and a lower bound `c E ≤ P Y` sharing
the same exponential factor `E` combine into a ratio bound free of `E`. -/
theorem ratio_bound_of_exp_cancel {X Y E U P c : ℝ} (hc : 0 < c) (hU : 0 ≤ U)
    (hX : X ≤ U * E) (hY : c * E ≤ P * Y) :
    c * X ≤ U * P * Y := by
  calc c * X ≤ c * (U * E) := mul_le_mul_of_nonneg_left hX hc.le
    _ = U * (c * E) := by ring
    _ ≤ U * (P * Y) := mul_le_mul_of_nonneg_left hY hU
    _ = U * P * Y := by ring

/-- The even numerator point sits one step right of the half-integer base line. -/
theorem gammaArg_even_num (t : ℝ) :
    ((3 : ℂ) - (t : ℂ) * Complex.I + ((0 : ℝ) : ℂ)) / 2
      = 1 / 2 + ((-t / 2 : ℝ) : ℂ) * Complex.I + ((1 : ℕ) : ℂ) := by
  push_cast
  ring

/-- The odd numerator point sits one step right of the integer base line. -/
theorem gammaArg_odd_num (t : ℝ) :
    ((3 : ℂ) - (t : ℂ) * Complex.I + ((1 : ℝ) : ℂ)) / 2
      = 1 + ((-t / 2 : ℝ) : ℂ) * Complex.I + ((1 : ℕ) : ℂ) := by
  push_cast
  ring

/-- The even denominator point sits two steps left of the integer base line. -/
theorem gammaArg_even_den (t : ℝ) :
    ((-2 : ℂ) + (t : ℂ) * Complex.I + ((0 : ℝ) : ℂ)) / 2
      = ((-1 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
  push_cast
  ring

/-- The odd denominator point sits one step left of the half-integer base line. -/
theorem gammaArg_odd_den (t : ℝ) :
    ((-2 : ℂ) + (t : ℂ) * Complex.I + ((1 : ℝ) : ℂ)) / 2
      = ((-1 / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
  push_cast
  ring

/-- The even denominator base point, two steps right. -/
theorem gammaArg_even_den_shift (t : ℝ) :
    ((-1 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I + ((2 : ℕ) : ℂ)
      = 1 + ((t / 2 : ℝ) : ℂ) * Complex.I := by
  push_cast
  ring

/-- The odd denominator base point, one step right. -/
theorem gammaArg_odd_den_shift (t : ℝ) :
    ((-1 / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I + ((1 : ℕ) : ℂ)
      = 1 / 2 + ((t / 2 : ℝ) : ℂ) * Complex.I := by
  push_cast
  ring

/-- The two half-arguments have imaginary parts of equal modulus. -/
theorem abs_half_eq (t : ℝ) : |(-t / 2 : ℝ)| = |(t / 2 : ℝ)| := by
  rw [neg_div, abs_neg]

/-- Beyond `|t| = 2` the halved ordinate clears the base-line threshold. -/
theorem one_le_abs_half {t : ℝ} (ht : 2 ≤ |t|) : 1 ≤ |(t / 2 : ℝ)| := by
  rw [abs_div]
  rw [show |(2 : ℝ)| = 2 by norm_num]
  linarith

/-- **The Archimedean ratio, even case.**  At `Re w = -2` and `s = 1 - w` the two `Γ` factors of an
even character have equal exponential size, so their ratio is bounded by a cubic polynomial. -/
theorem norm_Gamma_ratio_even {t : ℝ} (ht : 2 ≤ |t|) :
    ‖Complex.Gamma (((3 : ℂ) - (t : ℂ) * Complex.I + ((0 : ℝ) : ℂ)) / 2)‖
      ≤ 40 * |t / 2| ^ (3 : ℕ) *
        ‖Complex.Gamma ((((-2 : ℂ) + (t : ℂ) * Complex.I) + ((0 : ℝ) : ℂ)) / 2)‖ := by
  set v : ℝ := t / 2 with hv
  have hv1 : 1 ≤ |v| := one_le_abs_half ht
  have hv0 : (0 : ℝ) < |v| := by linarith
  set E : ℝ := Real.exp (-(Real.pi * |v| / 2)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  -- numerator
  have hnumpt : ((3 : ℂ) - (t : ℂ) * Complex.I + ((0 : ℝ) : ℂ)) / 2
      = 1 / 2 + ((-t / 2 : ℝ) : ℂ) * Complex.I + ((1 : ℕ) : ℂ) := gammaArg_even_num t
  have habs : |(-t / 2 : ℝ)| = |v| := by rw [hv]; exact abs_half_eq t
  have hnumbound := (norm_Gamma_half_add_nat_bounds 1
    (t := (-t / 2 : ℝ)) (by rw [habs]; exact hv1)).2
  rw [habs] at hnumbound
  -- denominator
  have hdenpt : (((-2 : ℂ) + (t : ℂ) * Complex.I) + ((0 : ℝ) : ℂ)) / 2
      = ((-1 : ℝ) : ℂ) + ((v : ℝ) : ℂ) * Complex.I := by rw [hv]; exact gammaArg_even_den t
  have hbase := (norm_Gamma_one_add_I_bounds (t := v) hv1).1
  have hshift : ((-1 : ℝ) : ℂ) + ((v : ℝ) : ℂ) * Complex.I + ((2 : ℕ) : ℂ)
      = 1 + ((v : ℝ) : ℂ) * Complex.I := by rw [hv]; exact gammaArg_even_den_shift t
  have hlow : Real.sqrt (2 * Real.pi * |v|) * E
      ≤ ‖Complex.Gamma (((-1 : ℝ) : ℂ) + ((v : ℝ) : ℂ) * Complex.I + ((2 : ℕ) : ℂ))‖ := by
    rw [hshift]
    exact hbase
  have hdenbound := norm_Gamma_lower_of_shift (a := (-1 : ℝ)) 2 hv1 hlow
  -- cancel the exponentials
  set X : ℝ := ‖Complex.Gamma (1 / 2 + ((-t / 2 : ℝ) : ℂ) * Complex.I + ((1 : ℕ) : ℂ))‖ with hX
  set Y : ℝ := ‖Complex.Gamma (((-1 : ℝ) : ℂ) + ((v : ℝ) : ℂ) * Complex.I)‖ with hY
  have hYnn : 0 ≤ Y := norm_nonneg _
  have hU : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi) * (((3 : ℝ) / 2 + (1 : ℕ)) * |v|) ^ (1 : ℕ) := by
    positivity
  have hSpos : 0 < Real.sqrt (2 * Real.pi * |v|) := by
    refine Real.sqrt_pos.mpr ?_
    positivity
  have hcombine := ratio_bound_of_exp_cancel (X := X) (Y := Y) (E := E)
    (U := Real.sqrt (2 * Real.pi) * (((3 : ℝ) / 2 + (1 : ℕ)) * |v|) ^ (1 : ℕ))
    (P := ((|(-1 : ℝ)| + ((2 : ℕ) : ℝ) + 1) * |v|) ^ (2 : ℕ))
    (c := Real.sqrt (2 * Real.pi * |v|)) hSpos hU hnumbound hdenbound
  -- remove the square root
  have hSge : Real.sqrt (2 * Real.pi) ≤ Real.sqrt (2 * Real.pi * |v|) := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith [Real.pi_pos]
  have hcubic : Real.sqrt (2 * Real.pi) * (((3 : ℝ) / 2 + (1 : ℕ)) * |v|) ^ (1 : ℕ) *
      ((|(-1 : ℝ)| + ((2 : ℕ) : ℝ) + 1) * |v|) ^ (2 : ℕ) * Y
      ≤ Real.sqrt (2 * Real.pi * |v|) * (40 * |v| ^ (3 : ℕ) * Y) := by
    have hone : ((1 : ℕ) : ℝ) = 1 := by norm_num
    have htwo : ((2 : ℕ) : ℝ) = 2 := by norm_num
    have habs1 : |(-1 : ℝ)| = 1 := by norm_num
    rw [hone, htwo, habs1, pow_one]
    have hstep : Real.sqrt (2 * Real.pi) * (((3 : ℝ) / 2 + 1) * |v|) * ((1 + 2 + 1) * |v|) ^ (2 : ℕ) * Y
        = Real.sqrt (2 * Real.pi) * (40 * |v| ^ (3 : ℕ) * Y) := by ring
    rw [hstep]
    exact mul_le_mul_of_nonneg_right hSge (by positivity)
  rw [hnumpt, hdenpt, ← hX, ← hY]
  have hfinal : Real.sqrt (2 * Real.pi * |v|) * X
      ≤ Real.sqrt (2 * Real.pi * |v|) * (40 * |v| ^ (3 : ℕ) * Y) := le_trans hcombine hcubic
  exact le_of_mul_le_mul_left hfinal hSpos

/-- **The Archimedean ratio, odd case.** -/
theorem exists_norm_Gamma_ratio_odd :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, 2 ≤ |t| →
      ‖Complex.Gamma (((3 : ℂ) - (t : ℂ) * Complex.I + ((1 : ℝ) : ℂ)) / 2)‖
        ≤ A * |t / 2| ^ (3 : ℕ) *
          ‖Complex.Gamma ((((-2 : ℂ) + (t : ℂ) * Complex.I) + ((1 : ℝ) : ℂ)) / 2)‖ := by
  have he2 : Real.exp (-2 : ℝ) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  have he2pos : (0 : ℝ) < 1 - Real.exp (-2 : ℝ) := by linarith
  have hbig : (0 : ℝ) < 2 * Real.pi / (1 - Real.exp (-2 : ℝ)) := by positivity
  have hsqpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  refine ⟨Real.sqrt (2 * Real.pi / (1 - Real.exp (-2 : ℝ))) * (15 / 2) / Real.sqrt Real.pi,
    by positivity, fun t ht => ?_⟩
  set v : ℝ := t / 2 with hv
  have hv1 : 1 ≤ |v| := one_le_abs_half ht
  have hv0 : (0 : ℝ) < |v| := by linarith
  set E : ℝ := Real.exp (-(Real.pi * |v| / 2)) with hE
  have hnumpt : ((3 : ℂ) - (t : ℂ) * Complex.I + ((1 : ℝ) : ℂ)) / 2
      = 1 + ((-t / 2 : ℝ) : ℂ) * Complex.I + ((1 : ℕ) : ℂ) := gammaArg_odd_num t
  have habs : |(-t / 2 : ℝ)| = |v| := by rw [hv]; exact abs_half_eq t
  have hnumbound := (norm_Gamma_one_add_nat_bounds 1
    (t := (-t / 2 : ℝ)) (by rw [habs]; exact hv1)).2
  rw [habs] at hnumbound
  have hdenpt : (((-2 : ℂ) + (t : ℂ) * Complex.I) + ((1 : ℝ) : ℂ)) / 2
      = ((-1 / 2 : ℝ) : ℂ) + ((v : ℝ) : ℂ) * Complex.I := by rw [hv]; exact gammaArg_odd_den t
  have hshift : ((-1 / 2 : ℝ) : ℂ) + ((v : ℝ) : ℂ) * Complex.I + ((1 : ℕ) : ℂ)
      = 1 / 2 + ((v : ℝ) : ℂ) * Complex.I := by rw [hv]; exact gammaArg_odd_den_shift t
  have hlow : Real.sqrt Real.pi * E
      ≤ ‖Complex.Gamma (((-1 / 2 : ℝ) : ℂ) + ((v : ℝ) : ℂ) * Complex.I + ((1 : ℕ) : ℂ))‖ := by
    rw [hshift]
    exact (norm_Gamma_half_add_I_bounds v).1
  have hdenbound := norm_Gamma_lower_of_shift (a := (-1 / 2 : ℝ)) 1 hv1 hlow
  set X : ℝ := ‖Complex.Gamma (1 + ((-t / 2 : ℝ) : ℂ) * Complex.I + ((1 : ℕ) : ℂ))‖ with hX
  set Y : ℝ := ‖Complex.Gamma (((-1 / 2 : ℝ) : ℂ) + ((v : ℝ) : ℂ) * Complex.I)‖ with hY
  have hYnn : 0 ≤ Y := norm_nonneg _
  have hU : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi * |v| / (1 - Real.exp (-2))) *
      (((2 : ℝ) + (1 : ℕ)) * |v|) ^ (1 : ℕ) := by positivity
  have hcombine := ratio_bound_of_exp_cancel (X := X) (Y := Y) (E := E)
    (U := Real.sqrt (2 * Real.pi * |v| / (1 - Real.exp (-2))) *
      (((2 : ℝ) + (1 : ℕ)) * |v|) ^ (1 : ℕ))
    (P := ((|(-1 / 2 : ℝ)| + ((1 : ℕ) : ℝ) + 1) * |v|) ^ (1 : ℕ))
    (c := Real.sqrt Real.pi) hsqpi hU hnumbound hdenbound
  -- separate the square root of `|v|`
  have hsplit : Real.sqrt (2 * Real.pi * |v| / (1 - Real.exp (-2)))
      = Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) * Real.sqrt |v| := by
    rw [← Real.sqrt_mul hbig.le]
    congr 1
    field_simp
  have hsqle : Real.sqrt |v| ≤ |v| := by
    have h1 : Real.sqrt |v| ≤ Real.sqrt (|v| ^ (2 : ℕ)) := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (abs_nonneg v)] at h1
  have hcubic : Real.sqrt (2 * Real.pi * |v| / (1 - Real.exp (-2))) *
      (((2 : ℝ) + (1 : ℕ)) * |v|) ^ (1 : ℕ) *
      ((|(-1 / 2 : ℝ)| + ((1 : ℕ) : ℝ) + 1) * |v|) ^ (1 : ℕ) * Y
      ≤ Real.sqrt Real.pi *
        (Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) * (15 / 2) / Real.sqrt Real.pi *
          |v| ^ (3 : ℕ) * Y) := by
    have hone : ((1 : ℕ) : ℝ) = 1 := by norm_num
    have habs2 : |(-1 / 2 : ℝ)| = 1 / 2 := by rw [abs_of_nonpos (by norm_num)]; norm_num
    rw [hone, habs2, pow_one, pow_one, hsplit]
    have hcan : Real.sqrt Real.pi *
        (Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) * (15 / 2) / Real.sqrt Real.pi *
          |v| ^ (3 : ℕ) * Y)
        = Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) * ((15 / 2) * (|v| ^ (3 : ℕ) * Y)) := by
      field_simp
    rw [hcan]
    have hlhs : Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) * Real.sqrt |v| *
        ((2 + 1) * |v|) * ((1 / 2 + 1 + 1) * |v|) * Y
        = Real.sqrt (2 * Real.pi / (1 - Real.exp (-2))) *
          ((15 / 2) * (Real.sqrt |v| * |v| ^ (2 : ℕ) * Y)) := by ring
    rw [hlhs]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have : Real.sqrt |v| * |v| ^ (2 : ℕ) ≤ |v| * |v| ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right hsqle (by positivity)
    nlinarith [hYnn, this]
  rw [hnumpt, hdenpt, ← hX, ← hY]
  exact le_of_mul_le_mul_left (le_trans hcombine hcubic) hsqpi

end RHTower
