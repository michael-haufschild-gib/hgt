import GaloisForLFunctions.RHTower.RadialPSWFInteractionPicture

/-!
# The interaction amplitudes are controlled by the potential alone

For `W'' + c²W = ψW` the interaction amplitudes transport with derivatives

```text
A₊' =  e^{-icx}·ψ·W/(2ic),        A₋' = −e^{icx}·ψ·W/(2ic),
```

whose phases have unit modulus.  So both derivatives have norm exactly `‖ψ‖‖W‖/(2|c|)`, and since
the reconstruction expresses `W` as a sum of the two amplitudes against unit-modulus phases,

```text
‖A₊'‖ + ‖A₋'‖ ≤ (‖ψ‖/|c|)·(‖A₊‖ + ‖A₋‖).
```

The total amplitude is therefore governed by `ψ` alone, with the oscillation entirely absent: the
frequency `c` enters only as the divisor `1/|c|`.  This is the estimate whose integrated form
bounds the amplitudes by `exp(∫‖ψ‖/|c|)` and, when `ψ` is integrable, forces the amplitudes to
converge — the constants of the asymptotic oscillation.
-/

open Complex

noncomputable section

namespace RHTower

/-! ## Unit-modulus phases -/

theorem norm_exp_I_mul_ofReal (c x : ℝ) :
    ‖Complex.exp (Complex.I * (c : ℂ) * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  norm_num

theorem norm_exp_neg_I_mul_ofReal (c x : ℝ) :
    ‖Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  norm_num

/-! ## The transport derivatives -/

/-- The positive-frequency amplitude moves at rate `‖ψ‖‖W‖/(2|c|)`. -/
theorem norm_deriv_radialInteractionPlus (c x : ℝ) (W psi : ℝ → ℂ) :
    ‖Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x / (2 * Complex.I * (c : ℂ))‖
      = ‖psi x‖ * ‖W x‖ / (2 * |c|) := by
  rw [norm_div, norm_mul, norm_mul, norm_exp_neg_I_mul_ofReal, one_mul]
  congr 1
  rw [norm_mul, norm_mul]
  simp [Complex.norm_I]

/-- The negative-frequency amplitude moves at the same rate. -/
theorem norm_deriv_radialInteractionMinus (c x : ℝ) (W psi : ℝ → ℂ) :
    ‖-Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x / (2 * Complex.I * (c : ℂ))‖
      = ‖psi x‖ * ‖W x‖ / (2 * |c|) := by
  rw [norm_div, norm_mul, norm_mul, norm_neg, norm_exp_I_mul_ofReal, one_mul]
  congr 1
  rw [norm_mul, norm_mul]
  simp [Complex.norm_I]

/-! ## The solution is bounded by its amplitudes -/

/-- **Reconstruction bound.**  The solution never exceeds the sum of its two interaction
amplitudes, because the reconstructing phases have unit modulus. -/
theorem norm_le_norm_radialInteraction_add {c x : ℝ} (hc : c ≠ 0) (W V : ℝ → ℂ) :
    ‖W x‖ ≤ ‖radialInteractionPlus c W V x‖ + ‖radialInteractionMinus c W V x‖ := by
  rw [← radialInteraction_reconstruct hc W V]
  calc ‖radialInteractionPlus c W V x * Complex.exp (Complex.I * (c : ℂ) * (x : ℂ))
        + radialInteractionMinus c W V x * Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ))‖
      ≤ ‖radialInteractionPlus c W V x * Complex.exp (Complex.I * (c : ℂ) * (x : ℂ))‖
        + ‖radialInteractionMinus c W V x * Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ))‖ :=
        norm_add_le _ _
    _ = ‖radialInteractionPlus c W V x‖ + ‖radialInteractionMinus c W V x‖ := by
        rw [norm_mul, norm_mul, norm_exp_I_mul_ofReal, norm_exp_neg_I_mul_ofReal, mul_one,
          mul_one]

/-! ## The closed estimate -/

/-- **The amplitudes are driven by the potential alone.**  The combined transport rate of the two
interaction amplitudes is at most `‖ψ‖/|c|` times their combined size — an estimate in which the
oscillation has disappeared entirely.

This is the differential form of the Liouville–Green error bound: integrating it gives
`‖A₊‖ + ‖A₋‖ ≤ (‖A₊‖ + ‖A₋‖)(x₀)·exp(∫‖ψ‖/|c|)`, and when `ψ` is integrable the amplitudes are
Cauchy at infinity, so the solution is asymptotically a pure oscillation with constant amplitude. -/
theorem norm_deriv_radialInteraction_add_le {c x : ℝ} (hc : c ≠ 0) (W V psi : ℝ → ℂ) :
    ‖Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x / (2 * Complex.I * (c : ℂ))‖
      + ‖-Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x
          / (2 * Complex.I * (c : ℂ))‖
      ≤ ‖psi x‖ / |c|
        * (‖radialInteractionPlus c W V x‖ + ‖radialInteractionMinus c W V x‖) := by
  have hcabs : (0 : ℝ) < |c| := abs_pos.mpr hc
  rw [norm_deriv_radialInteractionPlus, norm_deriv_radialInteractionMinus]
  have hW := norm_le_norm_radialInteraction_add (x := x) hc W V
  have hsum : ‖psi x‖ * ‖W x‖ / (2 * |c|) + ‖psi x‖ * ‖W x‖ / (2 * |c|)
      = ‖psi x‖ / |c| * ‖W x‖ := by
    field_simp
    ring
  rw [hsum]
  exact mul_le_mul_of_nonneg_left hW (by positivity)

/-- The transport rate vanishes wherever the potential does: a free solution has exactly constant
interaction amplitudes. -/
theorem norm_deriv_radialInteraction_eq_zero_of_psi_zero {c x : ℝ} (W psi : ℝ → ℂ)
    (hpsi : psi x = 0) :
    ‖Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x
      / (2 * Complex.I * (c : ℂ))‖ = 0 := by
  rw [norm_deriv_radialInteractionPlus, hpsi]
  simp

end RHTower

end
