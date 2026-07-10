import Mathlib

/-!
# Quiet flank growth bounds arithmetic support

The quiet-crossing contour argument produces, at each contour depth `M`, a coefficient estimate of
the shape

`‖a n / 2‖ ≤ H(M) * (n - 1/2)^(1-M)`.

This module isolates the growth-to-support endgame from the particular functional equation that
produces `H`.  If `H(M)` has a geometric envelope `C * R^M`, the fixed three-knot estimate kills
every coefficient with `R < n - 1/2`.  Allowing Perron knots `n ± δ` for every `0 < δ < 1` removes
that artifact: a nonzero coefficient then satisfies the exact bound `n ≤ R`.

The distinction matters: an arbitrary flank majorant can always be inflated, so its exponential
rate gives an upper support bound, not an equality.  Equality can only be discussed after choosing
an intrinsic minimal envelope.
-/

noncomputable section

namespace RHTower

open Filter
open scoped Topology

/-- The frequency scale left by the three-knot Perron kernel at coefficient index `n`. -/
def perronSupportScale (n : ℕ) : ℝ := (n : ℝ) - 1 / 2

/-- The coefficient estimate supplied by a quiet contour with flank majorant `H`.  Fixed numerical
constants from the contour can be absorbed into `H`. -/
def HasQuietFlankCoefficientBound (a : ℕ → ℂ) (H : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ᶠ M : ℕ in atTop,
    ‖a n * (1 / 2)‖ ≤ H M * perronSupportScale n ^ (1 - (M : ℝ))

/-- **Geometric flank envelopes decay past their support radius.**  If `H(M) ≤ C R^M` eventually
and `R < D`, then `H(M) D^(1-M)` tends to zero.  This is the abstract ratio-test endgame of the
conductor quiet-crossing theorem. -/
theorem tendsto_flank_product_of_geometric_envelope
    {H : ℕ → ℝ} {C R D : ℝ}
    (hR : 0 ≤ R) (hD : 0 < D) (hRD : R < D)
    (hH0 : ∀ᶠ M : ℕ in atTop, 0 ≤ H M)
    (hH : ∀ᶠ M : ℕ in atTop, H M ≤ C * R ^ M) :
    Tendsto (fun M : ℕ => H M * D ^ (1 - (M : ℝ))) atTop (𝓝 0) := by
  set r : ℝ := R * D⁻¹ with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr, ← div_eq_mul_inv, div_lt_one hD]; exact hRD
  have hpow : Tendsto (fun M : ℕ => r ^ M) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hmajor : Tendsto (fun M : ℕ => (C * D) * r ^ M) atTop (𝓝 0) := by
    simpa using hpow.const_mul (C * D)
  have hnonneg : ∀ᶠ M : ℕ in atTop, 0 ≤ H M * D ^ (1 - (M : ℝ)) := by
    filter_upwards [hH0] with M hHM0
    exact mul_nonneg hHM0 (Real.rpow_nonneg hD.le _)
  have hle : ∀ᶠ M : ℕ in atTop,
      H M * D ^ (1 - (M : ℝ)) ≤ (C * D) * r ^ M := by
    filter_upwards [hH] with M hHM
    calc
      H M * D ^ (1 - (M : ℝ)) ≤ (C * R ^ M) * D ^ (1 - (M : ℝ)) :=
        mul_le_mul_of_nonneg_right hHM (Real.rpow_nonneg hD.le _)
      _ = (C * D) * r ^ M := by
        rw [Real.rpow_sub hD, Real.rpow_one, Real.rpow_natCast, hr,
          div_eq_mul_inv, mul_pow]
        ring
  exact squeeze_zero' hnonneg hle hmajor

/-- If the full quiet-flank coefficient majorant tends to zero, the coefficient vanishes. -/
theorem coefficient_eq_zero_of_quiet_flank_decay
    {a : ℕ → ℂ} {H : ℕ → ℝ} {n : ℕ}
    (hbound : HasQuietFlankCoefficientBound a H n)
    (hdecay : Tendsto
      (fun M : ℕ => H M * perronSupportScale n ^ (1 - (M : ℝ))) atTop (𝓝 0)) :
    a n = 0 := by
  have hzero : ‖a n * (1 / 2)‖ ≤ 0 := ge_of_tendsto hdecay hbound
  have hmul : a n * (1 / 2) = 0 :=
    norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))
  exact (mul_eq_zero.mp hmul).resolve_right (by norm_num)

/-- **Growth-to-support capstone.**  A geometric flank radius strictly below the Perron frequency
scale forces the corresponding coefficient to vanish. -/
theorem coefficient_eq_zero_of_geometric_quiet_flank
    {a : ℕ → ℂ} {H : ℕ → ℝ} {n : ℕ} {C R : ℝ}
    (hn : 1 ≤ n) (hR : 0 ≤ R)
    (hRscale : R < perronSupportScale n)
    (hH0 : ∀ᶠ M : ℕ in atTop, 0 ≤ H M)
    (hH : ∀ᶠ M : ℕ in atTop, H M ≤ C * R ^ M)
    (hbound : HasQuietFlankCoefficientBound a H n) :
    a n = 0 := by
  apply coefficient_eq_zero_of_quiet_flank_decay hbound
  exact tendsto_flank_product_of_geometric_envelope hR
    (by
      rw [perronSupportScale]
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith)
    hRscale hH0 hH

/-- Contrapositive support form: every nonzero coefficient has Perron scale at most the geometric
flank radius. -/
theorem perronSupportScale_le_of_ne_zero_geometric_quiet_flank
    {a : ℕ → ℂ} {H : ℕ → ℝ} {n : ℕ} {C R : ℝ}
    (hn : 1 ≤ n) (hR : 0 ≤ R)
    (hH0 : ∀ᶠ M : ℕ in atTop, 0 ≤ H M)
    (hH : ∀ᶠ M : ℕ in atTop, H M ≤ C * R ^ M)
    (hbound : HasQuietFlankCoefficientBound a H n)
    (han : a n ≠ 0) :
    perronSupportScale n ≤ R := by
  by_contra hscale
  exact han (coefficient_eq_zero_of_geometric_quiet_flank hn hR (lt_of_not_ge hscale)
    hH0 hH hbound)

/-- Arithmetic-index form of the support bound: `a n ≠ 0` implies `n ≤ R + 1/2`. -/
theorem coefficient_index_le_flank_radius
    {a : ℕ → ℂ} {H : ℕ → ℝ} {n : ℕ} {C R : ℝ}
    (hn : 1 ≤ n) (hR : 0 ≤ R)
    (hH0 : ∀ᶠ M : ℕ in atTop, 0 ≤ H M)
    (hH : ∀ᶠ M : ℕ in atTop, H M ≤ C * R ^ M)
    (hbound : HasQuietFlankCoefficientBound a H n)
    (han : a n ≠ 0) :
    (n : ℝ) ≤ R + 1 / 2 := by
  have hscale := perronSupportScale_le_of_ne_zero_geometric_quiet_flank
    hn hR hH0 hH hbound han
  rw [perronSupportScale] at hscale
  linarith

/-! ### Variable Perron knots remove the half-unit artifact -/

/-- The left-edge frequency scale for Perron knots `n ± δ`. -/
def perronSupportScaleAt (n : ℕ) (δ : ℝ) : ℝ := (n : ℝ) - δ

/-- Quiet-flank coefficient estimates for every admissible knot width `0 < δ < 1`.  The smoothed
Perron second difference at `n+δ,n,n-δ` isolates `δ * a n`; its left-edge scale is `n-δ`. -/
def HasVariableQuietFlankCoefficientBound (a : ℕ → ℂ) (H : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → δ < (n : ℝ) →
    ∀ᶠ M : ℕ in atTop,
      ‖a n * (δ : ℂ)‖ ≤ H M * perronSupportScaleAt n δ ^ (1 - (M : ℝ))

/-- A geometric flank envelope of radius `R < n` forces `a n = 0` once the quiet coefficient
estimate is available at every Perron knot width.  Choose
`δ ≤ min(1/2,(n-R)/2)`, so `R < n-δ`, and apply the geometric decay theorem. -/
theorem coefficient_eq_zero_of_geometric_variable_quiet_flank
    {a : ℕ → ℂ} {H : ℕ → ℝ} {n : ℕ} {C R : ℝ}
    (hn : 1 ≤ n) (hR : 0 ≤ R) (hRn : R < (n : ℝ))
    (hH0 : ∀ᶠ M : ℕ in atTop, 0 ≤ H M)
    (hH : ∀ᶠ M : ℕ in atTop, H M ≤ C * R ^ M)
    (hbound : HasVariableQuietFlankCoefficientBound a H n) :
    a n = 0 := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set δ : ℝ := min (1 / 2) (((n : ℝ) - R) / 2) with hδ
  have hgap : 0 < (n : ℝ) - R := sub_pos.mpr hRn
  have hδ0 : 0 < δ := by rw [hδ, lt_min_iff]; constructor <;> linarith
  have hδhalf : δ ≤ 1 / 2 := by rw [hδ]; exact min_le_left _ _
  have hδgap : δ ≤ ((n : ℝ) - R) / 2 := by rw [hδ]; exact min_le_right _ _
  have hδ1 : δ < 1 := by linarith
  have hδn : δ < (n : ℝ) := by linarith
  have hDpos : 0 < perronSupportScaleAt n δ := by
    rw [perronSupportScaleAt]
    linarith
  have hRD : R < perronSupportScaleAt n δ := by
    rw [perronSupportScaleAt]
    linarith
  have hcoeff := hbound δ hδ0 hδ1 hδn
  have hdecay : Tendsto
      (fun M : ℕ => H M * perronSupportScaleAt n δ ^ (1 - (M : ℝ))) atTop (𝓝 0) :=
    tendsto_flank_product_of_geometric_envelope hR hDpos hRD hH0 hH
  have hzero : ‖a n * (δ : ℂ)‖ ≤ 0 := ge_of_tendsto hdecay hcoeff
  have hmul : a n * (δ : ℂ) = 0 :=
    norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))
  exact (mul_eq_zero.mp hmul).resolve_right (by exact_mod_cast ne_of_gt hδ0)

/-- **Exact variable-knot support bound.**  If a coefficient is nonzero, its integer index is at
most the geometric flank radius.  The `+1/2` in `coefficient_index_le_flank_radius` is therefore a
fixed-knot artifact, not an intrinsic loss. -/
theorem coefficient_index_le_exact_flank_radius
    {a : ℕ → ℂ} {H : ℕ → ℝ} {n : ℕ} {C R : ℝ}
    (hn : 1 ≤ n) (hR : 0 ≤ R)
    (hH0 : ∀ᶠ M : ℕ in atTop, 0 ≤ H M)
    (hH : ∀ᶠ M : ℕ in atTop, H M ≤ C * R ^ M)
    (hbound : HasVariableQuietFlankCoefficientBound a H n)
    (han : a n ≠ 0) :
    (n : ℝ) ≤ R := by
  by_contra hnr
  exact han (coefficient_eq_zero_of_geometric_variable_quiet_flank hn hR (lt_of_not_ge hnr)
    hH0 hH hbound)

end RHTower
