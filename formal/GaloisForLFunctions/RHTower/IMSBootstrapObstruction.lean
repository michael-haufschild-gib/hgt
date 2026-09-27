import GaloisForLFunctions.RHTower.IMSLocalizationWeilForm

/-!
# A scale-invariant model budget for IMS localization

Cycle 27 proposed feeding the elementary gap through the IMS localization bound.  The elementary
tower does carry a gap: dropping the nonnegative pole square,

```text
Q_{2ℓ}(h) ≥ δ₀(ℓ)‖h‖² ,     δ₀(ℓ) = (4ℓ/π)·θ(π/(2ℓ)) - 2(sinh ℓ - ℓ) ,
```

and `δ₀(ℓ) → +∞` as `ℓ → 0`, since `2θ(Ξ)/Ξ = log(Ξ/2π) - 1 + o(1)`.  Writing `L = 2ℓ` for the
support length, `δ₀ = log(1/(2L)) - 1 + o(1)`.  A quadratic partition of unity satisfies
`‖χ₁h‖² + ‖χ₂h‖² = ‖h‖²`, so IMS gives

```text
Q_{L+η} ≥ ( δ₀(L) - 2κ²M₂ ) ‖h‖² ,     κ = π/(L-η),  M₂ = ∫_{|u| ≤ L+η}|K(u)|u² du .
```

Near the diagonal the Weil kernel is dominated by the archimedean singularity `1/(2|u|)`, so

```text
M₂ ≈ ∫_{-(L+η)}^{L+η} u²/(2|u|) du = (L+η)²/2 ,
```

whence the error is

```text
2κ²M₂ ≈ π²·(L+η)²/(L-η)² ≥ π² ,
```

**independent of `L`** in this model. The competition
`log(1/(2L)) - 1 > π²` requires `L < exp(-1-π²)/2`.

The statements below prove the model second moment, its scale invariance, and
this exact logarithmic threshold. They do not bound the actual signed arithmetic
localization error below by the model budget. In particular, failure of a
sufficient estimate is not an impossibility theorem for localization, and these
lemmas do not establish failure of every IMS bootstrap for the full Weil form.
The final comparison applies to reference lengths at least `1/2`; it does not
compare with a claimed elementary threshold smaller than `1/2`.
-/

open Real

noncomputable section

namespace RHTower

/-- The near-diagonal second moment of the Weil kernel: `∫_0^R u²·(1/(2u)) du = R²/4` on each side,
so `M₂ ≈ R²/2` in total. -/
theorem near_diagonal_second_moment (R : ℝ) :
    (∫ u in (0:ℝ)..R, u / 2) = R ^ (2 : ℕ) / 4 := by
  rw [intervalIntegral.integral_div, integral_id]
  ring

/-- **Scale invariance of the IMS error.**  With `κ = π/(L-η)` and `M₂ = (L+η)²/2`, the error
`2κ²M₂` equals `π²(L+η)²/(L-η)²`, which is at least `π²` regardless of `L`. -/
theorem ims_error_scale_invariant {L η : ℝ} (hη : 0 ≤ η) (hlt : η < L) :
    Real.pi ^ (2 : ℕ) ≤ 2 * (Real.pi / (L - η)) ^ (2 : ℕ) * ((L + η) ^ (2 : ℕ) / 2) := by
  have hpos : (0 : ℝ) < L - η := by linarith
  have hL : (0 : ℝ) < L := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hrw : 2 * (Real.pi / (L - η)) ^ (2 : ℕ) * ((L + η) ^ (2 : ℕ) / 2)
      = Real.pi ^ (2 : ℕ) * ((L + η) ^ (2 : ℕ) / (L - η) ^ (2 : ℕ)) := by
    field_simp
  rw [hrw]
  have hratio : (1 : ℝ) ≤ (L + η) ^ (2 : ℕ) / (L - η) ^ (2 : ℕ) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hη, hpos, hL]
  nlinarith [hratio, hpi]

/-- **The bootstrap threshold.**  The logarithmic gap `log(1/(2L)) - 1` exceeds the scale-invariant
error `π²` only for `L < e^{-1-π²}/2`. -/
theorem bootstrap_threshold {L : ℝ} (hL : 0 < L)
    (hgap : Real.pi ^ (2 : ℕ) < Real.log (1 / (2 * L)) - 1) :
    L < Real.exp (-1 - Real.pi ^ (2 : ℕ)) / 2 := by
  have h2L : (0 : ℝ) < 2 * L := by linarith
  have hlog : Real.pi ^ (2 : ℕ) + 1 < Real.log (1 / (2 * L)) := by linarith
  have hexp : Real.exp (Real.pi ^ (2 : ℕ) + 1) < 1 / (2 * L) := by
    have h := Real.exp_lt_exp.mpr hlog
    rwa [Real.exp_log (by positivity)] at h
  have hposexp : (0 : ℝ) < Real.exp (Real.pi ^ (2 : ℕ) + 1) := Real.exp_pos _
  have hstep : 2 * L < 1 / Real.exp (Real.pi ^ (2 : ℕ) + 1) := by
    rw [lt_div_iff₀ hposexp]
    rw [lt_div_iff₀ h2L] at hexp
    linarith
  have hinv : 1 / Real.exp (Real.pi ^ (2 : ℕ) + 1) = Real.exp (-1 - Real.pi ^ (2 : ℕ)) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  rw [hinv] at hstep
  linarith

/-- The model threshold is below `1/2`. This alone gives no comparison with a
reference length smaller than `1/2`. -/
theorem bootstrap_threshold_small : Real.exp (-1 - Real.pi ^ (2 : ℕ)) / 2 < 1 / 2 := by
  have hpi : (0 : ℝ) < Real.pi ^ (2 : ℕ) := by positivity
  have h1 : Real.exp (-1 - Real.pi ^ (2 : ℕ)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  linarith

/-- A length satisfying the model gap condition is below every reference length
at least `1/2`. The name records the original proposed application. -/
theorem ims_never_extends {L₀ : ℝ} (hL₀ : 1 / 2 ≤ L₀) {L : ℝ} (hL : 0 < L)
    (hgap : Real.pi ^ (2 : ℕ) < Real.log (1 / (2 * L)) - 1) :
    L < L₀ := by
  have h1 := bootstrap_threshold hL hgap
  have h2 := bootstrap_threshold_small
  linarith

end RHTower
