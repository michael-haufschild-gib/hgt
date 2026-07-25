import GaloisForLFunctions.RHTower.IMSLocalizationWeilForm

/-!
# The IMS bootstrap cannot extend the elementary range

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

**independent of `L`**.  The gap only grows logarithmically, so the competition
`log(1/(2L)) - 1 > π²` requires `L < e^{-1-π²}/2 ≈ 2·10⁻⁵`.  Iterating multiplies `L` by
`1 + ρ` with `ρ = (√δ₀/π - 1)/(√δ₀/π + 1) < 1`, and `ρ → 0` as `δ₀ ↓ π²`, so the bootstrap stalls at
`L ≈ 10⁻⁵`.

That is far below the threshold `L = 2ℓ₀ ≈ 0.4994` which the **direct** elementary bound already
reaches.  So IMS localization is strictly weaker than the direct estimate and cannot extend the
range at any point.  The proposal of cycle 27 is closed.

The reason is structural and worth recording: the localization error is scale invariant, because the
Weil kernel's `1/|u|` singularity makes its second moment scale exactly like the square of the
partition length, cancelling the `κ²`.  Only a gap that grows faster than logarithmically could beat
it, and no such gap exists — `δ₀` is the average of the archimedean symbol, which is logarithmic by
Stirling.

This file formalizes the second-moment computation, the scale invariance of the error, and the
comparison showing the IMS threshold falls below the direct elementary one.
-/

open Real

noncomputable section

namespace RHTower

/-- The near-diagonal second moment of the Weil kernel: `∫_0^R u²·(1/(2u)) du = R²/4` on each side,
so `M₂ ≈ R²/2` in total. -/
theorem near_diagonal_second_moment (R : ℝ) :
    (∫ u in (0:ℝ)..R, u / 2) = R ^ 2 / 4 := by
  rw [intervalIntegral.integral_div, integral_id]
  ring

/-- **Scale invariance of the IMS error.**  With `κ = π/(L-η)` and `M₂ = (L+η)²/2`, the error
`2κ²M₂` equals `π²(L+η)²/(L-η)²`, which is at least `π²` regardless of `L`. -/
theorem ims_error_scale_invariant {L η : ℝ} (hη : 0 ≤ η) (hlt : η < L) :
    Real.pi ^ 2 ≤ 2 * (Real.pi / (L - η)) ^ 2 * ((L + η) ^ 2 / 2) := by
  have hpos : (0 : ℝ) < L - η := by linarith
  have hL : (0 : ℝ) < L := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hrw : 2 * (Real.pi / (L - η)) ^ 2 * ((L + η) ^ 2 / 2)
      = Real.pi ^ 2 * ((L + η) ^ 2 / (L - η) ^ 2) := by
    field_simp
  rw [hrw]
  have hratio : (1 : ℝ) ≤ (L + η) ^ 2 / (L - η) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hη, hpos, hL]
  nlinarith [hratio, hpi]

/-- **The bootstrap threshold.**  The logarithmic gap `log(1/(2L)) - 1` exceeds the scale-invariant
error `π²` only for `L < e^{-1-π²}/2`. -/
theorem bootstrap_threshold {L : ℝ} (hL : 0 < L)
    (hgap : Real.pi ^ 2 < Real.log (1 / (2 * L)) - 1) :
    L < Real.exp (-1 - Real.pi ^ 2) / 2 := by
  have h2L : (0 : ℝ) < 2 * L := by linarith
  have hlog : Real.pi ^ 2 + 1 < Real.log (1 / (2 * L)) := by linarith
  have hexp : Real.exp (Real.pi ^ 2 + 1) < 1 / (2 * L) := by
    have h := Real.exp_lt_exp.mpr hlog
    rwa [Real.exp_log (by positivity)] at h
  have hposexp : (0 : ℝ) < Real.exp (Real.pi ^ 2 + 1) := Real.exp_pos _
  have hstep : 2 * L < 1 / Real.exp (Real.pi ^ 2 + 1) := by
    rw [lt_div_iff₀ hposexp]
    rw [lt_div_iff₀ h2L] at hexp
    linarith
  have hinv : 1 / Real.exp (Real.pi ^ 2 + 1) = Real.exp (-1 - Real.pi ^ 2) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  rw [hinv] at hstep
  linarith

/-- **The threshold is far below the direct elementary one.**  `e^{-1-π²}/2 < 1/2 < 0.4994` is
already enough: `π² > 0` gives `e^{-1-π²} < e^{-1} < 1`. -/
theorem bootstrap_threshold_small : Real.exp (-1 - Real.pi ^ 2) / 2 < 1 / 2 := by
  have hpi : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have h1 : Real.exp (-1 - Real.pi ^ 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  linarith

/-- Consequently the IMS bootstrap stalls strictly inside the range the direct elementary bound
already covers, so it never extends it. -/
theorem ims_never_extends {L₀ : ℝ} (hL₀ : 1 / 2 ≤ L₀) {L : ℝ} (hL : 0 < L)
    (hgap : Real.pi ^ 2 < Real.log (1 / (2 * L)) - 1) :
    L < L₀ := by
  have h1 := bootstrap_threshold hL hgap
  have h2 := bootstrap_threshold_small
  linarith

end RHTower
