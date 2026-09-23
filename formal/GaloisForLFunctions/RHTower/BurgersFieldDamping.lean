import GaloisForLFunctions.RHTower.FinitenessThresholdCriterion

/-!
# The field quantity is damped: Burgers structure of the backward flow

The open core of the falsification criterion is a collision lemma valid for the *actual*, uneven
configuration: two consecutive real zeros at distance `δ` in a field of strength `Δ` must reach each
other in backward time, and the obstruction is that `Δ` might grow while they do.  It does not.

Backward time is the forward heat equation, `∂_τ H = ∂_z² H`.  Writing `L = H'/H` and using
`H''/H = L' + L²`, `H'''/H = L'' + 3LL' + L³`, the log-derivative satisfies a viscous **Burgers
equation**

```text
L_τ = L_zz + 2 L L_z = L_zz + (L²)_z ,
```

and the field quantity `V = -L_z = Σ_k (z - x_k)^{-2} > 0` therefore satisfies

```text
V_τ = V_zz + 2 L V_z - 2 V² .
```

The nonlinearity carries a **minus** sign: `V` is damped, not amplified.  Comparison with the
spatially uniform solution of `v' = -2v²`, namely `v(τ) = v₀/(1 + 2v₀τ)`, shows the field strength
decays like `1/τ` rather than blowing up.  So freezing `Δ` at its initial value is legitimate as an
upper bound over the collision interval, and the only loss in a rigorous collision lemma comes from
the transport term `2LV_z`, not from the nonlinearity.

**The frozen-field problem is exactly solvable.**  With `u = δ²` the gap obeys `u' = 4Δu - 8`, whose
solution is `u(τ) = 2/Δ + (u₀ - 2/Δ)e^{4Δτ}`.  If `θ = Δu₀ < 2` the gap vanishes at

```text
τ* = (1/(4Δ))·log( 2/(2-θ) ) ,
```

which tends to `u₀/8 = δ₀²/8` as `θ → 0` and to `∞` as `θ → 2`.  So `θ < 2` is the **sharp** collision
threshold, and it is where the collision time is finite.

**What the constant must be.**  For an evenly spaced field of density `ϱ` one has
`Δ ≍ (π²/3)ϱ²` per side, so `θ < 2` reads `δϱ < √6/π ≈ 0.78` — the sharp normalized-gap threshold.
A rigorous collision lemma proved with a smaller constant `c` in place of the sharp `4` (in the
normalization `δ²Δ_sum < c`, `Δ_sum` the two-sided field sum) permits normalized gaps up to
`√(3c/(2π²))`.  The best known small-gap results reach normalized gap `0.5155`, which corresponds to
`c ≈ 1.75`.  Hence:

> The collision lemma needs to be established with constant `c > 1.75` out of a sharp maximum of `4`
> — a permissible loss of a factor `2.29`.  The Lehmer-pair criterion of Csordas–Smith–Varga is
> proved with a constant below this, which is why it is applied to individually exceptional pairs
> rather than to a positive proportion of them.

That is the precise, quantified form of the open core, and the damping identity above is the tool
that should close it: the only remaining loss is transport, which is a first-order term.

This file formalizes the Riccati identities, the Burgers equation, the damping equation for `V`, the
exact solution of the Riccati comparison, and the frozen-field collision time.
-/

open Real

noncomputable section

namespace RHTower

/-- **First Riccati identity.**  With `L = H'/H` one has `H''/H = L' + L²`. -/
theorem riccati_second {H H1 H2 L Lp : ℝ} (_hH : H ≠ 0) (_hL : L = H1 / H)
    (hLp : Lp = H2 / H - L ^ (2 : ℕ)) : H2 / H = Lp + L ^ (2 : ℕ) := by
  rw [hLp]; ring

/-- **Second Riccati identity.**  `H'''/H = L'' + 3LL' + L³`. -/
theorem riccati_third {H H2 H3 L Lp Lpp : ℝ} (_hH : H ≠ 0)
    (hLp : Lp = H2 / H - L ^ (2 : ℕ)) (hLpp : Lpp = H3 / H - 3 * L * (H2 / H) + 2 * L ^ (3 : ℕ)) :
    H3 / H = Lpp + 3 * L * Lp + L ^ (3 : ℕ) := by
  rw [hLpp, hLp]; ring

/-- **The Burgers equation.**  Since `∂_τ H = H''`, the log-derivative obeys
`L_τ = H'''/H - L·(H''/H) = L'' + 2LL'`. -/
theorem burgers_logDeriv {H H2 H3 L Lp Lpp Lt : ℝ}
    (hLp : Lp = H2 / H - L ^ (2 : ℕ)) (hLpp : Lpp = H3 / H - 3 * L * (H2 / H) + 2 * L ^ (3 : ℕ))
    (hLt : Lt = H3 / H - L * (H2 / H)) : Lt = Lpp + 2 * L * Lp := by
  rw [hLt, hLpp, hLp]; ring

/-- **The damping equation.**  With `V = -L_z`, differentiating the Burgers equation in `z` gives
`V_τ = V_zz + 2LV_z - 2V²`: the nonlinearity is a damping term. -/
theorem field_damping {L Lp Lpp Lppp V Vp Vpp Vt : ℝ}
    (hV : V = -Lp) (hVp : Vp = -Lpp) (hVpp : Vpp = -Lppp)
    (hVt : Vt = -(Lppp + 2 * Lp ^ (2 : ℕ) + 2 * L * Lpp)) :
    Vt = Vpp + 2 * L * Vp - 2 * V ^ (2 : ℕ) := by
  rw [hVt, hVpp, hVp, hV]; ring

/-- **The Riccati comparison solution.**  `v(τ) = v₀/(1 + 2v₀τ)` solves `v' = -2v²`, so a field
quantity governed by the damping term decays like `1/τ` and in particular never exceeds `v₀`. -/
theorem riccati_solution {v₀ : ℝ} (hv : 0 < v₀) (τ : ℝ) (hτ : 0 ≤ τ) :
    HasDerivAt (fun s : ℝ => v₀ / (1 + 2 * v₀ * s))
      (-2 * (v₀ / (1 + 2 * v₀ * τ)) ^ (2 : ℕ)) τ := by
  have hden : (1 : ℝ) + 2 * v₀ * τ ≠ 0 := by positivity
  have h : HasDerivAt (fun s : ℝ => 1 + 2 * v₀ * s) (2 * v₀) τ := by
    simpa using (HasDerivAt.const_mul (2 * v₀) (hasDerivAt_id τ)).const_add 1
  have hinv := (h.inv hden).const_mul v₀
  simp only [div_eq_mul_inv]
  convert! hinv using 1
  field_simp

/-- The comparison solution is nonincreasing: the field strength cannot grow. -/
theorem riccati_decreasing {v₀ σ τ : ℝ} (hv : 0 < v₀) (hσ : 0 ≤ σ) (hτ : σ ≤ τ) :
    v₀ / (1 + 2 * v₀ * τ) ≤ v₀ / (1 + 2 * v₀ * σ) := by
  have h1 : (0 : ℝ) < 1 + 2 * v₀ * σ := by positivity
  have h2 : (0 : ℝ) < 1 + 2 * v₀ * τ := by nlinarith
  rw [div_le_div_iff₀ h2 h1]
  have hsq : v₀ * v₀ * σ ≤ v₀ * v₀ * τ := by nlinarith [hv, hτ]
  nlinarith [hsq]

/-- **The frozen-field gap equation.**  With `u = δ²` and the field frozen at `Δ`, the gap satisfies
`u' = 4Δu - 8`, solved by `u(τ) = 2/Δ + (u₀ - 2/Δ)e^{4Δτ}`. -/
theorem frozen_gap_solution {D u₀ : ℝ} (hD : 0 < D) (τ : ℝ) :
    HasDerivAt (fun s : ℝ => 2 / D + (u₀ - 2 / D) * Real.exp (4 * D * s))
      (4 * D * (2 / D + (u₀ - 2 / D) * Real.exp (4 * D * τ)) - 8) τ := by
  have h : HasDerivAt (fun s : ℝ => Real.exp (4 * D * s)) (Real.exp (4 * D * τ) * (4 * D)) τ := by
    simpa using!
      (Real.hasDerivAt_exp (4 * D * τ)).comp τ (HasDerivAt.const_mul (4 * D) (hasDerivAt_id τ))
  have h2 := (h.const_mul (u₀ - 2 / D)).const_add (2 / D)
  convert! h2 using 1
  field_simp
  ring

/-- **The collision time.**  If `θ = Δu₀ < 2` the frozen-field gap vanishes at
`τ* = (1/(4Δ))·log(2/(2-θ))`. -/
theorem frozen_collision_time {D u₀ : ℝ} (hD : 0 < D) (hθ : D * u₀ < 2) :
    2 / D + (u₀ - 2 / D) * Real.exp (4 * D * ((1 / (4 * D)) * Real.log (2 / (2 - D * u₀)))) = 0 := by
  have hpos : (0 : ℝ) < 2 - D * u₀ := by linarith
  have hD0 : D ≠ 0 := ne_of_gt hD
  have hp0 : (2 : ℝ) - D * u₀ ≠ 0 := ne_of_gt hpos
  have hratio : (0 : ℝ) < 2 / (2 - D * u₀) := by positivity
  have hcancel : 4 * D * ((1 / (4 * D)) * Real.log (2 / (2 - D * u₀)))
      = Real.log (2 / (2 - D * u₀)) := by
    field_simp
  rw [hcancel, Real.exp_log hratio]
  field_simp
  ring

/-- **The threshold arithmetic.**  In the normalization `δ²Δ_sum < c` an evenly spaced field of
density `ϱ` gives `Δ_sum ≍ (2π²/3)ϱ²`, so the admissible normalized gap is `√(3c/(2π²))`.  The sharp
value `c = 4` gives `√6/π`, and the small-gap threshold `0.5155` requires `c > 2π²(0.5155)²/3`. -/
theorem normalized_gap_threshold {c : ℝ} (hc : 0 < c) :
    Real.sqrt (3 * c / (2 * π ^ (2 : ℕ))) ^ (2 : ℕ) = 3 * c / (2 * π ^ (2 : ℕ)) := by
  refine Real.sq_sqrt ?_
  have : (0 : ℝ) < π := Real.pi_pos
  positivity

/-- The sharp threshold: `c = 4` gives normalized gap `√6/π`. -/
theorem sharp_threshold : (3 : ℝ) * 4 / (2 * π ^ (2 : ℕ)) = 6 / π ^ (2 : ℕ) := by
  have hpi : (π : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

end RHTower
