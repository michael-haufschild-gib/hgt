import GaloisForLFunctions.RHTower.IMSBootstrapObstruction

/-!
# The second spectral moment adds nothing, and the elementary tower is optimal

The last unused elementary constraint was the second spectral moment.  For `h ∈ H¹₀([-ℓ,ℓ])` with
`‖h‖₂ = 1`, the Dirichlet eigenvalue of the interval gives

```text
∫ ξ² dν(ξ) = ‖h'‖₂² ≥ π²/(4ℓ²) = Ξ_*² ,      Ξ_* = π/(2ℓ) ,
```

exactly the square of the cutoff that appeared in the threshold law.  The uniform measure on
`[0,Ξ_*]` — the extremal measure of the band constraint — has second moment `Ξ_*²/3`, so it
**violates** this constraint, and one might hope the true minimum is strictly larger.

It is not.  Take `ν_q` = the uniform density `1/Ξ_*` on `[0,(1-q)Ξ_*]` together with an atom of mass
`q` at

```text
b_q = Ξ_* · sqrt( (1 - (1-q)³/3) / q ) .
```

By construction `ν_q` satisfies the band constraint (its density never exceeds `1/Ξ_*` below `b_q`)
and meets the second-moment constraint with equality.  Its cost is

```text
∫ σ dν_q = (1/Ξ_*)∫_0^{(1-q)Ξ_*} σ + q σ(b_q) ,
```

and with `σ(ξ) ≤ C + log ξ`,

```text
q σ(b_q) ≤ q(C + log Ξ_*) + (q/2)·log( (1 - (1-q)³/3)/q ) ≤ q(C + log Ξ_*) + (q/2)log(1/q) + q ,
```

which tends to `0`, uniformly bounded by `q(C + log Ξ_*) + 1/(2e) + q` since `q log(1/q) ≤ 1/e`.  So
as `q → 0` the cost converges to the old value: **a vanishing mass at a diverging frequency satisfies
the second-moment constraint for free.**

With that, every elementary lever is closed:

* damped primes — never activated, the archimedean baseline binds first (cycle 26);
* IMS bootstrap — scale-invariant error `≥ π²` beats the logarithmic gap (cycle 28);
* second moment — vacuous, by the family above (this file);
* prolate refinement — re-enters the Connes–Consani machinery the tower was built to avoid.

The elementary threshold `ℓ₀ = π/(2t₀) ≈ 0.2497`, `t₀` the first zero of the Riemann–Siegel theta
function, is therefore **optimal within these means**, and the residual gap to `(log 2)/2` requires a
genuinely different input.

This file formalizes the construction, its second moment, the logarithmic cost bound, and the
elementary inequality `q log(1/q) ≤ 1/e` that makes the cost uniformly small.
-/

open Real

noncomputable section

namespace RHTower

/-- `log t ≤ t/e` for `t > 0`, from `log u ≤ u - 1` at `u = t/e`. -/
theorem log_le_div_exp_one {t : ℝ} (ht : 0 < t) : Real.log t ≤ t / Real.exp 1 := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hu : (0 : ℝ) < t / Real.exp 1 := by positivity
  have h := Real.log_le_sub_one_of_pos hu
  rw [Real.log_div (ne_of_gt ht) (ne_of_gt he), Real.log_exp] at h
  linarith

/-- **`q·log(1/q) ≤ 1/e`** for `0 < q`, the uniform bound making the atom's cost negligible. -/
theorem mul_log_inv_le {q : ℝ} (hq : 0 < q) : q * Real.log (1 / q) ≤ 1 / Real.exp 1 := by
  have hinv : (0 : ℝ) < 1 / q := by positivity
  have h := log_le_div_exp_one hinv
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hstep : q * Real.log (1 / q) ≤ q * ((1 / q) / Real.exp 1) :=
    mul_le_mul_of_nonneg_left h hq.le
  have hrw : q * ((1 / q) / Real.exp 1) = 1 / Real.exp 1 := by
    field_simp
  linarith [hrw ▸ hstep]

/-- **The extremal family.**  With mass `q` placed at `b_q`, the second-moment constraint is met with
equality. -/
theorem atom_second_moment {Ξ q b : ℝ} (hq : 0 < q) (hΞ : 0 < Ξ)
    (hb : b ^ 2 = Ξ ^ 2 * (1 - (1 - q) ^ 3 / 3) / q) :
    (1 - q) ^ 3 * Ξ ^ 2 / 3 + q * b ^ 2 = Ξ ^ 2 := by
  rw [hb]
  field_simp
  ring

/-- The atom sits above the uniform block, so the band constraint is respected. -/
theorem atom_above_block {Ξ q b : ℝ} (hq : 0 < q) (hq1 : q < 1) (hΞ : 0 < Ξ)
    (hb : b ^ 2 = Ξ ^ 2 * (1 - (1 - q) ^ 3 / 3) / q) (hbpos : 0 < b) :
    (1 - q) * Ξ ≤ b := by
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have h1qle : (1 : ℝ) - q ≤ 1 := by linarith
  have hcube : (1 - q) ^ 3 ≤ 1 := pow_le_one₀ h1q.le h1qle
  have hsq : (1 - q) ^ 2 ≤ 1 := pow_le_one₀ h1q.le h1qle
  have hcube0 : (0 : ℝ) ≤ (1 - q) ^ 3 := by positivity
  have hkey : ((1 - q) * Ξ) ^ 2 ≤ b ^ 2 := by
    rw [hb, le_div_iff₀ hq]
    nlinarith [hsq, hcube0, sq_nonneg Ξ, h1q]
  have hposprod : 0 < (1 - q) * Ξ := mul_pos h1q hΞ
  nlinarith [hkey, hbpos, hposprod]

/-- **Cost of the atom.**  With `σ(ξ) ≤ C + log ξ`, the atom contributes at most
`q(C + log Ξ) + (q/2)log(1/q) + q`, hence at most `q(C + log Ξ) + 1/(2e) + q`. -/
theorem atom_cost_bound {Ξ q C σb : ℝ} (hq : 0 < q) (_hq1 : q < 1) (_hΞ : 0 < Ξ)
    (hσ : σb ≤ C + Real.log Ξ + Real.log (1 / q) / 2 + 1) :
    q * σb ≤ q * (C + Real.log Ξ) + 1 / (2 * Real.exp 1) + q := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hstep : q * σb ≤ q * (C + Real.log Ξ + Real.log (1 / q) / 2 + 1) :=
    mul_le_mul_of_nonneg_left hσ hq.le
  have hlog := mul_log_inv_le hq
  have hrw : q * (C + Real.log Ξ + Real.log (1 / q) / 2 + 1)
      = q * (C + Real.log Ξ) + (q * Real.log (1 / q)) / 2 + q := by ring
  have hhalf : (q * Real.log (1 / q)) / 2 ≤ 1 / (2 * Real.exp 1) := by
    have hrw2 : 1 / (2 * Real.exp 1) = (1 / Real.exp 1) / 2 := by
      field_simp
    rw [hrw2]
    linarith [hlog]
  linarith [hrw ▸ hstep, hhalf]

end RHTower
