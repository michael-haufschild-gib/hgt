import Mathlib

/-!
# Blow-up of an Euler recursion

A recursion `Φ_{i+1} ≥ Φ_i + β e^{σ Φ_i}` drives `ψ = e^{-σΦ}` down by at least `σβ/2` per step
while `ψ` is above half its initial value, because `e^{-u} ≤ 1/(1+u)` turns one step into
`ψ ↦ ψ²/(ψ + σβ)`, and `ψ²/(ψ + σβ) ≤ ψ − σβ/2` exactly when `σβ ≤ ψ`.

Hence `ψ` halves within `ψ₀/(σβ)` steps.  The point is the scaling: `β` is proportional to the step
length `h`, so the number of steps is proportional to `1/h` and the *elapsed parameter* `N h` is
independent of `h`.  Halving repeatedly therefore drives `Φ` past every bound in a bounded parameter
range — the discrete replacement for the differential inequality `φ' ≥ c e^{σφ}`.
-/

namespace GaloisForLFunctions.HTGeometry

/-- One Euler step halves the reciprocal exponential by at least `σβ/2`. -/
theorem euler_step {Φ β σ x : ℝ} (hβ : 0 < β) (hσ : 0 < σ)
    (hstep : Φ + β * Real.exp (σ * Φ) ≤ x)
    (hge : σ * β ≤ Real.exp (-(σ * Φ))) :
    Real.exp (-(σ * x)) ≤ Real.exp (-(σ * Φ)) - σ * β / 2 := by
  set ψ : ℝ := Real.exp (-(σ * Φ)) with hψ
  have hψ0 : 0 < ψ := Real.exp_pos _
  have hinv : Real.exp (σ * Φ) = ψ⁻¹ := by
    rw [hψ, ← Real.exp_neg]
    congr 1
    ring
  -- the step in the exponent
  have hexp : Real.exp (-(σ * x)) ≤ ψ * Real.exp (-(σ * β * ψ⁻¹)) := by
    have hle : -(σ * x) ≤ -(σ * Φ) + -(σ * β * ψ⁻¹) := by
      have h1 : σ * (Φ + β * Real.exp (σ * Φ)) ≤ σ * x :=
        mul_le_mul_of_nonneg_left hstep hσ.le
      rw [hinv] at h1
      nlinarith [h1]
    calc Real.exp (-(σ * x)) ≤ Real.exp (-(σ * Φ) + -(σ * β * ψ⁻¹)) := Real.exp_le_exp.mpr hle
      _ = ψ * Real.exp (-(σ * β * ψ⁻¹)) := by rw [Real.exp_add]
  -- `exp(-u) ≤ 1/(1+u)`
  have hu0 : (0 : ℝ) < σ * β * ψ⁻¹ := by positivity
  have hrecip : Real.exp (-(σ * β * ψ⁻¹)) ≤ 1 / (1 + σ * β * ψ⁻¹) := by
    have h1 : 1 + σ * β * ψ⁻¹ ≤ Real.exp (σ * β * ψ⁻¹) := by
      have := Real.add_one_le_exp (σ * β * ψ⁻¹)
      linarith
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by linarith)]
    linarith
  have hchain : Real.exp (-(σ * x)) ≤ ψ * (1 / (1 + σ * β * ψ⁻¹)) := by
    refine le_trans hexp ?_
    exact mul_le_mul_of_nonneg_left hrecip hψ0.le
  -- algebra: `ψ/(1 + σβ/ψ) = ψ²/(ψ + σβ) ≤ ψ − σβ/2` when `σβ ≤ ψ`
  have hval : ψ * (1 / (1 + σ * β * ψ⁻¹)) = ψ ^ 2 / (ψ + σ * β) := by
    field_simp
  have hden : (0 : ℝ) < ψ + σ * β := by positivity
  have hfin : ψ ^ 2 / (ψ + σ * β) ≤ ψ - σ * β / 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_right hge (le_of_lt (mul_pos hσ hβ)), hψ0]
  rw [hval] at hchain
  linarith [hchain, hfin]

/-- **Euler blow-up in `N` steps.**  A recursion `Φ_{i+1} ≥ Φ_i + β e^{σ Φ_i}` halves
`e^{-σ Φ}` within `ψ₀/(σβ)` steps, and the number of steps needed is inversely proportional to `β`
— so the *time* consumed, `N·h` with `β` proportional to `h`, does not depend on `h`. -/
theorem exp_le_half_of_euler_recursion {Φ : ℕ → ℝ} {β σ : ℝ} (hβ : 0 < β) (hσ : 0 < σ)
    {N : ℕ} (hrec : ∀ i, i < N → Φ i + β * Real.exp (σ * Φ i) ≤ Φ (i + 1))
    (hhalf : σ * β ≤ Real.exp (-(σ * Φ 0)) / 2)
    (hN : Real.exp (-(σ * Φ 0)) ≤ (N : ℝ) * (σ * β)) :
    Real.exp (-(σ * Φ N)) ≤ Real.exp (-(σ * Φ 0)) / 2 := by
  set ψ₀ : ℝ := Real.exp (-(σ * Φ 0)) with hψ₀
  have hψ₀0 : 0 < ψ₀ := Real.exp_pos _
  have hmono : ∀ i, i < N → Φ i ≤ Φ (i + 1) := by
    intro i hi
    have h := hrec i hi
    have : 0 < β * Real.exp (σ * Φ i) := by positivity
    linarith
  have hinv : ∀ i, i ≤ N →
      Real.exp (-(σ * Φ i)) ≤ ψ₀ - (i : ℝ) * (σ * β) / 2
        ∨ Real.exp (-(σ * Φ i)) ≤ ψ₀ / 2 := by
    intro i
    induction i with
    | zero => intro _; left; simp [hψ₀]
    | succ i ih =>
        intro hle
        have hiN : i < N := by omega
        have hiN' : i ≤ N := by omega
        have hdec : Real.exp (-(σ * Φ (i + 1))) ≤ Real.exp (-(σ * Φ i)) := by
          refine Real.exp_le_exp.mpr ?_
          have := hmono i hiN
          nlinarith [this, hσ]
        rcases ih hiN' with hleft | hright
        · rcases le_or_gt (Real.exp (-(σ * Φ i))) (ψ₀ / 2) with hsmall | hbig
          · right; linarith
          · left
            have hge : σ * β ≤ Real.exp (-(σ * Φ i)) := by linarith
            have hstep := euler_step hβ hσ (hrec i hiN) hge
            push_cast
            linarith [hstep, hleft]
        · right; linarith
  rcases hinv N le_rfl with hleft | hright
  · linarith [hleft, hN]
  · exact hright

end GaloisForLFunctions.HTGeometry
