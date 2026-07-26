import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Uniform envelope of the complementary-packet power-sum kernel

The complementary boundary packet of the shifted-Euler source is built from the classical
power-sum remainder

```text
R_ω(Y) = ∑_{m ≤ Y} m^ω − Y^(1+ω)/(1+ω)
```

and the divisor-clock kernel `k_ω(t) = e^(-(1+ω)t) R_ω(e^t)`.

This module proves the exact sandwich `Y^(1+ω)/(1+ω) ≤ ∑_{m ≤ Y} m^ω ≤ (Y+1)^(1+ω)/(1+ω)` at
integer arguments, deduces the sharp remainder bound `|R_ω(Y)| ≤ (Y+1)^ω` for `Y ≥ 1`, and
concludes the uniform exponential envelope

```text
|k_ω(t)| ≤ 2^ω e^(-t)      (t ≥ 0),
```

which is what makes the kernel uniformly integrable and square integrable as `ω ↓ 0`.  Only
monotonicity of `x ↦ x^ω` and the exact power integral are used; no Euler–Maclaurin expansion and
no asymptotic input enters.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-! ### The exact sum/integral sandwich for a real power -/

private theorem monotoneOn_rpow (ω : ℝ) (hω : 0 ≤ ω) (b : ℝ) :
    MonotoneOn (fun x : ℝ => x ^ ω) (Set.Icc 0 b) := by
  intro x hx y hy hxy
  exact Real.rpow_le_rpow hx.1 hxy hω

private theorem integral_rpow_zero (ω : ℝ) (hω : 0 ≤ ω) (b : ℝ) :
    (∫ x in (0 : ℝ)..b, x ^ ω) = b ^ (1 + ω) / (1 + ω) := by
  rw [integral_rpow (Or.inl (by linarith))]
  have h0 : (0 : ℝ) ^ (ω + 1) = 0 := Real.zero_rpow (by linarith)
  rw [h0, sub_zero]
  rw [show ω + 1 = 1 + ω by ring]

/-- Left endpoint sum bound: the open Riemann sum is below the power integral. -/
theorem sum_rpow_range_le (ω : ℝ) (hω : 0 ≤ ω) (N : ℕ) :
    ∑ i ∈ Finset.range N, (i : ℝ) ^ ω ≤ (N : ℝ) ^ (1 + ω) / (1 + ω) := by
  have h := MonotoneOn.sum_le_integral (f := fun x : ℝ => x ^ ω) (x₀ := 0) (a := N)
    (by simpa using monotoneOn_rpow ω hω ((0 : ℝ) + (N : ℕ)))
  simpa [integral_rpow_zero ω hω] using h

/-- Right endpoint sum bound: the closed Riemann sum is above the power integral. -/
theorem le_sum_rpow_range (ω : ℝ) (hω : 0 ≤ ω) (N : ℕ) :
    (N : ℝ) ^ (1 + ω) / (1 + ω) ≤ ∑ i ∈ Finset.range N, ((i : ℝ) + 1) ^ ω := by
  have h := MonotoneOn.integral_le_sum (f := fun x : ℝ => x ^ ω) (x₀ := 0) (a := N)
    (by simpa using monotoneOn_rpow ω hω ((0 : ℝ) + (N : ℕ)))
  simpa [integral_rpow_zero ω hω] using h

/-! ### The power-sum remainder -/

/-- The classical power-sum remainder `R_ω(Y) = ∑_{m ≤ Y} m^ω − Y^(1+ω)/(1+ω)`. -/
def powerSumRemainder (ω Y : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (⌊Y⌋₊ + 1), (i : ℝ) ^ ω) - Y ^ (1 + ω) / (1 + ω)

/-- Exact increment bound for the power primitive: `(b+1)^(1+ω) − b^(1+ω) ≤ (1+ω)(b+1)^ω`. -/
theorem rpow_succ_sub_le (ω : ℝ) (hω : 0 ≤ ω) {b : ℝ} (hb : 0 ≤ b) :
    (b + 1) ^ (1 + ω) - b ^ (1 + ω) ≤ (1 + ω) * (b + 1) ^ ω := by
  have hint : (∫ x in b..(b + 1), x ^ ω) ≤ (b + 1) ^ ω := by
    have hle : ∀ x ∈ Set.Icc b (b + 1), x ^ ω ≤ (b + 1) ^ ω := by
      intro x hx
      exact Real.rpow_le_rpow (le_trans hb hx.1) hx.2 hω
    have hmono : (∫ x in b..(b + 1), x ^ ω) ≤ ∫ _x in b..(b + 1), (b + 1) ^ ω := by
      refine intervalIntegral.integral_mono_on (by linarith) ?_ intervalIntegrable_const hle
      exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
    simpa using hmono
  have hval : (∫ x in b..(b + 1), x ^ ω)
      = ((b + 1) ^ (1 + ω) - b ^ (1 + ω)) / (1 + ω) := by
    rw [integral_rpow (Or.inl (by linarith)), show ω + 1 = 1 + ω by ring]
  rw [hval] at hint
  have hpos : (0 : ℝ) < 1 + ω := by linarith
  calc (b + 1) ^ (1 + ω) - b ^ (1 + ω)
      = (1 + ω) * (((b + 1) ^ (1 + ω) - b ^ (1 + ω)) / (1 + ω)) := by
        field_simp
    _ ≤ (1 + ω) * (b + 1) ^ ω := by
        exact mul_le_mul_of_nonneg_left hint hpos.le

/-- **Sharp power-sum remainder bound.**  For every nonnegative exponent and every `Y ≥ 0`,
`|R_ω(Y)| ≤ (Y+1)^ω`. -/
theorem abs_powerSumRemainder_le (ω : ℝ) (hω : 0 ≤ ω) {Y : ℝ} (hY : 0 ≤ Y) :
    |powerSumRemainder ω Y| ≤ (Y + 1) ^ ω := by
  have hpos : (0 : ℝ) < 1 + ω := by linarith
  set N : ℕ := ⌊Y⌋₊ with hN
  have hNY : (N : ℝ) ≤ Y := Nat.floor_le hY
  have hYN : Y < (N : ℝ) + 1 := Nat.lt_floor_add_one Y
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  -- the sum lies between the two power integrals
  have hlow : (N : ℝ) ^ (1 + ω) / (1 + ω)
      ≤ ∑ i ∈ Finset.range (N + 1), (i : ℝ) ^ ω := by
    refine le_trans (le_sum_rpow_range ω hω N) ?_
    rw [Finset.sum_range_succ']
    have heq : ∑ i ∈ Finset.range N, ((i : ℝ) + 1) ^ ω
        = ∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℝ)) ^ ω := by
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring_nf
    rw [heq]
    exact le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) ω)
  have hhigh : ∑ i ∈ Finset.range (N + 1), (i : ℝ) ^ ω
      ≤ ((N : ℝ) + 1) ^ (1 + ω) / (1 + ω) := by
    have h := sum_rpow_range_le ω hω (N + 1)
    push_cast at h
    exact h
  -- upper bound
  have hup : powerSumRemainder ω Y ≤ (Y + 1) ^ ω := by
    have h1 : powerSumRemainder ω Y
        ≤ ((N : ℝ) + 1) ^ (1 + ω) / (1 + ω) - Y ^ (1 + ω) / (1 + ω) := by
      rw [powerSumRemainder, ← hN]
      linarith
    have h2 : ((N : ℝ) + 1) ^ (1 + ω) ≤ (Y + 1) ^ (1 + ω) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    have h3 : (Y + 1) ^ (1 + ω) - Y ^ (1 + ω) ≤ (1 + ω) * (Y + 1) ^ ω :=
      rpow_succ_sub_le ω hω hY
    have h4 : ((N : ℝ) + 1) ^ (1 + ω) / (1 + ω) - Y ^ (1 + ω) / (1 + ω)
        ≤ (Y + 1) ^ ω := by
      rw [div_sub_div_same, div_le_iff₀ hpos]
      calc ((N : ℝ) + 1) ^ (1 + ω) - Y ^ (1 + ω)
          ≤ (Y + 1) ^ (1 + ω) - Y ^ (1 + ω) := by linarith
        _ ≤ (1 + ω) * (Y + 1) ^ ω := h3
        _ = (Y + 1) ^ ω * (1 + ω) := by ring
    linarith
  -- lower bound
  have hlo : -((Y + 1) ^ ω) ≤ powerSumRemainder ω Y := by
    have h1 : (N : ℝ) ^ (1 + ω) / (1 + ω) - Y ^ (1 + ω) / (1 + ω)
        ≤ powerSumRemainder ω Y := by
      rw [powerSumRemainder, ← hN]
      linarith
    have h3 : Y ^ (1 + ω) ≤ ((N : ℝ) + 1) ^ (1 + ω) :=
      Real.rpow_le_rpow hY (by linarith) (by linarith)
    have h4 : ((N : ℝ) + 1) ^ (1 + ω) - (N : ℝ) ^ (1 + ω) ≤ (1 + ω) * ((N : ℝ) + 1) ^ ω :=
      rpow_succ_sub_le ω hω hN0
    have h5 : ((N : ℝ) + 1) ^ ω ≤ (Y + 1) ^ ω :=
      Real.rpow_le_rpow (by linarith) (by linarith) hω
    have h6 : -((Y + 1) ^ ω)
        ≤ (N : ℝ) ^ (1 + ω) / (1 + ω) - Y ^ (1 + ω) / (1 + ω) := by
      rw [div_sub_div_same, le_div_iff₀ hpos]
      calc -((Y + 1) ^ ω) * (1 + ω) = -((1 + ω) * (Y + 1) ^ ω) := by ring
        _ ≤ -((1 + ω) * ((N : ℝ) + 1) ^ ω) := by nlinarith
        _ ≤ -(((N : ℝ) + 1) ^ (1 + ω) - (N : ℝ) ^ (1 + ω)) := by linarith
        _ ≤ (N : ℝ) ^ (1 + ω) - Y ^ (1 + ω) := by linarith
    linarith
  rw [abs_le]
  exact ⟨hlo, hup⟩

/-! ### The divisor-clock kernel and its uniform envelope -/

/-- The complementary-packet divisor-clock kernel `k_ω(t) = e^(-(1+ω)t) R_ω(e^t)`. -/
def complementaryPacketKernel (ω t : ℝ) : ℝ :=
  Real.exp (-(1 + ω) * t) * powerSumRemainder ω (Real.exp t)

/-- **Uniform exponential envelope.**  On the nonnegative clock axis the packet kernel is
dominated by `2^ω e^(-t)`, uniformly in the shift. -/
theorem abs_complementaryPacketKernel_le (ω : ℝ) (hω : 0 ≤ ω) {t : ℝ} (ht : 0 ≤ t) :
    |complementaryPacketKernel ω t| ≤ 2 ^ ω * Real.exp (-t) := by
  have hexp : (0 : ℝ) ≤ Real.exp t := (Real.exp_pos t).le
  have hone : (1 : ℝ) ≤ Real.exp t := Real.one_le_exp ht
  have hbound := abs_powerSumRemainder_le ω hω hexp
  have hsplit : (Real.exp t + 1) ^ ω ≤ (2 * Real.exp t) ^ ω :=
    Real.rpow_le_rpow (by linarith) (by linarith) hω
  have hmul : (2 * Real.exp t) ^ ω = 2 ^ ω * Real.exp (ω * t) := by
    rw [Real.mul_rpow (by norm_num) hexp, ← Real.exp_mul, mul_comm t ω]
  rw [complementaryPacketKernel, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (-(1 + ω) * t) * |powerSumRemainder ω (Real.exp t)|
      ≤ Real.exp (-(1 + ω) * t) * (2 * Real.exp t) ^ ω := by
        exact mul_le_mul_of_nonneg_left (le_trans hbound hsplit) (Real.exp_pos _).le
    _ = 2 ^ ω * Real.exp (-t) := by
        rw [hmul, ← mul_assoc, mul_comm (Real.exp (-(1 + ω) * t)) (2 ^ ω), mul_assoc,
          ← Real.exp_add]
        congr 2
        ring

end

end RHTower
