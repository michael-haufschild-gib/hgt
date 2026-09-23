import GaloisForLFunctions.RHTower.FirstRowModelVariation

/-!
# The leading first-row factor is a half-power symbol beyond the second dilation

Away from the turning point the Bessel comparison model no longer needs its flatness: the phase
speed `ξ_s′` is bounded there, so differentiating `J₀(cξ_s)` costs exactly one power of the
bandwidth and nothing else.  Combined with the amplitude bounds this puts the leading first-row
factor `U = A_s · J₀(c ξ_s)` in the half-power symbol class of `firstRowWeight_symbol_bounds`:

```text
|U(x)| ≤ 2/√x ,        |U′(x)| ≤ (4 + 16c/(3π))/√x       (x ≥ 2) .
```

The bandwidth appears once, in `Q′`, which is exactly where the `O(c)` of the card's
bounded-variation budget comes from.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Beyond the second dilation the exterior phase speed is at most `4/3`. -/
theorem xiSpeed_le_four_thirds {s t : ℝ} (hs : 0 ≤ s) (ht : 2 ≤ t) :
    xiSpeed s t ≤ 4 / 3 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hsq : (4 : ℝ) ≤ t ^ (2 : ℕ) := by nlinarith
  have hden : (0 : ℝ) < t ^ (2 : ℕ) - 1 := by linarith
  have hratio : (t ^ (2 : ℕ) - s) / (t ^ (2 : ℕ) - 1) ≤ (4 / 3 : ℝ) ^ (2 : ℕ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  have h := Real.sqrt_le_sqrt hratio
  rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (4 : ℝ) / 3)] at h
  exact h

/-- The leading first-row factor obeys the half-power bound on the whole exterior ray. -/
theorem abs_firstRowModel_le {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    |firstRowModel s c x| ≤ 2 / Real.sqrt x := by
  rw [firstRowModel, abs_mul]
  calc |xiAmplitude s x| * |lgBesselModel s c x|
      ≤ (2 / Real.sqrt x) * 1 := by
        refine mul_le_mul (abs_xiAmplitude_le_two_div_sqrt hs0 hs1 hx) ?_ (abs_nonneg _) ?_
        · exact abs_besselJ0_le_one _
        · have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr (lt_trans zero_lt_one hx)
          positivity
    _ = 2 / Real.sqrt x := by ring

/-- **The derivative of the leading first-row factor is a half-power symbol beyond the second
dilation**, with the bandwidth entering exactly once. -/
theorem abs_firstRowModelDeriv_le {s c x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 ≤ c)
    (hx : 2 ≤ x) :
    |firstRowModelDeriv s c x| ≤ (4 + 16 * c / (3 * Real.pi)) / Real.sqrt x := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hx1 : (1 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsx1 : (1 : ℝ) ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hspeed : xiSpeed s x ≤ 4 / 3 := xiSpeed_le_four_thirds hs0 hx
  have hspeed0 : (0 : ℝ) ≤ xiSpeed s x := (xiSpeed_pos hs1 hx1).le
  -- the two pieces
  have h1 : |xiAmplitudeDeriv s x * lgBesselModel s c x| ≤ 4 / (x * Real.sqrt x) := by
    rw [abs_mul]
    calc |xiAmplitudeDeriv s x| * |lgBesselModel s c x|
        ≤ (4 / (x * Real.sqrt x)) * 1 := by
          refine mul_le_mul (abs_xiAmplitudeDeriv_le hs0 hs1 hx) (abs_besselJ0_le_one _)
            (abs_nonneg _) (by positivity)
      _ = 4 / (x * Real.sqrt x) := by ring
  have h2 : |xiAmplitude s x * lgBesselModelDeriv s c x|
      ≤ 16 * c / (3 * Real.pi) / Real.sqrt x := by
    rw [abs_mul, lgBesselModelDeriv, abs_mul]
    have hb : |besselJ0Deriv (c * xiEndpointPhase s x)| ≤ 2 / Real.pi :=
      abs_besselJ0Deriv_le _
    have hcs : |c * xiSpeed s x| ≤ c * (4 / 3) := by
      rw [abs_of_nonneg (mul_nonneg hc hspeed0)]
      exact mul_le_mul_of_nonneg_left hspeed hc
    calc |xiAmplitude s x| * (|besselJ0Deriv (c * xiEndpointPhase s x)| * |c * xiSpeed s x|)
        ≤ (2 / Real.sqrt x) * ((2 / Real.pi) * (c * (4 / 3))) := by
          refine mul_le_mul (abs_xiAmplitude_le_two_div_sqrt hs0 hs1 hx1) ?_
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
          exact mul_le_mul hb hcs (abs_nonneg _) (by positivity)
      _ = 16 * c / (3 * Real.pi) / Real.sqrt x := by
          field_simp
          ring
  have hsum : |firstRowModelDeriv s c x|
      ≤ 4 / (x * Real.sqrt x) + 16 * c / (3 * Real.pi) / Real.sqrt x := by
    rw [firstRowModelDeriv]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  refine hsum.trans ?_
  have hxs : 4 / (x * Real.sqrt x) ≤ 4 / Real.sqrt x := by
    gcongr
    nlinarith
  have hsplit : (4 + 16 * c / (3 * Real.pi)) / Real.sqrt x
      = 4 / Real.sqrt x + 16 * c / (3 * Real.pi) / Real.sqrt x := by
    field_simp
  rw [hsplit]
  linarith

end GaloisForLFunctions.RHTower

end
