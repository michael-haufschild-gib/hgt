import GaloisForLFunctions.RHTower.Sieve.PairFibre

/-!
# Markers in the upper half of the outer block dominate every cofactor
-/

namespace RHTower.Sieve

open Finset

/-- **A marker above `(3/2)√x` exceeds every cofactor of every such marker.**  This is the
`hsmall` side condition of `Sieve/MarkerBlockLower.card_markerBlockTargets_ge`: restricting the
markers to the upper part of the outer block makes every fibre element smaller than every marker. -/
theorem fibre_lt_marker {x h : ℝ} (hx : 16 ≤ x) (hh : 0 ≤ h) (hhx : h ≤ Real.sqrt x)
    {p r b : ℕ} (hpge : (3 / 2) * Real.sqrt x ≤ (p : ℝ))
    (hrge : (3 / 2) * Real.sqrt x ≤ (r : ℝ))
    (hb : b ∈ innerFibre x h p) : b < r := by
  rw [mem_innerFibre] at hb
  obtain ⟨-, -, hhigh⟩ := hb
  have hx0 : (0 : ℝ) < x := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hs4 : (4 : ℝ) ≤ Real.sqrt x := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hcast : ((p * b : ℕ) : ℝ) = (p : ℝ) * (b : ℝ) := by push_cast; ring
  rw [hcast] at hhigh
  -- the top of the window is at most `2x`
  have htop : x + h * Real.sqrt x ≤ 2 * x := by nlinarith [hhx, hs0, hsq]
  have hpb : (p : ℝ) * (b : ℝ) ≤ 2 * x := by linarith
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg _
  -- hence `b ≤ (4/3)√x < (3/2)√x ≤ r`
  have hble : (b : ℝ) ≤ (4 / 3) * Real.sqrt x := by
    nlinarith [hpb, hpge, hb0, hs0, hsq]
  have hlt : (b : ℝ) < (r : ℝ) := by
    have : (4 / 3) * Real.sqrt x < (3 / 2) * Real.sqrt x := by nlinarith [hs0]
    linarith
  exact_mod_cast hlt

end RHTower.Sieve
