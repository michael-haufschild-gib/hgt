import GaloisForLFunctions.RHTower.HurwitzZetaRightAsymptotics
import GaloisForLFunctions.RHTower.XiSourceNormalConeDivisorConservation
import GaloisForLFunctions.HTGeometry.CosineShiftRootLimsup

/-!
# The functional-equation decomposition of the shifted standard twist

Applying the Hurwitz formula at `1 - s₀ + k` writes the factorially normalized
shifted twist `F(s₀ - k, α)/k!` as a geometric factor `(2π)^{-k}` times a
remainder built from a constant, the Gamma quotient `Γ(1-s₀+k)/Γ(1+k)`, two
quarter-turn exponentials, and the two Hurwitz zeta values at the shifts `α` and
`-α`.

Each Hurwitz value grows at its own geometric rate: the value at `α` like
`A^{-k}` and the value at `-α` like `B^{-k}`, where `A` and `B` are the smallest
exponents of the two Hurwitz series.  Those two numbers are the distances from
`α` to the integer lattice on either side, so the faster of the two rates is
`1/min(A,B)` — the reciprocal of the cusp gap.
-/

open Complex HurwitzZeta Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

section TwistFirst

/-- The smallest exponent of the Hurwitz series attached to a real shift. -/
noncomputable def twistFirst (α : ℝ) : ℝ :=
  if Int.fract α = 0 then 1 else Int.fract α

theorem twistFirst_pos (α : ℝ) : 0 < twistFirst α := by
  rw [twistFirst]
  split
  · exact one_pos
  · rename_i h
    exact lt_of_le_of_ne (Int.fract_nonneg α) (Ne.symm h)

theorem twistFirst_le_one (α : ℝ) : twistFirst α ≤ 1 := by
  rw [twistFirst]
  split
  · exact le_rfl
  · exact (Int.fract_lt_one α).le

/-- A real shift and its fractional part have the same image on the circle. -/
theorem coe_fract_unitAddCircle (α : ℝ) :
    ((Int.fract α : ℝ) : UnitAddCircle) = ((α : ℝ) : UnitAddCircle) := by
  rw [Int.fract, QuotientAddGroup.mk_sub, sub_eq_self, AddCircle.coe_eq_zero_iff]
  exact ⟨⌊α⌋, by simp⟩

/-- **The normalized Hurwitz value at a real shift tends to one.**  The
normalisation is by the smallest exponent of the series, which is one at an
integer shift and the fractional part otherwise. -/
theorem tendsto_normalizedTwist (α : ℝ) (w₀ : ℂ) :
    Tendsto (fun k : ℕ => ((twistFirst α : ℝ) : ℂ) ^ (w₀ + (k : ℂ))
        * hurwitzZeta ((α : ℝ) : UnitAddCircle) (w₀ + (k : ℂ))) atTop (𝓝 1) := by
  by_cases h : Int.fract α = 0
  · have hz : ((α : ℝ) : UnitAddCircle) = 0 := by
      rw [← coe_fract_unitAddCircle α, h]
      rfl
    have hfirst : twistFirst α = 1 := by rw [twistFirst, if_pos h]
    have hre : Tendsto (fun k : ℕ => (w₀ + (k : ℂ)).re) atTop atTop := by
      have hsimp : ∀ k : ℕ, (w₀ + (k : ℂ)).re = w₀.re + (k : ℝ) := by
        intro k; simp
      refine Tendsto.congr (fun k => (hsimp k).symm) ?_
      exact tendsto_atTop_add_const_left atTop w₀.re tendsto_natCast_atTop_atTop
    have hzeta := tendsto_riemannZeta_of_re_atTop hre
    refine hzeta.congr fun k => ?_
    rw [hfirst, hz, hurwitzZeta_zero, Complex.ofReal_one, Complex.one_cpow, one_mul]
  · have ha : 0 < Int.fract α := lt_of_le_of_ne (Int.fract_nonneg α) (Ne.symm h)
    have ha1 : Int.fract α < 1 := Int.fract_lt_one α
    have hfirst : twistFirst α = Int.fract α := by rw [twistFirst, if_neg h]
    have hbase := tendsto_normalizedHurwitz ha ha1 w₀
    refine hbase.congr fun k => ?_
    rw [hfirst, coe_fract_unitAddCircle α]

/-- The cusp gap of the standard twist at a real shift: the smaller of the two
Hurwitz exponents at `α` and at `-α`. -/
noncomputable def twistGap (α : ℝ) : ℝ := min (twistFirst α) (twistFirst (-α))

theorem twistGap_pos (α : ℝ) : 0 < twistGap α :=
  lt_min (twistFirst_pos α) (twistFirst_pos (-α))

theorem twistGap_le_one (α : ℝ) : twistGap α ≤ 1 :=
  le_trans (min_le_left _ _) (twistFirst_le_one α)

/-- At an integer shift both Hurwitz exponents are one, so the gap is one. -/
theorem twistGap_of_fract_zero {α : ℝ} (h : Int.fract α = 0) : twistGap α = 1 := by
  have hneg : Int.fract (-α) = 0 := Int.fract_neg_eq_zero.mpr h
  rw [twistGap, twistFirst, twistFirst, if_pos h, if_pos hneg, min_self]

/-- At a non-integer shift the two exponents are the distances to the integers on
either side. -/
theorem twistGap_of_fract_ne_zero {α : ℝ} (h : Int.fract α ≠ 0) :
    twistGap α = min (Int.fract α) (1 - Int.fract α) := by
  have hneg : Int.fract (-α) = 1 - Int.fract α := Int.fract_neg h
  have h2 : Int.fract (-α) ≠ 0 := by
    rw [hneg]
    intro hc
    have := Int.fract_lt_one α
    have hle : Int.fract α ≤ 1 := this.le
    have : Int.fract α = 1 := by linarith
    linarith [Int.fract_lt_one α]
  rw [twistGap, twistFirst, twistFirst, if_neg h, if_neg h2, hneg]

end TwistFirst

section Decomposition

variable {s₀ : ℂ}

/-- The remainder of the Hurwitz-formula decomposition of the shifted twist. -/
noncomputable def twistRemainder (α : ℝ) (s₀ : ℂ) (k : ℕ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ (-(1 - s₀))
    * (Complex.Gamma (1 - s₀ + (k : ℂ)) / Complex.Gamma (1 + (k : ℂ)))
    * (Complex.exp ((Real.pi : ℂ) * Complex.I * (1 - s₀ + (k : ℂ)) / 2)
          * hurwitzZeta ((α : ℝ) : UnitAddCircle) (1 - s₀ + (k : ℂ))
        + Complex.exp (-(Real.pi : ℂ) * Complex.I * (1 - s₀ + (k : ℂ)) / 2)
          * hurwitzZeta (((-α : ℝ)) : UnitAddCircle) (1 - s₀ + (k : ℂ)))

theorem shift_ne_one_sub_natCast (hs : ∀ m : ℕ, s₀ ≠ (m : ℂ)) (k n : ℕ) :
    1 - s₀ + (k : ℂ) ≠ 1 - (n : ℂ) := by
  intro hcon
  refine hs (k + n) ?_
  push_cast
  linear_combination -hcon

/-- **Hurwitz-formula decomposition of the shifted standard twist.** -/
theorem zetaTwist_decomposition (α : ℝ) (hs : ∀ m : ℕ, s₀ ≠ (m : ℂ)) (k : ℕ) :
    expZeta ((α : ℝ) : UnitAddCircle) (s₀ - (k : ℂ)) / (Nat.factorial k : ℂ)
      = ((2 * (Real.pi : ℂ))⁻¹) ^ k * twistRemainder α s₀ k := by
  have hfe := expZeta_one_sub ((α : ℝ) : UnitAddCircle)
    (s := 1 - s₀ + (k : ℂ)) (shift_ne_one_sub_natCast hs k)
  have harg : 1 - (1 - s₀ + (k : ℂ)) = s₀ - (k : ℂ) := by ring
  rw [harg] at hfe
  have hneg : -((α : ℝ) : UnitAddCircle) = (((-α : ℝ)) : UnitAddCircle) := by
    rw [← QuotientAddGroup.mk_neg]
  rw [hneg] at hfe
  have hfact : Complex.Gamma (1 + (k : ℂ)) = (Nat.factorial k : ℂ) := by
    rw [add_comm]
    exact Complex.Gamma_nat_eq_factorial k
  have hfactne : Complex.Gamma (1 + (k : ℂ)) ≠ 0 := by
    rw [hfact]
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [hfe, two_pi_cpow_shift, ← hfact, twistRemainder]
  field_simp

end Decomposition

end RHTower
