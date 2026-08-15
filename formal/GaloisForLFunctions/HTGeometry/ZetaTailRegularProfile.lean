import GaloisForLFunctions.HTGeometry.GammaShiftRatio
import GaloisForLFunctions.HTGeometry.GevreyZetaTailBounds
import GaloisForLFunctions.HTGeometry.ZetaTailClosedModulus
import GaloisForLFunctions.HTGeometry.IrrationalSineSubsequence

/-!
# The zeta tail is a bounded oscillation times a regular profile

The closed modulus of the irrational-power zeta tail factors exactly as

```text
|ζ(−s k)| = (|sin(π s k / 2)| · ζ(1 + s k) / π) · Γ(1 + s k) · ((2π)^{-s})^k ,
```

so with the profile `Θ(k) = C · Γ(1 + s k) · β^k`, `β = (2π)^{-s}`, the modulus is **bounded above by
`Θ` for every `k` and bounded below by a fixed multiple of the same `Θ` along the infinite set where
the sine is not small**.

The single profile on both sides is what the dominant-transfer obstruction needs: a two-sided
factorial bound with two different geometric bases would leave an exponential gap between the upper
and the lower estimate, and the comparison of one term of the coefficient recursion with the others
would fail.  Here the only irregular factor is the sine, which is bounded by `1` and bounded below
along an infinite set precisely because `s` is irrational.
-/

open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-- The geometric base of the zeta-tail profile. -/
noncomputable def zetaTailBase (s : ℝ) : ℝ := ((2 * Real.pi) ^ s)⁻¹

theorem zetaTailBase_pos (s : ℝ) : 0 < zetaTailBase s := by
  rw [zetaTailBase]
  have h : (0 : ℝ) < (2 * Real.pi) ^ s :=
    Real.rpow_pos_of_pos (by positivity) s
  exact inv_pos.mpr h

/-- **The closed modulus, written on the regular profile.** -/
theorem zetaTailModulus_eq_profile {s : ℝ} (hs : 0 < s) (k : ℕ) :
    |zetaTailModulus s k|
      = (|Real.sin (Real.pi * s * k / 2)| * zetaTailFactor s k / Real.pi)
        * gammaProfile s (zetaTailBase s) k := by
  have h2pi : (0 : ℝ) < (2 * Real.pi) ^ s := Real.rpow_pos_of_pos (by positivity) s
  have hpow : (0 : ℝ) < ((2 * Real.pi) ^ s) ^ k := pow_pos h2pi k
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [zetaTailModulus_eq hs, two_pi_rpow_split, gammaProfile, zetaTailBase, inv_pow]
  field_simp

/-- The profile itself. -/
noncomputable def zetaTailProfile (s : ℝ) (k : ℕ) : ℝ :=
  (max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖ / Real.pi) * gammaProfile s (zetaTailBase s) k

theorem zetaTailProfile_pos {s : ℝ} (hs : 0 < s) (k : ℕ) : 0 < zetaTailProfile s k := by
  rw [zetaTailProfile]
  have h1 : (0 : ℝ) < max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖ :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact mul_pos (by positivity) (gammaProfile_pos (le_of_lt hs) (zetaTailBase_pos s) k)

/-- **The tail is bounded above by the profile.** -/
theorem abs_zetaTailModulus_le_profile {s : ℝ} (hs : 0 < s) (k : ℕ) :
    |zetaTailModulus s k| ≤ zetaTailProfile s k := by
  rw [zetaTailModulus_eq_profile hs, zetaTailProfile]
  refine mul_le_mul_of_nonneg_right ?_
    (le_of_lt (gammaProfile_pos (le_of_lt hs) (zetaTailBase_pos s) k))
  have hsin : |Real.sin (Real.pi * s * k / 2)| ≤ 1 := Real.abs_sin_le_one _
  have hfac : zetaTailFactor s k ≤ max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖ := zetaTailFactor_le hs k
  have hfac0 : (0 : ℝ) ≤ zetaTailFactor s k :=
    le_trans zero_le_one (one_le_zetaTailFactor hs k)
  have hsin0 : (0 : ℝ) ≤ |Real.sin (Real.pi * s * k / 2)| := abs_nonneg _
  have hprod : |Real.sin (Real.pi * s * k / 2)| * zetaTailFactor s k
      ≤ max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖ := by
    calc |Real.sin (Real.pi * s * k / 2)| * zetaTailFactor s k
        ≤ 1 * zetaTailFactor s k := mul_le_mul_of_nonneg_right hsin hfac0
      _ = zetaTailFactor s k := by ring
      _ ≤ max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖ := hfac
  exact div_le_div_of_nonneg_right hprod (le_of_lt Real.pi_pos)

/-- **The tail meets a fixed multiple of the profile infinitely often.** -/
theorem infinite_setOf_profile_le_abs_zetaTailModulus {s : ℝ} (hs : 0 < s) (hirr : Irrational s) :
    {k : ℕ | (1 / (2 * max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖)) * zetaTailProfile s k
      ≤ |zetaTailModulus s k|}.Infinite := by
  refine Set.Infinite.mono ?_ (infinite_setOf_half_le_abs_sin_half hirr)
  intro k hk
  simp only [Set.mem_setOf_eq] at hk ⊢
  rw [zetaTailModulus_eq_profile hs, zetaTailProfile]
  set K : ℝ := max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖ with hK
  have hK1 : (1 : ℝ) ≤ K := le_max_left _ _
  have hgp : 0 < gammaProfile s (zetaTailBase s) k :=
    gammaProfile_pos (le_of_lt hs) (zetaTailBase_pos s) k
  have hKne : K ≠ 0 := by linarith
  have hstep : 1 / (2 * K) * (K / Real.pi) = 1 / (2 * Real.pi) := by
    field_simp
  have hassoc : 1 / (2 * K) * (K / Real.pi * gammaProfile s (zetaTailBase s) k)
      = (1 / (2 * Real.pi)) * gammaProfile s (zetaTailBase s) k := by
    rw [← hstep]
    ring
  rw [hassoc]
  refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hgp)
  have hfac : (1 : ℝ) ≤ zetaTailFactor s k := one_le_zetaTailFactor hs k
  rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
  have hsin0 : (0 : ℝ) ≤ |Real.sin (Real.pi * s * k / 2)| := abs_nonneg _
  nlinarith [hk, hfac, hsin0, Real.pi_pos]

/-- **The zeta tail has a regular profile**: bounded above by it everywhere and below by a fixed
multiple of it infinitely often. -/
theorem exists_regular_profile_zetaTail {s : ℝ} (hs : 0 < s) (hirr : Irrational s) :
    ∃ (Θ : ℕ → ℝ) (δ : ℝ), (∀ k, 0 < Θ k) ∧ 0 < δ ∧
      (∀ k, |zetaTailModulus s k| ≤ Θ k) ∧
      {k : ℕ | δ * Θ k ≤ |zetaTailModulus s k|}.Infinite :=
  ⟨zetaTailProfile s, 1 / (2 * max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖),
    zetaTailProfile_pos hs,
    by
      have hK1 : (1 : ℝ) ≤ max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖ := le_max_left _ _
      positivity,
    abs_zetaTailModulus_le_profile hs,
    infinite_setOf_profile_le_abs_zetaTailModulus hs hirr⟩

end GaloisForLFunctions.HTGeometry
