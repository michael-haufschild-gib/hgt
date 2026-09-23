import GaloisForLFunctions.RHTower.DirichletLPhragmenInputs

/-!
# A cubic bound for the L-function on a disc

On any disc centred on the line `Re s = a` whose left edge stays right of `Re s = -2`, the
L-function is `O((2 + |t|)^(3 : ℕ))`, with `t` the height of the centre and the implied constant depending
only on the radius and on `a`.

Right of `Re s = 2` the Dirichlet series is bounded outright; on the remaining part of the disc the
Phragmén–Lindelöf cubic bound applies, and `‖z - 4‖` is controlled by the radius plus the height.
-/

open Complex Metric

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- **Cubic bound on a disc.** -/
theorem exists_bound_LFunction_disc {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {a R : ℝ} (hR : 0 ≤ R) (hlow : -2 ≤ a - R) :
    ∃ E : ℝ, 0 < E ∧ ∀ t : ℝ, ∀ z : ℂ, ‖z - ((a : ℂ) + (t : ℝ) * I)‖ ≤ R →
      ‖DirichletCharacter.LFunction χ z‖ ≤ E * (2 + |t|) ^ (3 : ℕ) := by
  obtain ⟨C₁, hC₁, hright⟩ := exists_bound_LFunction_of_two_le_re χ
  obtain ⟨C₂, hC₂, hstrip⟩ := bound_LFunction_strip hχ hprim
  set D : ℝ := R + |a - 4| with hD
  have hD0 : (0 : ℝ) ≤ D := by rw [hD]; positivity
  refine ⟨C₁ + C₂ * (D + 1) ^ (3 : ℕ), by positivity, fun t z hz => ?_⟩
  set c : ℂ := (a : ℂ) + (t : ℝ) * I with hc
  have hcre : c.re = a := by rw [hc]; simp
  have hcim : c.im = t := by rw [hc]; simp
  have ht0 : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hbase : (1 : ℝ) ≤ 2 + |t| := by linarith
  have hbase3 : (1 : ℝ) ≤ (2 + |t|) ^ (3 : ℕ) := one_le_pow₀ hbase
  have hD1 : (0 : ℝ) ≤ (D + 1) ^ (3 : ℕ) := by positivity
  have hEle : C₁ ≤ C₁ + C₂ * (D + 1) ^ (3 : ℕ) := by nlinarith [hC₂.le, hD1]
  rcases le_or_gt 2 z.re with hge | hlt
  · calc ‖DirichletCharacter.LFunction χ z‖ ≤ C₁ := hright z hge
      _ ≤ (C₁ + C₂ * (D + 1) ^ (3 : ℕ)) * (2 + |t|) ^ (3 : ℕ) := by nlinarith [hC₁.le, hbase3, hEle]
  · -- the real part is trapped between `-2` and `3`
    have hrele : |z.re - a| ≤ R := by
      have hre := Complex.abs_re_le_norm (z - c)
      rw [Complex.sub_re, hcre] at hre
      exact le_trans hre hz
    have hre2 : (-2 : ℝ) ≤ z.re := by
      have := abs_le.mp hrele
      linarith [this.1]
    have hre3 : z.re ≤ 3 := by linarith
    have hz4 : ‖z - 4‖ ≤ D + |t| := by
      have h1 : ‖z - 4‖ ≤ ‖z - c‖ + ‖c - 4‖ := by
        have hsplit : z - 4 = (z - c) + (c - 4) := by ring
        rw [hsplit]
        exact norm_add_le _ _
      have h2 : ‖c - 4‖ ≤ |a - 4| + |t| := by
        refine (Complex.norm_le_abs_re_add_abs_im (c - 4)).trans ?_
        rw [Complex.sub_re, Complex.sub_im, hcre, hcim]
        simp
      rw [hD]
      linarith
    have hz4' : ‖z - 4‖ ≤ (D + 1) * (2 + |t|) := by nlinarith [hD0, ht0]
    calc ‖DirichletCharacter.LFunction χ z‖ ≤ C₂ * ‖z - 4‖ ^ (3 : ℕ) := hstrip z hre2 hre3
      _ ≤ C₂ * ((D + 1) * (2 + |t|)) ^ (3 : ℕ) := by
          refine mul_le_mul_of_nonneg_left ?_ hC₂.le
          exact pow_le_pow_left₀ (norm_nonneg _) hz4' 3
      _ = C₂ * (D + 1) ^ (3 : ℕ) * (2 + |t|) ^ (3 : ℕ) := by ring
      _ ≤ (C₁ + C₂ * (D + 1) ^ (3 : ℕ)) * (2 + |t|) ^ (3 : ℕ) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          linarith [hC₁.le]

end RHTower
