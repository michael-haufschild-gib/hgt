import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# Modular horocycle-cutoff rigidity

A scalar cutoff which preserves every horocycle mode by depending only on
height cannot also be modular invariant unless it is constant.  In particular,
no nonzero compact cusp exhaustion can simultaneously be a globally modular
scalar and an exact all-height horocycle multiplier.

This is the sharp obstruction at the finite-deck cuspidal Friedrichs boundary:
a valid compact-core argument must transport the zero mode non-scalar-wise, or
prove a compensating boundary cancellation.  A height-only scalar cutoff cannot
do both jobs.
-/

open Complex UpperHalfPlane ModularGroup

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- A point on the horocycle of height `y`. -/
def horocyclePoint (x y : ℝ) (hy : 0 < y) : ℍ :=
  ⟨(x : ℂ) + (y : ℂ) * Complex.I, by
    simpa using hy⟩

theorem horocyclePoint_im (x y : ℝ) (hy : 0 < y) :
    (horocyclePoint x y hy).im = y := by
  simp [horocyclePoint]

/-- The literal height of the modular-inverted horocycle point. -/
theorem modularS_horocyclePoint_im (x y : ℝ) (hy : 0 < y) :
    (ModularGroup.S • horocyclePoint x y hy).im = y / (x ^ 2 + y ^ 2) := by
  rw [UpperHalfPlane.modular_S_smul]
  change (((-((x : ℂ) + (y : ℂ) * Complex.I))⁻¹).im) = _
  rw [inv_im]
  simp only [neg_im, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
    Complex.ofReal_re, zero_add, neg_neg]
  rw [Complex.normSq_apply]
  norm_num
  field_simp

/-- Inversion maps a suitable point on height `y` to any prescribed lower
height `t < y⁻¹`. -/
theorem modularS_horocyclePoint_hits {y t : ℝ} (hy : 0 < y) (ht : 0 < t)
    (hty : t < y⁻¹) :
    (ModularGroup.S • horocyclePoint (Real.sqrt (y / t - y ^ 2)) y hy).im = t := by
  have hty' : t * y < 1 := by
    have h : t / 1 < 1 / y := by
      simpa only [div_one, one_div] using hty
    have h' := (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 1) hy).mp h
    simpa using h'
  have hsq : t * y ^ 2 < y := by
    have h := mul_lt_mul_of_pos_right hty' hy
    nlinarith
  have hnonneg : 0 ≤ y / t - y ^ 2 := by
    apply sub_nonneg.mpr
    rw [le_div_iff₀ ht]
    nlinarith
  rw [modularS_horocyclePoint_im, Real.sq_sqrt hnonneg]
  field_simp
  ring

/-- A height profile invariant under modular inversion is constant throughout
the positive-height cusp.  No regularity or asymptotic hypothesis is used. -/
theorem modular_heightProfile_eq {α : Sort*} (g : ℝ → α)
    (hS : ∀ z : ℍ, g (ModularGroup.S • z).im = g z.im)
    {y w : ℝ} (hy : 0 < y) (hw : 0 < w) : g y = g w := by
  let t : ℝ := 1 / (y + w + 1)
  have hden : 0 < y + w + 1 := by linarith
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hty : t < y⁻¹ := by
    dsimp [t]
    have h : 1 / (y + w + 1) < 1 / y := by
      rw [div_lt_div_iff₀ hden hy]
      nlinarith
    simpa only [one_div] using h
  have htw : t < w⁻¹ := by
    dsimp [t]
    have h : 1 / (y + w + 1) < 1 / w := by
      rw [div_lt_div_iff₀ hden hw]
      nlinarith
    simpa only [one_div] using h
  let zy : ℍ := horocyclePoint (Real.sqrt (y / t - y ^ 2)) y hy
  let zw : ℍ := horocyclePoint (Real.sqrt (w / t - w ^ 2)) w hw
  have hzy : (ModularGroup.S • zy).im = t := by
    exact modularS_horocyclePoint_hits hy ht hty
  have hzw : (ModularGroup.S • zw).im = t := by
    exact modularS_horocyclePoint_hits hw ht htw
  calc
    g y = g zy.im := by rw [show zy.im = y from horocyclePoint_im _ _ hy]
    _ = g (ModularGroup.S • zy).im := (hS zy).symm
    _ = g t := by rw [hzy]
    _ = g (ModularGroup.S • zw).im := by rw [hzw]
    _ = g zw.im := hS zw
    _ = g w := by rw [show zw.im = w from horocyclePoint_im _ _ hw]

/-- Therefore a modular-invariant height profile with a zero high-cusp tail
vanishes at every positive height. -/
theorem modular_heightProfile_eq_zero_of_tail {g : ℝ → ℂ}
    (hS : ∀ z : ℍ, g (ModularGroup.S • z).im = g z.im)
    (htail : ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y → g y = 0)
    {y : ℝ} (hy : 0 < y) : g y = 0 := by
  obtain ⟨Y, hY⟩ := htail
  let w : ℝ := max Y 1
  have hw : 0 < w := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  calc
    g y = g w := modular_heightProfile_eq g hS hy hw
    _ = 0 := hY w (le_max_left _ _)

end

end GaloisForLFunctions.RHTower
