import GaloisForLFunctions.RHTower.XiMassCausticIterate

/-!
# The balance window lies inside the region

Every point within `√u` of the balance ray has propagation argument with real part at least
`(κ_B²−1)u²/2`:

`Re(τ² + w²) = σ² + (κ_B²−1)u² + 2κ_B u·Re s + Re(s²)`,  `w = κ_B u + s`,

and the two displacement terms are `O(u^{3/2})`.  So the whole window sits in the region where the
principal square root is genuine, and there the propagation rate is at least `√((κ_B²−1)/2)·u`.

That is the geometric input the Cauchy iteration needs: every disc it uses stays inside the region,
and the radius is bounded below by a multiple of the height.
-/

open Complex Metric

namespace RHTower

noncomputable section

/-- The height threshold past which the balance window is admissible. -/
def xiMassWindowThreshold (a : ℝ) : ℝ :=
  max 1 (((4 * xiMassSpacelikeSharpSlope a + 2) / (xiMassSpacelikeSharpSlope a ^ (2 : ℕ) - 1)) ^ (2 : ℕ))

theorem one_le_xiMassWindowThreshold (a : ℝ) : 1 ≤ xiMassWindowThreshold a := le_max_left _ _

/-- **The balance window has a positive propagation argument.** -/
theorem re_propagation_ge_of_window {a sigma u : ℝ} (ha : 1 / 2 < a)
    (hu : xiMassWindowThreshold a ≤ u) {s : ℂ} (hs : ‖s‖ ≤ Real.sqrt u) :
    (xiMassSpacelikeSharpSlope a ^ (2 : ℕ) - 1) * u ^ (2 : ℕ) / 2
      ≤ (((sigma : ℂ) + (u : ℂ) * Complex.I) ^ (2 : ℕ)
          + ((((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ) + s) ^ (2 : ℕ)).re := by
  set κ : ℝ := xiMassSpacelikeSharpSlope a with hκdef
  have hκ1 : 1 < κ := one_lt_xiMassSpacelikeSharpSlope ha
  have hκ0 : (0 : ℝ) < κ := by linarith
  set q : ℝ := κ ^ (2 : ℕ) - 1 with hqdef
  have hq0 : (0 : ℝ) < q := by rw [hqdef]; nlinarith
  have hu1 : (1 : ℝ) ≤ u := le_trans (one_le_xiMassWindowThreshold a) hu
  have hu0 : (0 : ℝ) < u := by linarith
  have huth : (((4 * κ + 2) / q) ^ (2 : ℕ) : ℝ) ≤ u := by
    refine le_trans ?_ hu
    rw [xiMassWindowThreshold, ← hκdef, ← hqdef]
    exact le_max_right _ _
  set r : ℝ := Real.sqrt u with hrdef
  have hr0 : (0 : ℝ) < r := Real.sqrt_pos.2 hu0
  have hrsq : r ^ (2 : ℕ) = u := Real.sq_sqrt hu0.le
  have hr1 : (1 : ℝ) ≤ r := by nlinarith
  have hrq : (4 * κ + 2) / q ≤ r := by
    have hnn : (0 : ℝ) ≤ (4 * κ + 2) / q := by positivity
    nlinarith
  have hqr : 4 * κ + 2 ≤ q * r := by
    rw [div_le_iff₀ hq0] at hrq
    linarith
  -- the real part, expanded
  have hre : (((sigma : ℂ) + (u : ℂ) * Complex.I) ^ (2 : ℕ)
        + ((((κ * u : ℝ)) : ℂ) + s) ^ (2 : ℕ)).re
      = sigma ^ (2 : ℕ) + q * u ^ (2 : ℕ) + 2 * κ * u * s.re + (s ^ (2 : ℕ)).re := by
    have hexp : ((sigma : ℂ) + (u : ℂ) * Complex.I) ^ (2 : ℕ) + ((((κ * u : ℝ)) : ℂ) + s) ^ (2 : ℕ)
        = (((sigma ^ (2 : ℕ) + q * u ^ (2 : ℕ) : ℝ)) : ℂ) + ((2 * κ * u : ℝ) : ℂ) * s + s ^ (2 : ℕ)
          + (((2 * sigma * u : ℝ)) : ℂ) * Complex.I := by
      rw [hqdef]
      push_cast
      linear_combination Complex.I_sq * ((u : ℂ) ^ (2 : ℕ))
    rw [hexp]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hsre : |s.re| ≤ r := le_trans (Complex.abs_re_le_norm s) hs
  have hs2 : |(s ^ (2 : ℕ)).re| ≤ u := by
    have h1 : |(s ^ (2 : ℕ)).re| ≤ ‖s ^ (2 : ℕ)‖ := Complex.abs_re_le_norm _
    have h2 : ‖s ^ (2 : ℕ)‖ ≤ u := by
      rw [norm_pow]
      nlinarith [norm_nonneg s, hs, hrsq]
    linarith
  have hmid : -(2 * κ * u * r) ≤ 2 * κ * u * s.re := by
    have h := (abs_le.mp hsre).1
    have hscale := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 * κ * u)
    nlinarith [hscale]
  have hlow : -u ≤ (s ^ (2 : ℕ)).re := (abs_le.mp hs2).1
  rw [hre]
  have hgeom : 2 * κ * u * r + u ≤ q * u ^ (2 : ℕ) / 2 := by
    have hprod : (4 * κ + 2) * r ^ (3 : ℕ) ≤ (q * r) * r ^ (3 : ℕ) :=
      mul_le_mul_of_nonneg_right hqr (by positivity)
    rw [← hrsq]
    nlinarith [hprod, hr1, hr0]
  nlinarith [sq_nonneg sigma, hmid, hlow, hgeom]

/-- **The balance window lies inside the region.** -/
theorem window_subset_xiMassHeightRegion {a sigma u : ℝ} (ha : 1 / 2 < a)
    (hu : xiMassWindowThreshold a ≤ u) {w : ℂ}
    (hw : ‖w - (((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ)‖ ≤ Real.sqrt u) :
    w ∈ xiMassHeightRegion ((sigma : ℂ) + (u : ℂ) * Complex.I) := by
  have hκ1 : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  have hq0 : (0 : ℝ) < xiMassSpacelikeSharpSlope a ^ (2 : ℕ) - 1 := by nlinarith
  have hu1 : (1 : ℝ) ≤ u := le_trans (one_le_xiMassWindowThreshold a) hu
  have hu0 : (0 : ℝ) < u := by linarith
  have hs : w = (((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ)
      + (w - (((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ)) := by ring
  rw [mem_xiMassHeightRegion, hs]
  have hbound := re_propagation_ge_of_window (sigma := sigma) ha hu hw
  have hpos : (0 : ℝ) < (xiMassSpacelikeSharpSlope a ^ (2 : ℕ) - 1) * u ^ (2 : ℕ) / 2 := by positivity
  linarith

end

end RHTower
