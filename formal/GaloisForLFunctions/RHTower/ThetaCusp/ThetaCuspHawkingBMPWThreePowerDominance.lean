import Mathlib

/-!
Three-power cusp dominance used by PW-B cross-clock source analysis. A unique
maximal real exponent determines the normalized complex limit without phase
assumptions. The source-specific instantiation lives in the subsequent leaf.
-/

open Complex Filter Topology
namespace RHTower.D4BMPWThreePowerDominance
noncomputable section
set_option autoImplicit false

private theorem cpow_tendsto_zero {w : ℂ} (hw : w.re < 0) :
    Tendsto (fun y : ℝ => (y : ℂ) ^ w) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hpos : 0 < -w.re := neg_pos.mpr hw
  have h : Tendsto (fun y : ℝ => (y ^ (-w.re))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop hpos)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
  rw [← Real.rpow_neg hy.le]
  congr 1
  ring

theorem three_power_dominance (c0 c1 c2 p0 p1 p2 : ℂ)
    (h0 : (p0 - p2).re < 0) (h1 : (p1 - p2).re < 0) :
    Tendsto (fun y : ℝ => (y : ℂ) ^ (-p2) *
      (c0 * (y : ℂ) ^ p0 + c1 * (y : ℂ) ^ p1 + c2 * (y : ℂ) ^ p2))
      atTop (𝓝 c2) := by
  have ht0 : Tendsto (fun y : ℝ => c0 * (y : ℂ) ^ (p0 - p2)) atTop (𝓝 0) := by
    simpa using (cpow_tendsto_zero h0).const_mul c0
  have ht1 : Tendsto (fun y : ℝ => c1 * (y : ℂ) ^ (p1 - p2)) atTop (𝓝 0) := by
    simpa using (cpow_tendsto_zero h1).const_mul c1
  have ht : Tendsto (fun y : ℝ => c0 * (y : ℂ) ^ (p0 - p2) +
      c1 * (y : ℂ) ^ (p1 - p2) + c2) atTop (𝓝 c2) := by
    simpa using (ht0.add ht1).add tendsto_const_nhds
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hp (p : ℂ) : (y : ℂ) ^ (-p2) * (y : ℂ) ^ p =
      (y : ℂ) ^ (p - p2) := by
    rw [← Complex.cpow_add _ _ hy0]
    congr 1
    ring
  have h2 : (y : ℂ) ^ (p2 - p2) = 1 := by simp
  symm
  calc
    _ = c0 * ((y : ℂ) ^ (-p2) * (y : ℂ) ^ p0) +
        c1 * ((y : ℂ) ^ (-p2) * (y : ℂ) ^ p1) +
        c2 * ((y : ℂ) ^ (-p2) * (y : ℂ) ^ p2) := by ring
    _ = _ := by rw [hp p0, hp p1, hp p2, h2]; ring

/-- The three literal cusp powers, before substituting source coefficients. -/
def reflectedThreePower (rho c0 c1 c2 : ℂ) (y : ℝ) : ℂ :=
  c0 * (y : ℂ) ^ (2 * rho) + c1 * (y : ℂ) ^ (1 : ℂ) +
    c2 * (y : ℂ) ^ (2 - 2 * rho)

theorem reflectedThreePower_left_dominance (rho c0 c1 c2 : ℂ)
    (hleft : rho.re < 1/2) :
    Tendsto (fun y : ℝ => (y : ℂ) ^ (-(2 - 2 * rho)) *
      reflectedThreePower rho c0 c1 c2 y) atTop (𝓝 c2) := by
  have h0 : (2 * rho - (2 - 2 * rho)).re < 0 := by
    norm_num [Complex.sub_re, Complex.mul_re]
    linarith
  have h1 : ((1 : ℂ) - (2 - 2 * rho)).re < 0 := by
    norm_num [Complex.sub_re, Complex.mul_re]
    linarith
  exact three_power_dominance c0 c1 c2 (2 * rho) 1 (2 - 2 * rho) h0 h1

/-- The crossed principal product cannot lose its leading coefficient on an
off-critical left-half fibre. This remains true for arbitrary lower coefficients. -/
theorem reflectedThreePower_cross_left_dominance
    (rho a0 a1 a2 b0 b1 b2 : ℂ) (hleft : rho.re < 1/2)
    (ha : a2 ≠ 0) (hb : b2 ≠ 0) :
    a2 * b2 ≠ 0 ∧
      Tendsto (fun y : ℝ =>
        ((y : ℂ) ^ (-(2 - 2 * rho)) * reflectedThreePower rho a0 a1 a2 y) *
          ((y : ℂ) ^ (-(2 - 2 * rho)) * reflectedThreePower rho b0 b1 b2 y))
        atTop (𝓝 (a2 * b2)) := by
  exact ⟨mul_ne_zero ha hb,
    (reflectedThreePower_left_dominance rho a0 a1 a2 hleft).mul
      (reflectedThreePower_left_dominance rho b0 b1 b2 hleft)⟩

end
end RHTower.D4BMPWThreePowerDominance
