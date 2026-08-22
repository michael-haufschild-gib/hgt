import GaloisForLFunctions.RHTower.ZetaHardyQuotient

/-!
# Dividing the zeta quotient by a zero

The renormalised quotient `(s-1)ζ(s)/s^{l+2}` is a Hardy function of `w = s - 1/2` for every `l`,
because it is the Hardy function `(s-1)ζ(s)/s²` multiplied `l` times by the bounded Cauchy kernel
`1/s`.  Dividing it further by `(s-ρ)^l`, where `ρ` is a zero of `ζ` of order at least `l`, keeps it
in the Hardy space: the quotient is holomorphic across `ρ`, hence bounded there, while away from
`ρ` the multiplier `(s/(s-ρ))^l` is bounded.  This is Burnol's Proposition 4.2
(arXiv:math/0203120).

## Main results

* `zetaHardyCore`
* `zetaHardyPow_eq`
* `isHalfPlaneHardy_zetaQuotient`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Hardy representative of `(s-1)ζ(s)/s²` in the half-plane variable `w = s - 1/2`. -/
def zetaHardyCore : ℂ → ℂ :=
  fun w => (w + 1 / 2)⁻¹
    + (-1 : ℂ) * ((w - 1 / 2) / (w + 1 / 2) * laplaceRay (logChart 1 fractOverId) w)

theorem isHalfPlaneHardy_zetaHardyCore : ∃ M : ℝ, IsHalfPlaneHardy zetaHardyCore M :=
  isHalfPlaneHardy_zetaCore

theorem halfShift_re_pos {w : ℂ} (hw : 0 < w.re) : 0 < (w + 1 / 2).re := by
  have h : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  rw [Complex.add_re, h]
  linarith

theorem halfShift_ne_zero {w : ℂ} (hw : 0 < w.re) : w + 1 / 2 ≠ 0 := by
  intro hzero
  have h := halfShift_re_pos hw
  rw [hzero] at h
  simp at h

/-- The Hardy representative computes the renormalised zeta quotient. -/
theorem zetaHardyCore_eq {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1 / 2) :
    zetaHardyCore w = (w + 1 / 2 - 1) * riemannZeta (w + 1 / 2) / (w + 1 / 2) ^ 2 := by
  have hre : 0 < (w + 1 / 2).re := halfShift_re_pos hw
  have hne1 : w + 1 / 2 ≠ 1 := by
    intro h
    exact hw1 (by linear_combination h)
  have hne0 : w + 1 / 2 ≠ 0 := halfShift_ne_zero hw
  have h := zetaCore_eq hre hne1 hne0
  rw [zetaHardyCore, h]
  have hsub : (w + 1 / 2) - 1 / 2 = w := by ring
  have hsub2 : (w + 1 / 2) - 1 = w - 1 / 2 := by ring
  rw [hsub, hsub2]
  ring

/-- Iterated division by `s` stays in the Hardy space. -/
theorem isHalfPlaneHardy_zetaHardyPow (l : ℕ) :
    ∃ N : ℝ, IsHalfPlaneHardy (fun w => zetaHardyCore w * ((w + 1 / 2)⁻¹) ^ l) N := by
  obtain ⟨M, hM⟩ := isHalfPlaneHardy_zetaHardyCore
  have hhalf : (0 : ℝ) < ((1 : ℂ) / 2).re := by norm_num
  exact isHalfPlaneHardy_mul_inv_shift_pow hM hhalf l

/-- The iterated quotient computes `(s-1)ζ(s)/s^{l+2}`. -/
theorem zetaHardyPow_eq (l : ℕ) {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1 / 2) :
    zetaHardyCore w * ((w + 1 / 2)⁻¹) ^ l
      = (w + 1 / 2 - 1) * riemannZeta (w + 1 / 2) / (w + 1 / 2) ^ (l + 2) := by
  have hne0 : w + 1 / 2 ≠ 0 := halfShift_ne_zero hw
  rw [zetaHardyCore_eq hw hw1, pow_add, inv_pow]
  field_simp

/-- **Burnol's Proposition 4.2, Hardy half.**  A function holomorphic on the half-plane, continuous
at `ρ - 1/2`, whose product with `(w - (ρ - 1/2))^l` is the renormalised zeta quotient, is a Hardy
function. -/
theorem isHalfPlaneHardy_zetaQuotient {ρ : ℂ} {l : ℕ} {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H {w : ℂ | 0 < w.re})
    (hcont : ContinuousAt H (ρ - 1 / 2))
    (hHeq : ∀ w : ℂ, 0 < w.re → w ≠ ρ - 1 / 2 →
      H w * (w - (ρ - 1 / 2)) ^ l = zetaHardyCore w * ((w + 1 / 2)⁻¹) ^ l) :
    ∃ N : ℝ, IsHalfPlaneHardy H N := by
  obtain ⟨N, hN⟩ := isHalfPlaneHardy_zetaHardyPow l
  exact isHalfPlaneHardy_of_div_pow hN hH hcont hHeq

/-- **Burnol's Proposition 4.2, Hardy half, boundary form.**  The zero `ρ` may sit on the boundary
`Re ρ = 1/2` of the half-plane: only a one-sided bound on the quotient near `ρ - 1/2` is needed. -/
theorem isHalfPlaneHardy_zetaQuotient_bounded {ρ : ℂ} {l : ℕ} {H : ℂ → ℂ} {B δ : ℝ}
    (hH : DifferentiableOn ℂ H {w : ℂ | 0 < w.re}) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hHB : ∀ w : ℂ, 0 < w.re → ‖w - (ρ - 1 / 2)‖ < δ → ‖H w‖ ≤ B)
    (hHeq : ∀ w : ℂ, 0 < w.re → w ≠ ρ - 1 / 2 →
      H w * (w - (ρ - 1 / 2)) ^ l = zetaHardyCore w * ((w + 1 / 2)⁻¹) ^ l) :
    ∃ N : ℝ, IsHalfPlaneHardy H N := by
  obtain ⟨N, hN⟩ := isHalfPlaneHardy_zetaHardyPow l
  exact isHalfPlaneHardy_of_div_pow_bounded hN hH hB hδ hHB hHeq


end

end RHTower
