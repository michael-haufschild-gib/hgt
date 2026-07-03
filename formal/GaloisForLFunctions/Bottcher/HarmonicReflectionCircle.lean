/-
# Harmonic Schwarz reflection across the unit circle

The circle counterpart of `harmonicAt_reflect_line` (`HarmonicReflection.lean`).  The Green potential
`u₀ = log‖β∘γ‖` of the exterior Böttcher map is harmonic on the outer side of a smooth Julia arc and
tends to `0` at the arc (Green boundary regularity).  Its **odd reflection across the unit circle**,

  `reflectCircle u₀ w = if 1 ≤ ‖w‖ then u₀ w else - u₀ (1 / conj w)`,

is harmonic on the whole ball around a circle point — this is exactly the harmonic-extension
hypothesis `hu` of `continuesAcross_of_greenPotential_harmonic_extension` (`BottcherArcExtension.lean`).

The reflection is proved by **transport to the real axis**: the entire map `Ψ(t) = exp(-i t)` carries
the real axis to the unit circle, the upper half-plane to the exterior `{‖w‖ > 1}`, and *intertwines
complex conjugation with the circle inversion* `σ(w) = 1/conj w`:  `Ψ(conj t) = σ(Ψ t)`.  Hence
`reflectCircle u₀ ∘ Ψ` is the odd reflection across the real axis of `u₀ ∘ Ψ`, and the line reflection
`harmonicAt_reflect_line` applies; pulling back by the analytic local inverse of `Ψ`
(`exists_localInverse_of_continuation`, no branch cut) transports harmonicity to the circle point.

Off the circle the reflection is harmonic directly: `= u₀` (outer) or `= -u₀ ∘ σ` with
`σ = conj ∘ inv`, via `harmonicAt_comp_conj` and `harmonicAt_comp_analytic`.  Continuity across the arc
is the `ContinuousOn.piecewise` gluing of the two closed half-plane pieces, agreeing on the axis where
`u₀` vanishes.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import Mathlib
import GaloisForLFunctions.Bottcher.HarmonicReflection
import GaloisForLFunctions.Bottcher.InteriorModulusObstruction

open Complex Set Metric InnerProductSpace Topology Filter
open scoped Classical

namespace Bottcher

/-- **Circle inversion** `σ(w) = 1 / conj w = w / ‖w‖²`.  Fixes the unit circle, swaps interior and
exterior, and is an involution off `0`. -/
noncomputable def circleInv (w : ℂ) : ℂ := ((starRingEnd ℂ) w)⁻¹

theorem norm_circleInv (w : ℂ) : ‖circleInv w‖ = ‖w‖⁻¹ := by
  rw [circleInv, norm_inv, RCLike.norm_conj]

theorem circleInv_ne_zero {w : ℂ} (hw : w ≠ 0) : circleInv w ≠ 0 := by
  rw [circleInv]; exact inv_ne_zero (by simpa using hw)

theorem circleInv_circleInv (w : ℂ) : circleInv (circleInv w) = w := by
  rw [circleInv, circleInv, map_inv₀, Complex.conj_conj, inv_inv]

theorem circleInv_fixes {w : ℂ} (hw : ‖w‖ = 1) : circleInv w = w := by
  have hmul : (starRingEnd ℂ) w * w = 1 := by
    rw [mul_comm, Complex.mul_conj]; norm_cast
    rw [normSq_eq_norm_sq, hw]; norm_num
  rw [circleInv]; exact inv_eq_of_mul_eq_one_right hmul

/-- **Odd reflection of `u₀` across the unit circle.** -/
noncomputable def reflectCircle (u₀ : ℂ → ℝ) (w : ℂ) : ℝ :=
  if 1 ≤ ‖w‖ then u₀ w else - u₀ (circleInv w)

theorem reflectCircle_outer {u₀ : ℂ → ℝ} {w : ℂ} (hw : 1 ≤ ‖w‖) :
    reflectCircle u₀ w = u₀ w := if_pos hw

theorem reflectCircle_inner {u₀ : ℂ → ℝ} {w : ℂ} (hw : ‖w‖ < 1) :
    reflectCircle u₀ w = - u₀ (circleInv w) := if_neg (not_le.mpr hw)

/-- **Oddness of the circle reflection under inversion.**  `reflectCircle u₀ (σ w) = -reflectCircle u₀ w`
for `w ≠ 0`, provided `u₀` vanishes on the circle (needed only at `‖w‖ = 1`, where `σ` fixes `w`). -/
theorem reflectCircle_circleInv {u₀ : ℂ → ℝ} {w : ℂ} (hw : w ≠ 0)
    (hz : ‖w‖ = 1 → u₀ w = 0) :
    reflectCircle u₀ (circleInv w) = - reflectCircle u₀ w := by
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rcases lt_trichotomy ‖w‖ 1 with hlt | heq | hgt
  · have h1 : 1 < ‖circleInv w‖ := by rw [norm_circleInv]; exact (one_lt_inv₀ hpos).mpr hlt
    rw [reflectCircle_outer (le_of_lt h1), reflectCircle_inner hlt]; ring
  · rw [circleInv_fixes heq, reflectCircle_outer (le_of_eq heq.symm), hz heq]; ring
  · have h1 : ‖circleInv w‖ < 1 := by rw [norm_circleInv]; exact (inv_lt_one₀ hpos).mpr hgt
    rw [reflectCircle_inner h1, reflectCircle_outer (le_of_lt hgt), circleInv_circleInv w]

/-- **Off-circle harmonicity, exterior side.**  Where `1 < ‖w‖` and `u₀` is harmonic, so is the
reflection (there `reflectCircle u₀ = u₀`). -/
theorem harmonicAt_reflectCircle_outer {u₀ : ℂ → ℝ} {w : ℂ} (hw : 1 < ‖w‖)
    (h : HarmonicAt u₀ w) : HarmonicAt (reflectCircle u₀) w := by
  refine (harmonicAt_congr_nhds ?_).mpr h
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hw] with z hz
  exact reflectCircle_outer (le_of_lt hz)

/-- **Off-circle harmonicity, interior side.**  Where `‖w‖ < 1` (and `w ≠ 0`) and `u₀` is harmonic at
the reflected point `σ w`, the reflection `= -u₀ ∘ σ` is harmonic.  `σ = conj ∘ (·)⁻¹`, so this is
`harmonicAt_comp_conj` followed by `harmonicAt_comp_analytic` with the analytic `z ↦ z⁻¹`. -/
theorem harmonicAt_reflectCircle_inner {u₀ : ℂ → ℝ} {w : ℂ} (hw : ‖w‖ < 1) (hwne : w ≠ 0)
    (hσ : HarmonicAt u₀ (circleInv w)) : HarmonicAt (reflectCircle u₀) w := by
  -- u₀ ∘ conj is harmonic at w⁻¹  (since conj (w⁻¹) = (conj w)⁻¹ = circleInv w)
  have hcc : HarmonicAt (fun z => u₀ ((starRingEnd ℂ) z)) (w⁻¹) := by
    apply harmonicAt_comp_conj
    rw [map_inv₀]; exact hσ
  have hinv : AnalyticAt ℂ (fun z : ℂ => z⁻¹) w := by
    simpa using (analyticAt_id (𝕜 := ℂ) (z := w)).inv hwne
  have hcomp := harmonicAt_comp_analytic hcc hinv
  have hneg := hcomp.neg
  refine (harmonicAt_congr_nhds ?_).mpr hneg
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hw] with z hz
  simp only [reflectCircle_inner hz, circleInv, Pi.neg_apply, map_inv₀]

/-! ### Transport map `Ψ(t) = exp(-i t)` -/

/-- The transport map `Ψ(t) = exp(-i·t)`: it carries the real axis to the unit circle, the upper
half-plane `{Im t > 0}` to the exterior `{‖w‖ > 1}`, and **intertwines complex conjugation with the
circle inversion** `σ = circleInv`:  `σ (Ψ t) = Ψ (conj t)`. -/
noncomputable def reflTransport (t : ℂ) : ℂ := Complex.exp (-(Complex.I * t))

theorem norm_reflTransport (t : ℂ) : ‖reflTransport t‖ = Real.exp t.im := by
  rw [reflTransport, Complex.norm_exp]
  congr 1
  simp only [neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  ring

theorem reflTransport_ne_zero (t : ℂ) : reflTransport t ≠ 0 := Complex.exp_ne_zero _

theorem analyticAt_reflTransport (t : ℂ) : AnalyticAt ℂ reflTransport t := by
  apply analyticAt_cexp.comp
  exact (analyticAt_const.mul analyticAt_id).neg

theorem hasDerivAt_reflTransport (t : ℂ) :
    HasDerivAt reflTransport (reflTransport t * (-Complex.I)) t := by
  have h1 : HasDerivAt (fun t : ℂ => -(Complex.I * t)) (-Complex.I) t := by
    simpa using ((hasDerivAt_id t).const_mul Complex.I).neg
  exact h1.cexp

theorem deriv_reflTransport_ne_zero (t : ℂ) : deriv reflTransport t ≠ 0 := by
  rw [(hasDerivAt_reflTransport t).deriv]
  exact mul_ne_zero (reflTransport_ne_zero t) (by simp [Complex.I_ne_zero])

/-- **The intertwining identity.**  `circleInv (Ψ t) = Ψ (conj t)`. -/
theorem circleInv_reflTransport (t : ℂ) :
    circleInv (reflTransport t) = reflTransport ((starRingEnd ℂ) t) := by
  simp only [circleInv, reflTransport]
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_I]
  ring

end Bottcher
