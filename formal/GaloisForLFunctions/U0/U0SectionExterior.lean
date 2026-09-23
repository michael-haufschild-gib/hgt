/-
# Large parameters push the tower geometry into `u₀`'s domain

The `GBExt` clause of the all-parameters U0 card needs `u₀` to extend analytically to the tower's
extension domains — impossible in general because `u₀` has the unit circle as natural boundary.
This file proves that for `‖b‖` large the obstruction is EMPTY:

* `green_sublevel_exterior` — the whole Green sublevel set `{G_b < t}` lies outside the closed
  unit disk once `exp(4t) + 4 ≤ (‖b‖−1)² − ‖b‖`.  A unit-disk point takes two quadratic steps to
  modulus `≥ (‖b‖−1)² − ‖b‖`, where `‖φ_b‖ = exp(G_b)` and `‖φ_b(y) − y‖ ≤ 4‖b‖/‖y‖` force
  `G_b ≥ ¼·log((‖b‖−1)² − ‖b‖ − 4)` — so small Green level means large modulus.
* `tower_section_image_exterior` / `tower_section_image_subset_Ext` — every tower section on a
  band `rlo < ‖w‖ < rhi` with `rhi⁴ + 4 ≤ (‖b‖−1)² − ‖b‖` has its image inside `{|z| > 1}`,
  i.e. inside `u₀`'s domain: `u₀` restricts to the section geometry directly.

Consequence for the tower certificate: at large `‖b‖` the `GBExt` element exists wherever the
extension domain is built inside a Green sublevel band — the geometric obstruction to the
`u₀`-clause is confined to small parameters.
-/
import GaloisForLFunctions.U0.U0PhiLargeCarrier
import GaloisForLFunctions.Bottcher.SectionTower
import GaloisForLFunctions.Bottcher.GreenSublevel
import GaloisForLFunctions.Bottcher.PolyAsymptotic
import GaloisForLFunctions.Bottcher.BasinColimit

open Complex Set Metric Bottcher U0NaturalBoundary
open U0PhiLargeCarrier

namespace U0SectionExterior

/-- **Green sublevel sets of large parameters avoid the closed unit disk.**  If
`exp(4t) + 4 ≤ (‖b‖−1)² − ‖b‖` then every `z` with `G_b(z) < t` has `‖z‖ > 1`. -/
theorem green_sublevel_exterior {b : ℂ} (hb : 4 ≤ ‖b‖) {t : ℝ}
    (hband : Real.exp (4 * t) + 4 ≤ (‖b‖ - 1) ^ (2 : ℕ) - ‖b‖)
    {z : ℂ} (hz : greenFunctionDyn b z < t) :
    1 < ‖z‖ := by
  by_cases hK : z ∈ filledJulia b
  · exact filledJulia_exterior hb hK
  by_contra hle
  push Not at hle
  -- two quadratic steps reach the deep escape regime
  have hfz : ‖b‖ - 1 ≤ ‖quadratic b z‖ := by
    have htri : ‖b‖ ≤ ‖z ^ (2 : ℕ) + b‖ + ‖z ^ (2 : ℕ)‖ := by
      calc ‖b‖ = ‖z ^ (2 : ℕ) + b - z ^ (2 : ℕ)‖ := by ring_nf
        _ ≤ ‖z ^ (2 : ℕ) + b‖ + ‖z ^ (2 : ℕ)‖ := norm_sub_le _ _
    have hp : ‖z ^ (2 : ℕ)‖ = ‖z‖ ^ (2 : ℕ) := norm_pow z 2
    show ‖b‖ - 1 ≤ ‖z ^ (2 : ℕ) + b‖
    nlinarith [htri, hle, norm_nonneg z]
  set y : ℂ := quadratic b (quadratic b z) with hy
  have hyL : (‖b‖ - 1) ^ (2 : ℕ) - ‖b‖ ≤ ‖y‖ := by
    have htri : ‖(quadratic b z) ^ (2 : ℕ)‖ ≤ ‖(quadratic b z) ^ (2 : ℕ) + b‖ + ‖b‖ :=
      norm_le_add_norm_add _ _
    have hp : ‖(quadratic b z) ^ (2 : ℕ)‖ = ‖quadratic b z‖ ^ (2 : ℕ) := norm_pow _ 2
    show (‖b‖ - 1) ^ (2 : ℕ) - ‖b‖ ≤ ‖(quadratic b z) ^ (2 : ℕ) + b‖
    nlinarith [htri, hfz, hb]
  have hexp_pos : (0 : ℝ) < Real.exp (4 * t) := Real.exp_pos _
  have hyb : ‖b‖ < ‖y‖ := by nlinarith [hyL, hb, hexp_pos]
  have hy2 : (2 : ℝ) < ‖y‖ := by linarith [hyb, hb]
  have hyesc : y ∈ escapeOpen b := by
    show max 2 ‖b‖ < ‖y‖
    rw [max_eq_right (by linarith : (2 : ℝ) ≤ ‖b‖)]
    exact hyb
  have hynotK : y ∉ filledJulia b := escapeOpen_subset_compl_filledJulia b hyesc
  -- the Böttcher modulus bound: exp(G_b(y)) = ‖φ_b(y)‖ ≥ ‖y‖ − 4
  have hphi : ‖bottcherCoord b y‖ = Real.exp (greenLimit b y) :=
    norm_bottcherCoord_eq_exp_green_escape hyesc
  have hsub : ‖bottcherCoord b y - y‖ ≤ 4 * ‖b‖ / ‖y‖ :=
    norm_bottcherCoord_sub_id_le hyb.le hy2
  have hdivle : 4 * ‖b‖ / ‖y‖ ≤ 4 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖y‖)]
    nlinarith [hyb, hb]
  have hlower : ‖y‖ - 4 ≤ ‖bottcherCoord b y‖ := by
    have htri : ‖y‖ ≤ ‖bottcherCoord b y‖ + ‖bottcherCoord b y - y‖ := by
      calc ‖y‖ = ‖bottcherCoord b y - (bottcherCoord b y - y)‖ := by ring_nf
        _ ≤ ‖bottcherCoord b y‖ + ‖bottcherCoord b y - y‖ := norm_sub_le _ _
    linarith [htri, hsub, hdivle]
  -- Green comparison: 4·G_b(z) = G_b(y) = greenLimit(y) ≥ 4t
  have hGy : greenFunctionDyn b y = greenLimit b y := by
    rw [greenFunctionDyn, if_neg hynotK]
  have hGiter : greenFunctionDyn b ((quadratic b)^[2] z) = 2 ^ (2 : ℕ) * greenFunctionDyn b z :=
    greenFunctionDyn_iterate b z 2
  have hy_iter : (quadratic b)^[2] z = y := by
    rw [hy, Function.iterate_succ_apply', Function.iterate_one]
  rw [hy_iter, hGy] at hGiter
  have hexp_ge : Real.exp (4 * t) ≤ Real.exp (greenLimit b y) := by
    rw [← hphi]
    calc Real.exp (4 * t) ≤ (‖b‖ - 1) ^ (2 : ℕ) - ‖b‖ - 4 := by linarith [hband]
      _ ≤ ‖y‖ - 4 := by linarith [hyL]
      _ ≤ ‖bottcherCoord b y‖ := hlower
  have hglim : 4 * t ≤ greenLimit b y := Real.exp_le_exp.mp hexp_ge
  have hGz : 4 * t ≤ 4 * greenFunctionDyn b z := by
    rw [show (4 : ℝ) * greenFunctionDyn b z = 2 ^ (2 : ℕ) * greenFunctionDyn b z from by ring,
      ← hGiter]
    exact hglim
  linarith [hGz, hz]

/-- **Tower section images of large parameters live in `u₀`'s domain.**  A section on the band
`rlo < ‖w‖ < rhi` with `1 < rlo` and `rhi⁴ + 4 ≤ (‖b‖−1)² − ‖b‖` maps into `{|z| > 1}`. -/
theorem tower_section_image_exterior {b : ℂ} {rlo rhi : ℝ} (hb : 4 ≤ ‖b‖) (hrlo : 1 < rlo)
    (hband : rhi ^ (4 : ℕ) + 4 ≤ (‖b‖ - 1) ^ (2 : ℕ) - ‖b‖)
    (S : TowerSection b rlo rhi) {w : ℂ} (hw : w ∈ annulusSet rlo rhi) :
    1 < ‖S.T w‖ := by
  have hw1 : rlo < ‖w‖ := hw.1
  have hw2 : ‖w‖ < rhi := hw.2
  have hrhi1 : (1 : ℝ) < rhi := lt_trans hrlo (lt_trans hw1 hw2)
  have hlevel := S.level w hw
  refine green_sublevel_exterior hb (t := Real.log rhi) ?_ ?_
  · have hexp : Real.exp (4 * Real.log rhi) = rhi ^ (4 : ℕ) := by
      rw [show (4 : ℝ) * Real.log rhi = Real.log rhi + Real.log rhi
          + Real.log rhi + Real.log rhi from by ring]
      rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by linarith)]
      ring
    rw [hexp]
    exact hband
  · rw [hlevel]
    exact Real.log_lt_log (by linarith) hw2

/-- The section image is inside `Ext` — `u₀` is analytic on the whole section geometry. -/
theorem tower_section_image_subset_Ext {b : ℂ} {rlo rhi : ℝ} (hb : 4 ≤ ‖b‖) (hrlo : 1 < rlo)
    (hband : rhi ^ (4 : ℕ) + 4 ≤ (‖b‖ - 1) ^ (2 : ℕ) - ‖b‖) (S : TowerSection b rlo rhi) :
    S.T '' (annulusSet rlo rhi) ⊆ Ext := by
  rintro z ⟨w, hw, rfl⟩
  exact tower_section_image_exterior hb hrlo hband S hw

end U0SectionExterior
