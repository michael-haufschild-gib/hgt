/-
The (L3) base-case machinery: the transversal (linear) cosine-band law and
the three-phase Fubini reduction (doc 87 App B, rungs 3–4).

The caustic ladder's √-law (`cos_band_measure_shifted`,
`two_phase_sublevel_r32`) is unconditional but saturates at the caustic
(band endpoints at ±1).  Away from the caustic the band is LINEAR in its
width.  This module proves that rung and hands (L3)'s third-phase averaging
the two surfaces it consumes:

* `cos_band_measure_shifted_gap` — the covering step isolated: any shifted
  cosine band has measure ≤ `4·(arccos u₁ − arccos u₂)`; both the √-law and
  the linear law specialize this.
* `arccos_gap_mul` — the transversal arccos-gap inequality
  `(arccos u₁ − arccos u₂)·(√(1−u₁²) + √(1−u₂²)) ≤ π·(u₂ − u₁)`,
  by pure product-formula algebra (`sin_add_sin` + Jordan; no MVT).
* `cos_band_measure_shifted_linear` — the linear band law: measure ≤
  `4π(u₂−u₁)/m` at transversality margin `m ≤ √(1−u₁²) + √(1−u₂²)`.
* `radial_band_measure_transversal` — the radial caustic band away from
  tangency: measure ≤ `2π·r(2ρ+r)/(√m·‖c‖‖B‖)` — LINEAR in `r`.
* `two_phase_sublevel_r2` — the transversal two-phase r² law: the caustic
  ladder's third rung, fully formal.
* `three_phase_sublevel` — the three-phase Fubini reduction: the 3D
  sublevel measure ≤ `(2πr/‖A‖)` × (2D ANNULUS measure of the remaining
  two-phase field around radius `‖A‖`) — the exact object the third-phase
  caustic averaging integrates.
-/
import Mathlib
import GaloisForLFunctions.RHTower.RouteBSublevel
import GaloisForLFunctions.RHTower.RouteBSublevel

namespace RHTower
namespace Sublevel

open MeasureTheory

/-- **The transversal arccos-gap inequality** (multiplied, division-free
form): `(arccos u₁ − arccos u₂)·(√(1−u₁²) + √(1−u₂²)) ≤ π·(u₂ − u₁)`.
Pure product-formula algebra: `sin_add_sin` turns the sine sum into
`2·sin M·cos D`, `cos_sub_cos` turns the width into `2·sin M·sin D`, and
Jordan (`mul_le_sin`) dominates `2D·cos D` by `π·sin D`. -/
theorem arccos_gap_mul {u₁ u₂ : ℝ} (h1 : -1 ≤ u₁) (h12 : u₁ ≤ u₂)
    (h2 : u₂ ≤ 1) :
    (Real.arccos u₁ - Real.arccos u₂)
        * (Real.sqrt (1 - u₁ ^ 2) + Real.sqrt (1 - u₂ ^ 2))
      ≤ Real.pi * (u₂ - u₁) := by
  set α := Real.arccos u₂ with hαdef
  set β := Real.arccos u₁ with hβdef
  have hα0 : 0 ≤ α := Real.arccos_nonneg _
  have hβ0 : 0 ≤ β := Real.arccos_nonneg _
  have hαπ : α ≤ Real.pi := Real.arccos_le_pi _
  have hβπ : β ≤ Real.pi := Real.arccos_le_pi _
  have hαβ : α ≤ β := Real.arccos_le_arccos h12
  have hsinα : Real.sin α = Real.sqrt (1 - u₂ ^ 2) := Real.sin_arccos u₂
  have hsinβ : Real.sin β = Real.sqrt (1 - u₁ ^ 2) := Real.sin_arccos u₁
  have hcosα : Real.cos α = u₂ := Real.cos_arccos (by linarith) h2
  have hcosβ : Real.cos β = u₁ := Real.cos_arccos h1 (by linarith)
  have hsum : Real.sin β + Real.sin α
      = 2 * Real.sin ((β + α) / 2) * Real.cos ((β - α) / 2) :=
    Real.sin_add_sin β α
  have hdiff : u₂ - u₁ = 2 * Real.sin ((β + α) / 2) * Real.sin ((β - α) / 2) := by
    have h := Real.cos_sub_cos β α
    rw [hcosα, hcosβ] at h
    linear_combination -h
  set M := (β + α) / 2 with hM
  set D := (β - α) / 2 with hD
  have hM0 : 0 ≤ Real.sin M :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by rw [hM]; linarith)
      (by rw [hM]; linarith)
  have hD0 : 0 ≤ D := by rw [hD]; linarith
  have hDπ : D ≤ Real.pi / 2 := by rw [hD]; linarith
  have hcosD : Real.cos D ≤ 1 := Real.cos_le_one _
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hj : 2 / Real.pi * D ≤ Real.sin D := Real.mul_le_sin hD0 hDπ
  have key : 2 * D * Real.cos D ≤ Real.pi * Real.sin D := by
    have hstep1 : 2 * D * Real.cos D ≤ 2 * D := by nlinarith
    have hstep2 : 2 * D ≤ Real.pi * Real.sin D := by
      have hmul := mul_le_mul_of_nonneg_left hj (le_of_lt hπ)
      calc 2 * D = Real.pi * (2 / Real.pi * D) := by field_simp
        _ ≤ Real.pi * Real.sin D := hmul
    linarith
  have hβα : β - α = 2 * D := by rw [hD]; ring
  rw [← hsinβ, ← hsinα, hsum, hdiff, hβα]
  nlinarith [mul_le_mul_of_nonneg_left key
    (by linarith : (0 : ℝ) ≤ 2 * Real.sin M)]

/-- **The transversal (linear) shifted band law.**  At transversality margin
`m ≤ √(1−u₁²) + √(1−u₂²)` the shifted cosine band has measure at most
`4π(u₂ − u₁)/m` — linear in the band width: the caustic ladder's third
rung, replacing the unconditional √-law away from tangency. -/
theorem cos_band_measure_shifted_linear {u₁ u₂ ψ m : ℝ} (h1 : -1 ≤ u₁)
    (h12 : u₁ ≤ u₂) (h2 : u₂ ≤ 1) (hψ0 : 0 ≤ ψ) (hψ2 : ψ < 2 * Real.pi)
    (hm : 0 < m)
    (hden : m ≤ Real.sqrt (1 - u₁ ^ 2) + Real.sqrt (1 - u₂ ^ 2)) :
    volume {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        Real.cos (φ - ψ) ∈ Set.Icc u₁ u₂}
      ≤ ENNReal.ofReal (4 * Real.pi * (u₂ - u₁) / m) := by
  refine le_trans (cos_band_measure_shifted_gap h1 h12 h2 hψ0 hψ2) ?_
  apply ENNReal.ofReal_le_ofReal
  have hgap := arccos_gap_mul h1 h12 h2
  have hL0 : 0 ≤ Real.arccos u₁ - Real.arccos u₂ := by
    have := Real.arccos_le_arccos h12
    linarith
  rw [le_div_iff₀ hm]
  have hmono : (Real.arccos u₁ - Real.arccos u₂) * m
      ≤ (Real.arccos u₁ - Real.arccos u₂)
          * (Real.sqrt (1 - u₁ ^ 2) + Real.sqrt (1 - u₂ ^ 2)) :=
    mul_le_mul_of_nonneg_left hden hL0
  nlinarith [hgap, hmono]

/-- The cosine-band center of the radial condition
`|‖c + Be^{iφ}‖ − ρ| ≤ r` in the variable `cos(φ − ψ)`. -/
noncomputable def bandCenter (c B : ℂ) (ρ : ℝ) : ℝ :=
  (ρ ^ 2 - ‖c‖ ^ 2 - ‖B‖ ^ 2) / (2 * (‖c‖ * ‖B‖))

/-- The cosine-band half-width of the radial condition. -/
noncomputable def bandHalf (c B : ℂ) (ρ r : ℝ) : ℝ :=
  r * (2 * ρ + r) / (2 * (‖c‖ * ‖B‖))

theorem bandCenter_def (c B : ℂ) (ρ : ℝ) :
    bandCenter c B ρ = (ρ ^ 2 - ‖c‖ ^ 2 - ‖B‖ ^ 2) / (2 * (‖c‖ * ‖B‖)) := rfl

theorem bandHalf_def (c B : ℂ) (ρ r : ℝ) :
    bandHalf c B ρ r = r * (2 * ρ + r) / (2 * (‖c‖ * ‖B‖)) := rfl

/-- **The transversal radial band bound.**  When the cosine band
`[bandCenter − bandHalf, bandCenter + bandHalf]` stays `m` away from the
caustic endpoints `±1`, the radial band has measure at most
`2π·r(2ρ+r)/(√m·‖c‖‖B‖)` — LINEAR in `r`, versus the unconditional
`√r`-law of `radial_band_measure`. -/
theorem radial_band_measure_transversal {B c : ℂ} {ρ r m : ℝ} (hc : c ≠ 0)
    (hB : B ≠ 0) (hρ : 0 ≤ ρ) (hr : 0 ≤ r) (hm : 0 < m) (hm1 : m ≤ 1)
    (htrans : |bandCenter c B ρ| + bandHalf c B ρ r ≤ 1 - m) :
    volume {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        |‖c + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ρ| ≤ r}
      ≤ ENNReal.ofReal (2 * Real.pi * (r * (2 * ρ + r))
          / (Real.sqrt m * (‖c‖ * ‖B‖))) := by
  classical
  set w : ℂ := (starRingEnd ℂ) c * B with hwdef
  have hw : w ≠ 0 := mul_ne_zero (star_ne_zero.mpr hc) hB
  have hnw : ‖w‖ = ‖c‖ * ‖B‖ := by
    rw [hwdef, norm_mul, RCLike.norm_conj]
  have hnw0 : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  set U₀ : ℝ := (ρ ^ 2 - ‖c‖ ^ 2 - ‖B‖ ^ 2) / (2 * ‖w‖) with hU₀
  set H : ℝ := r * (2 * ρ + r) / (2 * ‖w‖) with hH
  have hU₀eq : U₀ = bandCenter c B ρ := by rw [hU₀, bandCenter_def, hnw]
  have hHeq : H = bandHalf c B ρ r := by rw [hH, bandHalf_def, hnw]
  have htrans' : |U₀| + H ≤ 1 - m := by rw [hU₀eq, hHeq]; exact htrans
  have hH0 : 0 ≤ H := by
    rw [hH]
    positivity
  set ψ₀ : ℝ := -w.arg with hψ₀
  set ψ : ℝ := if 0 ≤ ψ₀ then ψ₀ else ψ₀ + 2 * Real.pi with hψdef
  have harg := Complex.arg_mem_Ioc w
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hψ0 : 0 ≤ ψ := by
    rw [hψdef]
    split
    · assumption
    · rw [hψ₀]
      have := harg.2
      linarith
  have hψ2 : ψ < 2 * Real.pi := by
    rw [hψdef]
    split
    · rw [hψ₀]
      have := harg.1
      linarith
    · rename_i h0
      rw [hψ₀] at h0 ⊢
      linarith [harg.2, hπ]
  have hcosψ : ∀ φ : ℝ, Real.cos (φ - ψ) = Real.cos (φ + w.arg) := by
    intro φ
    rw [hψdef]
    split
    · rw [hψ₀, show φ - -w.arg = φ + w.arg by ring]
    · rw [hψ₀, show φ - (-w.arg + 2 * Real.pi)
          = φ + w.arg - 2 * Real.pi by ring, Real.cos_sub_two_pi]
  have hmem : ∀ φ : ℝ, φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) →
      |‖c + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ρ| ≤ r →
      Real.cos (φ - ψ) ∈ Set.Icc (U₀ - H) (U₀ + H) := by
    intro φ _ hband
    set g : ℝ := ‖c + B * Complex.exp ((φ : ℂ) * Complex.I)‖ with hg
    have hg0 : 0 ≤ g := norm_nonneg _
    have hgρ : g ≤ ρ + r := by
      have := abs_le.mp hband
      linarith [this.2]
    have hsq2 : |g ^ 2 - ρ ^ 2| ≤ r * (2 * ρ + r) := by
      have hfac : g ^ 2 - ρ ^ 2 = (g - ρ) * (g + ρ) := by ring
      rw [hfac, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ g + ρ)]
      have h1 : |g - ρ| ≤ r := hband
      nlinarith [abs_nonneg (g - ρ), h1]
    have hcosval : 2 * ‖w‖ * Real.cos (φ + w.arg)
        = g ^ 2 - ‖c‖ ^ 2 - ‖B‖ ^ 2 := by
      have hexp := norm_add_circle_sq c B φ
      have hre := re_w_exp w φ
      rw [hwdef] at hre
      rw [hre] at hexp
      rw [← hwdef] at hexp
      rw [hg]
      linarith [hexp]
    have hclose : |Real.cos (φ + w.arg) - U₀| ≤ H := by
      have hval : Real.cos (φ + w.arg) - U₀ = (g ^ 2 - ρ ^ 2) / (2 * ‖w‖) := by
        rw [hU₀]
        field_simp
        linarith [hcosval]
      rw [hval, abs_div, abs_of_pos (by linarith : (0:ℝ) < 2 * ‖w‖), hH]
      gcongr
    rw [hcosψ φ]
    have habs := abs_le.mp hclose
    exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
  have hu1 : (-1 : ℝ) ≤ U₀ - H := by
    have hna := neg_abs_le U₀
    linarith [hm.le]
  have hu2 : U₀ + H ≤ 1 := by
    have hla := le_abs_self U₀
    linarith [hm.le]
  have h12 : U₀ - H ≤ U₀ + H := by linarith
  have habs1 : |U₀ - H| ≤ 1 - m := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le U₀]
    · linarith [le_abs_self U₀, hH0]
  have habs2 : |U₀ + H| ≤ 1 - m := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le U₀, hH0]
    · linarith [le_abs_self U₀]
  have hs1 : Real.sqrt m ≤ Real.sqrt (1 - (U₀ - H) ^ 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith [mul_self_le_mul_self (abs_nonneg (U₀ - H)) habs1,
      sq_abs (U₀ - H), hm1]
  have hs2 : Real.sqrt m ≤ Real.sqrt (1 - (U₀ + H) ^ 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith [mul_self_le_mul_self (abs_nonneg (U₀ + H)) habs2,
      sq_abs (U₀ + H), hm1]
  have hsm : (0 : ℝ) < 2 * Real.sqrt m := by positivity
  have hden : 2 * Real.sqrt m
      ≤ Real.sqrt (1 - (U₀ - H) ^ 2) + Real.sqrt (1 - (U₀ + H) ^ 2) := by
    linarith
  have hcover : {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        |‖c + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ρ| ≤ r}
      ⊆ {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
          Real.cos (φ - ψ) ∈ Set.Icc (U₀ - H) (U₀ + H)} := by
    rintro φ ⟨hφI, hband⟩
    exact ⟨hφI, hmem φ hφI hband⟩
  calc volume {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        |‖c + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ρ| ≤ r}
      ≤ volume {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
          Real.cos (φ - ψ) ∈ Set.Icc (U₀ - H) (U₀ + H)} :=
        measure_mono hcover
    _ ≤ ENNReal.ofReal (4 * Real.pi * (U₀ + H - (U₀ - H))
          / (2 * Real.sqrt m)) :=
        cos_band_measure_shifted_linear hu1 h12 hu2 hψ0 hψ2 hsm hden
    _ = ENNReal.ofReal (2 * Real.pi * (r * (2 * ρ + r))
          / (Real.sqrt m * (‖c‖ * ‖B‖))) := by
        congr 1
        have hsm0 : Real.sqrt m ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hm)
        have hcb : (0 : ℝ) < ‖c‖ * ‖B‖ :=
          mul_pos (norm_pos_iff.mpr hc) (norm_pos_iff.mpr hB)
        rw [hH, hnw]
        field_simp
        ring

/-- **The transversal two-phase r² law** (the caustic ladder's third rung,
doc 87 App B).  Away from the caustic (`bandCenter ± bandHalf` at margin
`m` from `±1`), the two-phase sublevel measure is
≤ `(2πr/‖A‖)·(2π·r(2‖A‖+r)/(√m·‖c‖‖B‖))` — quadratic in `r`. -/
theorem two_phase_sublevel_r2 {A B c : ℂ} {r m : ℝ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hc : c ≠ 0) (hr : 0 ≤ r) (hm : 0 < m) (hm1 : m ≤ 1)
    (htrans : |bandCenter c B ‖A‖| + bandHalf c B ‖A‖ r ≤ 1 - m) :
    (volume.prod volume)
      ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) ∩
        {p : ℝ × ℝ | ‖c + B * Complex.exp ((p.1 : ℂ) * Complex.I)
            + A * Complex.exp ((p.2 : ℂ) * Complex.I)‖ ≤ r})
      ≤ ENNReal.ofReal (2 * (Real.pi * r / ‖A‖))
        * ENNReal.ofReal (2 * Real.pi * (r * (2 * ‖A‖ + r))
            / (Real.sqrt m * (‖c‖ * ‖B‖))) :=
  le_trans (two_phase_sublevel hA hr) (by
    gcongr
    exact radial_band_measure_transversal hc hB (norm_nonneg A) hr hm hm1
      htrans)

/-- **The three-phase Fubini reduction (the (L3) base-case surface).**  The
3D sublevel measure of a three-phase circle sum is at most the per-phase
arc bound `2πr/‖A‖` times the 2D ANNULUS measure of the remaining two-phase
field around radius `‖A‖`.  The annulus measure is exactly the object the
third-phase caustic averaging integrates: slicing IT in the third phase
gives the moving radial band whose transversal bulk obeys the linear law
above and whose caustic core obeys the unconditional √-law. -/
theorem three_phase_sublevel {A B C c : ℂ} {r : ℝ} (hA : A ≠ 0) (hr : 0 ≤ r) :
    (volume.prod (volume.prod volume))
      ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
          (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))) ∩
        {q : ℝ × ℝ × ℝ | ‖c + C * Complex.exp ((q.1 : ℂ) * Complex.I)
            + B * Complex.exp ((q.2.1 : ℂ) * Complex.I)
            + A * Complex.exp ((q.2.2 : ℂ) * Complex.I)‖ ≤ r})
      ≤ ENNReal.ofReal (2 * (Real.pi * r / ‖A‖))
        * (volume.prod volume)
            ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) ∩
              {p : ℝ × ℝ | |‖c + C * Complex.exp ((p.1 : ℂ) * Complex.I)
                  + B * Complex.exp ((p.2 : ℂ) * Complex.I)‖ - ‖A‖| ≤ r}) := by
  classical
  set S : Set (ℝ × ℝ × ℝ) :=
    (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
        (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))) ∩
      {q : ℝ × ℝ × ℝ | ‖c + C * Complex.exp ((q.1 : ℂ) * Complex.I)
          + B * Complex.exp ((q.2.1 : ℂ) * Complex.I)
          + A * Complex.exp ((q.2.2 : ℂ) * Complex.I)‖ ≤ r} with hS
  set Ann : Set (ℝ × ℝ) :=
    (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) ∩
      {p : ℝ × ℝ | |‖c + C * Complex.exp ((p.1 : ℂ) * Complex.I)
          + B * Complex.exp ((p.2 : ℂ) * Complex.I)‖ - ‖A‖| ≤ r} with hAnn
  have hcont3 : Continuous fun q : ℝ × ℝ × ℝ =>
      ‖c + C * Complex.exp ((q.1 : ℂ) * Complex.I)
        + B * Complex.exp ((q.2.1 : ℂ) * Complex.I)
        + A * Complex.exp ((q.2.2 : ℂ) * Complex.I)‖ := by
    refine Continuous.norm ?_
    refine Continuous.add (Continuous.add (Continuous.add continuous_const ?_)
      ?_) ?_
    · exact continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const))
    · exact continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp
          (continuous_fst.comp continuous_snd)).mul continuous_const))
    · exact continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp
          (continuous_snd.comp continuous_snd)).mul continuous_const))
  have hcontA : Continuous fun p : ℝ × ℝ =>
      |‖c + C * Complex.exp ((p.1 : ℂ) * Complex.I)
        + B * Complex.exp ((p.2 : ℂ) * Complex.I)‖ - ‖A‖| := by
    apply Continuous.abs
    apply Continuous.sub _ continuous_const
    apply Continuous.norm
    refine Continuous.add (Continuous.add continuous_const ?_) ?_
    · exact continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const))
    · exact continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hSm : MeasurableSet S := by
    apply IsClosed.measurableSet
    rw [hS]
    exact (isClosed_Icc.prod (isClosed_Icc.prod isClosed_Icc)).inter
      (isClosed_le hcont3 continuous_const)
  have hAnnm : MeasurableSet Ann := by
    apply IsClosed.measurableSet
    rw [hAnn]
    exact (isClosed_Icc.prod isClosed_Icc).inter
      (isClosed_le hcontA continuous_const)
  have hint : ∫⁻ η in Set.Icc (0 : ℝ) (2 * Real.pi),
      volume {φ : ℝ | φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧
        |‖c + C * Complex.exp ((η : ℂ) * Complex.I)
          + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ‖A‖| ≤ r}
      = (volume.prod volume) Ann := by
    rw [Measure.prod_apply hAnnm, ← lintegral_indicator measurableSet_Icc]
    congr 1
    funext η
    by_cases hη : η ∈ Set.Icc (0 : ℝ) (2 * Real.pi)
    · rw [Set.indicator_of_mem hη]
      congr 1
      ext φ
      constructor
      · rintro ⟨hφI, hband⟩
        exact ⟨⟨hη, hφI⟩, hband⟩
      · rintro ⟨⟨_, hφI⟩, hband⟩
        exact ⟨hφI, hband⟩
    · rw [Set.indicator_of_notMem hη]
      have hempty : Prod.mk η ⁻¹' Ann = ∅ := by
        ext φ
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨hη', _⟩, _⟩
        exact hη hη'
      rw [hempty, measure_empty]
  rw [Measure.prod_apply hSm]
  have hsec : ∀ η : ℝ, (volume.prod volume) (Prod.mk η ⁻¹' S)
      ≤ (Set.Icc (0 : ℝ) (2 * Real.pi)).indicator
          (fun η => ENNReal.ofReal (2 * (Real.pi * r / ‖A‖))
            * volume {φ : ℝ | φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧
                |‖c + C * Complex.exp ((η : ℂ) * Complex.I)
                  + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ‖A‖| ≤ r}) η := by
    intro η
    by_cases hη : η ∈ Set.Icc (0 : ℝ) (2 * Real.pi)
    · rw [Set.indicator_of_mem hη]
      have hpre : Prod.mk η ⁻¹' S
          = (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) ∩
              {p : ℝ × ℝ | ‖c + C * Complex.exp ((η : ℂ) * Complex.I)
                  + B * Complex.exp ((p.1 : ℂ) * Complex.I)
                  + A * Complex.exp ((p.2 : ℂ) * Complex.I)‖ ≤ r} := by
        rw [hS]
        ext p
        constructor
        · rintro ⟨⟨_, hp⟩, hnorm⟩
          exact ⟨hp, hnorm⟩
        · rintro ⟨hp, hnorm⟩
          exact ⟨⟨hη, hp⟩, hnorm⟩
      rw [hpre]
      exact two_phase_sublevel hA hr
    · rw [Set.indicator_of_notMem hη]
      have hempty : Prod.mk η ⁻¹' S = ∅ := by
        rw [hS]
        ext p
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨hη', _⟩, _⟩
        exact hη hη'
      rw [hempty, measure_empty]
  calc ∫⁻ η, (volume.prod volume) (Prod.mk η ⁻¹' S)
      ≤ ∫⁻ η, (Set.Icc (0 : ℝ) (2 * Real.pi)).indicator
          (fun η => ENNReal.ofReal (2 * (Real.pi * r / ‖A‖))
            * volume {φ : ℝ | φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧
                |‖c + C * Complex.exp ((η : ℂ) * Complex.I)
                  + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ‖A‖| ≤ r}) η :=
        lintegral_mono hsec
    _ = ∫⁻ η in Set.Icc (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal (2 * (Real.pi * r / ‖A‖))
            * volume {φ : ℝ | φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧
                |‖c + C * Complex.exp ((η : ℂ) * Complex.I)
                  + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ‖A‖| ≤ r} :=
        lintegral_indicator measurableSet_Icc _
    _ = ENNReal.ofReal (2 * (Real.pi * r / ‖A‖))
          * ∫⁻ η in Set.Icc (0 : ℝ) (2 * Real.pi),
              volume {φ : ℝ | φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧
                |‖c + C * Complex.exp ((η : ℂ) * Complex.I)
                  + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ‖A‖| ≤ r} :=
        MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (2 * (Real.pi * r / ‖A‖))
          * (volume.prod volume) Ann := by rw [hint]

end Sublevel
end RHTower
