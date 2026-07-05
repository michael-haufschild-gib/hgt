/-
The caustic shell toolkit (doc 87 App B, the dyadic averaging inputs).

The (L3) base case bounds the annulus measure `μ²(Ann)` (the RHS of
`three_phase_sublevel`) by slicing in the third phase: the η-section is a
radial band whose cosine-band center moves with `‖c + Ce^{iη}‖`.  The
dyadic assembly needs exactly the tools this module provides:

* `cos_band_measure_shift_gap'/_sqrt'/_linear'` — the three band laws for
  an ARBITRARY real phase shift (`cos(φ + ψ)` form), by mod-2π reduction:
  no more `[0, 2π)` bookkeeping at call sites.
* `radial_band_subset_cos_band` — the radial band is contained in the
  cosine band `[bandCenter − bandHalf, bandCenter + bandHalf]` at the
  explicit shift `arg(conj c · B)`: the reduction extracted once, reusable.
* `radial_band_measure_zero_of_high/_low` — outside the reachable annulus
  the radial band is EMPTY (band center beyond ±1 by more than the half
  width).
* `one_sub_bandCenter_sq` — the caustic factorization
  `1 − U₀² = ((ρ+‖B‖)² − x²)(x² − (ρ−‖B‖)²)/(4x²‖B‖²)`, `x = ‖c‖`:
  the tangency margin is a product of distances to the two caustic radii
  `x₊ = ρ+‖B‖`, `x₋ = |ρ−‖B‖|` — in the SQUARED variable, where the
  η-distribution of `x²` is an affine image of a cosine (next lemma).
* `norm_center_sq_cos` — `‖c + Ce^{iη}‖² = ‖c‖² + ‖C‖² +
  2‖c‖‖C‖·cos(η + arg(conj c · C))`: shells in `x²` ARE cosine bands.
* `one_sub_abs_ge` — `(1 − u²)/2 ≤ 1 − |u|`: converts the factorized
  margin into the `|bandCenter| + bandHalf ≤ 1 − m` hypothesis of the
  transversal law.
-/
import Mathlib
import GaloisForLFunctions.RHTower.RouteBThreePhase

namespace RHTower
namespace Sublevel

open MeasureTheory

/-- **The gap band law at an arbitrary real shift** (`cos(φ + ψ)` form),
by mod-2π reduction to `cos_band_measure_shifted_gap`. -/
theorem cos_band_measure_shift_gap' {u₁ u₂ ψ : ℝ} (h1 : -1 ≤ u₁)
    (h12 : u₁ ≤ u₂) (h2 : u₂ ≤ 1) :
    volume {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        Real.cos (φ + ψ) ∈ Set.Icc u₁ u₂}
      ≤ ENNReal.ofReal (4 * (Real.arccos u₁ - Real.arccos u₂)) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set t : ℝ := -ψ / (2 * Real.pi) with ht
  set ψ' : ℝ := 2 * Real.pi * Int.fract t with hψ'
  have h0 : 0 ≤ ψ' := mul_nonneg (by positivity) (Int.fract_nonneg t)
  have h2π : ψ' < 2 * Real.pi := by
    rw [hψ']
    nlinarith [Int.fract_lt_one t]
  have hcos : ∀ φ : ℝ, Real.cos (φ - ψ') = Real.cos (φ + ψ) := by
    intro φ
    have h2t : 2 * Real.pi * t = -ψ := by
      rw [ht]
      field_simp
    have heq : φ - ψ' = φ + ψ + (⌊t⌋ : ℤ) * (2 * Real.pi) := by
      rw [hψ', show Int.fract t = t - (⌊t⌋ : ℤ) from rfl]
      nlinarith [h2t]
    rw [heq, Real.cos_add_int_mul_two_pi]
  have hset : {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        Real.cos (φ + ψ) ∈ Set.Icc u₁ u₂}
      = {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
          Real.cos (φ - ψ') ∈ Set.Icc u₁ u₂} := by
    ext φ
    simp only [Set.mem_setOf_eq, hcos φ]
  rw [hset]
  exact cos_band_measure_shifted_gap h1 h12 h2 h0 h2π

/-- The √-law at an arbitrary real shift. -/
theorem cos_band_measure_shift_sqrt' {u₁ u₂ ψ : ℝ} (h1 : -1 ≤ u₁)
    (h12 : u₁ ≤ u₂) (h2 : u₂ ≤ 1) :
    volume {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        Real.cos (φ + ψ) ∈ Set.Icc u₁ u₂}
      ≤ ENNReal.ofReal (2 * Real.pi * Real.sqrt (2 * (u₂ - u₁))) := by
  refine le_trans (cos_band_measure_shift_gap' h1 h12 h2)
    (ENNReal.ofReal_le_ofReal ?_)
  have hgapL := arccos_gap_le h1 h12 h2
  linarith

/-- The transversal linear law at an arbitrary real shift. -/
theorem cos_band_measure_shift_linear' {u₁ u₂ ψ m : ℝ} (h1 : -1 ≤ u₁)
    (h12 : u₁ ≤ u₂) (h2 : u₂ ≤ 1) (hm : 0 < m)
    (hden : m ≤ Real.sqrt (1 - u₁ ^ 2) + Real.sqrt (1 - u₂ ^ 2)) :
    volume {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        Real.cos (φ + ψ) ∈ Set.Icc u₁ u₂}
      ≤ ENNReal.ofReal (4 * Real.pi * (u₂ - u₁) / m) := by
  refine le_trans (cos_band_measure_shift_gap' h1 h12 h2)
    (ENNReal.ofReal_le_ofReal ?_)
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

/-- **The radial band is a cosine band, extracted once.**  Every angle in
the radial band `|‖c + Be^{iφ}‖ − ρ| ≤ r` satisfies
`cos(φ + arg(conj c · B)) ∈ [bandCenter − bandHalf, bandCenter + bandHalf]`.
All three band laws apply downstream at the explicit shift. -/
theorem radial_band_subset_cos_band {B c : ℂ} {ρ r : ℝ} (hc : c ≠ 0)
    (hB : B ≠ 0) (hρ : 0 ≤ ρ) :
    {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        |‖c + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ρ| ≤ r}
      ⊆ {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
          Real.cos (φ + ((starRingEnd ℂ) c * B).arg)
            ∈ Set.Icc (bandCenter c B ρ - bandHalf c B ρ r)
                (bandCenter c B ρ + bandHalf c B ρ r)} := by
  set w : ℂ := (starRingEnd ℂ) c * B with hwdef
  have hw : w ≠ 0 := mul_ne_zero (star_ne_zero.mpr hc) hB
  have hnw : ‖w‖ = ‖c‖ * ‖B‖ := by
    rw [hwdef, norm_mul, RCLike.norm_conj]
  have hnw0 : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  rintro φ ⟨hφI, hband⟩
  refine ⟨hφI, ?_⟩
  set g : ℝ := ‖c + B * Complex.exp ((φ : ℂ) * Complex.I)‖ with hg
  have hg0 : 0 ≤ g := norm_nonneg _
  have hgρ : g ≤ ρ + r := by
    have := abs_le.mp hband
    linarith [this.2]
  have hsq2 : |g ^ 2 - ρ ^ 2| ≤ r * (2 * ρ + r) := by
    have hfac : g ^ 2 - ρ ^ 2 = (g - ρ) * (g + ρ) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ g + ρ)]
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
  have hclose : |Real.cos (φ + w.arg) - bandCenter c B ρ|
      ≤ bandHalf c B ρ r := by
    have hval : Real.cos (φ + w.arg) - bandCenter c B ρ
        = (g ^ 2 - ρ ^ 2) / (2 * ‖w‖) := by
      rw [bandCenter_def, ← hnw]
      field_simp
      linarith [hcosval]
    rw [hval, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * ‖w‖),
      bandHalf_def, ← hnw]
    gcongr
  have habs := abs_le.mp hclose
  exact ⟨by linarith [habs.1], by linarith [habs.2]⟩

/-- **Empty band, high side**: if the band center exceeds `1` by more than
the half width (the second arm cannot reach DOWN to radius ρ), the radial
band is null. -/
theorem radial_band_measure_zero_of_high {B c : ℂ} {ρ r : ℝ} (hc : c ≠ 0)
    (hB : B ≠ 0) (hρ : 0 ≤ ρ)
    (hhigh : 1 < bandCenter c B ρ - bandHalf c B ρ r) :
    volume {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        |‖c + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ρ| ≤ r} = 0 := by
  refine measure_mono_null (radial_band_subset_cos_band hc hB hρ) ?_
  have hempty : {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
      Real.cos (φ + ((starRingEnd ℂ) c * B).arg)
        ∈ Set.Icc (bandCenter c B ρ - bandHalf c B ρ r)
            (bandCenter c B ρ + bandHalf c B ρ r)} = ∅ := by
    ext φ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨_, h1, _⟩
    have := Real.cos_le_one (φ + ((starRingEnd ℂ) c * B).arg)
    linarith
  rw [hempty]
  exact measure_empty

/-- **Empty band, low side**: if the band center is below `−1` by more than
the half width (the second arm cannot come DOWN to radius ρ from above),
the radial band is null. -/
theorem radial_band_measure_zero_of_low {B c : ℂ} {ρ r : ℝ} (hc : c ≠ 0)
    (hB : B ≠ 0) (hρ : 0 ≤ ρ)
    (hlow : bandCenter c B ρ + bandHalf c B ρ r < -1) :
    volume {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        |‖c + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ρ| ≤ r} = 0 := by
  refine measure_mono_null (radial_band_subset_cos_band hc hB hρ) ?_
  have hempty : {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
      Real.cos (φ + ((starRingEnd ℂ) c * B).arg)
        ∈ Set.Icc (bandCenter c B ρ - bandHalf c B ρ r)
            (bandCenter c B ρ + bandHalf c B ρ r)} = ∅ := by
    ext φ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨_, _, h2⟩
    have := Real.neg_one_le_cos (φ + ((starRingEnd ℂ) c * B).arg)
    linarith
  rw [hempty]
  exact measure_empty

/-- **The caustic factorization.**  The tangency margin of the radial band
factors over the two caustic radii `x₊ = ρ + ‖B‖`, `x₋ = |ρ − ‖B‖|` in the
SQUARED center-modulus variable:
`1 − U₀² = ((ρ+‖B‖)² − ‖c‖²)·(‖c‖² − (ρ−‖B‖)²)/(4‖c‖²‖B‖²)`. -/
theorem one_sub_bandCenter_sq {c B : ℂ} (ρ : ℝ) (hc : c ≠ 0) (hB : B ≠ 0) :
    1 - bandCenter c B ρ ^ 2
      = ((ρ + ‖B‖) ^ 2 - ‖c‖ ^ 2) * (‖c‖ ^ 2 - (ρ - ‖B‖) ^ 2)
          / (4 * (‖c‖ ^ 2 * ‖B‖ ^ 2)) := by
  have hc0 : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
  have hB0 : (0 : ℝ) < ‖B‖ := norm_pos_iff.mpr hB
  rw [bandCenter_def]
  field_simp
  ring

/-- **Shells in the squared center modulus are cosine bands**:
`‖c + Ce^{iη}‖² = ‖c‖² + ‖C‖² + 2‖c‖‖C‖·cos(η + arg(conj c · C))`. -/
theorem norm_center_sq_cos (c C : ℂ) (η : ℝ) :
    ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2
      = ‖c‖ ^ 2 + ‖C‖ ^ 2
        + 2 * (‖c‖ * ‖C‖)
            * Real.cos (η + ((starRingEnd ℂ) c * C).arg) := by
  rw [norm_add_circle_sq c C η, re_w_exp, norm_mul, RCLike.norm_conj]
  ring

/-- Margin conversion: `(1 − u²)/2 ≤ 1 − |u|` for `|u| ≤ 1` — the
factorized caustic margin implies the `|bandCenter| + bandHalf ≤ 1 − m`
hypothesis of the transversal law. -/
theorem one_sub_abs_ge {u : ℝ} (hu : |u| ≤ 1) :
    (1 - u ^ 2) / 2 ≤ 1 - |u| := by
  have h2 : 1 - u ^ 2 = (1 - |u|) * (1 + |u|) := by
    rw [← sq_abs]
    ring
  rw [h2]
  nlinarith [abs_nonneg u]

end Sublevel
end RHTower
