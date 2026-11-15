import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.EveryRulerCarriesTheSeedAndEveryLever
import GaloisForLFunctions.BlackHoleRingdown.TheEternalAdSPrimeMarkedDictionary

/-!
# Expanding forcing laws, rulers, and the Riemann hypothesis

This module answers the positive structural half of the zero-forcing question: if an arithmetic or
analytic mechanism forces from any off-line zero `ρ` in a real-part band a zero farther from the
critical line (or into the right-half-plane Dirichlet `L`-family right of `7/8`), what follows
unconditionally?

1. **Band levers (`bandLever`, `closedRightBandLever`)**:
   - `bandLever b₁ b₂ x = if x < b₂ then min x b₁ else x` is monotone for `b₁ ≤ b₂` with gap
     `excluded (bandLever b₁ b₂) = (b₁, b₂)`.
   - `closedRightBandLever b₁ b₂ x = if x ≤ b₂ then min x b₁ else x` is monotone for `b₁ ≤ b₂` with
     gap `excluded (closedRightBandLever b₁ b₂) = (b₁, b₂]` and `closedRightBandLever b₁ b₂ b₂ = b₁`.

2. **Band-expanding zero forcing (`zetaZeroAbscissa_notMem_Ioo_of_band_forcing`,
   `zetaZeroAbscissa_notMem_Ioc_of_band_forcing`)**:
   Combining the supremum characterization of `zetaZeroAbscissa` with the unconditional `7/8`
   zero-free half-plane for all Dirichlet `L`-functions (`dirichlet_nonzero`), any continuous
   expanding map `g(x) > x` on `(b₁, b₂)` (resp. `(b₁, b₂]`) whose zero-forcing rule produces
   either a `ζ`-zero of real part `≥ g(Re ρ)` or a Dirichlet `L`-zero on `Re w > 7/8` (away from
   `χ = 1, w = 1`) unconditionally excludes `zetaZeroAbscissa` from `(b₁, b₂)` (resp. `(b₁, b₂]`)
   and certifies `bandLever b₁ b₂` (resp. `closedRightBandLever b₁ b₂`) as a lever for
   `zetaZeroAbscissa`.

3. **Simultaneous ruler jump and eternal-AdS Wightman strip jump
   (`band_forcing_width_ruler_jump`, `band_forcing_modularWightmanRL_strip_jump`,
   `unconditional_modularWightmanRL_strip_of_seven_eighths_band_forcing`)**:
   An `(b₁, b₂]` expanding forcing law jumps every reading of every `zetaZeroWidth` ruler from
   `b₂ - 1/2` down to `b₁ - 1/2`, jumps strip analyticity of the eternal-AdS two-boundary Wightman
   correlator `modularWightmanRL` from `0 < |Im ω| < (1 - b₂)/2` to `0 < |Im ω| < (1 - b₁)/2`, and
   at `b₂ = 7/8` widens the unconditional `1/16` Wightman strip to `(1 - b₁)/2` with no extra
   assumption.

4. **Global consequences (`riemannHypothesis_of_depth_expanding_forcing`,
   `riemannHypothesis_of_covering_levers`, `wall_eq_half_of_covering_monotone_levers`)**:
   Because `1/2 ≤ zetaZeroAbscissa ≤ 7/8` holds unconditionally, any continuous expanding forcing
   law on `(1/2, 7/8]` — or any family of levers whose excluded sets cover `(1/2, 7/8]` — collapses
   `wall = 1/2`, `zetaZeroAbscissa = 1/2`, `zetaZeroWidth = 0`, and proves `RiemannHypothesis`.
-/

noncomputable section
set_option autoImplicit false

open Complex Set Filter Topology
open GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

namespace GaloisForLFunctions.ZeroForcingCalculus

/-! ## 1. Open and right-closed band levers -/

/-- Monotone step map with excluded gap `(b₁, b₂)`: values `< b₂` clamp down to `min x b₁`. -/
def bandLever (b₁ b₂ x : ℝ) : ℝ :=
  if x < b₂ then min x b₁ else x

/-- Monotone step map with excluded gap `(b₁, b₂]`: values `≤ b₂` clamp down to `min x b₁`, sending
`b₂` directly to `b₁` when `b₁ ≤ b₂`. -/
def closedRightBandLever (b₁ b₂ x : ℝ) : ℝ :=
  if x ≤ b₂ then min x b₁ else x

theorem monotone_bandLever {b₁ b₂ : ℝ} (hb : b₁ ≤ b₂) : Monotone (bandLever b₁ b₂) := by
  intro x y hxy
  unfold bandLever
  by_cases hy : y < b₂
  · rw [if_pos (lt_of_le_of_lt hxy hy), if_pos hy]
    exact min_le_min_right b₁ hxy
  · rw [if_neg hy]
    by_cases hx : x < b₂
    · rw [if_pos hx]
      exact (min_le_right x b₁).trans (hb.trans (not_lt.mp hy))
    · rw [if_neg hx]
      exact hxy

theorem monotone_closedRightBandLever {b₁ b₂ : ℝ} (hb : b₁ ≤ b₂) :
    Monotone (closedRightBandLever b₁ b₂) := by
  intro x y hxy
  unfold closedRightBandLever
  by_cases hy : y ≤ b₂
  · rw [if_pos (hxy.trans hy), if_pos hy]
    exact min_le_min_right b₁ hxy
  · rw [if_neg hy]
    by_cases hx : x ≤ b₂
    · rw [if_pos hx]
      exact (min_le_right x b₁).trans (hb.trans (le_of_lt (not_le.mp hy)))
    · rw [if_neg hx]
      exact hxy

theorem excluded_bandLever_eq_Ioo (b₁ b₂ : ℝ) :
    excluded (bandLever b₁ b₂) = Set.Ioo b₁ b₂ := by
  ext x
  simp only [excluded, bandLever, Set.mem_setOf_eq, Set.mem_Ioo]
  by_cases hx2 : x < b₂
  · rw [if_pos hx2]
    rcases le_or_gt x b₁ with hx1 | hx1
    · rw [min_eq_left hx1]
      exact ⟨fun h => absurd h (lt_irrefl x), fun h => absurd h.1 (not_lt.mpr hx1)⟩
    · rw [min_eq_right hx1.le]
      exact ⟨fun _ => ⟨hx1, hx2⟩, fun h => h.1⟩
  · rw [if_neg hx2]
    exact ⟨fun h => absurd h (lt_irrefl x), fun h => absurd h.2 hx2⟩

theorem excluded_closedRightBandLever_eq_Ioc (b₁ b₂ : ℝ) :
    excluded (closedRightBandLever b₁ b₂) = Set.Ioc b₁ b₂ := by
  ext x
  simp only [excluded, closedRightBandLever, Set.mem_setOf_eq, Set.mem_Ioc]
  by_cases hx2 : x ≤ b₂
  · rw [if_pos hx2]
    rcases le_or_gt x b₁ with hx1 | hx1
    · rw [min_eq_left hx1]
      exact ⟨fun h => absurd h (lt_irrefl x), fun h => absurd h.1 (not_lt.mpr hx1)⟩
    · rw [min_eq_right hx1.le]
      exact ⟨fun _ => ⟨hx1, hx2⟩, fun h => h.1⟩
  · rw [if_neg hx2]
    exact ⟨fun h => absurd h (lt_irrefl x), fun h => absurd h.2 hx2⟩

theorem isLever_bandLever_iff {θ b₁ b₂ : ℝ} (hb : b₁ ≤ b₂) :
    IsLever θ (bandLever b₁ b₂) ↔ θ ∉ Set.Ioo b₁ b₂ := by
  rw [isLever_iff_notMem_excluded (monotone_bandLever hb), excluded_bandLever_eq_Ioo]

theorem isLever_closedRightBandLever_iff {θ b₁ b₂ : ℝ} (hb : b₁ ≤ b₂) :
    IsLever θ (closedRightBandLever b₁ b₂) ↔ θ ∉ Set.Ioc b₁ b₂ := by
  rw [isLever_iff_notMem_excluded (monotone_closedRightBandLever hb),
    excluded_closedRightBandLever_eq_Ioc]

theorem closedRightBandLever_apply_right {b₁ b₂ : ℝ} (hb : b₁ ≤ b₂) :
    closedRightBandLever b₁ b₂ b₂ = b₁ := by
  rw [closedRightBandLever, if_pos le_rfl, min_eq_right hb]

/-! ## 2. Unconditional emptiness of right-of-`7/8` Dirichlet `L`-zeros -/

/-- Witness predicate for a zero of any Dirichlet `L`-function on `Re w > 7/8` away from the
principal pole `(χ = 1, w = 1)`. -/
def ExistsDirichletZeroRightOfSevenEighths : Prop :=
  ∃ (q : ℕ) (hq : q ≠ 0) (χ : DirichletCharacter ℂ q) (w : ℂ),
    ¬(χ = 1 ∧ w = 1) ∧ (7 / 8 : ℝ) < w.re ∧
      (letI : NeZero q := ⟨hq⟩; DirichletCharacter.LFunction χ w = 0)

/-- Unconditionally, no Dirichlet `L`-function has a zero on `Re w > 7/8` away from `(χ = 1, w = 1)`. -/
theorem not_existsDirichletZeroRightOfSevenEighths :
    ¬ ExistsDirichletZeroRightOfSevenEighths := by
  rintro ⟨q, hq, χ, w, hexc, hw78, hw0⟩
  exact MetaplecticMobiusDescent.CubicEisenstein.ProbeFinalAssemblyUnconditional.dirichlet_nonzero
    q hq χ w hw78 hexc hw0

/-! ## 3. Band-expanding zero forcing excludes abscissa bands and yields levers -/

/-- **Open-band zero-forcing theorem.** Let `1/2 ≤ b₁ < b₂` and let `g : ℝ → ℝ` be continuous on
`(b₁, b₂)` with `x < g x` for all `x ∈ (b₁, b₂)`. If every zero `ρ` of `ζ` with `Re ρ ∈ (b₁, b₂)`
forces either a `ζ`-zero of real part `≥ g(Re ρ)` or a Dirichlet `L`-zero on `Re w > 7/8` away from
`(χ = 1, w = 1)`, then `zetaZeroAbscissa ∉ (b₁, b₂)` and `bandLever b₁ b₂` is a lever for
`zetaZeroAbscissa`. -/
theorem zetaZeroAbscissa_notMem_Ioo_of_band_forcing {b₁ b₂ : ℝ} (hb₁ : (1 / 2 : ℝ) ≤ b₁)
    (hb₁₂ : b₁ < b₂) {g : ℝ → ℝ} (hg_cont : ContinuousOn g (Set.Ioo b₁ b₂))
    (hg_gt : ∀ x ∈ Set.Ioo b₁ b₂, x < g x)
    (hforce : ∀ ρ : ℂ, 0 < ρ.re → riemannZeta ρ = 0 → ρ.re ∈ Set.Ioo b₁ b₂ →
      (∃ w : ℂ, riemannZeta w = 0 ∧ g ρ.re ≤ w.re) ∨ ExistsDirichletZeroRightOfSevenEighths) :
    RHTower.zetaZeroAbscissa ∉ Set.Ioo b₁ b₂ ∧
      IsLever RHTower.zetaZeroAbscissa (bandLever b₁ b₂) := by
  have hnotMem : RHTower.zetaZeroAbscissa ∉ Set.Ioo b₁ b₂ := by
    intro hΘ
    set Θ : ℝ := RHTower.zetaZeroAbscissa
    have hgtΘ : Θ < g Θ := hg_gt Θ hΘ
    have hε : 0 < (g Θ - Θ) / 2 := by linarith
    obtain ⟨δ, hδ_pos, hδ⟩ :=
      Metric.continuousWithinAt_iff.mp (hg_cont Θ hΘ) ((g Θ - Θ) / 2) hε
    set β : ℝ := max b₁ (Θ - δ / 2)
    have hβ_lt : β < Θ := max_lt hΘ.1 (by linarith)
    have hσ : 0 ≤ β - 1 / 2 := by
      have : b₁ ≤ β := le_max_left _ _
      linarith
    have hnot_all : ¬ ∀ ρ ∈ Zeta23.zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + (β - 1 / 2) := by
      intro hall
      have hle := (SquareRootThreshold.zetaZeroAbscissa_le_iff_zetaZeroConfig_re_le hσ).mpr hall
      linarith
    push Not at hnot_all
    obtain ⟨ρ, hρ_mem, hρ_gt⟩ := hnot_all
    obtain ⟨hζ, h0, _⟩ := (show Zeta23.IsNontrivialZero ρ from hρ_mem)
    have hρ_le : ρ.re ≤ Θ := RHTower.re_le_zetaZeroAbscissa hζ
    have hρ_b₁ : b₁ < ρ.re := lt_of_le_of_lt (le_max_left _ _) (by linarith)
    have hρ_Ioo : ρ.re ∈ Set.Ioo b₁ b₂ := ⟨hρ_b₁, lt_of_le_of_lt hρ_le hΘ.2⟩
    have hρ_dist : dist ρ.re Θ < δ := by
      rw [Real.dist_eq, abs_lt]
      have hlo : Θ - δ / 2 < ρ.re := lt_of_le_of_lt (le_max_right _ _) (by linarith)
      exact ⟨by linarith, by linarith⟩
    have hg_dist : |g ρ.re - g Θ| < (g Θ - Θ) / 2 := by
      simpa [Real.dist_eq] using hδ hρ_Ioo hρ_dist
    have hg_above : Θ < g ρ.re := by linarith [(abs_lt.mp hg_dist).1]
    rcases hforce ρ h0 hζ hρ_Ioo with ⟨w, hwζ, hgw⟩ | hdir
    · have hw_le : w.re ≤ Θ := RHTower.re_le_zetaZeroAbscissa hwζ
      linarith
    · exact not_existsDirichletZeroRightOfSevenEighths hdir
  exact ⟨hnotMem, (isLever_bandLever_iff hb₁₂.le).mpr hnotMem⟩

/-- **Right-closed band zero-forcing theorem.** Let `1/2 ≤ b₁ < b₂` and let `g : ℝ → ℝ` be
continuous on `(b₁, b₂]` with `x < g x` for all `x ∈ (b₁, b₂]`. Under the same forcing disjunction
on `(b₁, b₂]`, `zetaZeroAbscissa ∉ (b₁, b₂]` and `closedRightBandLever b₁ b₂` is a lever for
`zetaZeroAbscissa` (so `zetaZeroAbscissa ≤ b₂ → zetaZeroAbscissa ≤ b₁`). -/
theorem zetaZeroAbscissa_notMem_Ioc_of_band_forcing {b₁ b₂ : ℝ} (hb₁ : (1 / 2 : ℝ) ≤ b₁)
    (hb₁₂ : b₁ < b₂) {g : ℝ → ℝ} (hg_cont : ContinuousOn g (Set.Ioc b₁ b₂))
    (hg_gt : ∀ x ∈ Set.Ioc b₁ b₂, x < g x)
    (hforce : ∀ ρ : ℂ, 0 < ρ.re → riemannZeta ρ = 0 → ρ.re ∈ Set.Ioc b₁ b₂ →
      (∃ w : ℂ, riemannZeta w = 0 ∧ g ρ.re ≤ w.re) ∨ ExistsDirichletZeroRightOfSevenEighths) :
    RHTower.zetaZeroAbscissa ∉ Set.Ioc b₁ b₂ ∧
      IsLever RHTower.zetaZeroAbscissa (closedRightBandLever b₁ b₂) := by
  have hnotMem : RHTower.zetaZeroAbscissa ∉ Set.Ioc b₁ b₂ := by
    intro hΘ
    set Θ : ℝ := RHTower.zetaZeroAbscissa
    have hgtΘ : Θ < g Θ := hg_gt Θ hΘ
    have hε : 0 < (g Θ - Θ) / 2 := by linarith
    obtain ⟨δ, hδ_pos, hδ⟩ :=
      Metric.continuousWithinAt_iff.mp (hg_cont Θ hΘ) ((g Θ - Θ) / 2) hε
    set β : ℝ := max b₁ (Θ - δ / 2)
    have hβ_lt : β < Θ := max_lt hΘ.1 (by linarith)
    have hσ : 0 ≤ β - 1 / 2 := by
      have : b₁ ≤ β := le_max_left _ _
      linarith
    have hnot_all : ¬ ∀ ρ ∈ Zeta23.zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + (β - 1 / 2) := by
      intro hall
      have hle := (SquareRootThreshold.zetaZeroAbscissa_le_iff_zetaZeroConfig_re_le hσ).mpr hall
      linarith
    push Not at hnot_all
    obtain ⟨ρ, hρ_mem, hρ_gt⟩ := hnot_all
    obtain ⟨hζ, h0, _⟩ := (show Zeta23.IsNontrivialZero ρ from hρ_mem)
    have hρ_le : ρ.re ≤ Θ := RHTower.re_le_zetaZeroAbscissa hζ
    have hρ_b₁ : b₁ < ρ.re := lt_of_le_of_lt (le_max_left _ _) (by linarith)
    have hρ_Ioc : ρ.re ∈ Set.Ioc b₁ b₂ := ⟨hρ_b₁, hρ_le.trans hΘ.2⟩
    have hρ_dist : dist ρ.re Θ < δ := by
      rw [Real.dist_eq, abs_lt]
      have hlo : Θ - δ / 2 < ρ.re := lt_of_le_of_lt (le_max_right _ _) (by linarith)
      exact ⟨by linarith, by linarith⟩
    have hg_dist : |g ρ.re - g Θ| < (g Θ - Θ) / 2 := by
      simpa [Real.dist_eq] using hδ hρ_Ioc hρ_dist
    have hg_above : Θ < g ρ.re := by linarith [(abs_lt.mp hg_dist).1]
    rcases hforce ρ h0 hζ hρ_Ioc with ⟨w, hwζ, hgw⟩ | hdir
    · have hw_le : w.re ≤ Θ := RHTower.re_le_zetaZeroAbscissa hwζ
      linarith
    · exact not_existsDirichletZeroRightOfSevenEighths hdir
  exact ⟨hnotMem, (isLever_closedRightBandLever_iff hb₁₂.le).mpr hnotMem⟩

/-! ## 4. Simultaneous transport across all `zetaZeroWidth` rulers and eternal-AdS strip jump -/

/-- **Simultaneous jump across every `zetaZeroWidth` ruler.** Under an `(b₁, b₂]` expanding forcing
law (`1/2 ≤ b₁ < b₂`), `closedRightBandLever (b₁ - 1/2) (b₂ - 1/2)` is a lever for `zetaZeroWidth`,
and for **every** ruler `IsRuler zetaZeroWidth D P` containing `b₁ - 1/2` and `b₂ - 1/2` (including
`isRuler_moebiusPoly_pointwise`, `isRuler_unit_window`, `isRuler_moebiusPoly_zero_free`,
`isRuler_signal`, `isRuler_twoEndOdd`, and `isRuler_squarefreePowerQuotient`), the reading
`P (b₂ - 1/2)` jumps unconditionally to `P (b₁ - 1/2)`. -/
theorem band_forcing_width_ruler_jump {b₁ b₂ : ℝ} (hb₁ : (1 / 2 : ℝ) ≤ b₁) (hb₁₂ : b₁ < b₂)
    {g : ℝ → ℝ} (hg_cont : ContinuousOn g (Set.Ioc b₁ b₂))
    (hg_gt : ∀ x ∈ Set.Ioc b₁ b₂, x < g x)
    (hforce : ∀ ρ : ℂ, 0 < ρ.re → riemannZeta ρ = 0 → ρ.re ∈ Set.Ioc b₁ b₂ →
      (∃ w : ℂ, riemannZeta w = 0 ∧ g ρ.re ≤ w.re) ∨ ExistsDirichletZeroRightOfSevenEighths) :
    SquareRootThreshold.zetaZeroWidth ∉ Set.Ioc (b₁ - 1 / 2) (b₂ - 1 / 2) ∧
      IsLever SquareRootThreshold.zetaZeroWidth
        (closedRightBandLever (b₁ - 1 / 2) (b₂ - 1 / 2)) ∧
      ∀ (D : Set ℝ) (P : ℝ → Prop),
        IsRuler SquareRootThreshold.zetaZeroWidth D P →
          b₁ - 1 / 2 ∈ D → b₂ - 1 / 2 ∈ D → P (b₂ - 1 / 2) → P (b₁ - 1 / 2) := by
  have hΘ := (zetaZeroAbscissa_notMem_Ioc_of_band_forcing hb₁ hb₁₂ hg_cont hg_gt hforce).1
  have hw_notMem : SquareRootThreshold.zetaZeroWidth ∉ Set.Ioc (b₁ - 1 / 2) (b₂ - 1 / 2) := by
    rw [SquareRootThreshold.zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
    intro hw
    exact hΘ ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hw_lever : IsLever SquareRootThreshold.zetaZeroWidth
      (closedRightBandLever (b₁ - 1 / 2) (b₂ - 1 / 2)) :=
    (isLever_closedRightBandLever_iff (by linarith : b₁ - 1 / 2 ≤ b₂ - 1 / 2)).mpr hw_notMem
  refine ⟨hw_notMem, hw_lever, fun D P hR hb₁D hb₂D hP₂ => ?_⟩
  have heval := closedRightBandLever_apply_right (by linarith : b₁ - 1 / 2 ≤ b₂ - 1 / 2)
  have hread := hw_lever.reading hR hb₂D (heval.symm ▸ hb₁D) hP₂
  rwa [heval] at hread

/-- **Eternal-AdS two-boundary Wightman strip jump.** For `1/2 ≤ b₁ < b₂ < 1`, an `(b₁, b₂]`
expanding zero-forcing law widens strip analyticity of `BlackHoleRingdown.modularWightmanRL` from
`0 < |Im ω| < (1 - b₂)/2` directly to `0 < |Im ω| < (1 - b₁)/2`. -/
theorem band_forcing_modularWightmanRL_strip_jump {b₁ b₂ : ℝ} (hb₁ : (1 / 2 : ℝ) ≤ b₁)
    (hb₁₂ : b₁ < b₂) (hb₂ : b₂ < 1) {g : ℝ → ℝ} (hg_cont : ContinuousOn g (Set.Ioc b₁ b₂))
    (hg_gt : ∀ x ∈ Set.Ioc b₁ b₂, x < g x)
    (hforce : ∀ ρ : ℂ, 0 < ρ.re → riemannZeta ρ = 0 → ρ.re ∈ Set.Ioc b₁ b₂ →
      (∃ w : ℂ, riemannZeta w = 0 ∧ g ρ.re ≤ w.re) ∨ ExistsDirichletZeroRightOfSevenEighths)
    (han : AnalyticOnNhd ℂ BlackHoleRingdown.modularWightmanRL
      {ω : ℂ | 0 < |ω.im| ∧ |ω.im| < (1 - b₂) / 2}) :
    AnalyticOnNhd ℂ BlackHoleRingdown.modularWightmanRL
      {ω : ℂ | 0 < |ω.im| ∧ |ω.im| < (1 - b₁) / 2} := by
  have hlev := (zetaZeroAbscissa_notMem_Ioc_of_band_forcing hb₁ hb₁₂ hg_cont hg_gt hforce).2
  have hz₂ := (BlackHoleRingdown.modularWightmanRL_analyticOnNhd_strip_iff
    (by linarith : 0 < (1 - b₂) / 2) (by linarith : (1 - b₂) / 2 ≤ 1 / 4)).mp han
  have hΘ_b₂ : RHTower.zetaZeroAbscissa ≤ b₂ := by
    have hle : RHTower.zetaZeroAbscissa ≤ 1 / 2 + (b₂ - 1 / 2) := by
      rw [SquareRootThreshold.zetaZeroAbscissa_le_iff_zetaZeroConfig_re_le (by linarith)]
      intro ρ hρ
      obtain ⟨hζ, h0, _⟩ := (show Zeta23.IsNontrivialZero ρ from hρ)
      have hb := hz₂ ρ hζ h0
      linarith
    linarith
  have hΘ_b₁ : RHTower.zetaZeroAbscissa ≤ b₁ := by
    have h := hlev b₂ hΘ_b₂
    rwa [closedRightBandLever_apply_right hb₁₂.le] at h
  rw [BlackHoleRingdown.modularWightmanRL_analyticOnNhd_strip_iff
    (by linarith : 0 < (1 - b₁) / 2) (by linarith : (1 - b₁) / 2 ≤ 1 / 4)]
  intro ρ hζ h0
  have hle := (RHTower.re_le_zetaZeroAbscissa hζ).trans hΘ_b₁
  linarith

/-- **Unconditional eternal-AdS Wightman strip widening from `(b₁, 7/8]` forcing.** Combining the
unconditional `1/16` strip analyticity `modularWightmanRL_analyticOnNhd_one_sixteenth` with an
expanding forcing law on `(b₁, 7/8]` (`1/2 ≤ b₁ < 7/8`) establishes strip analyticity of
`modularWightmanRL` on `0 < |Im ω| < (1 - b₁)/2` with no auxiliary analyticity premise. -/
theorem unconditional_modularWightmanRL_strip_of_seven_eighths_band_forcing {b₁ : ℝ}
    (hb₁ : (1 / 2 : ℝ) ≤ b₁) (hb₁₂ : b₁ < 7 / 8) {g : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Set.Ioc b₁ (7 / 8)))
    (hg_gt : ∀ x ∈ Set.Ioc b₁ (7 / 8), x < g x)
    (hforce : ∀ ρ : ℂ, 0 < ρ.re → riemannZeta ρ = 0 → ρ.re ∈ Set.Ioc b₁ (7 / 8) →
      (∃ w : ℂ, riemannZeta w = 0 ∧ g ρ.re ≤ w.re) ∨ ExistsDirichletZeroRightOfSevenEighths) :
    AnalyticOnNhd ℂ BlackHoleRingdown.modularWightmanRL
      {ω : ℂ | 0 < |ω.im| ∧ |ω.im| < (1 - b₁) / 2} := by
  refine band_forcing_modularWightmanRL_strip_jump hb₁ hb₁₂ (by norm_num) hg_cont hg_gt hforce ?_
  rw [show ((1 - (7 / 8 : ℝ)) / 2 : ℝ) = 1 / 16 by norm_num]
  exact BlackHoleRingdown.modularWightmanRL_analyticOnNhd_one_sixteenth

/-! ## 5. Depth-expanding forcing and covering lever families imply `RiemannHypothesis` -/

/-- **Continuous depth-expanding zero forcing on `(1/2, 7/8]` implies `RiemannHypothesis`.**
Because `1/2 ≤ zetaZeroAbscissa ≤ 7/8` holds unconditionally, any continuous map `g` on `(1/2, 7/8]`
with `x < g x` whose zero-forcing rule produces either a `ζ`-zero of real part `≥ g(Re ρ)` or a
Dirichlet `L`-zero right of `7/8` forces `zetaZeroAbscissa = 1/2`, `zetaZeroWidth = 0`, and
`RiemannHypothesis`. -/
theorem riemannHypothesis_of_depth_expanding_forcing {g : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Set.Ioc (1 / 2) (7 / 8)))
    (hg_gt : ∀ x ∈ Set.Ioc (1 / 2) (7 / 8), x < g x)
    (hforce : ∀ ρ : ℂ, 0 < ρ.re → riemannZeta ρ = 0 → ρ.re ∈ Set.Ioc (1 / 2) (7 / 8) →
      (∃ w : ℂ, riemannZeta w = 0 ∧ g ρ.re ≤ w.re) ∨ ExistsDirichletZeroRightOfSevenEighths) :
    RHTower.zetaZeroAbscissa = 1 / 2 ∧
      SquareRootThreshold.zetaZeroWidth = 0 ∧
      RiemannHypothesis := by
  have hnotMem := (zetaZeroAbscissa_notMem_Ioc_of_band_forcing le_rfl (by norm_num)
    hg_cont hg_gt hforce).1
  have hhi : RHTower.zetaZeroAbscissa ≤ 7 / 8 := zetaZeroAbscissa_le_seven_eighths
  have hlo : (1 / 2 : ℝ) ≤ RHTower.zetaZeroAbscissa := RHTower.half_le_zetaZeroAbscissa
  have hΘ : RHTower.zetaZeroAbscissa = 1 / 2 := by
    by_contra hne
    exact hnotMem ⟨lt_of_le_of_ne hlo (Ne.symm hne), hhi⟩
  have hw : SquareRootThreshold.zetaZeroWidth = 0 := by
    rw [SquareRootThreshold.zetaZeroWidth_eq_zetaZeroAbscissa_sub_half, hΘ]
    ring
  exact ⟨hΘ, hw, SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr hw⟩

/-- **Covering lever family on `(1/2, 7/8]` implies `RiemannHypothesis`.** If every map `T ∈ 𝒯` is
a lever for `zetaZeroAbscissa` and their excluded sets cover `(1/2, 7/8]`, then
`zetaZeroAbscissa = 1/2`, `zetaZeroWidth = 0`, and `RiemannHypothesis` hold. -/
theorem riemannHypothesis_of_covering_levers {𝒯 : Set (ℝ → ℝ)}
    (hlev : ∀ T ∈ 𝒯, IsLever RHTower.zetaZeroAbscissa T)
    (hcov : Set.Ioc (1 / 2 : ℝ) (7 / 8) ⊆ ⋃ T ∈ 𝒯, excluded T) :
    RHTower.zetaZeroAbscissa = 1 / 2 ∧
      SquareRootThreshold.zetaZeroWidth = 0 ∧
      RiemannHypothesis := by
  have hhi : RHTower.zetaZeroAbscissa ≤ 7 / 8 := zetaZeroAbscissa_le_seven_eighths
  have hlo : (1 / 2 : ℝ) ≤ RHTower.zetaZeroAbscissa := RHTower.half_le_zetaZeroAbscissa
  have hΘ : RHTower.zetaZeroAbscissa = 1 / 2 := by
    by_contra hne
    have hmem : RHTower.zetaZeroAbscissa ∈ Set.Ioc (1 / 2 : ℝ) (7 / 8) :=
      ⟨lt_of_le_of_ne hlo (Ne.symm hne), hhi⟩
    obtain ⟨_, ⟨T, rfl⟩, _, ⟨hT, rfl⟩, hex⟩ := hcov hmem
    exact absurd (hlev T hT).le_apply_self (not_le.mpr hex)
  have hw : SquareRootThreshold.zetaZeroWidth = 0 := by
    rw [SquareRootThreshold.zetaZeroWidth_eq_zetaZeroAbscissa_sub_half, hΘ]
    ring
  exact ⟨hΘ, hw, SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr hw⟩

/-- **Collapse of the lever wall below `7/8`.** For any family `𝒯` of monotone maps fixing or
raising `1/2` (`1/2 ≤ T (1/2)`) whose excluded sets cover `(1/2, 7/8]`, both `wall 𝒯 (7/8)` and the
generated wall `wall {T | Generated 𝒯 T} (7/8)` equal `1/2`. -/
theorem wall_eq_half_of_covering_monotone_levers {𝒯 : Set (ℝ → ℝ)}
    (hmono : ∀ T ∈ 𝒯, Monotone T)
    (hhalf : ∀ T ∈ 𝒯, (1 / 2 : ℝ) ≤ T (1 / 2))
    (hcov : Set.Ioc (1 / 2 : ℝ) (7 / 8) ⊆ ⋃ T ∈ 𝒯, excluded T) :
    wall 𝒯 (7 / 8) = 1 / 2 ∧ wall {T | Generated 𝒯 T} (7 / 8) = 1 / 2 := by
  have hmem_half : (1 / 2 : ℝ) ∈ allowed 𝒯 (7 / 8) := ⟨by norm_num, hhalf⟩
  have hle1 : (1 / 2 : ℝ) ≤ wall 𝒯 (7 / 8) :=
    le_csSup (bddAbove_allowed 𝒯 (7 / 8)) hmem_half
  have hle2 : wall 𝒯 (7 / 8) ≤ 1 / 2 := by
    refine csSup_le ⟨1 / 2, hmem_half⟩ fun b hb => ?_
    by_contra hgt
    rw [not_le] at hgt
    obtain ⟨_, ⟨T, rfl⟩, _, ⟨hT, rfl⟩, hex⟩ := hcov ⟨hgt, hb.1⟩
    exact absurd (hb.2 T hT) (not_le.mpr hex)
  have hw : wall 𝒯 (7 / 8) = 1 / 2 := le_antisymm hle2 hle1
  exact ⟨hw, (wall_generated hmono (7 / 8)).trans hw⟩

end GaloisForLFunctions.ZeroForcingCalculus

#print axioms GaloisForLFunctions.ZeroForcingCalculus.isLever_bandLever_iff
#print axioms GaloisForLFunctions.ZeroForcingCalculus.isLever_closedRightBandLever_iff
#print axioms GaloisForLFunctions.ZeroForcingCalculus.not_existsDirichletZeroRightOfSevenEighths
#print axioms GaloisForLFunctions.ZeroForcingCalculus.zetaZeroAbscissa_notMem_Ioo_of_band_forcing
#print axioms GaloisForLFunctions.ZeroForcingCalculus.zetaZeroAbscissa_notMem_Ioc_of_band_forcing
#print axioms GaloisForLFunctions.ZeroForcingCalculus.band_forcing_width_ruler_jump
#print axioms GaloisForLFunctions.ZeroForcingCalculus.band_forcing_modularWightmanRL_strip_jump
#print axioms GaloisForLFunctions.ZeroForcingCalculus.unconditional_modularWightmanRL_strip_of_seven_eighths_band_forcing
#print axioms GaloisForLFunctions.ZeroForcingCalculus.riemannHypothesis_of_depth_expanding_forcing
#print axioms GaloisForLFunctions.ZeroForcingCalculus.riemannHypothesis_of_covering_levers
#print axioms GaloisForLFunctions.ZeroForcingCalculus.wall_eq_half_of_covering_monotone_levers
