import GaloisForLFunctions.ScaleSignedIncidenceCriticality.BoundedApertureReadingsHaveTheTrivialResolutionLimit
import GaloisForLFunctions.SquareRootThreshold.PositionAndDepthShareOneNyquistAperture
import GaloisForLFunctions.SquareRootThreshold.IsolatedOffLinePairVisibilityLaw

/-!
# Bounded-height readings cannot resolve the width

The reading here is the divisor truncated at height `T`: the zeros of ordinate at most `T` with
their multiplicities. By local finiteness this is a *finite* amount of data
(`finite_support_heightReading`), so it models every finite carrier — a finite spectral sum, a
finite-rank operator, a zero list computed up to a height.

Inserting one reflected off-line pair above height `T` into the doubled on-line lattice
(`SquareRootThreshold.isolatedPairConfig`) leaves the truncated divisor unchanged
(`heightReading_isolatedPairConfig`) and moves the width from `0` to the depth of the pair. Hence

* `not_resolves_heightReading_onLine`: no bounded-height reading decides whether the
  configuration is on the line;
* `resolutionLimit_width_heightReading`: the resolution limit of the width is exactly `½` at every
  height `T` — the trivial bound, as for a bounded aperture.

This is the "every scale, not almost every" criterion as a theorem, and the resolution form of the
no-finite-carrier wall: finitely many zeros, however many, carry no information about the width.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23

set_option autoImplicit false

/-! ### 1. The truncated divisor -/

/-- The divisor of `Z` truncated at height `T`: multiplicities of the zeros of ordinate at most
`T`, zero elsewhere. -/
noncomputable def heightReading (T : ℝ) (Z : TemperedZeroConfig) : ℂ → ℕ :=
  fun ρ => if ρ ∈ Z.1.carrier ∧ |ρ.im| ≤ T then Z.1.mult ρ else 0

/-- **The reading is finite data**: a truncated divisor is supported on a finite set of zeros. -/
theorem finite_support_heightReading (T : ℝ) (Z : TemperedZeroConfig) :
    {ρ : ℂ | heightReading T Z ρ ≠ 0}.Finite := by
  refine (Z.1.finite_window (-T - 1) T).subset fun ρ hρ => ?_
  by_cases h : ρ ∈ Z.1.carrier ∧ |ρ.im| ≤ T
  · obtain ⟨hc, hT⟩ := h
    have h1 : -T ≤ ρ.im := neg_le_of_abs_le hT
    exact ⟨hc, by constructor <;> [linarith; linarith [le_of_abs_le hT]]⟩
  · simp only [Set.mem_setOf_eq, heightReading, if_neg h, ne_eq, not_true_eq_false] at hρ

/-! ### 2. One off-line pair above the height is invisible -/

/-- The on-line lattice as a datum of the calculus. -/
def onLineLattice {L : ℝ} (hL : 0 < L) : TemperedZeroConfig :=
  ⟨onLineLatticeConfig hL, temperedConfig_onLineLatticeConfig hL⟩

/-- The same lattice with one reflected off-line pair of depth `δ` inserted at height `|T| + 1`. -/
def latticeWithPairAbove {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (T : ℝ) :
    TemperedZeroConfig :=
  ⟨isolatedPairConfig hL hδ hδ' (|T| + 1), temperedConfig_isolatedPairConfig hL hδ hδ' (|T| + 1)⟩

theorem width_onLineLattice {L : ℝ} (hL : 0 < L) : width (onLineLattice hL) = 0 :=
  configWidth_onLineLatticeConfig hL

/-- The inserted pair has depth `½` when `δ = ½`, so the width of the perturbed lattice is `½`. -/
theorem width_latticeWithPairAbove_half {L : ℝ} (hL : 0 < L) (T : ℝ) :
    width (latticeWithPairAbove hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl T) = 1 / 2 := by
  refine le_antisymm (width_le_half _) ?_
  have hmem : offLinePoint (1 / 2) (|T| + 1) ∈
      (isolatedPairConfig hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl (|T| + 1)).carrier :=
    Or.inl (Or.inr rfl)
  have h := abs_re_sub_half_le_configWidth hmem
  simpa [offLinePoint, abs_of_nonneg] using h

/-- **The pair above the height is invisible to the truncated divisor.** -/
theorem heightReading_isolatedPairConfig {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (T : ℝ) : heightReading T (latticeWithPairAbove hL hδ hδ' T) = heightReading T (onLineLattice hL) := by
  have habove : ¬ |(|T| + 1 : ℝ)| ≤ T := by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |T| + 1)]
    exact not_le.mpr (by linarith [le_abs_self T])
  funext ρ
  by_cases hρ : ρ ∈ (onLineLatticeConfig hL).carrier ∧ |ρ.im| ≤ T
  · obtain ⟨⟨k, rfl⟩, hT⟩ := hρ
    have hmem : verticalLatticePoint L 0 k ∈
        (isolatedPairConfig hL hδ hδ' (|T| + 1)).carrier := Or.inl (Or.inl ⟨k, rfl⟩)
    have hre : (verticalLatticePoint L 0 k).re = 1 / 2 := by simp [verticalLatticePoint]
    simp only [heightReading, latticeWithPairAbove, onLineLattice, if_pos ⟨hmem, hT⟩,
      if_pos ⟨⟨k, rfl⟩, hT⟩, isolatedPairConfig, onLineLatticeConfig, hre, if_pos rfl]
  · have hpair : ¬ (ρ ∈ (isolatedPairConfig hL hδ hδ' (|T| + 1)).carrier ∧ |ρ.im| ≤ T) := by
      rintro ⟨hc, hT⟩
      rcases hc with (hlat | hp) | hp
      · exact hρ ⟨hlat, hT⟩
      · rw [Set.mem_singleton_iff] at hp
        exact habove (by rw [hp] at hT; simpa [offLinePoint] using hT)
      · rw [Set.mem_singleton_iff] at hp
        exact habove (by rw [hp] at hT; simpa [offLinePoint] using hT)
    simp only [heightReading, latticeWithPairAbove, onLineLattice, if_neg hpair, if_neg hρ]

/-! ### 3. The gate -/

/-- **No bounded-height reading decides the critical line.** -/
theorem not_resolves_heightReading_onLine {L : ℝ} (hL : 0 < L) (T : ℝ) :
    ¬ Resolves (heightReading T) (fun Z : TemperedZeroConfig => width Z = 0) := by
  refine not_resolves_of_pair (d := onLineLattice hL)
    (e := latticeWithPairAbove hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl T)
    (heightReading_isolatedPairConfig hL _ _ T) (width_onLineLattice hL) ?_
  rw [width_latticeWithPairAbove_half hL T]
  norm_num

/-- **The resolution limit of the width at every finite height is `½`.** -/
theorem resolutionLimit_width_heightReading {L : ℝ} (hL : 0 < L) (T : ℝ) :
    resolutionLimit width (heightReading T) (onLineLattice hL) = 1 / 2 := by
  refine le_antisymm (csSup_le (shadow_image_nonempty width (heightReading T) _) ?_) ?_
  · rintro x ⟨W, -, rfl⟩
    exact width_le_half W
  · have hmem : latticeWithPairAbove hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl T ∈
      shadow (heightReading T) (onLineLattice hL) := heightReading_isolatedPairConfig hL _ _ T
    have := le_csSup (bddAbove_width_image (shadow (heightReading T) (onLineLattice hL)))
      ⟨_, hmem, rfl⟩
    rwa [width_latticeWithPairAbove_half hL T] at this

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
