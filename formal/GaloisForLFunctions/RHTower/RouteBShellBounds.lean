/-
Per-shell contribution bounds (doc 87 App B, the dyadic assembly's arms).

The (L3) base-case assembly splits the third-phase domain into dyadic
shells graded by tangency margin and pays a different law on each.  This
module provides the three arms as banked integral bounds over an ARBITRARY
measurable shell `E`, with the moving center `c + Ce^{iη}`:

* `setLIntegral_le_of_bound` — the trivial sup bound `∫⁻_E f ≤ C·vol E`.
* `shell_contribution` — on a shell with tangency margin `≥ m` and center
  modulus `≥ xmin`, the radial-band integral pays the transversal LINEAR
  law: `≤ 2π·r(2ρ+r)/(√m·xmin·‖B‖) · vol E`.
* `core_contribution` — on the caustic core, the unconditional √-law:
  `≤ 2π·√(2r(2ρ+r)/(xmin·‖B‖)) · vol E`.
* `center_shell_measure` — the measure of a shell in the SQUARED center
  modulus `‖c + Ce^{iη}‖² ∈ [a₁, a₂]` is `≤ 2π·√((a₂−a₁)/(‖c‖‖C‖))`:
  by `norm_center_sq_cos` the shell IS a cosine band at shift
  `arg(conj c · C)`, and the any-shift √-law applies.

Everything the dyadic sum consumes is now a one-line application.
-/
import Mathlib
import GaloisForLFunctions.RHTower.RouteBCausticShell

namespace RHTower
namespace Sublevel

open MeasureTheory

/-- The sup bound for a set integral: `∫⁻_E f ≤ C · vol E`. -/
theorem setLIntegral_le_of_bound {E : Set ℝ} (hE : MeasurableSet E)
    (f : ℝ → ENNReal) (C : ENNReal) (hf : ∀ η ∈ E, f η ≤ C) :
    ∫⁻ η in E, f η ≤ C * volume E := by
  calc ∫⁻ η in E, f η
      ≤ ∫⁻ _ in E, C := setLIntegral_mono' hE hf
    _ = C * volume E := setLIntegral_const E C

/-- **The transversal shell arm.**  On a shell `E` where the moving band
keeps tangency margin `m` and the center modulus stays `≥ xmin`, the
radial-band integral pays the LINEAR law times `vol E`. -/
theorem shell_contribution {B c C : ℂ} {ρ r m xmin : ℝ} {E : Set ℝ}
    (hE : MeasurableSet E) (hB : B ≠ 0) (hρ : 0 ≤ ρ) (hr : 0 ≤ r)
    (hm : 0 < m) (hm1 : m ≤ 1) (hx : 0 < xmin)
    (hEc : ∀ η ∈ E, c + C * Complex.exp ((η : ℂ) * Complex.I) ≠ 0)
    (hEx : ∀ η ∈ E,
      xmin ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖)
    (hEm : ∀ η ∈ E,
      |bandCenter (c + C * Complex.exp ((η : ℂ) * Complex.I)) B ρ|
        + bandHalf (c + C * Complex.exp ((η : ℂ) * Complex.I)) B ρ r
        ≤ 1 - m) :
    ∫⁻ η in E, volume {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        |‖c + C * Complex.exp ((η : ℂ) * Complex.I)
          + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ρ| ≤ r}
      ≤ ENNReal.ofReal (2 * Real.pi * (r * (2 * ρ + r))
          / (Real.sqrt m * (xmin * ‖B‖))) * volume E := by
  apply setLIntegral_le_of_bound hE
  intro η hη
  refine le_trans (radial_band_measure_transversal (hEc η hη) hB hρ hr hm hm1
    (hEm η hη)) (ENNReal.ofReal_le_ofReal ?_)
  have hB0 : (0 : ℝ) < ‖B‖ := norm_pos_iff.mpr hB
  have hsm : (0 : ℝ) < Real.sqrt m := Real.sqrt_pos.mpr hm
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  have hxx := hEx η hη
  gcongr

/-- **The caustic core arm.**  On any set `E` with center modulus `≥ xmin`,
the radial-band integral pays the unconditional √-law times `vol E`. -/
theorem core_contribution {B c C : ℂ} {ρ r xmin : ℝ} {E : Set ℝ}
    (hE : MeasurableSet E) (hB : B ≠ 0) (hρ : 0 ≤ ρ) (hr : 0 ≤ r)
    (hx : 0 < xmin)
    (hEc : ∀ η ∈ E, c + C * Complex.exp ((η : ℂ) * Complex.I) ≠ 0)
    (hEx : ∀ η ∈ E,
      xmin ≤ ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖) :
    ∫⁻ η in E, volume {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        |‖c + C * Complex.exp ((η : ℂ) * Complex.I)
          + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ρ| ≤ r}
      ≤ ENNReal.ofReal (2 * Real.pi
          * Real.sqrt (2 * (r * (2 * ρ + r) / (xmin * ‖B‖)))) * volume E := by
  apply setLIntegral_le_of_bound hE
  intro η hη
  refine le_trans (radial_band_measure (hEc η hη) hB hρ hr)
    (ENNReal.ofReal_le_ofReal ?_)
  have hB0 : (0 : ℝ) < ‖B‖ := norm_pos_iff.mpr hB
  have hxx := hEx η hη
  have hdiv : r * (2 * ρ + r)
        / (‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ * ‖B‖)
      ≤ r * (2 * ρ + r) / (xmin * ‖B‖) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_right hxx (norm_nonneg B))
  have hs : Real.sqrt (2 * (r * (2 * ρ + r)
        / (‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ * ‖B‖)))
      ≤ Real.sqrt (2 * (r * (2 * ρ + r) / (xmin * ‖B‖))) :=
    Real.sqrt_le_sqrt (by linarith)
  exact mul_le_mul_of_nonneg_left hs (by positivity)

/-- **The shell measure.**  A shell in the squared center modulus is a
cosine band (`norm_center_sq_cos`), so its measure obeys the √-law:
`vol{η : ‖c + Ce^{iη}‖² ∈ [a₁, a₂]} ≤ 2π·√((a₂−a₁)/(‖c‖‖C‖))`. -/
theorem center_shell_measure {c C : ℂ} {a₁ a₂ : ℝ} (hc : c ≠ 0)
    (hC : C ≠ 0) :
    volume {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
        ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 ∈ Set.Icc a₁ a₂}
      ≤ ENNReal.ofReal (2 * Real.pi
          * Real.sqrt (2 * ((a₂ - a₁) / (2 * (‖c‖ * ‖C‖))))) := by
  have hc0 : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
  have hC0 : (0 : ℝ) < ‖C‖ := norm_pos_iff.mpr hC
  set Y₀ : ℝ := ‖c‖ ^ 2 + ‖C‖ ^ 2 with hY₀
  set Y₁ : ℝ := 2 * (‖c‖ * ‖C‖) with hY₁
  have hY₁0 : (0 : ℝ) < Y₁ := by rw [hY₁]; positivity
  set u₁ : ℝ := max ((a₁ - Y₀) / Y₁) (-1) with hu₁
  set u₂ : ℝ := min ((a₂ - Y₀) / Y₁) 1 with hu₂
  have hmem : ∀ η : ℝ,
      ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 ∈ Set.Icc a₁ a₂ →
      Real.cos (η + ((starRingEnd ℂ) c * C).arg) ∈ Set.Icc u₁ u₂ := by
    intro η hy
    have hyval : ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2
        = Y₀ + Y₁ * Real.cos (η + ((starRingEnd ℂ) c * C).arg) := by
      rw [norm_center_sq_cos c C η, hY₀, hY₁]
    rw [hyval] at hy
    obtain ⟨hylo, hyhi⟩ := hy
    have hcos1 : (-1 : ℝ) ≤ Real.cos (η + ((starRingEnd ℂ) c * C).arg) :=
      Real.neg_one_le_cos _
    have hcos2 : Real.cos (η + ((starRingEnd ℂ) c * C).arg) ≤ 1 :=
      Real.cos_le_one _
    constructor
    · rw [hu₁]
      apply max_le
      · rw [div_le_iff₀ hY₁0]
        linarith
      · exact hcos1
    · rw [hu₂]
      apply le_min
      · rw [le_div_iff₀ hY₁0]
        linarith
      · exact hcos2
  rcases le_or_gt u₁ u₂ with hle | hgt
  · have hcover : {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
          ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 ∈ Set.Icc a₁ a₂}
        ⊆ {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
            Real.cos (η + ((starRingEnd ℂ) c * C).arg) ∈ Set.Icc u₁ u₂} := by
      rintro η ⟨hηI, hy⟩
      exact ⟨hηI, hmem η hy⟩
    have h1' : (-1 : ℝ) ≤ u₁ := le_max_right _ _
    have h2' : u₂ ≤ 1 := min_le_right _ _
    calc volume {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
          ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 ∈ Set.Icc a₁ a₂}
        ≤ volume {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
            Real.cos (η + ((starRingEnd ℂ) c * C).arg) ∈ Set.Icc u₁ u₂} :=
          measure_mono hcover
      _ ≤ ENNReal.ofReal (2 * Real.pi * Real.sqrt (2 * (u₂ - u₁))) :=
          cos_band_measure_shift_sqrt' h1' hle h2'
      _ ≤ ENNReal.ofReal (2 * Real.pi
            * Real.sqrt (2 * ((a₂ - a₁) / (2 * (‖c‖ * ‖C‖))))) := by
          apply ENNReal.ofReal_le_ofReal
          have hgap : u₂ - u₁ ≤ (a₂ - a₁) / Y₁ := by
            have hA1 : (a₁ - Y₀) / Y₁ ≤ u₁ := le_max_left _ _
            have hA2 : u₂ ≤ (a₂ - Y₀) / Y₁ := min_le_left _ _
            have hdiff : (a₂ - Y₀) / Y₁ - (a₁ - Y₀) / Y₁ = (a₂ - a₁) / Y₁ := by
              field_simp
              ring
            linarith
          rw [hY₁] at hgap
          have hs := Real.sqrt_le_sqrt
            (by linarith : 2 * (u₂ - u₁)
              ≤ 2 * ((a₂ - a₁) / (2 * (‖c‖ * ‖C‖))))
          exact mul_le_mul_of_nonneg_left hs (by positivity)
  · have hempty : {η : ℝ | η ∈ Set.Icc 0 (2 * Real.pi) ∧
        ‖c + C * Complex.exp ((η : ℂ) * Complex.I)‖ ^ 2 ∈ Set.Icc a₁ a₂}
        = ∅ := by
      ext η
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, hy⟩
      have := hmem η hy
      have h1 := this.1
      have h2 := this.2
      linarith
    rw [hempty, measure_empty]
    simp

end Sublevel
end RHTower
