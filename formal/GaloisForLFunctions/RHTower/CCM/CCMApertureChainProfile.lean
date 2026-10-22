import GaloisForLFunctions.RHTower.CCM.CCMApertureTranslationChains
import Mathlib.MeasureTheory.Function.Floor

/-!
# An order-independent correlation profile at every displacement

The chain length is determined by the aperture and translation, not by any
coefficient order. The full complex correlation is bounded by a measurable
cosine profile, strictly below one at every nonzero displacement.
-/

open Complex MeasureTheory Set
open scoped InnerProduct
noncomputable section
namespace RHTower

def ccmApertureChainProfile (a : SuzukiPositiveAperture) (h : ℝ) : ℝ :=
  if h = 0 then 1 else Real.cos (Real.pi / ((⌊2*a.1/|h|⌋₊ : ℝ) + 2))

theorem measurable_ccmApertureChainProfile (a : SuzukiPositiveAperture) :
    Measurable (ccmApertureChainProfile a) := by
  unfold ccmApertureChainProfile
  apply Measurable.ite (measurableSet_singleton 0) measurable_const
  fun_prop

theorem ccmApertureChainProfile_bounds (a : SuzukiPositiveAperture) (h : ℝ) :
    0 ≤ ccmApertureChainProfile a h ∧ ccmApertureChainProfile a h ≤ 1 := by
  by_cases hz : h = 0
  · simp [ccmApertureChainProfile, hz]
  · rw [ccmApertureChainProfile, if_neg hz]
    have hn : (0 : ℝ) ≤ (⌊2*a.1/|h|⌋₊ : ℝ) := Nat.cast_nonneg _
    have hd : (0 : ℝ) < (⌊2*a.1/|h|⌋₊ : ℝ) + 2 := by positivity
    refine ⟨Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩, Real.cos_le_one _⟩
    · have hp : 0 < Real.pi / ((⌊2*a.1/|h|⌋₊ : ℝ) + 2) := div_pos Real.pi_pos hd
      linarith [Real.pi_pos]
    · apply (div_le_div_iff₀ hd (by positivity : (0 : ℝ) < 2)).mpr
      nlinarith [Real.pi_pos]

theorem ccmApertureChainProfile_lt_one (a : SuzukiPositiveAperture)
    {h : ℝ} (hh : h ≠ 0) : ccmApertureChainProfile a h < 1 := by
  rw [ccmApertureChainProfile, if_neg hh]
  have hc := damping_lt_one (M := ⌊2*a.1/|h|⌋₊ + 1) (by omega)
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hc

/-- Every displacement and every full complex source vector satisfy one geometric profile. -/
theorem norm_ccmApertureCorrelation_le_profile (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (h : ℝ) :
    ‖ccmApertureCorrelation a f h‖ ≤ ccmApertureChainProfile a h * ‖f‖ ^ 2 := by
  by_cases hz : h = 0
  · simpa only [ccmApertureChainProfile, if_pos hz, one_mul] using
      norm_ccmApertureCorrelation_le a f h
  · have hp := abs_pos.mpr hz
    let n : ℕ := ⌊2*a.1/|h|⌋₊ + 1
    have hn : 2*a.1 < (n : ℝ) * |h| := (div_lt_iff₀ hp).mp (by
      simpa only [n, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (2*a.1/|h|))
    have hb := norm_ccmApertureCorrelation_le_chain a ⟨|h|, hp⟩ n hn f
    have he : ‖ccmApertureCorrelation a f |h|‖ = ‖ccmApertureCorrelation a f h‖ := by
      by_cases hpos : 0 ≤ h
      · rw [abs_of_nonneg hpos]
      · rw [abs_of_neg (lt_of_not_ge hpos), norm_ccmApertureCorrelation_neg]
    rw [he] at hb
    simpa only [ccmApertureChainProfile, if_neg hz, n, Nat.cast_add,
      Nat.cast_one, add_assoc, one_add_one_eq_two] using hb

theorem ccmApertureChainProfile_outer (a : SuzukiPositiveAperture)
    {h : ℝ} (hlo : a.1 < |h|) (hhi : |h| ≤ 2*a.1) :
    ccmApertureChainProfile a h = 1 / 2 := by
  have hp : 0 < |h| := a.property.trans hlo
  have ha : 0 < a.1 := a.property
  have hf : ⌊2*a.1/|h|⌋₊ = 1 := (Nat.floor_eq_iff (by positivity)).mpr ⟨by
      simpa only [Nat.cast_one] using (one_le_div hp).mpr hhi, by
      rw [div_lt_iff₀ hp]
      push_cast
      linarith only [hlo]⟩
  rw [ccmApertureChainProfile, if_neg (abs_pos.mp hp), hf, Nat.cast_one]
  convert Real.cos_pi_div_three using 1 <;> norm_num

/-- The complete next shell has the exact three-vertex sine coefficient. -/
theorem ccmApertureChainProfile_middle (a : SuzukiPositiveAperture)
    {h : ℝ} (hlo : 2*a.1/3 < |h|) (hhi : |h| ≤ a.1) :
    ccmApertureChainProfile a h = Real.sqrt 2 / 2 := by
  have ha : 0 < a.1 := a.property
  have hp : 0 < |h| := lt_trans (by positivity : 0 < 2*a.1/3) hlo
  have hf : ⌊2*a.1/|h|⌋₊ = 2 := (Nat.floor_eq_iff (by positivity)).mpr ⟨by
      rw [le_div_iff₀ hp]
      push_cast
      linarith only [hhi], by
      rw [div_lt_iff₀ hp]
      push_cast
      linarith only [hlo]⟩
  rw [ccmApertureChainProfile, if_neg (abs_pos.mp hp), hf]
  convert Real.cos_pi_div_four using 1 <;> norm_num

end RHTower
