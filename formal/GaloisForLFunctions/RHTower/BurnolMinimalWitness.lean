import GaloisForLFunctions.RHTower.ZetaDivPowHeadTail
import GaloisForLFunctions.RHTower.SoninFromHardyData
import GaloisForLFunctions.RHTower.MellinContinuationOrder
import GaloisForLFunctions.RHTower.MellinLineMass

/-!
# The vector of `L₁` whose Mellin transform is `ζ(s)/(s-ρ)^l`

Combining Burnol's Proposition 4.2 at `ρ` and at the mirror zero `1-ρ`
(`ZetaDivPowHeadTail`) with the two-sided converse of Proposition 4.1
(`SoninFromHardyData`) produces an actual vector of the extended Sonine space `L₁` whose continued
Mellin transform is the analytic representative of `ζ(s)/(s-ρ)^l` on the whole open critical strip.

These are Burnol's *dual* vectors: they are the witnesses that make the evaluator system minimal.

## Main results

* `exists_extendedSonin_zetaDivPow`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem isPreconnected_criticalOpenStrip : IsPreconnected {w : ℂ | 0 < w.re ∧ w.re < 1} := by
  have hconv : Convex ℝ {w : ℂ | 0 < w.re ∧ w.re < 1} := by
    have h1 : Convex ℝ {w : ℂ | 0 < w.re} := convex_halfSpace_re_gt 0
    have h2 : Convex ℝ {w : ℂ | w.re < 1} := convex_halfSpace_re_lt 1
    exact h1.inter h2
  exact hconv.isPreconnected

/-- **The dual vector attached to a zero `ρ` and an exponent `l ≤ m_ρ`.** -/
theorem exists_extendedSonin_zetaDivPow {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {l : ℕ}
    (hl : 1 ≤ l) (hord : (l : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) :
    ∃ (v : SoninL2) (c d : ℂ), v ∈ evenSubspace ∧ v ∈ centralSoninExtendedCarrier 1 ∧
      (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval 1 →
        ((fourierUnitary v : SoninL2) : ℝ → ℂ) x = c) ∧
      (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval 1 → (v : ℝ → ℂ) t = d) ∧
      ∀ s : ℂ, 0 < s.re → s.re < 1 →
        extendedMellinContinuation 1 c d v s = zetaDivPowNF ρ l s := by
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  obtain ⟨c₁, g₁, hg₁, heq₁⟩ := exists_headTail_zetaDivPowNF h0 h1 hl hord
  obtain ⟨c₂, g₂, hg₂, heq₂⟩ := exists_headTail_zetaDivPowNF_reflect h0 h1 hl hord
  have hFcont : ContinuousOn (zetaDivPowNF ρ l) {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    intro z hz
    have hz1 : z ≠ 1 := by
      intro h
      rw [h] at hz
      simp at hz
    exact ((analyticAt_zetaDivPowNF hρ1 hord hz1).continuousAt).continuousWithinAt
  obtain ⟨hmem, hband⟩ :=
    headTailVector_mem_centralSoninExtendedCarrier (a := 1) one_pos hFcont hg₁ heq₁ hg₂ heq₂
  set v : SoninL2 := headTailVector (a := 1) one_pos c₁ hg₁ with hvdef
  have hev : v ∈ evenSubspace := headTailVector_mem_evenSubspace one_pos c₁ hg₁
  have hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval 1 → (v : ℝ → ℂ) t = c₁ :=
    headTailVector_ae_band one_pos c₁ hg₁
  refine ⟨v, c₂, c₁, hev, hmem, hband, hd, ?_⟩
  -- the transform on the right half of the strip
  have hright : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      extendedMellinContinuation 1 c₂ c₁ v s = zetaDivPowNF ρ l s := by
    intro s hs1 hs2
    have hs0 : s ≠ 0 := by
      intro h; rw [h] at hs1; simp at hs1; linarith
    have hsne1 : s ≠ 1 := by
      intro h; rw [h] at hs2; simp at hs2
    rw [extendedMellinContinuation_eq_right 1 c₂ c₁ v (le_of_lt hs1) hs0 hsne1,
      extendedMellinRight, extendedTailMellin_eq one_pos hband hs1]
    have htail : (∫ t in Ioi (1 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * (v : ℝ → ℂ) t)
        = ∫ t in Ioi (1 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * g₁ t := by
      refine integral_congr_ae ?_
      filter_upwards [headTailVector_ae_tail one_pos c₁ hg₁] with t ht
      rw [ht]
    rw [htail, heq₁ s hs1 hs2, headTailMellin]
    ring
  -- extend to the whole strip by the identity theorem
  intro s hs0 hs1
  have hU : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} := isOpen_openStrip
  have hA1 : AnalyticOnNhd ℂ (extendedMellinContinuation 1 c₂ c₁ v)
      {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h; rw [h] at hz; simp at hz
    have hz1 : z ≠ 1 := by
      intro h; rw [h] at hz; simp at hz
    exact analyticAt_extendedMellinContinuation_of_ne one_pos hev hband hd hz0 hz1
  have hA2 : AnalyticOnNhd ℂ (zetaDivPowNF ρ l) {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    intro z hz
    have hz1 : z ≠ 1 := by
      intro h; rw [h] at hz; simp at hz
    exact analyticAt_zetaDivPowNF hρ1 hord hz1
  have hz₀ : ((3 / 4 : ℝ) : ℂ) ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    constructor <;> simp <;> norm_num
  have hev₀ : extendedMellinContinuation 1 c₂ c₁ v =ᶠ[𝓝 ((3 / 4 : ℝ) : ℂ)]
      zetaDivPowNF ρ l := by
    have hopen : IsOpen {z : ℂ | 1 / 2 < z.re ∧ z.re < 1} := isOpen_rightStrip
    have hmem₀ : ((3 / 4 : ℝ) : ℂ) ∈ {z : ℂ | 1 / 2 < z.re ∧ z.re < 1} := by
      constructor <;> simp <;> norm_num
    filter_upwards [hopen.mem_nhds hmem₀] with z hz
    exact hright z hz.1 hz.2
  exact hA1.eqOn_of_preconnected_of_eventuallyEq hA2 isPreconnected_criticalOpenStrip hz₀ hev₀ ⟨hs0, hs1⟩

end

end RHTower
