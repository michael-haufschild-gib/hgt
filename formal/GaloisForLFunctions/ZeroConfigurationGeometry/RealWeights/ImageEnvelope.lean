import GaloisForLFunctions.ZeroConfigurationGeometry.RealWeights.StripFourier
import GaloisForLFunctions.ZeroConfigurationGeometry.RealWeights.PositiveImages


/-!
# A central envelope and an absolute tail for weighted images

A finite central band is controlled by the common strip envelope. Outside
that band, sixth-order transform decay bounds the entire contribution by
absolute Lorentzian mass, uniformly over the modulation height.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23

/-- A common strip envelope pays for a finite central band; absolute Lorentzian
mass pays for the remaining weighted image by sixth-order Fourier decay. -/
theorem weightedImage_le_central_envelope {c : ℂ → ℂ}
    (hstrip : ∀ z, c z ≠ 0 → 0 ≤ z.re ∧ z.re ≤ 1)
    (hc : Summable fun z => ‖c z‖ / (1 + Complex.normSq (gammaOf z)))
    {b : ℝ → ℂ} {ε : ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbs : tsupport b ⊆ Icc (-ε) ε) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X R : ℝ) (s : Finset ℂ), 0 ≤ R →
      (∀ z, c z ≠ 0 → z ∉ s → R < |z.im - X|) →
      ‖weightedImage c (localWindow X b) (localWindow X b)‖ ≤
        (∑ z ∈ s, ‖c z‖ * cameraStripEnvelope b ε (z.im - X)) +
          C * C * Real.exp ε * (5 / 4 * (1 + |X|) ^ 2 / (1 + R) ^ 4) *
            ∑' z, ‖c z‖ / (1 + Complex.normSq (gammaOf z)) := by
  classical
  obtain ⟨C, hC, hdec⟩ := norm_paperFT_localWindow_mul_le hb hε.le hbs 3
  refine ⟨C, hC, fun X R s hR hfar => ?_⟩
  have hbw : ApertureWindow ε b := ⟨hb.of_le (by norm_cast), hbs⟩
  have hfw := apertureWindow_localWindow hbw X
  have hsum := summable_norm_weighted_pointImage hstrip hc
    hfw.1 hfw.hasCompactSupport hfw.1 hfw.hasCompactSupport
  obtain ⟨htail, htail_le⟩ := tsum_far_le hstrip hc (by norm_num : 1 ≤ (3 : ℕ)) hε.le
    (fun w _ => hdec X w) (fun w _ => hdec X w) hR
  let A : ℂ → ℝ := fun z => if z ∈ s then ‖c z‖ * cameraStripEnvelope b ε (z.im - X) else 0
  have hA : Summable A := summable_of_ne_finset_zero (s := s) fun z hz => if_neg hz
  have hAe : (∑' z, A z) = ∑ z ∈ s, ‖c z‖ * cameraStripEnvelope b ε (z.im - X) := by
    rw [tsum_eq_sum (s := s) fun z hz => if_neg hz]
    exact Finset.sum_congr rfl fun z hz => if_pos hz
  have hbound (z : ℂ) : ‖c z * pointImage (localWindow X b) (localWindow X b) z‖ ≤
      A z + farTerm c (localWindow X b) (localWindow X b) X R z := by
    have htail0 : 0 ≤ farTerm c (localWindow X b) (localWindow X b) X R z := by
      unfold farTerm
      split_ifs <;> positivity
    by_cases hcz : c z = 0
    · rw [hcz, zero_mul, norm_zero]
      have hA0 : 0 ≤ A z := by
        dsimp [A]
        split_ifs
        · exact mul_nonneg (norm_nonneg _) (cameraStripEnvelope_nonneg hε _)
        · exact le_rfl
      exact add_nonneg hA0 htail0
    by_cases hz : z ∈ s
    · have hsz := hstrip z hcz
      have hdepth : |depth z| ≤ 1 / 2 := by
        rw [depth, abs_le]
        constructor <;> linarith only [hsz.1, hsz.2]
      have hh := mul_le_mul_of_nonneg_left
        (norm_local_pointImage_le_cameraStripEnvelope hb.continuous hbw.hasCompactSupport
          hε z hdepth X) (norm_nonneg (c z))
      rw [norm_mul]
      exact hh.trans (by dsimp [A]; rw [if_pos hz]; exact le_add_of_nonneg_right htail0)
    · rw [show A z = 0 from if_neg hz, zero_add, farTerm, if_pos (hfar z hcz hz), norm_mul]
  calc
    _ ≤ ∑' z, ‖c z * pointImage (localWindow X b) (localWindow X b) z‖ :=
      norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' z, (A z + farTerm c (localWindow X b) (localWindow X b) X R z) :=
      hsum.tsum_le_tsum hbound (hA.add htail)
    _ = (∑ z ∈ s, ‖c z‖ * cameraStripEnvelope b ε (z.im - X)) +
        ∑' z, farTerm c (localWindow X b) (localWindow X b) X R z := by
      rw [hA.tsum_add htail, hAe]
    _ ≤ _ := add_le_add le_rfl (by simpa only [show 2 * 3 - 2 = (4 : ℕ) by norm_num] using htail_le)

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.weightedImage_le_central_envelope
