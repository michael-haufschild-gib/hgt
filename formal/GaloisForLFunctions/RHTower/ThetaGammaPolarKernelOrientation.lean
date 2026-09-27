import GaloisForLFunctions.RHTower.ThetaPositiveScalingEnergies
import GaloisForLFunctions.RHTower.SuzukiScrewDisjointCrossCoupling

/-!
# The exact sign threshold of the continuous theta coupling

The continuous ground coefficient is the corpus's regular screw kernel at
positive lag. Thus its sign reversal occurs at the plastic-number threshold.
The existing atom-free disjoint-bump construction transfers through division
by the positive theta source: its positive cross coupling survives the ground
coordinates. Pointwise nonpositive off-diagonal coupling is therefore not an
available route to the full energy comparison.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower.ThetaSourceWard

open GaloisForLFunctions.RHTower

theorem thetaGammaPolarScalingKernel_eq_screw {u : ℝ} (hu : 0 < u) :
    thetaGammaPolarScalingKernel u = screwRegularKernel u := by
  rw [screwRegularKernel_eq_tailForm hu, thetaGammaPolarScalingKernel, Real.cosh_eq]
  simp only [neg_div, neg_mul]
  ring

theorem thetaGammaPolarScalingKernel_pos_iff_threshold {u : ℝ} (hu : 0 < u) :
    0 < thetaGammaPolarScalingKernel u ↔ screwSignThreshold < u := by
  rw [thetaGammaPolarScalingKernel_eq_screw hu]
  exact screwRegularKernel_pos_iff hu

theorem thetaGammaPolarScalingKernel_neg_below_threshold {u : ℝ} (hu : 0 < u)
    (hlt : u < screwSignThreshold) : thetaGammaPolarScalingKernel u < 0 := by
  rw [thetaGammaPolarScalingKernel_eq_screw hu]
  exact screwRegularKernel_neg_of_lt_threshold hu hlt

def thetaGammaPolarGroundCrossPairing (phi psi : 𝓢(ℝ, ℝ)) : ℝ :=
  ∫ p : ℝ × ℝ, thetaGammaPolarScalingKernel (p.1 - p.2) *
    thetaCuspFullSource p.1 * thetaCuspFullSource p.2 * phi p.2 * psi p.1

private theorem ground_ne_zero (x : ℝ) : thetaCuspFullSource x ≠ 0 :=
  (show 0 < thetaCuspFullSource x from thetaCuspTiltSource.pos x).ne'

private def realGroundProfile (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) : 𝓢(ℝ, ℝ) :=
  HasCompactSupport.toSchwartzMap
    (show HasCompactSupport (fun x => f x / thetaCuspFullSource x) by
      have h : HasCompactSupport (fun x => f x * (thetaCuspFullSource x)⁻¹) := hc.mul_right
      simpa only [div_eq_mul_inv] using h)
    (hf.div contDiff_thetaCuspFullSource ground_ne_zero)

/-- Actual theta ground coordinates retain positive coupling between disjoint nonnegative profiles.
The support differences also avoid every prime-power translation. -/
theorem exists_disjoint_positive_compact_thetaGammaPolarGroundCrossPairing :
    ∃ phi psi : 𝓢(ℝ, ℝ),
      (∀ x, 0 ≤ phi x) ∧ (∀ x, 0 ≤ psi x) ∧
      Disjoint (Function.support phi) (Function.support psi) ∧
      (∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
        screwSignThreshold < x - y ∧ ∀ n : ℕ, 2 ≤ n → x - y ≠ Real.log n) ∧
      Integrable (fun p : ℝ × ℝ => thetaGammaPolarScalingKernel (p.1 - p.2) *
        thetaCuspFullSource p.1 * thetaCuspFullSource p.2 * phi p.2 * psi p.1) ∧
      0 < thetaGammaPolarGroundCrossPairing phi psi ∧
      HasCompactSupport phi ∧ HasCompactSupport psi := by
  obtain ⟨f, h, hf, hh, hfpos, hhpos, _, _, _, _, hd, hfc, hhc, hgap, hcross⟩ :=
    exists_disjoint_positive_screwRegularForm
      (a := screwSignThreshold + 1) (by linarith [screwSignThreshold_pos])
  let phi := realGroundProfile f hf hfc
  let psi := realGroundProfile h hh hhc
  have hp (x : ℝ) : phi x = f x / thetaCuspFullSource x := rfl
  have hq (x : ℝ) : psi x = h x / thetaCuspFullSource x := rfl
  have hps : Function.support phi = Function.support f := by
    ext x
    simp only [Function.mem_support, hp, div_ne_zero_iff]
    exact ⟨And.left, fun hx => ⟨hx, ground_ne_zero x⟩⟩
  have hqs : Function.support psi = Function.support h := by
    ext x
    simp only [Function.mem_support, hq, div_ne_zero_iff]
    exact ⟨And.left, fun hx => ⟨hx, ground_ne_zero x⟩⟩
  refine ⟨phi, psi, fun x => by rw [hp]; exact div_nonneg (hfpos x) (thetaCuspTiltSource.pos x).le,
    fun x => by rw [hq]; exact div_nonneg (hhpos x) (thetaCuspTiltSource.pos x).le,
    by rwa [hps, hqs], ?_, ?_⟩
  · rw [hps, hqs]
    exact fun x hx y hy => hgap x (subset_tsupport _ hx) y (subset_tsupport _ hy)
  · have he : thetaGammaPolarGroundCrossPairing phi psi = screwRegularForm f h := by
      unfold thetaGammaPolarGroundCrossPairing screwRegularForm
      apply integral_congr_ae
      filter_upwards with p
      rw [hp, hq]
      by_cases hfy : f p.2 = 0
      · simp only [hfy, zero_div, mul_zero, zero_mul]
      by_cases hhx : h p.1 = 0
      · simp only [hhx, zero_div, mul_zero]
      have hxy := (hgap p.1 (subset_tsupport _ hhx) p.2 (subset_tsupport _ hfy)).1
      rw [thetaGammaPolarScalingKernel_eq_screw (screwSignThreshold_pos.trans hxy)]
      field_simp [ground_ne_zero]
    have hpositive : 0 < thetaGammaPolarGroundCrossPairing phi psi := he.symm ▸ hcross
    refine ⟨?_, hpositive, ?_, ?_⟩
    · by_contra hi
      have hz : thetaGammaPolarGroundCrossPairing phi psi = 0 := integral_undef hi
      exact hpositive.ne' hz
    · simpa only [HasCompactSupport, tsupport, hps] using hfc
    · simpa only [HasCompactSupport, tsupport, hqs] using hhc

theorem exists_disjoint_positive_thetaGammaPolarGroundCrossPairing :
    ∃ phi psi : 𝓢(ℝ, ℝ),
      (∀ x, 0 ≤ phi x) ∧ (∀ x, 0 ≤ psi x) ∧
      Disjoint (Function.support phi) (Function.support psi) ∧
      (∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
        screwSignThreshold < x - y ∧ ∀ n : ℕ, 2 ≤ n → x - y ≠ Real.log n) ∧
      Integrable (fun p : ℝ × ℝ => thetaGammaPolarScalingKernel (p.1 - p.2) *
        thetaCuspFullSource p.1 * thetaCuspFullSource p.2 * phi p.2 * psi p.1) ∧
      0 < thetaGammaPolarGroundCrossPairing phi psi := by
  obtain ⟨phi, psi, hp, hq, hd, hg, hi, hpos, _, _⟩ :=
    exists_disjoint_positive_compact_thetaGammaPolarGroundCrossPairing
  exact ⟨phi, psi, hp, hq, hd, hg, hi, hpos⟩

end RHTower.ThetaSourceWard
