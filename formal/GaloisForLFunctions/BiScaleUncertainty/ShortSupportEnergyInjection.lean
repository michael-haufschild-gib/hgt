import GaloisForLFunctions.BiScaleUncertainty.UnitEnergySmallSources
import GaloisForLFunctions.BiScaleUncertainty.SmallSourceCorrelationStability

/-!
# Energy injection inside a fixed short source interval

A unit-energy bump of sufficiently small mass is translated off a fixed smooth seed.
One sign retains an energy gain, while both source support and normalized correlation
error remain controlled. Every quantity is constructed from actual scalar sources.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-- An arbitrarily small correlation perturbation can retain a fixed positive energy gain. -/
theorem exists_short_support_energy_injection {f : ℝ → ℝ} {b t : ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
    (hR : 0 < autocorr f 0) (hb : 0 < b) (hs : ∀ u, b < |u| → f u = 0)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ g : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) g ∧ HasCompactSupport g ∧
      0 < autocorr g 0 ∧ (∀ u, 5 * b < |u| → g u = 0) ∧
      normalizedArchEnergy g ≤ 2 * (biScaleLevyEnergy f + 1) / autocorr f 0 ∧
      normalizedArchEnergy f + 1 / (2 * autocorr f 0) ≤ normalizedArchEnergy g ∧
      (∫ u, (g u - f u) ^ 2) ≤ t ^ 2 ∧
      ∀ x, |autocorr g x / autocorr g 0 - autocorr f x / autocorr f 0| ≤
        t * (autocorr f 0 + 3) / autocorr f 0 := by
  have htwo : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
    WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hA := biScaleLevyEnergy_nonneg hfc hf.continuous
  have hden : 0 < 2 * biScaleLevyEnergy f + 1 := by positivity
  have hη : 0 < min (t ^ 2) (autocorr f 0 / (2 * biScaleLevyEnergy f + 1)) :=
    lt_min (sq_pos_of_pos ht) (div_pos hR hden)
  obtain ⟨q, hq, hqc, hqR, hqm, hqJ, hqs⟩ := exists_smooth_unit_energy_small_mass hb hη
  let p := sourceTranslate q (4 * b)
  have hp : ContDiff ℝ (↑(⊤ : ℕ∞)) p := hq.comp (contDiff_id.sub contDiff_const)
  have hpc : HasCompactSupport p := hqc.comp_homeomorph (Homeomorph.subRight (4 * b))
  have hpR : autocorr p 0 = autocorr q 0 := autocorr_sourceTranslate q (4 * b) 0
  have hpJ : biScaleLevyEnergy p = 1 := (biScaleLevyEnergy_sourceTranslate q (4 * b)).trans hqJ
  obtain ⟨s, hs2, hJlo, hJhi⟩ := exists_signed_source_energy_between
    (hf.of_le htwo) (hp.of_le htwo) hfc hpc
  let v := fun u => s * p u
  have hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v := contDiff_const.mul hp
  have hvc : HasCompactSupport v := hpc.mul_left
  have hvR : autocorr v 0 = autocorr q 0 := by
    dsimp [v]
    rw [autocorr_source_const_mul, hs2, one_mul, hpR]
  have hvs : ∀ u, b < |u - 4 * b| → v u = 0 := by
    intro u hu
    simp only [v, p, sourceTranslate, hqs _ hu, mul_zero]
  have hcross : ∀ u, f u * v u = 0 := by
    intro u
    by_cases hu : f u = 0
    · simp [hu]
    have hbu : |u| ≤ b := le_of_not_gt fun h => hu (hs u h)
    have hz : v u = 0 := hvs u (lt_of_lt_of_le
      (by linarith [le_abs_self u] : b < -(u - 4 * b)) (neg_le_abs _))
    simp [hz]
  let g := fun u => f u + v u
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g := hf.add hv
  have hgc : HasCompactSupport g := hfc.add hvc
  have hmass : autocorr g 0 = autocorr f 0 + autocorr q 0 := by
    dsimp [g]
    rw [autocorr_add_of_cross_zero hf.continuous hv.continuous hfc hvc 0 (by
      intro u
      simpa only [add_zero, mul_comm] using And.intro (hcross u) (hcross u)), hvR]
  have hgR : 0 < autocorr g 0 := by rw [hmass]; positivity
  have hsupport : ∀ u, 5 * b < |u| → g u = 0 := by
    intro u hu
    have hfu := hs u (by linarith)
    have htriangle : |u| ≤ |u - 4 * b| + 4 * b := by
      simpa only [sub_add_cancel, abs_of_pos (by positivity : 0 < 4 * b)] using
        abs_add_le (u - 4 * b) (4 * b)
    have hvu := hvs u (by linarith)
    simp only [g, hfu, hvu, add_zero]
  have hlo : biScaleLevyEnergy f + 1 ≤ biScaleLevyEnergy g := by
    simpa only [hpJ, g, v] using hJlo
  have hhi : biScaleLevyEnergy g ≤ 2 * (biScaleLevyEnergy f + 1) := by
    simpa only [hpJ, g, v] using hJhi
  have hsum : 0 < autocorr f 0 + autocorr q 0 := by positivity
  refine ⟨g, hg, hgc, hgR, hsupport, ?_, ?_, ?_, ?_⟩
  · unfold normalizedArchEnergy
    rw [hmass]
    exact (div_le_div_of_nonneg_right hhi hsum.le).trans
      (div_le_div_of_nonneg_left (by positivity) hR (by linarith))
  · unfold normalizedArchEnergy
    rw [hmass]
    apply le_trans ?_ (div_le_div_of_nonneg_right hlo hsum.le)
    have hrsmall : autocorr q 0 * (2 * biScaleLevyEnergy f + 1) ≤ autocorr f 0 :=
      (le_div_iff₀ hden).mp (hqm.le.trans (min_le_right _ _))
    have heq : biScaleLevyEnergy f / autocorr f 0 + 1 / (2 * autocorr f 0) =
        (2 * biScaleLevyEnergy f + 1) / (2 * autocorr f 0) := by field_simp
    rw [heq]
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * autocorr f 0) hsum).mpr
    nlinarith
  · have heq : (fun u => (g u - f u) ^ 2) = fun u => v u ^ 2 := by
      funext u
      simp only [g, add_sub_cancel_left]
    rw [heq, integral_sq_eq_autocorr_zero, hvR]
    exact hqm.le.trans (min_le_left _ _)
  · intro x
    apply normalized_autocorr_add_small_mass_le hf.continuous hv.continuous hfc hvc hR hcross ht ht1
    rw [hvR]
    exact hqm.le.trans (min_le_left _ _)

end

end GaloisForLFunctions.BiScaleUncertainty
