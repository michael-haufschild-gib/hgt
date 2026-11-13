import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ActualHalfLineLevyEnergy
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.ArchimedeanTailMassDiverges
import GaloisForLFunctions.RHTower.WeilLevyCoshPlasticCrossover
import GaloisForLFunctions.RHTower.WeilLevyHarmonicDoublingPairCoupling

/-!
# Cutoff Gamma rows and their square-integrable kernels

Removing a positive neighborhood of zero makes the Lévy kernel square
integrable. Its action on an L² profile is bounded by Cauchy–Schwarz, while
its total row mass becomes arbitrarily large as the cutoff approaches zero.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open WeilLevyCoshCrossover

/-- The singular Gamma density differs from the inverse-distance kernel by a bounded function. -/
theorem abs_archLevyDensity_sub_inverse_le {h : ℝ} (hh : 0 < h) :
    |archLevyDensity h - 1 / (2 * h)| ≤ 1 / 2 := by
  have hdpos : 0 < 1 - Real.exp (-2 * h) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [hh]))
  have hd : 1 - Real.exp (-2 * h) ≤ 2 * h := by
    linarith only [Real.add_one_le_exp (-2 * h)]
  have he : archLevyDensity h * (1 - Real.exp (-2 * h)) = Real.exp (-h / 2) := by
    unfold archLevyDensity
    field_simp [hdpos.ne']
  have hmul := mul_le_mul_of_nonneg_left hd (archLevyDensity_pos hh).le
  rw [he] at hmul
  have hlo : (1 - h / 2) / (2 * h) ≤ archLevyDensity h := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hh)).mpr
    nlinarith only [hmul, Real.add_one_le_exp (-h / 2)]
  have hid : (1 - h / 2) / (2 * h) = 1 / (2 * h) - 1 / 4 := by
    field_simp [hh.ne'] <;> ring
  rw [hid] at hlo
  have hup := WeilLevyHarmonicDoubling.two_mul_archLevyDensity_le_inv_add_half hh
  have hinv : 1 / h = 2 * (1 / (2 * h)) := by
    field_simp [hh.ne']
  rw [hinv] at hup
  exact abs_le.mpr ⟨by linarith only [hlo], by linarith only [hup]⟩

/-- Every positive cutoff removes the only obstruction to square integrability of the density. -/
theorem integrableOn_sq_archLevyDensity {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun h : ℝ => archLevyDensity h ^ 2) (Ioi δ) := by
  have hi : IntegrableOn (fun h : ℝ => Real.exp (-h)) (Ioi δ) := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) δ
  refine (hi.const_mul ((1 - Real.exp (-2 * δ))⁻¹ ^ 2)).mono'
    (measurable_archLevyDensity.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (archLevyDensity h))]
  have hb := pow_le_pow_left₀ (archLevyDensity_pos (hδ.trans hh)).le
    (archLevyDensity_le_of_le hδ hh.le) 2
  have he : Real.exp (-(1 / 2 : ℝ) * h) ^ 2 = Real.exp (-h) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  simpa only [mul_pow, he] using hb

/-- The ordinary cutoff row mass is unbounded, independently of all profiles. -/
theorem exists_halfLineGamma_cutoffMass_gt (C : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ C < 2 * ∫ h in Ioi δ, archLevyDensity h := by
  obtain ⟨δ, hδ, hδ1, hlarge⟩ :=
    CanonicalSystemOfTheWindowTower.archimedean_tail_integral_unbounded (C / 2)
  have hmono : (∫ h in δ..1, archLevyDensity h) ≤ ∫ h in Ioi δ, archLevyDensity h := by
    rw [intervalIntegral.integral_of_le hδ1.le]
    apply setIntegral_mono_set (integrableOn_archLevyDensity_Ioi hδ)
      ((ae_restrict_mem measurableSet_Ioi).mono fun h hh => (archLevyDensity_pos (hδ.trans hh)).le)
    exact Eventually.of_forall fun h hh => hh.1
  refine ⟨δ, hδ, hδ1, ?_⟩
  linarith only [hlarge, hmono]

/-- The cutoff kernel pairs boundedly with any square-integrable real profile. -/
theorem abs_integral_cutoff_archLevyDensity_mul_le {δ : ℝ} (hδ : 0 < δ)
    {H : ℝ → ℝ} (hHm : Measurable H) (hHsq : Integrable (fun h => H h ^ 2)) :
    |∫ h in Ioi δ, archLevyDensity h * H h| ≤
      Real.sqrt (∫ h in Ioi δ, archLevyDensity h ^ 2) * Real.sqrt (∫ h, H h ^ 2) := by
  have hcs := HTGeometry.sq_integral_mul_le
    (μ := volume.restrict (Ioi δ))
    measurable_archLevyDensity.aestronglyMeasurable hHm.aestronglyMeasurable
    (integrableOn_sq_archLevyDensity hδ) hHsq.integrableOn
  have hmass : (∫ h in Ioi δ, H h ^ 2) ≤ ∫ h, H h ^ 2 :=
    setIntegral_le_integral hHsq (Eventually.of_forall fun h => sq_nonneg _)
  have hkernel : 0 ≤ ∫ h in Ioi δ, archLevyDensity h ^ 2 :=
    integral_nonneg fun h => sq_nonneg _
  have hb := hcs.trans (mul_le_mul_of_nonneg_left hmass hkernel)
  rw [← Real.sqrt_mul hkernel]
  apply Real.le_sqrt_of_sq_le
  simpa only [sq_abs] using hb

#print axioms integrableOn_sq_archLevyDensity
#print axioms abs_archLevyDensity_sub_inverse_le
#print axioms exists_halfLineGamma_cutoffMass_gt
#print axioms abs_integral_cutoff_archLevyDensity_mul_le
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
