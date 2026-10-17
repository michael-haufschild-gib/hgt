import GaloisForLFunctions.BiScaleUncertainty.FiniteSourceEnergyScalarization

/-!
# Small-source stability and energy-retaining signs

Young's inequality bounds mixed correlations uniformly by the two actual source masses.
For disjoint sources this gives a normalized correlation modulus. The exact energy
parallelogram chooses a sign retaining at least the sum of the component energies.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-- Young's inequality for two actual translated sources, with all integrability derived. -/
theorem source_cross_integral_young {f q : ℝ → ℝ} (hf : Continuous f) (hq : Continuous q)
    (hfc : HasCompactSupport f) (hqc : HasCompactSupport q) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    2 * |∫ u, f u * q (u + x)| ≤ t * autocorr f 0 + autocorr q 0 / t := by
  have hif := integrable_sq hf hfc
  have hiq : Integrable (fun u => q (u + x) ^ 2) :=
    integrable_sq (hq.comp (continuous_add_const x)) (hasCompactSupport_comp_add hqc x)
  have hprod : Integrable (fun u => f u * q (u + x)) :=
    (hf.mul (hq.comp (continuous_add_const x))).integrable_of_hasCompactSupport hfc.mul_right
  have hp (a b : ℝ) : 2 * |a * b| ≤ t * a ^ 2 + b ^ 2 / t := by
    have hs : 0 ≤ (t * |a| - |b|) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
    have he : (t * |a| - |b|) ^ 2 / t = t * a ^ 2 + b ^ 2 / t - 2 * |a * b| := by
      rw [abs_mul]
      field_simp
      nlinarith only [sq_abs a, sq_abs b]
    linarith
  calc
    _ ≤ 2 * ∫ u, |f u * q (u + x)| :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by norm_num)
    _ = ∫ u, 2 * |f u * q (u + x)| := (integral_const_mul _ _).symm
    _ ≤ ∫ u, t * f u ^ 2 + q (u + x) ^ 2 / t :=
      integral_mono (hprod.abs.const_mul 2) ((hif.const_mul t).add (hiq.div_const t))
        (fun u => hp (f u) (q (u + x)))
    _ = _ := by
      rw [integral_add (hif.const_mul t) (hiq.div_const t), integral_const_mul,
        integral_div, integral_add_right_eq_self (fun u : ℝ => q u ^ 2) x, integral_sq_eq_autocorr_zero,
        integral_sq_eq_autocorr_zero]

/-- Adding a small-mass source changes every correlation by the same explicit bound. -/
theorem autocorr_add_abs_sub_le_young {f q : ℝ → ℝ} (hf : Continuous f) (hq : Continuous q)
    (hfc : HasCompactSupport f) (hqc : HasCompactSupport q) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |autocorr (fun u => f u + q u) x - autocorr f x| ≤
      autocorr q 0 + t * autocorr f 0 + autocorr q 0 / t := by
  have hif := integrable_mul_shift hf hfc x
  have hiq := integrable_mul_shift hq hqc x
  have hifq : Integrable (fun u => f u * q (u + x)) :=
    (hf.mul (hq.comp (continuous_add_const x))).integrable_of_hasCompactSupport hfc.mul_right
  have hiqf : Integrable (fun u => q u * f (u + x)) :=
    (hq.mul (hf.comp (continuous_add_const x))).integrable_of_hasCompactSupport hqc.mul_right
  have heq : autocorr (fun u => f u + q u) x - autocorr f x =
      autocorr q x + (∫ u, f u * q (u + x)) + ∫ u, q u * f (u + x) := by
    have he : autocorr (fun u => f u + q u) x =
        autocorr f x + autocorr q x + (∫ u, f u * q (u + x)) + ∫ u, q u * f (u + x) := by
      unfold autocorr
      calc
        _ = ∫ u, (f u * f (u + x) + q u * q (u + x)) +
            (f u * q (u + x) + q u * f (u + x)) := by
          apply integral_congr_ae
          filter_upwards [] with u
          ring
        _ = _ := by
          rw [integral_add (f := fun u => f u * f (u + x) + q u * q (u + x))
            (g := fun u => f u * q (u + x) + q u * f (u + x))
            (hif.add hiq) (hifq.add hiqf), integral_add hif hiq, integral_add hifq hiqf]
          ring
    linarith
  have h1 := source_cross_integral_young hf hq hfc hqc ht x
  have h2 := source_cross_integral_young hq hf hqc hfc (one_div_pos.mpr ht) x
  have he2 : 1 / t * autocorr q 0 + autocorr f 0 / (1 / t) =
      t * autocorr f 0 + autocorr q 0 / t := by field_simp; ring
  rw [he2] at h2
  rw [heq]
  have hh := abs_autocorr_le_zero hqc hq x
  have ha := abs_add_le (autocorr q x + ∫ u, f u * q (u + x)) (∫ u, q u * f (u + x))
  have hb := abs_add_le (autocorr q x) (∫ u, f u * q (u + x))
  linarith

/-- A disjoint small perturbation has a global normalized correlation modulus. -/
theorem normalized_autocorr_add_small_mass_le {f q : ℝ → ℝ}
    (hf : Continuous f) (hq : Continuous q) (hfc : HasCompactSupport f) (hqc : HasCompactSupport q)
    (hR : 0 < autocorr f 0) (hcross : ∀ u, f u * q u = 0)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hm : autocorr q 0 ≤ t ^ 2) (x : ℝ) :
    |autocorr (fun u => f u + q u) x / autocorr (fun u => f u + q u) 0 -
      autocorr f x / autocorr f 0| ≤ t * (autocorr f 0 + 3) / autocorr f 0 := by
  have hr : 0 ≤ autocorr q 0 := autocorr_zero_nonneg q
  have hsum : 0 < autocorr f 0 + autocorr q 0 := add_pos_of_pos_of_nonneg hR hr
  have hmass : autocorr (fun u => f u + q u) 0 = autocorr f 0 + autocorr q 0 := by
    apply autocorr_add_of_cross_zero hf hq hfc hqc 0
    intro u
    simpa only [add_zero, mul_comm] using And.intro (hcross u) (hcross u)
  have hraw := autocorr_add_abs_sub_le_young hf hq hfc hqc ht x
  have hnorm : |autocorr f x / autocorr f 0| ≤ 1 := by
    rw [abs_div, abs_of_pos hR]
    exact (div_le_one hR).mpr (abs_autocorr_le_zero hfc hf x)
  have hrt : autocorr q 0 ≤ t := by nlinarith
  have hdiv : autocorr q 0 / t ≤ t := (div_le_iff₀ ht).mpr (by nlinarith only [hm])
  rw [hmass]
  have heq : autocorr (fun u => f u + q u) x / (autocorr f 0 + autocorr q 0) -
      autocorr f x / autocorr f 0 =
      (autocorr (fun u => f u + q u) x - autocorr f x) / (autocorr f 0 + autocorr q 0) -
      (autocorr f x / autocorr f 0) * (autocorr q 0 / (autocorr f 0 + autocorr q 0)) := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |(autocorr (fun u => f u + q u) x - autocorr f x) /
          (autocorr f 0 + autocorr q 0)| +
        |(autocorr f x / autocorr f 0) *
          (autocorr q 0 / (autocorr f 0 + autocorr q 0))| := abs_sub _ _
    _ ≤ (autocorr q 0 + t * autocorr f 0 + autocorr q 0 / t) /
          (autocorr f 0 + autocorr q 0) + autocorr q 0 / (autocorr f 0 + autocorr q 0) := by
      rw [abs_div, abs_of_pos hsum, abs_mul, abs_of_nonneg (div_nonneg hr hsum.le)]
      exact add_le_add (div_le_div_of_nonneg_right hraw hsum.le)
        (by simpa using mul_le_mul_of_nonneg_right hnorm (div_nonneg hr hsum.le))
    _ = (2 * autocorr q 0 + t * autocorr f 0 + autocorr q 0 / t) /
        (autocorr f 0 + autocorr q 0) := by ring
    _ ≤ (t * (autocorr f 0 + 3)) / (autocorr f 0 + autocorr q 0) :=
      div_le_div_of_nonneg_right (by nlinarith) hsum.le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hR (by linarith)

/-- One of two signs retains at least the sum of energies, with a factor-two upper bound. -/
theorem exists_signed_source_energy_between {f q : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hq : ContDiff ℝ 2 q)
    (hfc : HasCompactSupport f) (hqc : HasCompactSupport q) :
    ∃ s : ℝ, s ^ 2 = 1 ∧
      biScaleLevyEnergy f + biScaleLevyEnergy q ≤ biScaleLevyEnergy (fun u => f u + s * q u) ∧
      biScaleLevyEnergy (fun u => f u + s * q u) ≤ 2 * (biScaleLevyEnergy f + biScaleLevyEnergy q) := by
  have hp := biScaleLevyEnergy_source_parallelogram hf hq hfc hqc
  have hnplus := biScaleLevyEnergy_nonneg (hfc.add hqc) (hf.continuous.add hq.continuous)
  have hnminus := biScaleLevyEnergy_nonneg (hfc.sub hqc) (hf.continuous.sub hq.continuous)
  change 0 ≤ biScaleLevyEnergy (fun u => f u + q u) at hnplus
  change 0 ≤ biScaleLevyEnergy (fun u => f u - q u) at hnminus
  by_cases h : biScaleLevyEnergy f + biScaleLevyEnergy q ≤ biScaleLevyEnergy (fun u => f u + q u)
  · refine ⟨1, by norm_num, ?_, ?_⟩ <;> simp only [one_mul] <;> linarith
  · refine ⟨-1, by norm_num, ?_, ?_⟩ <;> simp only [neg_one_mul, ← sub_eq_add_neg] <;> linarith

end

end GaloisForLFunctions.BiScaleUncertainty
