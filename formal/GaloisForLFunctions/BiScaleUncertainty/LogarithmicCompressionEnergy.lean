import GaloisForLFunctions.BiScaleUncertainty.BroadSpectralCostRealization
import GaloisForLFunctions.BiScaleUncertainty.LogarithmicIncrementEnergy
import GaloisForLFunctions.RHTower.WeilLevyCoshPlasticCrossover

/-!
# Logarithmic upper cost of compressing a smooth source

The singular weight has a logarithmic tail integral. Splitting at the compressed
correlation support gives an upper bound with coefficient one. A radius-free estimate
with coefficient two also holds. The seed's regularity supplies every increment bound.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

theorem integrableOn_archLevySinhWeight_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn archLevySinhWeight (Ioi a) := by
  refine IntegrableOn.congr_fun
    ((RHTower.WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi ha).const_mul 2) ?_ measurableSet_Ioi
  intro x hx
  exact (exp_half_div_sinh_eq (ha.trans hx)).symm

theorem integral_archLevySinhWeight_Ioi {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi a, archLevySinhWeight x) =
      Real.log ((1 + Real.exp (-a / 2)) / (1 - Real.exp (-a / 2))) +
        2 * Real.arctan (Real.exp (-a / 2)) := by
  calc
    _ = ∫ x in Ioi a, 2 * RHTower.archLevyDensity x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact exp_half_div_sinh_eq (ha.trans hx)
    _ = _ := by
      rw [integral_const_mul, RHTower.WeilLevyCoshCrossover.integral_archLevyDensity_Ioi ha,
        RHTower.WeilLevyPoleGauss.archLevyAntideriv_eq_log_div ha]
      ring

theorem integral_archLevySinhWeight_Ioi_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ x in Ioi a, archLevySinhWeight x) ≤ Real.log (6 / a) + Real.pi := by
  have he : Real.exp (-a / 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hd : 0 < 1 - Real.exp (-a / 2) := by linarith
  have hb := RHTower.one_sub_exp_neg_two_mul_ge (show 0 < a / 4 by positivity)
  have heq : 2 * (a / 4) / (1 + 2 * (a / 4)) = a / (2 + a) := by field_simp; ring
  rw [heq, show -2 * (a / 4) = -a / 2 by ring] at hb
  have hthird : a / 3 ≤ 1 - Real.exp (-a / 2) := by
    calc
      a / 3 ≤ a / (2 + a) := div_le_div_of_nonneg_left ha.le (by positivity) (by linarith)
      _ ≤ _ := hb
  have hr : (1 + Real.exp (-a / 2)) / (1 - Real.exp (-a / 2)) ≤ 6 / a := by
    apply (div_le_iff₀ hd).mpr
    have hm := mul_le_mul_of_nonneg_left hthird (show 0 ≤ 6 / a by positivity)
    have hcancel : (6 / a) * (a / 3) = 2 := by field_simp; ring
    rw [hcancel] at hm
    linarith
  have hl := Real.log_le_log (show 0 < (1 + Real.exp (-a / 2)) /
    (1 - Real.exp (-a / 2)) by positivity) hr
  rw [integral_archLevySinhWeight_Ioi ha]
  linarith [Real.arctan_lt_pi_div_two (Real.exp (-a / 2))]

theorem biScaleLevyEnergy_le_linear_log_tail {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {M a K : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x, autocorr f 0 - autocorr f x ≤ M * |x|)
    (ha : 0 < a) (ha1 : a ≤ 1) (hK : 0 ≤ K)
    (htailbound : ∀ x, a < x → autocorr f 0 - autocorr f x ≤ K) :
    biScaleLevyEnergy f ≤ 3 * M * a + K * (Real.log (6 / a) + Real.pi) := by
  let F := fun x => (autocorr f 0 - autocorr f x) * archLevySinhWeight x
  have hi := integrableOn_biScaleLevyIntegrand hf hfc
  have hi0 : IntegrableOn F (Ioc 0 a) := hi.mono_set fun x hx => hx.1
  have hia : IntegrableOn F (Ioi a) := hi.mono_set fun x hx => ha.trans hx
  have hnear : (∫ x in Ioc 0 a, F x) ≤ 3 * M * a := by
    calc
      _ ≤ ∫ x in Ioc 0 a, 3 * M := by
        apply setIntegral_mono_on hi0 (integrableOn_const (by simp)) measurableSet_Ioc
        intro x hx
        have hx1 : x ≤ 1 := hx.2.trans ha1
        have hw : x * archLevySinhWeight x ≤ 3 := by
          calc
            _ ≤ (2 * x + 1) * Real.exp (-(1 / 2 * x)) := mul_archLevySinhWeight_le hx.1
            _ ≤ (2 * x + 1) * 1 := mul_le_mul_of_nonneg_left
              (Real.exp_le_one_iff.mpr (by linarith [hx.1])) (by linarith [hx.1])
            _ ≤ 3 := by linarith
        calc
          F x ≤ (M * x) * archLevySinhWeight x := by
            apply mul_le_mul_of_nonneg_right _ (archLevySinhWeight_pos hx.1).le
            simpa only [abs_of_pos hx.1] using hbound x
          _ = M * (x * archLevySinhWeight x) := by ring
          _ ≤ M * 3 := mul_le_mul_of_nonneg_left hw hM
          _ = _ := by ring
      _ = _ := by rw [← intervalIntegral.integral_of_le ha.le, intervalIntegral.integral_const]; simp; ring
  have htail : (∫ x in Ioi a, F x) ≤
      K * (Real.log (6 / a) + Real.pi) := by
    calc
      _ ≤ ∫ x in Ioi a, K * archLevySinhWeight x := by
        apply setIntegral_mono_on hia ((integrableOn_archLevySinhWeight_Ioi ha).const_mul _) measurableSet_Ioi
        intro x hx
        apply mul_le_mul_of_nonneg_right _ (archLevySinhWeight_pos (ha.trans hx)).le
        exact htailbound x hx
      _ = K * ∫ x in Ioi a, archLevySinhWeight x := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (integral_archLevySinhWeight_Ioi_le ha ha1) hK
  have hsplit : biScaleLevyEnergy f = (∫ x in Ioc 0 a, F x) + ∫ x in Ioi a, F x := by
    unfold biScaleLevyEnergy
    rw [← Ioc_union_Ioi_eq_Ioi ha.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hi0 hia
  rw [hsplit]
  exact add_le_add hnear htail

/-- Compression costs at most twice the logarithm of scale, plus a seed-dependent constant. -/
theorem exists_sourceRescale_logarithmic_energy_bound {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0) :
    ∃ A : ℝ, ∀ L : ℝ, 1 ≤ L →
      normalizedArchEnergy (sourceRescale f L) ≤ A + 2 * Real.log L := by
  obtain ⟨M, hM, hb⟩ := exists_autocorr_increment_linear_bound hf hfc
  refine ⟨3 * M / autocorr f 0 + 2 * (Real.log 6 + Real.pi), ?_⟩
  intro L hL1
  have hL : 0 < L := by linarith
  have hmass : autocorr (sourceRescale f L) 0 = L⁻¹ * autocorr f 0 := by
    simpa only [mul_zero] using autocorr_sourceRescale f hL 0
  have hinc : ∀ x, autocorr (sourceRescale f L) 0 -
      autocorr (sourceRescale f L) x ≤ M * |x| := by
    intro x
    rw [hmass, autocorr_sourceRescale f hL, ← mul_sub]
    calc
      _ ≤ L⁻¹ * (M * |L * x|) := mul_le_mul_of_nonneg_left (hb _) (inv_pos.mpr hL).le
      _ = _ := by rw [abs_mul, abs_of_pos hL]; field_simp
  have hraw := biScaleLevyEnergy_le_linear_log_tail (contDiff_sourceRescale hf L)
    (hasCompactSupport_sourceRescale hfc hL) hM hinc (inv_pos.mpr hL)
    ((inv_le_one₀ hL).mpr hL1)
    (show 0 ≤ 2 * autocorr (sourceRescale f L) 0 by rw [hmass]; positivity)
    (fun x _ => by
      have ht := autocorr_add_nonneg (hasCompactSupport_sourceRescale hfc hL)
        (contDiff_sourceRescale hf L).continuous x
      linarith)
  have hl : Real.log (6 / L⁻¹) = Real.log 6 + Real.log L := by
    rw [div_inv_eq_mul, Real.log_mul (by norm_num) hL.ne']
  unfold normalizedArchEnergy
  rw [hmass] at hraw ⊢
  calc
    _ ≤ (3 * M * L⁻¹ + 2 * (L⁻¹ * autocorr f 0) *
        (Real.log (6 / L⁻¹) + Real.pi)) / (L⁻¹ * autocorr f 0) :=
      div_le_div_of_nonneg_right hraw (by positivity)
    _ = _ := by rw [hl]; field_simp [hL.ne', hR.ne']; ring

/-- Compact correlation support improves the leading compression coefficient from two to one. -/
theorem exists_sourceRescale_logarithmic_energy_bound_of_support {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    {D : ℝ} (hD : 0 < D) (hsupp : ∀ x, D < |x| → autocorr f x = 0) :
    ∃ A : ℝ, ∀ L : ℝ, 0 < L → D ≤ L →
      normalizedArchEnergy (sourceRescale f L) ≤ A + Real.log L := by
  obtain ⟨M, hM, hb⟩ := exists_autocorr_increment_linear_bound hf hfc
  refine ⟨3 * M * D / autocorr f 0 + Real.log (6 / D) + Real.pi, ?_⟩
  intro L hL hDL
  have hmass : autocorr (sourceRescale f L) 0 = L⁻¹ * autocorr f 0 := by
    simpa only [mul_zero] using autocorr_sourceRescale f hL 0
  have hinc : ∀ x, autocorr (sourceRescale f L) 0 -
      autocorr (sourceRescale f L) x ≤ M * |x| := by
    intro x
    rw [hmass, autocorr_sourceRescale f hL, ← mul_sub]
    calc
      _ ≤ L⁻¹ * (M * |L * x|) := mul_le_mul_of_nonneg_left (hb _) (inv_pos.mpr hL).le
      _ = _ := by rw [abs_mul, abs_of_pos hL]; field_simp
  have ha : 0 < D / L := div_pos hD hL
  have ha1 : D / L ≤ 1 := (div_le_iff₀ hL).mpr (by simpa using hDL)
  have htail : ∀ x, D / L < x → autocorr (sourceRescale f L) 0 -
      autocorr (sourceRescale f L) x ≤ autocorr (sourceRescale f L) 0 := by
    intro x hx
    have hx0 : 0 < x := ha.trans hx
    have hz : autocorr f (L * x) = 0 := hsupp _ (by
      rw [abs_of_pos (mul_pos hL hx0)]
      simpa only [mul_comm] using (div_lt_iff₀ hL).mp hx)
    rw [autocorr_sourceRescale f hL x, hz, mul_zero, sub_zero]
  have hraw := biScaleLevyEnergy_le_linear_log_tail (contDiff_sourceRescale hf L)
    (hasCompactSupport_sourceRescale hfc hL) hM hinc ha ha1
    (show 0 ≤ autocorr (sourceRescale f L) 0 by rw [hmass]; positivity) htail
  have hl : Real.log (6 / (D / L)) = Real.log (6 / D) + Real.log L := by
    rw [show (6 : ℝ) / (D / L) = (6 / D) * L by field_simp,
      Real.log_mul (by positivity) hL.ne']
  unfold normalizedArchEnergy
  rw [hmass] at hraw ⊢
  calc
    _ ≤ (3 * M * (D / L) + (L⁻¹ * autocorr f 0) *
        (Real.log (6 / (D / L)) + Real.pi)) / (L⁻¹ * autocorr f 0) :=
      div_le_div_of_nonneg_right hraw (by positivity)
    _ = _ := by rw [hl]; field_simp [hL.ne', hR.ne']; ring

theorem integral_abs_autocorr_sourceRescale (f : ℝ → ℝ) {L : ℝ} (hL : 0 < L) :
    (∫ x, |autocorr (sourceRescale f L) x|) = L⁻¹ * L⁻¹ * ∫ x, |autocorr f x| := by
  simp_rw [autocorr_sourceRescale f hL, abs_mul, abs_of_pos (inv_pos.mpr hL)]
  rw [integral_const_mul]
  have h := Measure.integral_comp_mul_left (fun x => |autocorr f x|) L
  rw [abs_of_pos (inv_pos.mpr hL), smul_eq_mul] at h
  rw [h]
  ring

theorem polarEnergyErrorConstant_sourceRescale (f : ℝ → ℝ) {L : ℝ}
    (hL : 0 < L) (D : ℝ) :
    polarEnergyErrorConstant (sourceRescale f L) D = L⁻¹ * polarEnergyErrorConstant f D := by
  unfold polarEnergyErrorConstant
  rw [integral_abs_autocorr_sourceRescale f hL, autocorr_sourceRescale f hL, mul_zero]
  by_cases hR : autocorr f 0 = 0
  · simp [hR]
  · field_simp [hL.ne']

end

end GaloisForLFunctions.BiScaleUncertainty
