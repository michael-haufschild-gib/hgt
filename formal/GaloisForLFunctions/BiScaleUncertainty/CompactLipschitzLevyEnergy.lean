import GaloisForLFunctions.BiScaleUncertainty.LogarithmicCompressionEnergy
import GaloisForLFunctions.BiScaleUncertainty.FiniteSourceEnergyScalarization
import GaloisForLFunctions.BiScaleUncertainty.SignedDyadicCollarPartition

/-! Literal jump-energy admission and estimates for compact Lipschitz sources. -/

open MeasureTheory Set
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

theorem autocorr_increment_le_lipschitz (f : C_c(ℝ, ℝ)) {K : ℝ}
    (hK : ∀ u v, |f u-f v| ≤ K*|u-v|) (x : ℝ) :
    autocorr f 0-autocorr f x ≤ K*(∫ u, |f u|)*|x| := by
  have hia : Integrable (fun u => |f u|) :=
    (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).abs
  have hi0 : Integrable (fun u => f u*f u) := by
    simpa using integrable_mul_shift (g := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport 0
  have hix := integrable_mul_shift (g := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport x
  have hi : Integrable (fun u => f u*(f u-f (u+x))) := by
    refine (hi0.sub hix).congr ?_
    filter_upwards [] with u
    dsimp only [Pi.sub_apply]
    ring
  have hid : autocorr f 0-autocorr f x = ∫ u, f u*(f u-f (u+x)) := by
    unfold autocorr
    simp only [add_zero]
    rw [← integral_sub hi0 hix]
    apply integral_congr_ae
    filter_upwards [] with u
    ring
  rw [hid]
  calc
    _ ≤ |∫ u, f u*(f u-f (u+x))| := le_abs_self _
    _ ≤ ∫ u, |f u*(f u-f (u+x))| := abs_integral_le_integral_abs
    _ ≤ ∫ u, |f u| * (K*|x|) := by
      refine integral_mono hi.abs (hia.mul_const _) (fun u => ?_)
      rw [abs_mul]
      have hb := hK u (u+x)
      rw [show u-(u+x) = -x by ring, abs_neg] at hb
      exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by rw [integral_mul_const]; ring

theorem integrableOn_levy_of_increment_bound (f : C_c(ℝ, ℝ)) {M : ℝ}
    (hbound : ∀ x, autocorr f 0-autocorr f x ≤ M*|x|) :
    IntegrableOn (fun x => (autocorr f 0-autocorr f x)*archLevySinhWeight x) (Ioi 0) := by
  have hc := continuous_autocorr_compact f
  have hm : AEStronglyMeasurable
      (fun x => (autocorr f 0-autocorr f x)*archLevySinhWeight x)
      (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    exact (continuousOn_const.sub hc.continuousOn).mul
      ((Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn.div
        Real.continuous_sinh.continuousOn
        (fun x hx => (Real.sinh_pos_iff.mpr hx).ne'))
  refine (integrableOn_mul_archLevySinhWeight.const_mul M).mono' hm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hn := autocorr_sub_nonneg f.hasCompactSupport f.continuous x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hn (archLevySinhWeight_pos hx).le)]
  calc
    _ ≤ (M*|x|)*archLevySinhWeight x :=
      mul_le_mul_of_nonneg_right (hbound x) (archLevySinhWeight_pos hx).le
    _ = M*(x*archLevySinhWeight x) := by rw [abs_of_pos hx]; ring

theorem integrableOn_levy_of_lipschitz (f : C_c(ℝ, ℝ)) {K : ℝ}
    (hK : ∀ u v, |f u-f v| ≤ K*|u-v|) :
    IntegrableOn (fun x => (autocorr f 0-autocorr f x)*archLevySinhWeight x) (Ioi 0) :=
  integrableOn_levy_of_increment_bound f (autocorr_increment_le_lipschitz f hK)

theorem levyEnergy_le_linear_log_tail (f : C_c(ℝ, ℝ)) {M a K : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x, autocorr f 0-autocorr f x ≤ M*|x|)
    (ha : 0 < a) (ha1 : a ≤ 1) (hK : 0 ≤ K)
    (htail : ∀ x, a < x → autocorr f 0-autocorr f x ≤ K) :
    biScaleLevyEnergy f ≤ 3*M*a+K*(Real.log (6/a)+Real.pi) := by
  let F := fun x => (autocorr f 0-autocorr f x)*archLevySinhWeight x
  have hi := integrableOn_levy_of_increment_bound f hbound
  have hi0 : IntegrableOn F (Ioc 0 a) := hi.mono_set fun _ hx => hx.1
  have hia : IntegrableOn F (Ioi a) := hi.mono_set fun _ hx => ha.trans hx
  have hnear : (∫ x in Ioc 0 a, F x) ≤ 3*M*a := by
    calc
      _ ≤ ∫ x in Ioc 0 a, 3*M := by
        apply setIntegral_mono_on hi0 (integrableOn_const (by simp)) measurableSet_Ioc
        intro x hx
        have hx1 : x ≤ 1 := hx.2.trans ha1
        have hw : x*archLevySinhWeight x ≤ 3 := by
          calc
            _ ≤ (2*x+1)*Real.exp (-(1/2*x)) := mul_archLevySinhWeight_le hx.1
            _ ≤ (2*x+1)*1 := mul_le_mul_of_nonneg_left
              (Real.exp_le_one_iff.mpr (by linarith [hx.1])) (by linarith [hx.1])
            _ ≤ 3 := by linarith
        calc
          F x ≤ (M*x)*archLevySinhWeight x := by
            apply mul_le_mul_of_nonneg_right _ (archLevySinhWeight_pos hx.1).le
            simpa only [abs_of_pos hx.1] using hbound x
          _ = M*(x*archLevySinhWeight x) := by ring
          _ ≤ M*3 := mul_le_mul_of_nonneg_left hw hM
          _ = _ := by ring
      _ = _ := by
        rw [← intervalIntegral.integral_of_le ha.le, intervalIntegral.integral_const]
        simp
        ring
  have hfar : (∫ x in Ioi a, F x) ≤ K*(Real.log (6/a)+Real.pi) := by
    calc
      _ ≤ ∫ x in Ioi a, K*archLevySinhWeight x := by
        apply setIntegral_mono_on hia
          ((integrableOn_archLevySinhWeight_Ioi ha).const_mul _) measurableSet_Ioi
        intro x hx
        exact mul_le_mul_of_nonneg_right (htail x hx) (archLevySinhWeight_pos (ha.trans hx)).le
      _ = K*∫ x in Ioi a, archLevySinhWeight x := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (integral_archLevySinhWeight_Ioi_le ha ha1) hK
  have hsplit : biScaleLevyEnergy f = (∫ x in Ioc 0 a, F x)+∫ x in Ioi a, F x := by
    unfold biScaleLevyEnergy
    rw [← Ioc_union_Ioi_eq_Ioi ha.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hi0 hia
  rw [hsplit]
  exact add_le_add hnear hfar

/-- The parallelogram law only needs the four literal integral admissions. -/
theorem levyEnergy_parallelogram_admitted (f g : C_c(ℝ, ℝ))
    (hf : IntegrableOn (fun x => (autocorr f 0-autocorr f x)*archLevySinhWeight x) (Ioi 0))
    (hg : IntegrableOn (fun x => (autocorr g 0-autocorr g x)*archLevySinhWeight x) (Ioi 0))
    (hp : IntegrableOn (fun x => (autocorr (f+g) 0-autocorr (f+g) x)*archLevySinhWeight x) (Ioi 0))
    (hm : IntegrableOn (fun x => (autocorr (f-g) 0-autocorr (f-g) x)*archLevySinhWeight x) (Ioi 0)) :
    biScaleLevyEnergy (f+g)+biScaleLevyEnergy (f-g) =
      2*(biScaleLevyEnergy f+biScaleLevyEnergy g) := by
  unfold biScaleLevyEnergy
  rw [← integral_add hp hm, ← integral_add hf hg, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have h0 := autocorr_source_parallelogram f.continuous g.continuous
    f.hasCompactSupport g.hasCompactSupport 0
  have hx := autocorr_source_parallelogram f.continuous g.continuous
    f.hasCompactSupport g.hasCompactSupport x
  change (autocorr (fun u => f u+g u) 0-autocorr (fun u => f u+g u) x)*_+
    (autocorr (fun u => f u-g u) 0-autocorr (fun u => f u-g u) x)*_ = _
  linear_combination (archLevySinhWeight x)*h0-(archLevySinhWeight x)*hx

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
