import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeFourierEnergyBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Absolute Mellin admission of the complete original Fourier coefficient norm mass. -/
open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMCuspProjection
open D4BMAngularSeries D4BMGlobalAngularResponse D4BMModularCore D4BMJointSource
noncomputable section

/-- Each original Fourier--Bessel amplitude is continuous at every positive height. -/
theorem amplitude_continuousOn (u : ℂ) (N : ℕ) :
    ContinuousOn (fun y => amplitude u y N) (Ioi (0:ℝ)) := by
  intro y hy
  have ht : ContinuousAt (fun t : ℝ => term u u (1/2) 0 false N ![0,t]) y :=
    (term_hasFDerivAt u u (1/2) 0 false N ![0,y] hy).continuousAt.comp
      (f := fun t : ℝ => (![0,t] : Fin 2 → ℝ)) (x := y)
    (show ContinuousAt (fun t : ℝ => (![0,t] : Fin 2 → ℝ)) y by fun_prop)
  have he : (fun t : ℝ => term u u (1/2) 0 false N ![0,t]) = fun t => amplitude u t N := by
    funext t
    simp [term,amplitude,d4BMCompletedEisensteinFourierPhase]
  rw [he] at ht
  exact ht.continuousWithinAt

/-- Countable summation preserves measurability of the actual positive coefficient mass. -/
theorem amplitudeMass_aestronglyMeasurable (u : ℂ) {S : Set ℝ}
    (hS : MeasurableSet S) (hs : S ⊆ Ioi (0:ℝ)) :
    AEStronglyMeasurable (amplitudeMass u) (volume.restrict S) := by
  exact (AEMeasurable.tsum (fun N =>
    (((amplitude_continuousOn u N).mono hs).norm.pow 2).aestronglyMeasurable hS |>.aemeasurable)).aestronglyMeasurable

private theorem weighted_mass_measurable (u : ℂ) (r : ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) (hs : S ⊆ Ioi (0:ℝ)) :
    AEStronglyMeasurable (fun y : ℝ => y^(r-2)*amplitudeMass u y) (volume.restrict S) := by
  have hc : ContinuousOn (fun y : ℝ => y^(r-2)) S := by
    intro y hy
    exact (Real.contDiffAt_rpow_const_of_ne (ne_of_gt (hs hy)) (n := 0)).continuousAt.continuousWithinAt
  exact (hc.aestronglyMeasurable hS).mul (amplitudeMass_aestronglyMeasurable u hS hs)

/-- The native coefficient norm mass is Mellin-integrable down to height zero. -/
theorem nativeAmplitudeMass_lower_integrable (q : XiZeroCopy) (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun y : ℝ => y^(r-2)*amplitudeMass (center q) y) (Ioc (0:ℝ) 1) := by
  obtain ⟨A,B,hA,hB,hb⟩ := nativeAmplitudeMass_bound q
  have hg0 : IntegrableOn (fun y : ℝ => y^(r-2)) (Ioc (0:ℝ) 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < r-2) (a := (0:ℝ)) (b := (1:ℝ))).1
  have hg1 : IntegrableOn (fun y : ℝ => y^r) (Ioc (0:ℝ) 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < r) (a := (0:ℝ)) (b := (1:ℝ))).1
  have hg2 : IntegrableOn (fun y : ℝ => y^(r-3)) (Ioc (0:ℝ) 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < r-3) (a := (0:ℝ)) (b := (1:ℝ))).1
  apply ((hg0.const_mul A).add ((hg1.add (hg2.const_mul (cuspReflectionNorm 2))).const_mul B)).mono'
    (weighted_mass_measurable _ _ measurableSet_Ioc (fun _ hy => hy.1))
  apply ae_restrict_of_forall_mem measurableSet_Ioc
  intro y hy
  have he2 : y^(r-2)*y^2 = y^r := by
    rw [← Real.rpow_two,← Real.rpow_add hy.1]
    congr 1
    ring
  have he3 : y^(r-2)*y^(-1:ℝ) = y^(r-3) := by
    rw [← Real.rpow_add hy.1]
    congr 1
    ring
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hy.1.le _) (amplitudeMass_nonneg _ _))]
  calc
    _ ≤ y^(r-2)*(A+B*(y^2+cuspReflectionNorm 2*y^(-1:ℝ))) :=
      mul_le_mul_of_nonneg_left (hb y hy.1) (Real.rpow_nonneg hy.1.le _)
    _ = A*y^(r-2)+B*(y^r+cuspReflectionNorm 2*y^(r-3)) := by
      calc
        _ = A*y^(r-2)+B*(y^(r-2)*y^2+cuspReflectionNorm 2*(y^(r-2)*y^(-1:ℝ))) := by ring
        _ = _ := by rw [he2,he3]

/-- At the upper height end every Mellin weight is admitted for the full coefficient mass. -/
theorem amplitudeMass_upper_integrable (u : ℂ) (r : ℝ) :
    IntegrableOn (fun y : ℝ => y^(r-2)*amplitudeMass u y) (Ioi (1:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := amplitudeMass_weighted_bounded u r
  have hg : IntegrableOn (fun y : ℝ => y^(-2:ℝ)) (Ioi (1:ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) (by norm_num : (0:ℝ)<1)
  apply (hg.const_mul C).mono'
    (weighted_mass_measurable _ _ measurableSet_Ioi (fun _ hy => lt_trans (by norm_num : (0:ℝ)<1) hy))
  apply ae_restrict_of_forall_mem measurableSet_Ioi
  intro y hy
  have hy0 : 0 < y := lt_trans (by norm_num : (0:ℝ)<1) hy
  have he : y^(r-2) = y^(-2:ℝ)*y^r := by
    rw [← Real.rpow_add hy0]
    congr 1
    ring
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hy0.le _) (amplitudeMass_nonneg _ _)),he,mul_assoc]
  exact (mul_le_mul_of_nonneg_left (hb y hy.le) (Real.rpow_nonneg hy0.le _)).trans_eq (mul_comm _ _)

/-- The entire native coefficient norm mass has an absolutely admitted Mellin integral. -/
theorem nativeAmplitudeMass_mellin_integrable (q : XiZeroCopy) (r : ℝ) (hr : 2 < r) :
    IntegrableOn (fun y : ℝ => y^(r-2)*amplitudeMass (center q) y) (Ioi (0:ℝ)) := by
  apply ((nativeAmplitudeMass_lower_integrable q r hr).union
    (amplitudeMass_upper_integrable (center q) r)).mono_set
  intro y hy
  by_cases h : y ≤ 1
  · exact Or.inl ⟨hy,h⟩
  · exact Or.inr (lt_of_not_ge h)

end
end RHTower.D4BMCuspProjection
