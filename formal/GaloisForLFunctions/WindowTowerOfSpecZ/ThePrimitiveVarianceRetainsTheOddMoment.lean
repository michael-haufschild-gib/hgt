import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaRemainderPaysAUniformReserve
import GaloisForLFunctions.HTGeometry.CirclePoincareWirtinger

/-!
# Primitive variance and the first odd moment

Periodic Wirtinger bounds the variance of the compact primitive. Its mean is
minus the first position moment, so the primitive mass and the linear part of
the sinh pole can be charged to that same moment without discarding the mean.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.WeilMarkovPole
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open LatticeSectionTheory SpacingScaleHarmonicAnalysis

private theorem unit_source_vanish {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    ∀ x, x ∉ Ioo (-(1 / 2 : ℝ)) (1 / 2) → F x = 0 := by
  have hz : Ioi (1 / 2 : ℝ) ⊆ {x | F x = 0} := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport fun h => not_le_of_gt hx (hs h).2
  have hzr : ∀ x, (1 / 2 : ℝ) ≤ x → F x = 0 := by
    have h := closure_minimal hz (isClosed_eq hF continuous_const)
    rw [closure_Ioi] at h
    exact fun x hx => h hx
  intro x hx
  by_cases hr : (1 / 2 : ℝ) ≤ x
  · exact hzr x hr
  · have hl : x ≤ -(1 / 2 : ℝ) := by
      by_contra h
      exact hx ⟨lt_of_not_ge h, lt_of_not_ge hr⟩
    have h := hzr (-x) (by linarith only [hl])
    rw [ho] at h
    exact neg_eq_zero.mp h

private theorem unit_interval_eq_integral {f : ℝ → ℝ}
    (hz : ∀ x, x ∉ Ioo (-(1 / 2 : ℝ)) (1 / 2) → f x = 0) :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2), f x) = ∫ x, f x := by
  rw [intervalIntegral.integral_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => hz x (fun hi => hx ⟨hi.1, hi.2.le⟩))

/-- The odd source's primitive vanishes at and beyond the original unit endpoints. -/
theorem unit_odd_primitive_vanish {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    ∀ x, x ∉ Ioo (-(1 / 2 : ℝ)) (1 / 2) → unitSourcePrimitive F x = 0 := by
  have hz := unit_source_vanish hF hs ho
  have hleft : (∫ x in (-1 : ℝ)..(-(1 / 2 : ℝ)), F x) = 0 := by
    have he : (∫ x in (-1 : ℝ)..(-(1 / 2 : ℝ)), F x) =
        ∫ _x in (-1 : ℝ)..(-(1 / 2 : ℝ)), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ -(1 / 2 : ℝ))] at hx
      exact hz x (fun hi => not_lt_of_ge hx.2 hi.1)
    rw [he, intervalIntegral.integral_zero]
  have hbase (x : ℝ) : unitSourcePrimitive F x = ∫ y in (-(1 / 2 : ℝ))..x, F y := by
    have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hF.intervalIntegrable (-1) (-(1 / 2 : ℝ)))
      (hF.intervalIntegrable (-(1 / 2 : ℝ)) x)
    rw [hleft, zero_add] at h
    exact h.symm
  have hm : (∫ x, F x) = 0 := by
    have h := integral_neg_eq_self F volume
    rw [integral_congr_ae (Eventually.of_forall ho), integral_neg] at h
    linarith only [h]
  have hmi : (∫ x in (-(1 / 2 : ℝ))..(1 / 2), F x) = 0 := by
    rw [unit_interval_eq_integral hz, hm]
  intro x hx
  rw [hbase]
  exact HTGeometry.primitive_eq_zero_outside hF hz hmi x hx

/-- The primitive's mean is retained in the sharp unit-period variance bound. -/
theorem unit_odd_primitive_variance_le {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    (∫ x, unitSourcePrimitive F x ^ 2) - (∫ x, x * F x) ^ 2 ≤
      (∫ x, F x ^ 2) / (4 * Real.pi ^ 2) := by
  have hz := unit_source_vanish hF hs ho
  have hPz := unit_odd_primitive_vanish hF hs ho
  have hd (x : ℝ) : HasDerivAt (unitSourcePrimitive F) (F x) x :=
    (hF.integral_hasStrictDerivAt (-1) x).hasDerivAt
  have h := HTGeometry.wirtinger_intervalIntegral
    (a := -(1 / 2 : ℝ)) (b := 1 / 2) (by norm_num)
    (f := fun x => (unitSourcePrimitive F x : ℂ)) (f' := fun x => (F x : ℂ))
    (fun x _ => (hd x).ofReal_comp) (Complex.continuous_ofReal.comp hF).continuousOn
    (by rw [hPz (1 / 2) (by simp), hPz (-(1 / 2)) (by simp)])
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  rw [intervalIntegral.integral_ofReal] at h
  norm_num only [sub_neg_eq_add, add_halves, inv_one, one_mul, one_smul,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  rw [unit_interval_eq_integral (fun x hx => by rw [hPz x hx]; norm_num),
    unit_interval_eq_integral hPz,
    unit_interval_eq_integral (fun x hx => by rw [hz x hx]; norm_num)] at h
  rw [unit_odd_position_eq_primitive_integral hF hs ho, neg_sq]
  convert h using 1
  ring

/-- The nonlinear sinh remainder has a small squared pairing on the unit window. -/
theorem unit_sinhPairing_sub_position_square_le {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    (sinhPairing F - ∫ x, x * F x) ^ 2 ≤ (∫ x, F x ^ 2) / 241920 := by
  have hcs : HasCompactSupport F := HasCompactSupport.intro isCompact_Icc
    (fun x hx => image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)))
  let R : ℝ → ℝ := (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
    (fun x => 2 * Real.sinh (x / 2) - x)
  have hc : Continuous (fun x : ℝ => 2 * Real.sinh (x / 2) - x) := by fun_prop
  have hRm : AEStronglyMeasurable R := hc.aestronglyMeasurable.indicator measurableSet_Icc
  have hRsq : (fun x => R x ^ 2) =
      (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun x => (2 * Real.sinh (x / 2) - x) ^ 2) := by
    funext x
    by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
    · simp only [R, Set.indicator_of_mem hx]
    · simp only [R, Set.indicator_of_notMem hx, zero_pow two_ne_zero]
  have hRi : Integrable (fun x => R x ^ 2) := by
    rw [hRsq]
    exact (integrable_indicator_iff measurableSet_Icc).mpr (hc.pow 2).integrableOn_Icc
  have hFi : Integrable (fun x => F x ^ 2) := (hF.pow 2).integrable_of_hasCompactSupport
    (_root_.RHTower.CHMDPolar.hasCompactSupport_sq hcs)
  have hCS := HTGeometry.sq_integral_mul_le hF.aestronglyMeasurable hRm hFi hRi
  have hRbound : (∫ x, R x ^ 2) ≤ (1 / 241920 : ℝ) := by
    rw [hRsq, integral_indicator measurableSet_Icc]
    have h6 : (∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), x ^ 6) = (1 / 448 : ℝ) := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2),
        integral_pow]
      norm_num
    have hi6 : IntegrableOn (fun x : ℝ => x ^ 6)
        (Icc (-(1 / 2 : ℝ)) (1 / 2)) := (continuous_pow 6).integrableOn_Icc
    have hmono := setIntegral_mono_on (s := Icc (-(1 / 2 : ℝ)) (1 / 2))
      (f := fun x => (2 * Real.sinh (x / 2) - x) ^ 2) (g := fun x => x ^ 6 / 540)
      (hc.pow 2).integrableOn_Icc (hi6.div_const 540)
      measurableSet_Icc (fun _ hx => unit_sinh_linear_residual_square_le (abs_le.mpr hx))
    rw [integral_div, h6] at hmono
    norm_num at hmono
    exact hmono
  have hpoint : (fun x => F x * R x) = (fun x => F x * (2 * Real.sinh (x / 2) - x)) := by
    funext x
    by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
    · simp only [R, Set.indicator_of_mem hx]
    · have hz : F x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
      rw [hz, zero_mul, zero_mul]
  have hI1 : Integrable (fun x => F x * (2 * Real.sinh (x / 2))) :=
    (hF.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
  have hIx : Integrable (fun x => F x * x) :=
    (hF.mul continuous_id).integrable_of_hasCompactSupport hcs.mul_right
  have hsplit : (∫ x, F x * R x) = sinhPairing F - ∫ x, x * F x := by
    rw [hpoint]
    simp_rw [mul_sub]
    rw [integral_sub hI1 hIx]
    change sinhPairing F - (∫ x, F x * x) = _
    simp only [mul_comm]
  rw [hsplit] at hCS
  have hE : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg (F x)
  have hm := mul_le_mul_of_nonneg_left hRbound hE
  simpa only [div_eq_mul_inv, one_mul] using hCS.trans hm

/-- A single first moment pays the sinh pole, with the residual charged to the mass. -/
theorem unit_sinhPairing_square_le_position {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    sinhPairing F ^ 2 / 2 ≤ (97 / 192 : ℝ) * (∫ x, x * F x) ^ 2 +
      (97 / 483840 : ℝ) * (∫ x, F x ^ 2) := by
  have h := unit_sinhPairing_sub_position_square_le hF hs
  have hsq := sq_nonneg (96 * (sinhPairing F - ∫ x, x * F x) - ∫ x, x * F x)
  nlinarith only [h, hsq]

/-- Primitive variance and the pole leave one first-moment charge in the complete form. -/
theorem weilQuad_ge_logarithmic_first_moment {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    (∫ t in Ioc (0 : ℝ) 1, ((∫ x, F x ^ 2) - autocorr F t) / t) -
      (Real.eulerMascheroniConstant + Real.log Real.pi + Real.log 2 + 1 / 192 +
        1 / (96 * Real.pi ^ 2) + 97 / 483840) * (∫ x, F x ^ 2) -
      (39 / 64 : ℝ) * (∫ x, x * F x) ^ 2 -
      2 * (Real.log 2 / Real.sqrt 2) * autocorr F (Real.log 2) ≤ weilQuad F := by
  have h := weilQuad_ge_retainedOddGamma_add_reserve hF hs ho
  have hv := unit_odd_primitive_variance_le hF.continuous hs ho
  have hp := unit_sinhPairing_square_le_position hF.continuous hs
  have hM := unit_odd_jump_first_moment hF.continuous hs ho
  simp only [autocorr_zero_eq] at hM
  unfold retainedOddGammaLowerForm at h
  rw [hM] at h
  have he : (∫ x, F x ^ 2) / (4 * Real.pi ^ 2) / 24 =
      (1 / (96 * Real.pi ^ 2)) * (∫ x, F x ^ 2) := by ring
  linarith only [h, hp, hv, he]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.unit_odd_primitive_variance_le
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.unit_sinhPairing_sub_position_square_le
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.weilQuad_ge_logarithmic_first_moment
