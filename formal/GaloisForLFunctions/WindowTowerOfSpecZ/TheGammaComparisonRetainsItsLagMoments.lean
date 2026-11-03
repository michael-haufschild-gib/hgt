import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.OddAutocorrelationFirstMoment
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.OddAutocorrelationSecondMoment
import GaloisForLFunctions.WindowTowerOfSpecZ.TheCubicMomentPaysTheFrozenOddComplement
import GaloisForLFunctions.HTGeometry.CompactSupportIntegrationByParts

/-!
# Gamma payment with its lag moments retained

The local expansion of the Gamma jump kernel produces two polynomial lag costs.
Keeping these integrals preserves the source-dependent part lost by a uniform
mass estimate, including its coupling to the odd polynomial moments.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.WeilMarkovPole _root_.RHTower.WeilLevyPoleGauss
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open LatticeSectionTheory ArithmeticIncidencePositivity ArithmeticCriticalityTheory
open BiScaleUncertainty SpacingScaleHarmonicAnalysis

private theorem retained_gamma_weight_lower {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    1 / t + 1 / 2 - t / 24 - t ^ 2 / 16 ≤ archLevySinhWeight t := by
  refine le_of_mul_le_mul_left (a := t) ?_ ht
  have h := mul_archLevyDensity_ge_sharp ht ht1
  rw [archLevySinhWeight, exp_half_div_sinh_eq ht]
  have he : t * (1 / t + 1 / 2 - t / 24 - t ^ 2 / 16) =
      2 * (1 / 2 + t / 4 - t ^ 2 / 48 - t ^ 3 / 32) := by
    field_simp [ht.ne']
    ring
  rw [he]
  linarith only [h]

private theorem retained_gamma_tail_lower :
    Real.log 2 + Real.pi / 4 - 1 / 4 + 1 / 96 ≤ archLevyAntideriv 1 := by
  have hlog : Real.log (1 / 4 : ℝ) = -2 * Real.log 2 := by
    rw [show (1 / 4 : ℝ) = (2 ^ (2 : ℕ))⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    norm_num
  have h := archLevyAntideriv_ge_second (y := 1) (by norm_num) (by norm_num)
  rw [hlog] at h
  norm_num at h
  linarith only [h]

/-- Retaining the first two lag moments avoids replacing their Gamma cost by a mass bound. -/
theorem unit_odd_gamma_lag_moments_lower {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    (∫ t in Ioc (0 : ℝ) 1, (autocorr F 0 - autocorr F t) / t) -
      (Real.eulerMascheroniConstant + Real.log Real.pi + Real.log 2) * (∫ x, F x ^ 2) +
      (∫ x, F x ^ 2) / 48 -
      (∫ t in Ioc (0 : ℝ) 1, t * (autocorr F 0 - autocorr F t)) / 24 -
      (∫ t in Ioc (0 : ℝ) 1, t ^ 2 * (autocorr F 0 - autocorr F t)) / 16 ≤
        EF.gammaBracket 0 * (∫ x, F x ^ 2) + biScaleLevyEnergy F := by
  set M := autocorr F 0
  set D := fun t => M - autocorr F t
  set W := fun t => D t * archLevySinhWeight t
  have hc : Continuous (autocorr F) :=
    _root_.RHTower.ArchimedeanExactForm.continuous_autocorr hF hcs
  have hdc : Continuous D := continuous_const.sub hc
  have hd : ∀ t, 0 ≤ D t := fun t => sub_nonneg.mpr
    ((le_abs_self _).trans (abs_autocorr_le_zero hcs hF.continuous t))
  have hi : IntegrableOn W (Ioi (0 : ℝ)) := integrableOn_biScaleLevyIntegrand hF hcs
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioi 0 := fun _ ht => ht.1
  have hsubtail : Ioi (1 : ℝ) ⊆ Ioi 0 := fun t ht =>
    show (0 : ℝ) < t from lt_trans zero_lt_one ht
  have hilog : IntegrableOn (fun t => D t / t) (Ioc (0 : ℝ) 1) := by
    apply (hi.mono_set hsub).mono'
      ((hdc.measurable.div measurable_id).aestronglyMeasurable.restrict)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    change ‖D t / t‖ ≤ W t
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hd t) ht.1.le)]
    have hw := retained_gamma_weight_lower ht.1 ht.2
    have ht2 : t ^ 2 ≤ 1 := by nlinarith only [ht.1, ht.2]
    have hwinv : 1 / t ≤ archLevySinhWeight t := by linarith only [hw, ht.2, ht2]
    simpa only [W, div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hwinv (hd t)
  have hiD : IntegrableOn D (Ioc (0 : ℝ) 1) :=
    hdc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hitD : IntegrableOn (fun t => t * D t) (Ioc (0 : ℝ) 1) :=
    (continuous_id.mul hdc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hit2D : IntegrableOn (fun t => t ^ 2 * D t) (Ioc (0 : ℝ) 1) :=
    ((continuous_pow 2).mul hdc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hiSum : IntegrableOn (fun t => D t / t + D t / 2) (Ioc (0 : ℝ) 1) :=
    hilog.add (hiD.div_const 2)
  have hiSub : IntegrableOn (fun t => D t / t + D t / 2 - t * D t / 24)
      (Ioc (0 : ℝ) 1) := hiSum.sub (hitD.div_const 24)
  have hcomp : (∫ t in Ioc (0 : ℝ) 1,
      D t / t + D t / 2 - t * D t / 24 - t ^ 2 * D t / 16) ≤
      ∫ t in Ioc (0 : ℝ) 1, W t := by
    apply setIntegral_mono_on (hiSub.sub (hit2D.div_const 16))
      (hi.mono_set hsub) measurableSet_Ioc
    intro t ht
    have h := mul_le_mul_of_nonneg_left (retained_gamma_weight_lower ht.1 ht.2) (hd t)
    change D t / t + D t / 2 - t * D t / 24 - t ^ 2 * D t / 16 ≤ W t
    calc _ = D t * (1 / t + 1 / 2 - t / 24 - t ^ 2 / 16) := by ring
      _ ≤ W t := h
  have hzero := odd_autocorr_integral_zero ⟨hF, hcs⟩ hs ho
  norm_num at hzero
  have hD : (∫ t in Ioc (0 : ℝ) 1, D t) = M := by
    change (∫ t in Ioc (0 : ℝ) 1, M - autocorr F t) = M
    rw [integral_sub (f := fun _ : ℝ => M) (g := autocorr F)
      (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self), hzero, sub_zero, setIntegral_const]
    norm_num
  rw [integral_sub hiSub (hit2D.div_const 16), integral_sub hiSum (hitD.div_const 24),
    integral_add hilog (hiD.div_const 2), integral_div, integral_div, integral_div, hD] at hcomp
  have htail : (∫ t in Ioi (1 : ℝ), W t) = 2 * archLevyAntideriv 1 * M := by
    have he : ∀ t ∈ Ioi (1 : ℝ), W t = 2 * archLevyDensity t * M := by
      intro t ht
      dsimp [W, D, M]
      rw [autocorr_eq_zero_of_support (x := t) hs (by norm_num; exact ht), sub_zero,
        archLevySinhWeight, exp_half_div_sinh_eq (lt_trans zero_lt_one ht)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi he, integral_mul_const, integral_const_mul,
      WeilLevyCoshCrossover.integral_archLevyDensity_Ioi (by norm_num : (0 : ℝ) < 1)]
  have hsplit : (∫ t in Ioc (0 : ℝ) 1, W t) +
      (∫ t in Ioi (1 : ℝ), W t) = biScaleLevyEnergy F := by
    rw [← setIntegral_union (s := Ioc (0 : ℝ) 1) (t := Ioi (1 : ℝ))
      (Set.disjoint_left.mpr (fun t ht ht' => not_lt_of_ge ht.2 ht'))
      measurableSet_Ioi (hi.mono_set hsub) (hi.mono_set hsubtail),
      Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
    rfl
  rw [htail] at hsplit
  have hE : 0 ≤ M := by
    change 0 ≤ autocorr F 0
    rw [autocorr_zero_eq]
    exact integral_nonneg fun x => sq_nonneg _
  have htailM := mul_le_mul_of_nonneg_right retained_gamma_tail_lower hE
  have hGamma := congrArg (fun z : ℝ => z * M) neg_gammaBracket_zero_eq
  rw [← autocorr_zero_eq]
  change (∫ t in Ioc (0 : ℝ) 1, D t / t) -
    (Real.eulerMascheroniConstant + Real.log Real.pi + Real.log 2) * M + M / 48 -
    (∫ t in Ioc (0 : ℝ) 1, t * D t) / 24 -
    (∫ t in Ioc (0 : ℝ) 1, t ^ 2 * D t) / 16 ≤ _
  nlinarith only [hcomp, hsplit, htailM, hGamma]


/-- The quadratic lag cost is exactly the square of the first odd position moment. -/
theorem unit_odd_gamma_position_lower {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    (∫ t in Ioc (0 : ℝ) 1, (autocorr F 0 - autocorr F t) / t) -
      (Real.eulerMascheroniConstant + Real.log Real.pi + Real.log 2) * (∫ x, F x ^ 2) -
      (∫ t in Ioc (0 : ℝ) 1, t * (autocorr F 0 - autocorr F t)) / 24 -
      (∫ x, x * F x) ^ 2 / 16 ≤
        EF.gammaBracket 0 * (∫ x, F x ^ 2) + biScaleLevyEnergy F := by
  have h := unit_odd_gamma_lag_moments_lower hF hcs hs ho
  rw [unit_odd_jump_second_moment hF hcs hs ho] at h
  simp only [autocorr_zero_eq] at h ⊢
  linarith only [h]

/-- Exact odd moment cancellation reduces the unit Gamma loss from `5/96` to `7/192`. -/
theorem unit_odd_gamma_jump_second_moment_lower {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    (∫ t in Ioc (0 : ℝ) 1, (autocorr F 0 - autocorr F t) / t) -
      (Real.eulerMascheroniConstant + Real.log Real.pi + Real.log 2 + 7 / 192) *
        (∫ x, F x ^ 2) ≤ EF.gammaBracket 0 * (∫ x, F x ^ 2) + biScaleLevyEnergy F := by
  have h := unit_odd_gamma_lag_moments_lower hF hcs hs ho
  have h1 := odd_jump_first_moment_le ⟨hF, hcs⟩ (by norm_num : (0 : ℝ) < 1 / 2) hs ho
  norm_num at h1
  have h2 := unit_odd_jump_second_moment_le hF hcs hs ho
  simp only [autocorr_zero_eq] at h h1 h2 ⊢
  nlinarith only [h, h1, h2]


private theorem unit_odd_primitive_pairing {F g g' : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g') :
    (∫ x, F x * g x) = -(∫ x, unitSourcePrimitive F x * g' x) := by
  obtain ⟨hP, hPc, hPd⟩ := unit_odd_primitive_regular hF hs ho
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  have hFc : HasCompactSupport F :=
    HasCompactSupport.intro (K := Icc (-(1 / 2 : ℝ)) (1 / 2)) isCompact_Icc
      (fun x hx => image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)))
  have hd (x : ℝ) : HasDerivAt (fun x => unitSourcePrimitive F x * g x)
      (F x * g x + unitSourcePrimitive F x * g' x) x := by
    have h := (hP.differentiable one_ne_zero x).hasDerivAt
    rw [hPd] at h
    exact h.mul (hg x)
  have hzero := HTGeometry.integral_deriv_eq_zero_of_hasCompactSupport hd
    ((hF.mul hgc).add (hP.continuous.mul hg')) hPc.mul_right
  have hi1 : Integrable (fun x => F x * g x) :=
    (hF.mul hgc).integrable_of_hasCompactSupport hFc.mul_right
  have hi2 : Integrable (fun x => unitSourcePrimitive F x * g' x) :=
    (hP.continuous.mul hg').integrable_of_hasCompactSupport hPc.mul_right
  rw [integral_add hi1 hi2] at hzero
  linarith only [hzero]

/-- The first position moment is minus the integral of the compact primitive. -/
theorem unit_odd_position_eq_primitive_integral {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    (∫ x, x * F x) = -(∫ x, unitSourcePrimitive F x) := by
  have h := unit_odd_primitive_pairing hF hs ho
    (g := fun x : ℝ => x) (g' := fun _ : ℝ => 1)
    (fun x => by simpa only [id] using hasDerivAt_id x) continuous_const
  simpa only [mul_one, mul_comm] using h

/-- Both polynomial lag losses are masses or moments of the source's compact primitive. -/
theorem unit_odd_gamma_primitive_lower {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    (∫ t in Ioc (0 : ℝ) 1, (autocorr F 0 - autocorr F t) / t) -
      (Real.eulerMascheroniConstant + Real.log Real.pi + Real.log 2 + 1 / 48) *
        (∫ x, F x ^ 2) - (∫ x, unitSourcePrimitive F x ^ 2) / 24 -
      (∫ x, unitSourcePrimitive F x) ^ 2 / 16 ≤
        EF.gammaBracket 0 * (∫ x, F x ^ 2) + biScaleLevyEnergy F := by
  have h := unit_odd_gamma_position_lower hF hcs hs ho
  rw [unit_odd_jump_first_moment hF.continuous hs ho] at h
  rw [unit_odd_position_eq_primitive_integral hF.continuous hs ho] at h
  simp only [neg_sq, autocorr_zero_eq] at h ⊢
  linarith only [h]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.unit_odd_gamma_lag_moments_lower

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.unit_odd_gamma_position_lower
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.unit_odd_gamma_jump_second_moment_lower
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.unit_odd_gamma_primitive_lower
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.unit_odd_position_eq_primitive_integral
