import GaloisForLFunctions.ThetaCuspSections.FifthEvenPolynomialCrossLoad
import GaloisForLFunctions.HTGeometry.ThresholdDerivativeGlue

/-!
# A compact quartic flux for the fifth even theta matrix

Cut the quartic flux at its double zero. Matching values and derivatives
make the splice continuously differentiable. The discarded derivative tail
has zero integral, so the corrected source retains every mixed matrix entry.
Beyond the cutoff the source is native and strictly positive.
-/

noncomputable section
open Matrix MeasureTheory RHTower
open Set (Ioi)
namespace GaloisForLFunctions.ThetaCuspSections.FifthTruncatedCross
open EvenFiveEndpoint FifthNativeRay
open RHTower.ThetaCuspGaussianLimit

/-- Positive double zero of the quartic profile. -/
def cutoff : ℝ := Real.sqrt 2

/-- The quartic flux stopped at its positive double zero. -/
def flux (a r : ℝ) : ℝ :=
  if r < cutoff then FifthPolynomialCross.flux a r else 0

/-- The discarded derivative tail. -/
def tailCorrection (a : ℝ) : ℝ → ℝ :=
  (Ioi cutoff).indicator (deriv (FifthPolynomialCross.flux a))

/-- The compact correction density on the positive half-line. -/
def correction (a r : ℝ) : ℝ :=
  deriv (FifthPolynomialCross.flux a) r-tailCorrection a r

/-- The complete fifth even source after deleting the zero-mass tail. -/
def weightedRepair (a r : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  FifthPolynomialCross.weightedRepair a r-
    tailCorrection a r • crossLoad paidSevenSchur

theorem cutoff_nonneg : 0 ≤ cutoff := Real.sqrt_nonneg _

theorem cutoff_sq : cutoff^2=2 := Real.sq_sqrt (by norm_num)

theorem cutoff_pos : 0 < cutoff := Real.sqrt_pos.mpr (by norm_num)

theorem profile_cutoff : FifthPolynomialCross.profile cutoff=0 := by
  norm_num [FifthPolynomialCross.profile,cutoff_sq]

theorem flux_cutoff (a : ℝ) : FifthPolynomialCross.flux a cutoff=0 := by
  rw [FifthPolynomialCross.flux,profile_cutoff,zero_mul]

theorem deriv_flux_cutoff (a : ℝ) :
    deriv (FifthPolynomialCross.flux a) cutoff=0 := by
  have hs : (cutoff/2)^2=1/2 := by nlinarith only [cutoff_sq]
  rw [FifthPolynomialCross.deriv_flux_remainder]
  norm_num [FifthPolynomialCross.compensation,hs,profile_cutoff]

/-- On the positive half-line, the flux has the positive-part quartic profile. -/
theorem flux_eq_profile (a : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    flux a r=(max (1-r^2/2) 0)^2*thetaCuspCenterCompensationFlux a r := by
  by_cases h : r < cutoff
  · have hs := mul_self_le_mul_self hr h.le
    have hp : 0 ≤ 1-r^2/2 := by nlinarith only [hs,cutoff_sq]
    simp only [flux,if_pos h,max_eq_left hp,FifthPolynomialCross.flux,
      FifthPolynomialCross.profile]
  · have hs := mul_self_le_mul_self cutoff_nonneg (not_lt.mp h)
    have hp : 1-r^2/2 ≤ 0 := by nlinarith only [hs,cutoff_sq]
    simp only [flux,if_neg h,max_eq_right hp,zero_pow (by decide : (2 : ℕ) ≠ 0),zero_mul]

/-- The correction equals the original derivative below the cutoff and vanishes beyond it. -/
theorem correction_eq (a r : ℝ) : correction a r=
    if r < cutoff then deriv (FifthPolynomialCross.flux a) r else 0 := by
  rcases lt_trichotomy r cutoff with h | h | h
  · have hn : r ∉ Ioi cutoff := not_lt.mpr h.le
    simp only [correction,tailCorrection,Set.indicator_of_notMem hn,sub_zero,if_pos h]
  · subst r
    have hn : cutoff ∉ Ioi cutoff := by
      change ¬cutoff < cutoff
      exact lt_irrefl cutoff
    simp only [correction,tailCorrection,Set.indicator_of_notMem hn,
      deriv_flux_cutoff,sub_self,lt_self_iff_false,if_false]
  · have hm : r ∈ Ioi cutoff := h
    simp only [correction,tailCorrection,Set.indicator_of_mem hm,sub_self,
      if_neg (not_lt.mpr h.le)]

private theorem original_hasDerivAt (a r : ℝ) :
    HasDerivAt (FifthPolynomialCross.flux a)
      (deriv (FifthPolynomialCross.flux a) r) r := by
  apply DifferentiableAt.hasDerivAt
  unfold FifthPolynomialCross.flux FifthPolynomialCross.profile
  exact ((((hasDerivAt_const r (1 : ℝ)).sub
    (((hasDerivAt_id r).pow 2).div_const 2)).pow 2).mul
      (hasDerivAt_thetaCuspCenterCompensationFlux a r)).differentiableAt

/-- The zero value and derivative at the splice give the literal flux derivative. -/
theorem hasDerivAt_flux (a r : ℝ) : HasDerivAt (flux a) (correction a r) r := by
  rw [correction_eq]
  exact HTGeometry.hasDerivAt_ite_lt (original_hasDerivAt a)
    (fun y => hasDerivAt_const y (0 : ℝ)) (flux_cutoff a) (deriv_flux_cutoff a)

theorem deriv_flux (a r : ℝ) : deriv (flux a) r=correction a r :=
  (hasDerivAt_flux a r).deriv

/-- The correction density is continuous across the double zero. -/
theorem continuous_correction (a : ℝ) : Continuous (correction a) := by
  have hF : Continuous thetaCuspFullSource := thetaCuspSchwartzReal.continuous
  have hd : Continuous (deriv thetaCuspFullSource) :=
    (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal).continuous
  have hf : Continuous (deriv (FifthPolynomialCross.flux a)) := by
    change Continuous (fun r => deriv (FifthPolynomialCross.flux a) r)
    simp_rw [FifthPolynomialCross.deriv_flux_remainder]
    unfold FifthPolynomialCross.profile FifthPolynomialCross.compensation
      thetaCuspCenterCompensationSource
    fun_prop
  have he : correction a=(fun r => if r < cutoff then
      deriv (FifthPolynomialCross.flux a) r else 0) := funext (correction_eq a)
  rw [he]
  exact HTGeometry.continuous_ite_lt hf continuous_const (deriv_flux_cutoff a)

/-- The corrected matrix uses the literal derivative of the truncated flux. -/
theorem weightedRepair_eq_source (a r : ℝ) : weightedRepair a r=
    (r*Real.sinh (a*r)) • nativeShiftedMatrix 5 0 (r/2)+
      deriv (flux a) r • crossLoad paidSevenSchur := by
  rw [deriv_flux]
  ext i j
  simp only [weightedRepair,FifthPolynomialCross.weightedRepair,correction,
    Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

private theorem tail_subset : Ioi cutoff ⊆ Ioi (0 : ℝ) :=
  fun _ hr => lt_of_le_of_lt cutoff_nonneg hr

/-- The discarded tail has zero mass because its boundary flux vanishes. -/
theorem integral_deriv_flux_tail {a : ℝ} (ha : |a| < 1) :
    (∫ r : ℝ in Ioi cutoff, deriv (FifthPolynomialCross.flux a) r)=0 := by
  have h0 := (integrableOn_deriv_thetaCuspPolynomialFlux 0 ha).mono_set tail_subset
  have h2 := (integrableOn_deriv_thetaCuspPolynomialFlux 2 ha).mono_set tail_subset
  have h4 := (integrableOn_deriv_thetaCuspPolynomialFlux 4 ha).mono_set tail_subset
  have hs : IntegrableOn (fun r => deriv (thetaCuspPolynomialFlux 0 a) r-
      deriv (thetaCuspPolynomialFlux 2 a) r) (Ioi cutoff) := h0.sub h2
  simp_rw [FifthPolynomialCross.deriv_flux_eq]
  rw [integral_add hs (h4.const_mul (1/4)),integral_sub h0 h2,
    integral_const_mul,integral_Ioi_deriv_thetaCuspPolynomialFlux_eq_neg 0 ha,
    integral_Ioi_deriv_thetaCuspPolynomialFlux_eq_neg 2 ha,
    integral_Ioi_deriv_thetaCuspPolynomialFlux_eq_neg 4 ha]
  have hf := flux_cutoff a
  rw [FifthPolynomialCross.flux_eq] at hf
  linarith only [hf]

/-- The discarded derivative tail is absolutely integrable. -/
theorem tailCorrection_integrable {a : ℝ} (ha : |a| < 1) :
    IntegrableOn (tailCorrection a) (Ioi 0) :=
  (FifthPolynomialCross.integrable_deriv_flux ha).indicator measurableSet_Ioi

/-- Discarding the tail changes no integrated correction mass. -/
theorem tailCorrection_integral {a : ℝ} (ha : |a| < 1) :
    (∫ r : ℝ in Ioi 0, tailCorrection a r)=0 := by
  rw [tailCorrection,setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr tail_subset,integral_deriv_flux_tail ha]

/-- The compact correction density is absolutely integrable. -/
theorem correction_integrable {a : ℝ} (ha : |a| < 1) :
    IntegrableOn (correction a) (Ioi 0) :=
  (FifthPolynomialCross.integrable_deriv_flux ha).sub (tailCorrection_integrable ha)

/-- The truncated correction has zero total mass. -/
theorem correction_integral {a : ℝ} (ha : |a| < 1) :
    (∫ r : ℝ in Ioi 0, correction a r)=0 := by
  change (∫ r : ℝ in Ioi 0, deriv (FifthPolynomialCross.flux a) r-tailCorrection a r)=0
  rw [integral_sub (FifthPolynomialCross.integrable_deriv_flux ha)
    (tailCorrection_integrable ha),FifthPolynomialCross.integral_deriv_flux ha,
    tailCorrection_integral ha,sub_self]

/-- The literal truncated flux derivative integrates to zero. -/
theorem integral_deriv_flux {a : ℝ} (ha : |a| < 1) :
    (∫ r : ℝ in Ioi 0, deriv (flux a) r)=0 := by
  simp only [deriv_flux]
  exact correction_integral ha

/-- Inside the cutoff, the complete source agrees with the quartic repair. -/
theorem weightedRepair_eq_inner (a : ℝ) {r : ℝ} (hr : r ≤ cutoff) :
    weightedRepair a r=FifthPolynomialCross.weightedRepair a r := by
  have hn : r ∉ Ioi cutoff := not_lt.mpr hr
  simp only [weightedRepair,tailCorrection,Set.indicator_of_notMem hn,zero_smul,sub_zero]

/-- At and beyond the double zero, the complete source is native. -/
theorem weightedRepair_eq_outer (a : ℝ) {r : ℝ} (hr : cutoff ≤ r) :
    weightedRepair a r=(r*Real.sinh (a*r)) • nativeShiftedMatrix 5 0 (r/2) := by
  rcases hr.eq_or_lt with h | h
  · subst r
    rw [weightedRepair_eq_inner a le_rfl,FifthPolynomialCross.weightedRepair,
      deriv_flux_cutoff,zero_smul,add_zero]
  · have hm : r ∈ Ioi cutoff := h
    simp only [weightedRepair,tailCorrection,Set.indicator_of_mem hm,
      FifthPolynomialCross.weightedRepair,add_sub_cancel_right]

private theorem weighted_entry (a : ℝ) (i j : Fin 5) :
    (fun r => weightedRepair a r i j)=fun r =>
      FifthPolynomialCross.weightedRepair a r i j-
        crossLoad paidSevenSchur i j*tailCorrection a r := by
  funext r
  simp only [weightedRepair,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,mul_comm]

/-- Every mixed entry remains absolutely integrable in the critical aperture. -/
theorem weightedRepair_integrable {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2)
    (i j : Fin 5) : IntegrableOn (fun r => weightedRepair a r i j) (Ioi 0) := by
  have habs : |a| < 1 := by rw [abs_of_nonneg ha0]; linarith only [ha]
  rw [weighted_entry]
  exact (FifthPolynomialCross.weightedRepair_integrable ha0 ha i j).sub
    ((tailCorrection_integrable habs).const_mul _)

/-- Truncation preserves the actual fifth even mixed matrix entry by entry. -/
theorem weightedRepair_integral {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2)
    (i j : Fin 5) : (∫ r in Ioi 0, weightedRepair a r i j)=
      thetaCuspCenterMixedSignedJet a (2*(i.val+j.val)) := by
  have habs : |a| < 1 := by rw [abs_of_nonneg ha0]; linarith only [ha]
  rw [weighted_entry,integral_sub (FifthPolynomialCross.weightedRepair_integrable ha0 ha i j)
    ((tailCorrection_integrable habs).const_mul _),integral_const_mul,
    tailCorrection_integral habs,mul_zero,sub_zero,FifthPolynomialCross.weightedRepair_integral ha0 ha]

/-- The native source is strictly positive throughout the discarded tail. -/
theorem weightedRepair_outer_posDef {a r : ℝ} (ha : 0 < a) (hr : cutoff ≤ r) :
    (weightedRepair a r).PosDef := by
  have hr0 := lt_of_lt_of_le cutoff_pos hr
  have hroot : 1 ≤ cutoff := by nlinarith only [cutoff_nonneg,cutoff_sq]
  have hr1 : 1 ≤ r := hroot.trans hr
  have he : 2 ≤ Real.exp r := by linarith only [Real.add_one_le_exp r,hr1]
  have hp : 3 < Real.pi := Real.pi_gt_three
  have hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 (r/2) := by
    have h := mul_le_mul_of_nonneg_left he Real.pi_pos.le
    norm_num only [thetaCuspSingleAtomReflectionScale,Nat.cast_one,one_pow,mul_one,
      show 2*(r/2)=r by ring]
    nlinarith only [h,hp]
  rw [weightedRepair_eq_outer a hr]
  exact (native_even_five_posDef hq).smul
    (mul_pos hr0 (Real.sinh_pos_iff.mpr (mul_pos ha hr0)))

end GaloisForLFunctions.ThetaCuspSections.FifthTruncatedCross
