import GaloisForLFunctions.RHTower.SoninPrimePolarGroundRecovery
import GaloisForLFunctions.RHTower.SoninPrimeSquareCorrectionNuclear
import GaloisForLFunctions.RHTower.SoninTimeBandChannelRecovery

/-!
# Native full-response admission from the physical ground column

The original symmetric prime–polar tails commute with Fourier transform and
physical reflection and are self-adjoint. The proofs retain the complete
strong polar integral. Fixed bounded maps then identify their physical
time-band nuclear source with the complete original response pair.

Consequently the full response and the actual ground column control each
other with constants independent of all prime and continuum cutoffs.
Arithmetic ground-tail cancellation is not assumed or proved here.
-/

noncomputable section
open MeasureTheory Set
namespace RHTower
open ContinuousLinearMap
local notation "Op" => (SoninL2 →L[ℂ] SoninL2)


private theorem polar_integrable (b R sign : ℝ) (hb : 0 < b) (f : SoninL2) :
    Integrable (fun u => soninLogPolarDensity u • rayDilate (Real.exp (sign*u)) f)
      (volume.restrict (Icc b R)) := by
  have hd : ContinuousOn soninLogPolarDensity (Icc b R) := by
    intro u hu
    apply ContinuousAt.continuousWithinAt
    have hu0 : u ≠ 0 := ne_of_gt (hb.trans_le hu.1)
    unfold soninLogPolarDensity
    fun_prop
  exact (hd.smul ((continuous_dilationOrbit f).comp
    (continuous_const.mul continuous_id)).continuousOn).integrableOn_Icc

private theorem fourier_log_dilation (t : ℝ) (f : SoninL2) :
    fourierUnitary (rayDilate (Real.exp t) f) =
      rayDilate (Real.exp (-t)) (fourierUnitary f) := by
  rw [rayDilate_of_pos (Real.exp_pos _),rayDilate_of_pos (Real.exp_pos _),
    fourierUnitary_dilation]
  simp only [Real.exp_neg]

/-- Fourier transform reverses the direction of the entire original source,
including its actual strong polar integral. -/
theorem fourier_soninPrimePolarSourceOperator (P : Finset Nat.Primes)
    (b R sign : ℝ) (hb : 0 < b) (f : SoninL2) :
    fourierUnitary (soninPrimePolarSourceOperator P b R sign hb f) =
      soninPrimePolarSourceOperator P b R (-sign) hb (fourierUnitary f) := by
  rw [soninPrimePolarSourceOperator_apply,soninPrimePolarSourceOperator_apply,map_sub,map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    rw [map_smul,fourier_log_dilation,neg_mul]
  · let L : Op := fourierUnitary.toLinearIsometry.toContinuousLinearMap
    change L (∫ u in Icc b R, soninLogPolarDensity u • rayDilate (Real.exp (sign*u)) f) = _
    rw [← L.integral_comp_comm (polar_integrable b R sign hb f)]
    apply integral_congr_ae
    filter_upwards [] with u
    change fourierUnitary (soninLogPolarDensity u • rayDilate (Real.exp (sign*u)) f) = _
    rw [map_smul,fourier_log_dilation,neg_mul]

private theorem inner_log_dilation (t : ℝ) (f g : SoninL2) :
    inner ℂ (rayDilate (Real.exp t) f) g =
      inner ℂ f (rayDilate (Real.exp (-t)) g) := by
  rw [rayDilate_of_pos (Real.exp_pos _),rayDilate_of_pos (Real.exp_pos _)]
  change inner ℂ (dilationCLM (Real.exp t) (Real.exp_pos t) f) g = _
  rw [← adjoint_inner_right,adjoint_dilationCLM]
  simp only [Real.exp_neg,dilationCLM_apply]

private theorem inner_integral_left {μ : Measure ℝ} {f : ℝ → SoninL2}
    (hf : Integrable f μ) (y : SoninL2) :
    inner ℂ (∫ u, f u ∂μ) y = ∫ u, inner ℂ (f u) y ∂μ := by
  rw [← inner_conj_symm,← integral_inner hf,← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with u
  exact inner_conj_symm _ _

private theorem source_inner (P : Finset Nat.Primes) (b R sign : ℝ)
    (hb : 0 < b) (f g : SoninL2) :
    inner ℂ (soninPrimePolarSourceOperator P b R sign hb f) g =
      inner ℂ f (soninPrimePolarSourceOperator P b R (-sign) hb g) := by
  rw [soninPrimePolarSourceOperator_apply,soninPrimePolarSourceOperator_apply,
    inner_sub_left,inner_sub_right,sum_inner,inner_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    rw [inner_smul_left,inner_smul_right,map_inv₀,Complex.conj_ofReal,inner_log_dilation,neg_mul]
  · rw [inner_integral_left (polar_integrable b R sign hb f),
      ← integral_inner (polar_integrable b R (-sign) hb g)]
    apply integral_congr_ae
    filter_upwards [] with u
    rw [inner_smul_left,inner_smul_right,soninLogPolarDensity,Complex.conj_ofReal,
      inner_log_dilation,neg_mul]

/-- Adjoint reversal of the native source needs no limiting or regularity premise. -/
theorem adjoint_soninPrimePolarSourceOperator (P : Finset Nat.Primes)
    (b R sign : ℝ) (hb : 0 < b) :
    adjoint (soninPrimePolarSourceOperator P b R sign hb) =
      soninPrimePolarSourceOperator P b R (-sign) hb := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [adjoint_inner_right]
  exact source_inner P b R sign hb g f

/-- The complete native symmetric tail commutes with the actual Fourier unitary. -/
theorem fourier_soninPrimePolarSymmetricTail (P Q : Finset Nat.Primes)
    (b R S : ℝ) (hb : 0 < b) (f : SoninL2) :
    fourierUnitary (soninPrimePolarSymmetricTail P Q b R S hb f) =
      soninPrimePolarSymmetricTail P Q b R S hb (fourierUnitary f) := by
  simp only [soninPrimePolarSymmetricTail,sub_apply,add_apply,map_sub,map_add,
    fourier_soninPrimePolarSourceOperator,neg_neg]
  abel

/-- The complete native symmetric tail is self-adjoint on full physical L2. -/
theorem adjoint_soninPrimePolarSymmetricTail (P Q : Finset Nat.Primes)
    (b R S : ℝ) (hb : 0 < b) :
    adjoint (soninPrimePolarSymmetricTail P Q b R S hb) =
      soninPrimePolarSymmetricTail P Q b R S hb := by
  simp only [soninPrimePolarSymmetricTail,map_sub,map_add,
    adjoint_soninPrimePolarSourceOperator,neg_neg]
  abel

/-- Physical reflection also preserves the full original symmetric tail. -/
theorem reflection_soninPrimePolarSymmetricTail (P Q : Finset Nat.Primes)
    (b R S : ℝ) (hb : 0 < b) (f : SoninL2) :
    l2Reflection (soninPrimePolarSymmetricTail P Q b R S hb f) =
      soninPrimePolarSymmetricTail P Q b R S hb (l2Reflection f) := by
  have h (P : Finset Nat.Primes) (R sign : ℝ) :
      l2Reflection (soninPrimePolarSourceOperator P b R sign hb f) =
        soninPrimePolarSourceOperator P b R sign hb (l2Reflection f) :=
    soninPrimePolarSourceOperator_commutes l2Reflection
      (fun t g => by
        rw [rayDilate_of_pos (Real.exp_pos _),rayDilate_of_pos (Real.exp_pos _)]
        exact l2Reflection_dilation _ _ g) P b R sign hb f
  simp only [soninPrimePolarSymmetricTail,sub_apply,add_apply,map_sub,map_add,h]

local notation "S1" => SchattenOneOperator SoninL2
open GaloisForLFunctions.HTGeometry

private def nuclearSandwich (L R : Op) : S1 →L[ℂ] S1 :=
  LinearMap.mkContinuous
    { toFun := fun T => ⟨L ∘L T.val ∘L R,
        memSchattenClass_one_comp_right (memSchattenClass_one_comp_left T.property L) R⟩
      map_add' := by
        intro S T
        apply SchattenOneOperator.ext
        apply ContinuousLinearMap.ext
        intro x
        change L (S.val (R x)+T.val (R x)) = _
        exact map_add L _ _
      map_smul' := by
        intro c T
        apply SchattenOneOperator.ext
        apply ContinuousLinearMap.ext
        intro x
        change L (c • T.val (R x)) = _
        exact map_smul L c _ }
    (‖L‖*‖R‖) (fun T => by
      change traceNorm SoninL2 ((L ∘L T.val) ∘L R) ≤ _
      calc
        _ ≤ traceNorm SoninL2 (L ∘L T.val)*‖R‖ :=
          traceNorm_comp_right_le (memSchattenClass_one_comp_left T.property L).one_summable R
        _ ≤ (‖L‖*traceNorm SoninL2 T.val)*‖R‖ :=
          mul_le_mul_of_nonneg_right (traceNorm_comp_left_le T.summable L) (norm_nonneg _)
        _ = _ := by rw [SchattenOneOperator.norm_def]; ring)

private def fourierOp : Op := fourierUnitary.toLinearIsometry.toContinuousLinearMap
private def inverseFourierOp : Op := fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap
private def physicalBand (a : ℝ) (ha : 0 < a) : Op :=
  fullTimeBandFourier (-a) a (-a) a (neg_le_self ha.le)

private theorem fourierPhysical_factor (a : ℝ) (ha : 0 < a) :
    (centralFourierForbidden a).starProjection * (centralPhysicalForbidden a).starProjection =
      inverseFourierOp * physicalBand a ha := by
  dsimp only [centralPhysicalForbidden,centralFourierForbidden]
  rw [← indicatorCutoff_eq_physicalForbidden_starProjection,
    ← fourierCutoff_eq_fourierForbidden_starProjection]
  apply ContinuousLinearMap.ext
  intro f
  change fourierCutoff (centralInterval a) (measurableSet_centralInterval a)
    (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f) =
      fourierUnitary.symm (physicalBand a ha f)
  rw [fourierCutoff_apply,physicalBand,fullTimeBandFourier_eq_cutoffFourierCutoff]
  rfl

private theorem physicalFourier_factor (a : ℝ) (ha : 0 < a) :
    (centralPhysicalForbidden a).starProjection * (centralFourierForbidden a).starProjection =
      l2Reflection * physicalBand a ha * fourierOp := by
  dsimp only [centralPhysicalForbidden,centralFourierForbidden]
  rw [← indicatorCutoff_eq_physicalForbidden_starProjection,
    ← fourierCutoff_eq_fourierForbidden_starProjection]
  apply ContinuousLinearMap.ext
  intro f
  change indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
    (fourierUnitary.symm (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
      (fourierUnitary f))) = l2Reflection (physicalBand a ha (fourierUnitary f))
  rw [fourierUnitary_symm_eq_reflection_fourier,← l2Reflection_indicatorCutoff_central,
    physicalBand,fullTimeBandFourier_eq_cutoffFourierCutoff]
  rfl

private def leftSourceFromPhysical (a : ℝ) (ha : 0 < a) : S1 →L[ℂ] S1 :=
  nuclearSandwich l2Reflection
    (fourierOp*(1-(centralPhysicalForbidden a).starProjection*soninCorrectionSourceRightFactor a ha)) +
  nuclearSandwich inverseFourierOp (soninCorrectionSourceRightFactor a ha)

private def responseFromPhysical (a : ℝ) (ha : 0 < a) : S1 →L[ℝ] (S1 × S1) :=
  (soninPairedResponseForward a).comp
    (((leftSourceFromPhysical a ha).prod (leftSourceFromPhysical a ha)).restrictScalars ℝ)

private def physicalFromResponse (a : ℝ) : (S1 × S1) →L[ℝ] S1 :=
  ((nuclearSandwich fourierOp
    ((1+centralSoninProjectionCorrection a)*soninFourierPhysicalRecoveryFactor a)).restrictScalars ℝ).comp
    ((ContinuousLinearMap.fst ℝ S1 S1).comp (soninPairedResponseRecovery a))

private theorem native_fourier_commute (P Q : Finset Nat.Primes)
    (b R S : ℝ) (hb : 0 < b) :
    fourierOp * soninPrimePolarSymmetricTail P Q b R S hb =
      soninPrimePolarSymmetricTail P Q b R S hb * fourierOp := by
  apply ContinuousLinearMap.ext
  intro f
  exact fourier_soninPrimePolarSymmetricTail P Q b R S hb f

private theorem native_inverse_fourier_commute (P Q : Finset Nat.Primes)
    (b R S : ℝ) (hb : 0 < b) :
    soninPrimePolarSymmetricTail P Q b R S hb * inverseFourierOp =
      inverseFourierOp * soninPrimePolarSymmetricTail P Q b R S hb := by
  apply ContinuousLinearMap.ext
  intro f
  apply fourierUnitary.injective
  change fourierUnitary (soninPrimePolarSymmetricTail P Q b R S hb (fourierUnitary.symm f)) =
    fourierUnitary (fourierUnitary.symm (soninPrimePolarSymmetricTail P Q b R S hb f))
  rw [fourier_soninPrimePolarSymmetricTail,fourierUnitary.apply_symm_apply,
    fourierUnitary.apply_symm_apply]

private theorem sourceFromPhysical_apply (a : ℝ) (ha : 0 < a)
    (P Q : Finset Nat.Primes) (b R S : ℝ) (hb : 0 < b) :
    (leftSourceFromPhysical a ha (soninPrimePolarTimeBandTail a (-a) a ha P Q b R S hb)).val =
      soninPrimePolarSymmetricTail P Q b R S hb * centralSoninProjectionCorrection a := by
  let D := soninPrimePolarSymmetricTail P Q b R S hb
  let A := (centralPhysicalForbidden a).starProjection
  let B := (centralFourierForbidden a).starProjection
  let W := soninCorrectionSourceRightFactor a ha
  have hDR : D*l2Reflection=l2Reflection*D := by
    apply ContinuousLinearMap.ext
    intro f
    exact (reflection_soninPrimePolarSymmetricTail P Q b R S hb f).symm
  have hDU : D*inverseFourierOp=inverseFourierOp*D := native_inverse_fourier_commute P Q b R S hb
  have hJ : centralSoninProjectionCorrection a=A*B*(1-A*W)+B*A*W :=
    centralSoninProjectionCorrection_eq_timeBand_rightFactors a ha
  have hAB : A*B=l2Reflection*physicalBand a ha*fourierOp := physicalFourier_factor a ha
  have hBA : B*A=inverseFourierOp*physicalBand a ha := fourierPhysical_factor a ha
  change l2Reflection*(D*physicalBand a ha)*(fourierOp*(1-A*W)) +
    inverseFourierOp*(D*physicalBand a ha)*W = D*centralSoninProjectionCorrection a
  rw [hJ,hAB,hBA]
  calc
    _ = (D*l2Reflection)*physicalBand a ha*(fourierOp*(1-A*W)) +
      (D*inverseFourierOp)*physicalBand a ha*W := by
        rw [hDR,hDU]
        noncomm_ring
    _ = _ := by noncomm_ring

private theorem responseFromPhysical_apply (a : ℝ) (ha : 0 < a)
    (P Q : Finset Nat.Primes) (b R S : ℝ) (hb : 0 < b) :
    responseFromPhysical a ha (soninPrimePolarTimeBandTail a (-a) a ha P Q b R S hb) =
      soninNuclearResponsePair a ha (soninPrimePolarSymmetricTail P Q b R S hb) := by
  rw [← soninPairedResponseForward_apply]
  apply congrArg (soninPairedResponseForward a)
  apply Prod.ext <;> apply SchattenOneOperator.ext
  · exact sourceFromPhysical_apply a ha P Q b R S hb
  · change (leftSourceFromPhysical a ha
      (soninPrimePolarTimeBandTail a (-a) a ha P Q b R S hb)).val =
      adjoint (soninPrimePolarSymmetricTail P Q b R S hb)*centralSoninProjectionCorrection a
    rw [adjoint_soninPrimePolarSymmetricTail]
    exact sourceFromPhysical_apply a ha P Q b R S hb

private theorem physicalFromResponse_apply (a : ℝ) (ha : 0 < a)
    (P Q : Finset Nat.Primes) (b R S : ℝ) (hb : 0 < b) :
    physicalFromResponse a (soninNuclearResponsePair a ha (soninPrimePolarSymmetricTail P Q b R S hb)) =
      soninPrimePolarTimeBandTail a (-a) a ha P Q b R S hb := by
  let D := soninPrimePolarSymmetricTail P Q b R S hb
  change nuclearSandwich fourierOp
    ((1+centralSoninProjectionCorrection a)*soninFourierPhysicalRecoveryFactor a)
    (soninPairedResponseRecovery a (soninNuclearResponsePair a ha D)).1 = _
  rw [soninPairedResponseRecovery_apply]
  apply SchattenOneOperator.ext
  change fourierOp*(D*centralSoninProjectionCorrection a)*
    ((1+centralSoninProjectionCorrection a)*soninFourierPhysicalRecoveryFactor a) =
      D*physicalBand a ha
  have hJ : centralSoninProjectionCorrection a*(1+centralSoninProjectionCorrection a) =
      (centralPhysicalForbidden a).starProjection*(centralFourierForbidden a).starProjection +
      (centralFourierForbidden a).starProjection*(centralPhysicalForbidden a).starProjection := by
    rw [mul_add,mul_one,add_comm,centralSoninProjectionCorrection_sq_add_self_eq_anticommutator]
  have hFU : fourierOp*inverseFourierOp=1 := by
    apply ContinuousLinearMap.ext
    intro f
    exact fourierUnitary.apply_symm_apply f
  have hFD : fourierOp*D=D*fourierOp := native_fourier_commute P Q b R S hb
  calc
    _ = fourierOp*D*((centralSoninProjectionCorrection a*(1+centralSoninProjectionCorrection a))*
      soninFourierPhysicalRecoveryFactor a) := by noncomm_ring
    _ = fourierOp*D*((centralFourierForbidden a).starProjection*(centralPhysicalForbidden a).starProjection) := by
      rw [hJ,centralFourierPhysical_eq_anticommutator_rightFactor a ha]
    _ = _ := by rw [hFD,fourierPhysical_factor a ha,mul_assoc,← mul_assoc fourierOp,hFU,one_mul]

/-- The complete original response pair of a native symmetric prime–polar tail. -/
def soninPrimePolarResponseTail (a : ℝ) (ha : 0 < a)
    (P Q : Finset Nat.Primes) (b R S : ℝ) (hb : 0 < b) : S1 × S1 :=
  soninNuclearResponsePair a ha (soninPrimePolarSymmetricTail P Q b R S hb)

/-- Every full native response tail has a cutoff-independent nuclear bound
by its actual physical ground column. Fourier and adjoint transport are proved. -/
theorem soninPrimePolar_response_ground_nuclear (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q : Finset Nat.Primes) (b R S : ℝ) (hb : 0 < b),
      ‖soninPrimePolarResponseTail a ha P Q b R S hb‖ ≤
        C*‖soninPrimePolarSymmetricTail P Q b R S hb (soninCutoffMonomial a 0)‖ := by
  let M := responseFromPhysical a ha
  let G := soninGroundNuclearConstant a (-a) a ha
  refine ⟨1+|‖M‖*G|,by positivity,?_⟩
  intro P Q b R S hb
  have h := M.le_opNorm (soninPrimePolarTimeBandTail a (-a) a ha P Q b R S hb)
  rw [responseFromPhysical_apply] at h
  have ht := soninPrimePolar_timeBand_ground_nuclear a (-a) a ha P Q b R S hb
  have hm := mul_le_mul_of_nonneg_left ht (norm_nonneg M)
  change ‖soninPrimePolarResponseTail a ha P Q b R S hb‖ ≤ _ at h
  have hab := le_abs_self (‖M‖*G)
  have hg := norm_nonneg (soninPrimePolarSymmetricTail P Q b R S hb (soninCutoffMonomial a 0))
  dsimp only [G] at hab
  nlinarith

/-- The complete native response also controls the physical ground tail.
Together with the upper bound this is faithful full-response admission. -/
theorem soninPrimePolar_ground_le_response_nuclear (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q : Finset Nat.Primes) (b R S : ℝ) (hb : 0 < b),
      ‖soninPrimePolarSymmetricTail P Q b R S hb (soninCutoffMonomial a 0)‖ ≤
        C*‖soninPrimePolarResponseTail a ha P Q b R S hb‖ := by
  obtain ⟨C,hC,hG⟩ := soninPrimePolar_ground_le_timeBand_nuclear a ha
  let M := physicalFromResponse a
  refine ⟨C*(1+‖M‖),mul_pos hC (by positivity),?_⟩
  intro P Q b R S hb
  have h := M.le_opNorm (soninPrimePolarResponseTail a ha P Q b R S hb)
  change ‖physicalFromResponse a (soninNuclearResponsePair a ha
    (soninPrimePolarSymmetricTail P Q b R S hb))‖ ≤ _ at h
  rw [physicalFromResponse_apply] at h
  have hg := hG P Q b R S hb
  have hm := mul_le_mul_of_nonneg_left h hC.le
  have hn := norm_nonneg (soninPrimePolarResponseTail a ha P Q b R S hb)
  nlinarith

end RHTower
