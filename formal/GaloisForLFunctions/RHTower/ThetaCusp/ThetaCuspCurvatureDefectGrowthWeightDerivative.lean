import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthAbsorptionResidual
/-!
# Exact normalization-derivative cancellation for the growth transfer

Differentiating all eight finite logarithmic sector weights produces
one strictly negative term, -8! times the transfer leading coefficient
and the ninth power of the actual likelihood mean. The cancellation
follows from the order-eight vanishing of the centered moment series.
This removes normalization derivatives as an adverse error in the
remaining dominant-pair-relative source-sign problem. No sign of the
complete source transfer is assumed or concluded here.
-/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
open Filter Set Topology
noncomputable section

def finiteLogWeightSeries (k : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (9-k), (840/(k:ℝ))*((k+j-1).choose j:ℝ)*p^j

def finiteLogWeightSeriesJet (k : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (9-k), (840/(k:ℝ))*((k+j-1).choose j:ℝ)*(j:ℝ)*p^(j-1)

theorem finiteLogWeightSeries_eq (p : ℝ) {k : ℕ} (hk : 1 ≤ k ∧ k ≤ 8) :
    finiteLogWeightSeries k p=finiteLogWeight p k := by
  obtain ⟨hk1,hk8⟩ := hk
  interval_cases k <;> norm_num [finiteLogWeightSeries,finiteLogWeight,Finset.sum_range_succ,
    Nat.choose]
  all_goals ring

theorem hasDerivAt_finiteLogWeightSeries (p : ℝ) (k : ℕ) :
    HasDerivAt (finiteLogWeightSeries k) (finiteLogWeightSeriesJet k p) p := by
  unfold finiteLogWeightSeries finiteLogWeightSeriesJet
  apply HasDerivAt.fun_sum
  intro j hj
  simpa only [mul_assoc] using (hasDerivAt_pow j p).const_mul ((840/(k:ℝ))*((k+j-1).choose j:ℝ))

theorem finiteLogWeight_differential_identity (p : ℝ) {k : ℕ} (hk : 1 ≤ k ∧ k ≤ 8) :
    (1-p)*finiteLogWeightSeriesJet k p-(k:ℝ)*finiteLogWeight p k=
      -840*(Nat.choose 8 k:ℝ)*p^(8-k) := by
  obtain ⟨hk1,hk8⟩ := hk
  interval_cases k <;> norm_num [finiteLogWeightSeriesJet,finiteLogWeight,Finset.sum_range_succ,
    Nat.choose] <;> ring

def finiteNormalizedLogWeight (k : ℕ) (p : ℝ) : ℝ :=
  finiteLogWeight p k*(1-p)^k/840

theorem hasDerivAt_finiteNormalizedLogWeight (p : ℝ) {k : ℕ} (hk : 1 ≤ k ∧ k ≤ 8) :
    HasDerivAt (finiteNormalizedLogWeight k)
      (-(Nat.choose 8 k:ℝ)*(1-p)^(k-1)*p^(8-k)) p := by
  have hf : HasDerivAt (fun r => finiteLogWeight r k) (finiteLogWeightSeriesJet k p) p := by
    convert! hasDerivAt_finiteLogWeightSeries p k using 1
    funext r
    exact (finiteLogWeightSeries_eq r hk).symm
  have hg := (((hasDerivAt_const p (1:ℝ)).sub (hasDerivAt_id p)).pow k)
  have h := (hf.mul hg).div_const (840:ℝ)
  apply h.congr_deriv
  have hpow : (1-p)^k=(1-p)^(k-1)*(1-p) := by
    rw [←pow_succ]
    congr 1
    omega
  have hdiff := finiteLogWeight_differential_identity p hk
  simp only [Pi.pow_apply,Pi.sub_apply,id_eq,zero_sub,mul_neg_one] 
  rw [hpow]
  linear_combination ((1-p)^(k-1)/840)*hdiff

theorem one_sub_normalizedMoment_zero {q : ℝ} (hq : 0 < q) :
    1-thetaCuspLikelihoodNormalizedMoment q 0=(thetaCuspLikelihoodPartition q)⁻¹ := by
  have hp := thetaCuspLikelihoodPartition_pos hq
  have he := thetaCuspLikelihoodPartition_eq_one_add_moment_zero hq
  unfold thetaCuspLikelihoodNormalizedMoment
  field_simp
  linarith

theorem normalizedTransferWeight_eq_finite {q : ℝ} (hq : 0 < q) (k : ℕ) :
    normalizedTransferWeight q k=finiteNormalizedLogWeight k (thetaCuspLikelihoodNormalizedMoment q 0) := by
  unfold normalizedTransferWeight finiteNormalizedLogWeight
  rw [one_sub_normalizedMoment_zero hq]

theorem hasDerivAt_normalizedTransferWeight {q : ℝ} (hq : 0 < q) {k : ℕ}
    (hk : 1 ≤ k ∧ k ≤ 8) :
    HasDerivAt (fun r => normalizedTransferWeight r k)
      ((Nat.choose 8 k:ℝ)*thetaCuspLikelihoodMean q*(thetaCuspLikelihoodPartition q)⁻¹^k*
        thetaCuspLikelihoodNormalizedMoment q 0^(8-k)) q := by
  let p := thetaCuspLikelihoodNormalizedMoment q 0
  have h := (hasDerivAt_finiteNormalizedLogWeight p hk).comp q
    (hasDerivAt_thetaCuspLikelihoodNormalizedMoment hq 0)
  have hval : (-(Nat.choose 8 k:ℝ)*(1-p)^(k-1)*p^(8-k))*
      (-thetaCuspLikelihoodNormalizedMoment q (0+1)+
        thetaCuspLikelihoodMean q*thetaCuspLikelihoodNormalizedMoment q 0)=
      (Nat.choose 8 k:ℝ)*thetaCuspLikelihoodMean q*(thetaCuspLikelihoodPartition q)⁻¹^k*p^(8-k) := by
    rw [Nat.zero_add,thetaCuspLikelihoodNormalizedMoment_one_eq_mean]
    rw [←one_sub_normalizedMoment_zero hq]
    change (-(Nat.choose 8 k:ℝ)*(1-p)^(k-1)*p^(8-k))*(-thetaCuspLikelihoodMean q+
      thetaCuspLikelihoodMean q*p)=(Nat.choose 8 k:ℝ)*thetaCuspLikelihoodMean q*(1-p)^k*p^(8-k)
    have hpow : (1-p)^k=(1-p)^(k-1)*(1-p) := by rw [←pow_succ]; congr 1; omega
    rw [hpow]
    ring
  have hd := h.congr_deriv hval
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hq] with r hr
  exact normalizedTransferWeight_eq_finite hr k

theorem coeff_centered_eighth (P : PowerSeries ℝ) (j : ℕ) (hj : j ≤ 8) :
    PowerSeries.coeff j ((P-PowerSeries.C (PowerSeries.constantCoeff P))^8)=
      if j=8 then (PowerSeries.coeff 1 P)^8 else 0 := by
  have he : P-PowerSeries.C (PowerSeries.constantCoeff P)=
      (PowerSeries.mk fun r => PowerSeries.coeff (r+1) P)*PowerSeries.X := by
    exact sub_eq_iff_eq_add.mpr (PowerSeries.eq_shift_mul_X_add_const P)
  rw [he,mul_pow,PowerSeries.coeff_mul_X_pow']
  by_cases h8 : j=8
  · subst j
    simp only [le_refl,ite_true,Nat.sub_self,PowerSeries.coeff_zero_eq_constantCoeff_apply,
      map_pow,PowerSeries.constantCoeff_mk,Nat.zero_add]
  · simp only [show ¬8≤j by omega,ite_false,h8]

def centeredEighthMoment (m : ℕ → ℝ) (j : ℕ) : ℝ :=
  (j.factorial:ℝ)*PowerSeries.coeff j ((momentSeries m-PowerSeries.C (m 0))^8)

theorem centeredEighthMoment_eq (m : ℕ → ℝ) (j : ℕ) (hj : j ≤ 8) :
    centeredEighthMoment m j=if j=8 then 40320*m 1^8 else 0 := by
  have hc : PowerSeries.constantCoeff (momentSeries m)=m 0 := by simp [momentSeries]
  unfold centeredEighthMoment
  rw [←hc,coeff_centered_eighth _ j hj]
  by_cases h8 : j=8
  · subst j
    norm_num [momentSeries]
  · simp [h8]

theorem centeredEighth_transfer (q : ℝ) (m : ℕ → ℝ) :
    growthTransferFunctional q (centeredEighthMoment m)=
      40320*growthTransferLeadingCoefficient q*m 1^8 := by
  unfold growthTransferFunctional
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [centeredEighthMoment_eq,growthTransferLeadingCoefficient]
  ring

theorem centeredSeries_eight_rebase (P : PowerSeries ℝ) (p : ℝ) :
    (P-PowerSeries.C p)^8=
      PowerSeries.C (p^8)-PowerSeries.C (8*p^7)*P+
      PowerSeries.C (28*p^6)*P^2-PowerSeries.C (56*p^5)*P^3+
      PowerSeries.C (70*p^4)*P^4-PowerSeries.C (56*p^3)*P^5+
      PowerSeries.C (28*p^2)*P^6-PowerSeries.C (8*p)*P^7+P^8 := by
  simp only [map_pow,map_mul,map_ofNat]
  ring

theorem centeredEighthMoment_decomposition (m : ℕ → ℝ) {j : ℕ} (hj : j ≠ 0) :
    centeredEighthMoment m j=
      -8*m 0^7*spectralPowerMoment m 1 j+28*m 0^6*spectralPowerMoment m 2 j-
      56*m 0^5*spectralPowerMoment m 3 j+70*m 0^4*spectralPowerMoment m 4 j-
      56*m 0^3*spectralPowerMoment m 5 j+28*m 0^2*spectralPowerMoment m 6 j-
      8*m 0*spectralPowerMoment m 7 j+spectralPowerMoment m 8 j := by
  unfold centeredEighthMoment spectralPowerMoment
  rw [centeredSeries_eight_rebase]
  simp only [map_sub,map_add,PowerSeries.coeff_C_mul,PowerSeries.coeff_C_of_ne_zero hj,pow_one]
  ring

def weightDerivativeTransfer (q : ℝ) (m : ℕ → ℝ) : ℝ :=
  8*m 0^7*growthTransferFunctional q (spectralPowerMoment m 1)-
    28*m 0^6*growthTransferFunctional q (spectralPowerMoment m 2)+
    56*m 0^5*growthTransferFunctional q (spectralPowerMoment m 3)-
    70*m 0^4*growthTransferFunctional q (spectralPowerMoment m 4)+
    56*m 0^3*growthTransferFunctional q (spectralPowerMoment m 5)-
    28*m 0^2*growthTransferFunctional q (spectralPowerMoment m 6)+
    8*m 0*growthTransferFunctional q (spectralPowerMoment m 7)-
    growthTransferFunctional q (spectralPowerMoment m 8)

theorem weightDerivativeTransfer_eq (q : ℝ) (m : ℕ → ℝ) :
    weightDerivativeTransfer q m=-40320*growthTransferLeadingCoefficient q*m 1^8 := by
  have he : growthTransferFunctional q (centeredEighthMoment m)=-weightDerivativeTransfer q m := by
    unfold weightDerivativeTransfer growthTransferFunctional
    simp only [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib,←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [centeredEighthMoment_decomposition m (j := j+2) (by omega),
      centeredEighthMoment_decomposition m (j := j+3) (by omega)]
    ring
  have hc := centeredEighth_transfer q m
  linear_combination he-hc

def normalizationWeightTransfer (q : ℝ) : ℝ :=
  deriv (fun r => normalizedTransferWeight r 1) q*rawTransferSector q 1-
    deriv (fun r => normalizedTransferWeight r 2) q*rawTransferSector q 2+
    deriv (fun r => normalizedTransferWeight r 3) q*rawTransferSector q 3-
    deriv (fun r => normalizedTransferWeight r 4) q*rawTransferSector q 4+
    deriv (fun r => normalizedTransferWeight r 5) q*rawTransferSector q 5-
    deriv (fun r => normalizedTransferWeight r 6) q*rawTransferSector q 6+
    deriv (fun r => normalizedTransferWeight r 7) q*rawTransferSector q 7-
    deriv (fun r => normalizedTransferWeight r 8) q*rawTransferSector q 8

theorem normalizationWeightTransfer_eq {q : ℝ} (hq : 0 < q) :
    normalizationWeightTransfer q=-40320*growthTransferLeadingCoefficient q*thetaCuspLikelihoodMean q^9 := by
  have hk (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 8) :
      deriv (fun r => normalizedTransferWeight r k) q*rawTransferSector q k=
      (Nat.choose 8 k:ℝ)*thetaCuspLikelihoodMean q*thetaCuspLikelihoodNormalizedMoment q 0^(8-k)*
        growthTransferFunctional q (spectralPowerMoment (thetaCuspLikelihoodNormalizedMoment q) k) := by
    rw [(hasDerivAt_normalizedTransferWeight hq hk).deriv,
      growthTransferFunctional_normalized_power]
    ring
  unfold normalizationWeightTransfer
  rw [hk 1 (by omega),hk 2 (by omega),hk 3 (by omega),hk 4 (by omega),
    hk 5 (by omega),hk 6 (by omega),hk 7 (by omega),hk 8 (by omega)]
  norm_num only [Nat.choose,Nat.reduceSub,Nat.cast_ofNat,pow_zero,mul_one]
  calc
    _ = thetaCuspLikelihoodMean q*weightDerivativeTransfer q (thetaCuspLikelihoodNormalizedMoment q) := by
      unfold weightDerivativeTransfer
      ring
    _ = _ := by
      rw [weightDerivativeTransfer_eq,thetaCuspLikelihoodNormalizedMoment_one_eq_mean]
      ring

theorem normalizationWeightTransfer_neg {q : ℝ} (hq : 3/2 ≤ q) :
    normalizationWeightTransfer q < 0 := by
  have hq0 : 0 < q := by linarith
  have hc := growthTransferLeadingCoefficient_pos hq
  have hm : 0 < thetaCuspLikelihoodMean q := by
    unfold thetaCuspLikelihoodMean
    exact div_pos (thetaCuspHigherLikelihoodSpectralMoment_one_pos hq0)
      (thetaCuspLikelihoodPartition_pos hq0)
  rw [normalizationWeightTransfer_eq hq0]
  have h : 0 < 40320*growthTransferLeadingCoefficient q*thetaCuspLikelihoodMean q^9 := by positivity
  nlinarith

end
end RHTower.ThetaCuspDefect
