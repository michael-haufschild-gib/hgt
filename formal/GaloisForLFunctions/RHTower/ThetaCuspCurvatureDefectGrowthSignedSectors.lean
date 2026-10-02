import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthConvolution
/-!
# Exact signed-sector bound for the complete growth transfer

Normalization transports the finite logarithmic decomposition to the actual
unnormalized convolution sectors. Each weight is positive and bounded by
1/k. Dropping the favorable even sectors gives a complete-source upper
bound retaining sectors one and two exactly. Its sign remains open.
-/

namespace RHTower.ThetaCuspDefect
noncomputable section

def rawTransferSector (q : ℝ) (k : ℕ) : ℝ :=
  growthTransferFunctional q
    (spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) k)

def normalizedTransferWeight (q : ℝ) (k : ℕ) : ℝ :=
  finiteLogWeight (thetaCuspLikelihoodNormalizedMoment q 0) k*
    (thetaCuspLikelihoodPartition q)⁻¹^k/840

theorem growthTransferFunctional_normalized_power (q : ℝ) (k : ℕ) :
    growthTransferFunctional q (spectralPowerMoment (thetaCuspLikelihoodNormalizedMoment q) k)=
      (thetaCuspLikelihoodPartition q)⁻¹^k*rawTransferSector q k := by
  have hm : thetaCuspLikelihoodNormalizedMoment q=
      fun j => (thetaCuspLikelihoodPartition q)⁻¹*thetaCuspHigherLikelihoodSpectralMoment q j := by
    funext j
    unfold thetaCuspLikelihoodNormalizedMoment
    rw [div_eq_mul_inv,mul_comm]
  have hs : spectralPowerMoment
      (fun j => (thetaCuspLikelihoodPartition q)⁻¹*thetaCuspHigherLikelihoodSpectralMoment q j) k=
      fun j => (thetaCuspLikelihoodPartition q)⁻¹^k*
        spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) k j := by
    funext j
    exact spectralPowerMoment_smul _ _ _ _
  rw [hm,hs]
  exact growthTransferFunctional_smul _ _ _

theorem normalizedTransferWeight_pos {q : ℝ} (hq : 0 < q) {k : ℕ}
    (hk : 1 ≤ k ∧ k ≤ 8) : 0 < normalizedTransferWeight q k := by
  have hp := thetaCuspLikelihoodPartition_pos hq
  have hm : 0 ≤ thetaCuspLikelihoodNormalizedMoment q 0 :=
    div_nonneg (thetaCuspHigherLikelihoodSpectralMoment_nonneg 0) hp.le
  exact div_pos (mul_pos (finiteLogWeight_pos hm hk) (pow_pos (inv_pos.mpr hp) _)) (by norm_num)

theorem normalizedTransferWeight_le {q : ℝ} (hq : 0 < q) {k : ℕ}
    (hk : 1 ≤ k ∧ k ≤ 8) : normalizedTransferWeight q k ≤ 1/(k:ℝ) := by
  have hp := thetaCuspLikelihoodPartition_pos hq
  have he := thetaCuspLikelihoodPartition_eq_one_add_moment_zero hq
  have hm : 0 ≤ thetaCuspLikelihoodNormalizedMoment q 0 :=
    div_nonneg (thetaCuspHigherLikelihoodSpectralMoment_nonneg 0) hp.le
  have hm1 : thetaCuspLikelihoodNormalizedMoment q 0 ≤ 1 := by
    unfold thetaCuspLikelihoodNormalizedMoment
    rw [div_le_one hp]
    linarith
  have hr : 1-thetaCuspLikelihoodNormalizedMoment q 0=(thetaCuspLikelihoodPartition q)⁻¹ := by
    unfold thetaCuspLikelihoodNormalizedMoment
    field_simp
    linarith
  have hw := finiteLogWeight_normalized_le hm hm1 hk
  rw [hr] at hw
  unfold normalizedTransferWeight
  calc
    _ ≤ (840/(k:ℝ))/840 := div_le_div_of_nonneg_right hw (by norm_num)
    _ = _ := by ring

theorem sourceTransfer_raw_decomposition (q : ℝ) :
    growthTransferFunctional q (likelihoodCumulantEight q)=
      normalizedTransferWeight q 1*rawTransferSector q 1-
      normalizedTransferWeight q 2*rawTransferSector q 2+
      normalizedTransferWeight q 3*rawTransferSector q 3-
      normalizedTransferWeight q 4*rawTransferSector q 4+
      normalizedTransferWeight q 5*rawTransferSector q 5-
      normalizedTransferWeight q 6*rawTransferSector q 6+
      normalizedTransferWeight q 7*rawTransferSector q 7-
      normalizedTransferWeight q 8*rawTransferSector q 8 := by
  have h := growthTransferFunctional_source_decomposition q
  simp_rw [growthTransferFunctional_normalized_power] at h
  unfold normalizedTransferWeight
  linear_combination h/840

theorem normalizedTransferSector_le {q : ℝ} (hq : 3/2 ≤ q) {k : ℕ}
    (hk : 3 ≤ k ∧ k ≤ 8) :
    normalizedTransferWeight q k*rawTransferSector q k ≤
      (1/(k:ℝ))*growthTransferLeadingCoefficient q*(k:ℝ)^8*
        thetaCuspHigherLikelihoodSpectralMoment q 0^(k-1)*
        thetaCuspHigherLikelihoodSpectralMoment q 8 := by
  have hq0 : 0 < q := by linarith
  have h0 : 0 ≤ rawTransferSector q k := (sourceConvolution_transfer_bounds hq hk.1).1
  have hmoment := sourceConvolution_transfer_le hq (k-1) (by omega)
  rw [show k-1+1=k by omega] at hmoment
  calc
    _ ≤ (1/(k:ℝ))*rawTransferSector q k :=
      mul_le_mul_of_nonneg_right (normalizedTransferWeight_le hq0 (by omega)) h0
    _ ≤ (1/(k:ℝ))*(growthTransferLeadingCoefficient q*(k:ℝ)^8*
        thetaCuspHigherLikelihoodSpectralMoment q 0^(k-1)*
        thetaCuspHigherLikelihoodSpectralMoment q 8) :=
      mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ = _ := by ring

theorem sourceTransfer_signed_upper {q : ℝ} (hq : 3/2 ≤ q) :
    growthTransferFunctional q (likelihoodCumulantEight q) ≤
      normalizedTransferWeight q 1*rawTransferSector q 1-
      normalizedTransferWeight q 2*rawTransferSector q 2+
      growthTransferLeadingCoefficient q*
        ((3:ℝ)^7*thetaCuspHigherLikelihoodSpectralMoment q 0^2+
          (5:ℝ)^7*thetaCuspHigherLikelihoodSpectralMoment q 0^4+
          (7:ℝ)^7*thetaCuspHigherLikelihoodSpectralMoment q 0^6)*
        thetaCuspHigherLikelihoodSpectralMoment q 8 := by
  have hq0 : 0 < q := by linarith
  have h3 := normalizedTransferSector_le hq (k := 3) (by omega)
  have h5 := normalizedTransferSector_le hq (k := 5) (by omega)
  have h7 := normalizedTransferSector_le hq (k := 7) (by omega)
  have heven (k : ℕ) (hk : 3 ≤ k ∧ k ≤ 8) :
      0 ≤ normalizedTransferWeight q k*rawTransferSector q k :=
    mul_nonneg (normalizedTransferWeight_pos hq0 (by omega)).le
      (sourceConvolution_transfer_bounds hq hk.1).1
  have h4 := heven 4 (by omega)
  have h6 := heven 6 (by omega)
  have h8 := heven 8 (by omega)
  rw [sourceTransfer_raw_decomposition]
  norm_num at h3 h5 h7 ⊢
  nlinarith


end
end RHTower.ThetaCuspDefect
