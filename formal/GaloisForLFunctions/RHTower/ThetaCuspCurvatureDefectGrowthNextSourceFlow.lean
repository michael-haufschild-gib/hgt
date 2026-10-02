import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthNextConvolution
/-!
# Exact pair-relative derivative of the complete theta source transfer

The complete growth transfer divided by its dominant self-pair has
derivative minus an explicit positive factor times the next signed
source transfer. The latter retains all eight finite convolution sectors
and the favorable ninth-power normalization correction. Its positivity,
and thus global source-growth propagation, remains to be proved.
-/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
open Filter Set Topology
noncomputable section

def pairTransferLogNumerator (q : ℝ) : ℝ :=
  q*dominantPairPolynomialJet q-(6*q+9)*dominantPairPolynomial q

theorem hasDerivAt_dominantPairTransfer {q : ℝ} (hq : 0 < q) :
    HasDerivAt dominantPairTransfer
      (dominantAtomScale q^2*pairTransferLogNumerator q/q^10) q := by
  have ha := hasDerivAt_dominantAtomScale q
  have hp := hasDerivAt_dominantPairPolynomial q
  have h := ((ha.pow 2).mul hp).div (hasDerivAt_pow 9 q) (pow_ne_zero _ hq.ne')
  have hd : HasDerivAt (fun r => dominantAtomScale r^2*dominantPairPolynomial r/r^9)
      (dominantAtomScale q^2*pairTransferLogNumerator q/q^10) q := h.congr_deriv (by
    unfold pairTransferLogNumerator
    simp only [Pi.mul_apply,Pi.pow_apply]
    norm_num only [Nat.reduceSub,Nat.cast_ofNat,mul_one]
    field_simp [hq.ne']
    ring)
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hq] with r hr
  exact dominantPairTransfer_eq hr

def rawPairRelativeSector (q : ℝ) (k : ℕ) : ℝ :=
  pairRelativeTransferFunctional q (spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) k)

theorem hasDerivAt_rawTransferSector_relative {q : ℝ} (hq : 3/2 ≤ q) (k : ℕ) :
    HasDerivAt (fun r => rawTransferSector r k/dominantPairTransfer r)
      (-rawPairRelativeSector q k/(q*dominantPairPolynomial q*dominantPairTransfer q)) q := by
  have hq0 : 0 < q := by linarith
  have hp := dominantPairPolynomial_pos hq
  have hd : 0 < dominantPairTransfer q := growthTransferFunctional_dominant_pair_pos hq
  have ha := dominantAtomScale_pos q
  have h := (hasDerivAt_rawTransferSector hq0 k).div (hasDerivAt_dominantPairTransfer hq0) hd.ne'
  apply h.congr_deriv
  unfold rawPairRelativeSector pairTransferLogNumerator
  rw [pairRelativeTransferFunctional_flow,dominantPairTransfer_eq hq0]
  unfold rawTransferSector
  field_simp [hq0.ne',hp.ne',ha.ne']
  ring

def signedPairRelativeTransfer (q : ℝ) : ℝ :=
  normalizedTransferWeight q 1*rawPairRelativeSector q 1-
    normalizedTransferWeight q 2*rawPairRelativeSector q 2+
    normalizedTransferWeight q 3*rawPairRelativeSector q 3-
    normalizedTransferWeight q 4*rawPairRelativeSector q 4+
    normalizedTransferWeight q 5*rawPairRelativeSector q 5-
    normalizedTransferWeight q 6*rawPairRelativeSector q 6+
    normalizedTransferWeight q 7*rawPairRelativeSector q 7-
    normalizedTransferWeight q 8*rawPairRelativeSector q 8

def pairRelativeSourceTransfer (q : ℝ) : ℝ :=
  signedPairRelativeTransfer q+
    40320*q*dominantPairPolynomial q*growthTransferLeadingCoefficient q*thetaCuspLikelihoodMean q^9

theorem hasDerivAt_sourceTransfer_relative {q : ℝ} (hq : 3/2 ≤ q) :
    HasDerivAt (fun r => growthTransferFunctional r (likelihoodCumulantEight r)/dominantPairTransfer r)
      (-pairRelativeSourceTransfer q/(q*dominantPairPolynomial q*dominantPairTransfer q)) q := by
  have hq0 : 0 < q := by linarith
  have hp := dominantPairPolynomial_pos hq
  have hd : 0 < dominantPairTransfer q := growthTransferFunctional_dominant_pair_pos hq
  have hk (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 8) :=
    (hasDerivAt_normalizedTransferWeight hq0 hk).differentiableAt.hasDerivAt.mul
      (hasDerivAt_rawTransferSector_relative hq k)
  have h := (((((((hk 1 (by omega)).sub (hk 2 (by omega))).add (hk 3 (by omega))).sub
    (hk 4 (by omega))).add (hk 5 (by omega))).sub (hk 6 (by omega))).add
    (hk 7 (by omega))).sub (hk 8 (by omega))
  convert! h using 1
  · funext r
    rw [sourceTransfer_raw_decomposition]
    simp only [Pi.mul_apply,Pi.add_apply,Pi.sub_apply]
    ring
  · calc
      _ = normalizationWeightTransfer q/dominantPairTransfer q-
          signedPairRelativeTransfer q/(q*dominantPairPolynomial q*dominantPairTransfer q) := by
        unfold pairRelativeSourceTransfer
        rw [normalizationWeightTransfer_eq hq0]
        field_simp [hq0.ne',hp.ne',hd.ne']
        ring
      _ = _ := by
        unfold normalizationWeightTransfer signedPairRelativeTransfer
        ring

end
end RHTower.ThetaCuspDefect
