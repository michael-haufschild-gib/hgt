import GaloisForLFunctions.RHTower.XiTransverseSpectralUniversalityLaw
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilFloorGrowthSpectrum

/-!
# Xi transverse-certificate/restricted-Weil floor growth separation

Failure of the complete transverse certificate lies strictly below the intrinsic right-Xi
transverse supremum. Under false RH that same supremum is a lower bound for the sampled and
continuous restricted-Weil growth exponents and, after adding one, for the absolute-convergence
abscissa. Eliminating the supremum transfers certificate failure into three strict growth laws.
-/

open Complex Filter Function Set LSeries
open scoped Topology ENNReal

namespace RHTower

noncomputable section

/-- **Xi transverse-certificate/restricted-Weil floor growth-separation universality law.**
Under false RH, failure of the full transverse certificate at a positive aperture forces both
restricted-Weil logarithmic growth exponents strictly past that aperture and forces the sampled
absolute-convergence abscissa strictly past one plus the aperture. -/
theorem xiTransverseCertificate_failure_forces_restrictedWeilFloor_strictGrowth
    {tau L alpha : ℝ} (htau : 0 < tau) (hL : 0 < L) (halpha : 0 < alpha)
    {N : ℕ} (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    {a b : ℕ → ℝ} (hsplit : XiRectangularNegativeChannelSplit L N a b)
    {eta : ℝ → ℝ} (heta0 : ∀ aperture, 0 ≤ eta aperture)
    (henv : XiRestrictedWeilNegativeFloorEnvelope L N
      (fun n => eta (Real.log n / 2)))
    (hnotRH : ¬ RiemannHypothesis)
    (hfailure : ¬ XiTransverseUniversalCertificate tau L alpha N a b) :
    alpha < xiRightTransverseSup ∧
      ENNReal.ofReal alpha <
        SampledUpperLogPowerExponent
          (fun n => eta (Real.log n / 2)) ∧
      ENNReal.ofReal alpha < ApertureUpperLogGrowthExponent eta ∧
      (((1 + alpha : ℝ) : EReal)) <
        LSeries.abscissaOfAbsConv
          (fun n => ((eta (Real.log n / 2) : ℝ) : ℂ)) := by
  have hzeroSup :
      XiZeroHalfPlaneBound alpha ↔
        xiRightTransverseSup ≤ alpha :=
    (xiRectangularWeilTailPowerLower_iff_all_xiZeros_re_le
      hL halpha.le).symm.trans
      (xiRectangularWeilTailPowerLower_iff_transverseSup_le_global
        hL halpha.le)
  have hcertificate :
      XiTransverseUniversalCertificate tau L alpha N a b ↔
        xiRightTransverseSup ≤ alpha :=
    (hedenmalmGaussianHankelTailCone_iff_transverseUniversalCertificate
      htau hL halpha hN hsplit).symm.trans
      ((hedenmalmGaussianHankelTailCone_iff_xiZeroHalfPlaneBound
        htau halpha.le).trans hzeroSup)
  have hbelow : alpha < xiRightTransverseSup := by
    rw [lt_iff_not_ge]
    exact fun hle => hfailure (hcertificate.mpr hle)
  have hsupPos : 0 < xiRightTransverseSup :=
    halpha.trans hbelow
  have hsample :=
    transverseSup_le_sampledUpperLogPowerExponent_of_false_rh
      hL hnotRH henv
  have haperture :=
    transverseSup_le_apertureUpperLogGrowthExponent_of_false_rh
      hL hnotRH heta0 henv
  have habscissa :=
    restrictedWeilFloor_abscissa_lower_of_not_rh
      hL hN hnotRH henv
  refine ⟨hbelow, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le
      ((ENNReal.ofReal_lt_ofReal_iff hsupPos).2 hbelow) hsample
  · exact lt_of_lt_of_le
      ((ENNReal.ofReal_lt_ofReal_iff hsupPos).2 hbelow) haperture
  · apply lt_of_lt_of_le
      (b := (((1 + xiRightTransverseSup : ℝ) : EReal)))
      ?_ habscissa
    rw [EReal.coe_lt_coe_iff]
    linarith

end

end RHTower
