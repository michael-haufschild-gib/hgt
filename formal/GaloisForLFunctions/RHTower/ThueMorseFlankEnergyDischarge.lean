import GaloisForLFunctions.RHTower.ThueMorseMellinFlatness
import GaloisForLFunctions.RHTower.L2FourierIntegralBridge
import GaloisForLFunctions.RHTower.PerronCarrierFlankMass
import GaloisForLFunctions.RHTower.XiThetaCriticalTrace
import GaloisForLFunctions.RHTower.XiThetaPositiveL2Perron

/-!
# Thue--Morse Mellin carrier discharges Perron flank L2 energy

The concrete Thue--Morse kernel is Mellin-convergent at every complex parameter.  At the negative
integer line `-M+iy`, its Mellin transform is the Fourier transform of the logarithmic source
`u ↦ exp(Mu) K(exp(-u))`, evaluated at `y/(2π)`.  Mellin convergence at depths `M` and `2M`,
together with `norm K ≤ 1`, makes this source both `L¹` and `L²`.  The existing Fourier bridge and
Plancherel then put every negative vertical trace in `L²`, supplying the previously uninhabited
Perron flank-energy interface with a nonzero entire carrier.
-/

open Complex Real MeasureTheory Set Filter Topology FourierTransform
open scoped ENNReal Topology FourierTransform

namespace RHTower

noncomputable section

/-- The logarithmic source whose Fourier transform is the depth-`M` Mellin trace. -/
noncomputable def thueMorseNegativeMellinSource (M : ℕ) (u : ℝ) : ℂ :=
  Real.exp ((M : ℝ) * u) • thueMorseMellinKernel (Real.exp (-u))

theorem thueMorseNegativeMellinSource_eq_complexExp (M : ℕ) (u : ℝ) :
    thueMorseNegativeMellinSource M u =
      Complex.exp ((M : ℂ) * (u : ℂ)) * thueMorseMellinKernel (Real.exp (-u)) := by
  rw [thueMorseNegativeMellinSource, Complex.real_smul, Complex.ofReal_exp,
    Complex.ofReal_mul]
  norm_cast

/-- Mellin convergence at `-M` supplies `L¹` of the logarithmic source. -/
theorem thueMorseNegativeMellinSource_integrable (M : ℕ) :
    Integrable (thueMorseNegativeMellinSource M) := by
  have hconv : MellinConvergent thueMorseMellinKernel ((-(M : ℝ) : ℝ) : ℂ) := by
    simpa using
      thueMorseMellinKernel_isMellinFlatKernel.mellinConvergent (-(M : ℝ) : ℂ)
  have h := integrable_logMellinPullback_of_mellinConvergent
    thueMorseMellinKernel (-(M : ℝ)) hconv
  simpa only [neg_mul, neg_neg, thueMorseNegativeMellinSource] using h

/-- Mellin convergence at `-2M` and `norm K ≤ 1` promote the same source to `L²`. -/
theorem thueMorseNegativeMellinSource_memLp_two (M : ℕ) :
    MemLp (thueMorseNegativeMellinSource M) 2 volume := by
  have hmeas : AEStronglyMeasurable (thueMorseNegativeMellinSource M) volume :=
    (thueMorseNegativeMellinSource_integrable M).1
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  have hconv : MellinConvergent thueMorseMellinKernel ((-(2 * M : ℝ) : ℝ) : ℂ) := by
    simpa using
      thueMorseMellinKernel_isMellinFlatKernel.mellinConvergent (-(2 * M : ℝ) : ℂ)
  have hdom := integrable_logMellinPullback_of_mellinConvergent
    thueMorseMellinKernel (-(2 * M : ℝ)) hconv
  have hdomNorm : Integrable (fun u : ℝ =>
      Real.exp ((2 * M : ℝ) * u) *
        ‖thueMorseMellinKernel (Real.exp (-u))‖) := by
    simpa only [neg_mul, neg_neg, norm_smul,
      Real.norm_of_nonneg (Real.exp_nonneg _)] using hdom.norm
  refine hdomNorm.mono' (hmeas.norm.pow 2) (Eventually.of_forall fun u => ?_)
  have hK0 : 0 ≤ ‖thueMorseMellinKernel (Real.exp (-u))‖ := norm_nonneg _
  have hK1 : ‖thueMorseMellinKernel (Real.exp (-u))‖ ≤ 1 :=
    thueMorseMellinKernel_norm_le_one _
  rw [Real.norm_of_nonneg (sq_nonneg _), thueMorseNegativeMellinSource,
    norm_smul,
    Real.norm_of_nonneg (Real.exp_nonneg _)]
  change (Real.exp ((M : ℝ) * u) *
      ‖thueMorseMellinKernel (Real.exp (-u))‖) ^ 2 ≤
    Real.exp ((2 * M : ℝ) * u) * ‖thueMorseMellinKernel (Real.exp (-u))‖
  rw [mul_pow, ← Real.exp_nat_mul]
  ring_nf
  apply mul_le_mul_of_nonneg_left (by nlinarith) (Real.exp_pos _).le

/-- Exact Mellin--Fourier identity on the negative integer line. -/
theorem mellin_thueMorseMellinKernel_neg_line_eq_fourier (M : ℕ) (y : ℝ) :
    mellin thueMorseMellinKernel (↑(-(M : ℝ)) + ↑y * I) =
      𝓕 (thueMorseNegativeMellinSource M) (y / (2 * Real.pi)) := by
  have hsource :
      (fun u : ℝ => Real.exp
        (-(↑(-(M : ℝ)) + ↑y * I : ℂ).re * u) •
          thueMorseMellinKernel (Real.exp (-u))) =
        thueMorseNegativeMellinSource M := by
    funext u
    simp [thueMorseNegativeMellinSource]
  rw [mellin_eq_fourier]
  rw [hsource]
  simp

/-- Every negative-integer vertical trace of the concrete entire Mellin carrier belongs to `L²`. -/
theorem thueMorseMellinCarrier_negativeLine_memLp_two (M : ℕ) :
    MemLp (fun y : ℝ =>
      mellin thueMorseMellinKernel (↑(-(M : ℝ)) + ↑y * I)) 2 volume := by
  let g : ℝ → ℂ := thueMorseNegativeMellinSource M
  have hg1 : Integrable g := thueMorseNegativeMellinSource_integrable M
  have hg2 : MemLp g 2 volume := thueMorseNegativeMellinSource_memLp_two M
  let g2 : Lp ℂ 2 volume := hg2.toLp g
  have hcoe : (g2 : ℝ → ℂ) =ᵐ[volume] g := by
    simpa [g2] using hg2.coeFn_toLp
  have hg2int : Integrable (g2 : ℝ → ℂ) := hg1.congr hcoe.symm
  have hfourAE : ((𝓕 g2 : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] 𝓕 g := by
    calc
      ((𝓕 g2 : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume]
          (Real.Lp.fourierTransform
            ((memLp_one_iff_integrable.mpr hg2int).toLp g2) : ℝ → ℂ) :=
        l2_fourier_coeFn_eq_l1_fourier_of_integrable g2 hg2int
      _ =ᵐ[volume] 𝓕 g := Eventually.of_forall fun x => by
        rw [Real.fourierTransform_toLp]
        exact Real.fourier_congr_ae hcoe x
  have hfourMem : MemLp (𝓕 g) 2 volume :=
    (memLp_congr_ae hfourAE).mp (Lp.memLp (𝓕 g2))
  have hfourMeas : AEStronglyMeasurable (𝓕 g) volume := hfourMem.1
  have hfourSq : Integrable (fun x : ℝ => ‖𝓕 g x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hfourMeas).mp hfourMem
  have hscaleNe : (2 * Real.pi)⁻¹ ≠ 0 :=
    inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hscaledSq : Integrable (fun y : ℝ => ‖𝓕 g (y / (2 * Real.pi))‖ ^ 2) := by
    have hcomp := hfourSq.comp_mul_left' hscaleNe
    simpa [div_eq_mul_inv, mul_comm] using hcomp
  have hscaledMeas : AEStronglyMeasurable
      (fun y : ℝ => 𝓕 g (y / (2 * Real.pi))) volume := by
    exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hg1).comp_aestronglyMeasurable (by fun_prop)
  have hscaledMem : MemLp (fun y : ℝ => 𝓕 g (y / (2 * Real.pi))) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hscaledMeas).2 hscaledSq
  apply (memLp_congr_ae (Eventually.of_forall fun y =>
    mellin_thueMorseMellinKernel_neg_line_eq_fourier M y)).mpr
  simpa [g] using hscaledMem

/-- The exact `L²` line norm used as the Perron energy budget. -/
noncomputable def thueMorseMellinCarrierFlankL2Budget (M : ℕ) : ℝ :=
  Real.sqrt (∫ y : ℝ,
    ‖mellin thueMorseMellinKernel (↑(-(M : ℝ)) + ↑y * I)‖ ^ 2)

/-- The pointwise Perron flank-energy interface is unconditional for the Thue--Morse carrier. -/
theorem thueMorseMellinCarrier_hasPerronCarrierFlankL2EnergyAt (M : ℕ) :
    HasPerronCarrierFlankL2EnergyAt (mellin thueMorseMellinKernel) M
      (thueMorseMellinCarrierFlankL2Budget M) := by
  have hmem := thueMorseMellinCarrier_negativeLine_memLp_two M
  have hmeas : AEStronglyMeasurable (fun y : ℝ =>
      mellin thueMorseMellinKernel (↑(-(M : ℝ)) + ↑y * I)) volume := hmem.1
  refine ⟨(memLp_two_iff_integrable_sq_norm hmeas).mp hmem, ?_⟩
  exact le_rfl

/-- The eventual Perron flank-energy interface is inhabited at every depth. -/
theorem thueMorseMellinCarrier_hasPerronCarrierFlankL2Energy :
    HasPerronCarrierFlankL2Energy (mellin thueMorseMellinKernel)
      thueMorseMellinCarrierFlankL2Budget :=
  Eventually.of_forall thueMorseMellinCarrier_hasPerronCarrierFlankL2EnergyAt

/-! ### Canonical nonzero-source cross-line seam -/

/-- At every depth, the concrete Thue--Morse line splits canonically against the nonzero positive
theta source.  The cross-line defect predicate is therefore constructed rather than assumed. -/
theorem thueMorseMellinCarrier_hasCrossLineMellinDefectAt (M : ℕ) :
    HasCrossLineMellinDefectAt (mellin thueMorseMellinKernel)
      xiThetaPositiveSourceL2 0 xiThetaPositiveSourceL2_hasAELowerSupport
      (canonicalCrossLineMellinDefect (mellin thueMorseMellinKernel)
        xiThetaPositiveSourceL2 0 xiThetaPositiveSourceL2_hasAELowerSupport) M :=
  hasCrossLineMellinDefectAt_canonical_of_flankL2EnergyAt
    xiThetaPositiveSourceL2_hasAELowerSupport
    thueMorseMellinKernel_isMellinFlatKernel.mellin_differentiable
    (thueMorseMellinCarrier_hasPerronCarrierFlankL2EnergyAt M)

/-- The concrete Thue--Morse carrier has an all-depth canonical cross-line decomposition against
the positive theta source. -/
theorem thueMorseMellinCarrier_hasCrossLineMellinDefect :
    HasCrossLineMellinDefect (mellin thueMorseMellinKernel)
      xiThetaPositiveSourceL2 0 xiThetaPositiveSourceL2_hasAELowerSupport
      (canonicalCrossLineMellinDefect (mellin thueMorseMellinKernel)
        xiThetaPositiveSourceL2 0 xiThetaPositiveSourceL2_hasAELowerSupport) :=
  thueMorseMellinCarrier_hasCrossLineMellinDefectAt

/-- In particular, the eventual cross-line interface consumed by asymptotic extraction is
unconditional for the concrete Thue--Morse carrier and positive theta source. -/
theorem thueMorseMellinCarrier_hasEventuallyCrossLineMellinDefect :
    HasEventuallyCrossLineMellinDefect (mellin thueMorseMellinKernel)
      xiThetaPositiveSourceL2 0 xiThetaPositiveSourceL2_hasAELowerSupport
      (canonicalCrossLineMellinDefect (mellin thueMorseMellinKernel)
        xiThetaPositiveSourceL2 0 xiThetaPositiveSourceL2_hasAELowerSupport) :=
  thueMorseMellinCarrier_hasCrossLineMellinDefect.hasEventually

end

end RHTower
