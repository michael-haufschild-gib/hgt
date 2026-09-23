import GaloisForLFunctions.RHTower.DeningerGammaSixRegulatorDepthCrossover
import GaloisForLFunctions.RHTower.DeningerGammaSixGreenGibbsPhysicalReader

/-!
# Physical boundary recovery from actual adjacent-depth defects

At a common regulator tending to zero, the quotient of the complete source's
actual defects at depths `M + 1` and `M` recovers its original complex successor
ratio. No condition on the regulator/depth product is needed. A fixed nonlinear
decoder recovers the existing physical BV boundary value at the original anchor.
Every multiplicity-top Xi source supplies the required nonzero internal jet.
The actual reflected pair recovers the fixed Burnol conormal radial defect,
and finite diagonal repairs leave these readouts unchanged at late cutoffs.

Both raw defect measurements tend to zero. The literal totalized quotient decoder
is discontinuous at that zero pair, as witnessed by the actual Xi sources.
This recovers a physical value; it does not prove its vanishing or agreement with
the cyclic zero reader, and does not assert the Riemann Hypothesis.
-/

open Complex Real Filter Topology
open scoped BigOperators
namespace RHTower
noncomputable section

/-- Internal diagnostic used to prove a quotient law for actual unnormalized defects. -/
def deningerGammaSixDeattenuatedDefect (k l M : ℕ) (w : ℂ) (ε : ℝ) : ℂ :=
  (mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ M (mobiusThetaCenteredParameter w) *
    deningerOrdinaryIntegerAbelDefect ε (6 : PNat) (deningerGammaSixIntegralTailOperator k l M w) /
      (ε : ℂ)^(2 : ℕ)) / (Complex.ofReal ((6 : ℝ) ^ (-(M : ℝ) * ε)))

theorem tendsto_deningerGammaSixDeattenuatedDefect
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M) :
    Tendsto (fun M => deningerGammaSixDeattenuatedDefect k l M w (ε M)) atTop
      (𝓝 (deningerGammaSixTailBoundaryLimit k l w)) :=
  tendsto_deningerGammaSixIntegralTailOperator_crossover_deattenuated k l hw hrw ε hε hpos

/-- Adjacent depths are evaluated at the same regulator, however fast the depth/regulator product grows. -/
theorem tendsto_deningerGammaSixDeattenuatedDefect_next
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M) :
    Tendsto (fun M => deningerGammaSixDeattenuatedDefect k l (M + 1) w (ε M)) atTop
      (𝓝 (deningerGammaSixTailBoundaryLimit k l w)) := by
  have he : Tendsto (fun n : ℕ => ε (n - 1)) atTop (𝓝 0) :=
    hε.comp (tendsto_sub_atTop_nat 1)
  have hp : ∀ᶠ n : ℕ in atTop, 0 < ε (n - 1) :=
    (tendsto_sub_atTop_nat 1).eventually hpos
  have ht := (tendsto_deningerGammaSixDeattenuatedDefect k l hw hrw _ he hp).comp
    (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, Nat.add_sub_cancel] using ht

/-- Read only the two actual operator defects. No spectral parameter enters this quotient. -/
def deningerGammaSixAdjacentDefectQuotient
    (ε : ℝ) (T U : DeningerOrdinaryIntegerEnd) : ℂ :=
  deningerOrdinaryIntegerAbelDefect ε (6 : PNat) U /
    deningerOrdinaryIntegerAbelDefect ε (6 : PNat) T

theorem deningerGammaSixSuccessorNormalizer_next (M : ℕ) (w : ℂ) :
    mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ (M + 1) (mobiusThetaCenteredParameter w) =
      mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ M (mobiusThetaCenteredParameter w) *
        mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ 1 (mobiusThetaCenteredParameter w) := by
  rw [deningerGammaSixSuccessorNormalizer_pow (M + 1) w,
    deningerGammaSixSuccessorNormalizer_pow M w, pow_succ]

theorem deningerGammaSixAttenuation_next (M : ℕ) (ε : ℝ) :
    (6 : ℝ) ^ (-((M + 1 : ℕ) : ℝ) * ε) =
      (6 : ℝ) ^ (-(M : ℝ) * ε) * (6 : ℝ) ^ (-ε) := by
  rw [show -((M + 1 : ℕ) : ℝ) * ε = -(M : ℝ) * ε + (-ε) by push_cast; ring,
    Real.rpow_add (by norm_num)]

/-- The common regulator factors cancel exactly; the physical defect values remain the inputs. -/
theorem deningerGammaSixAdjacentDefectQuotient_eq
    (k l M : ℕ) (w : ℂ) {ε : ℝ} (hε : ε ≠ 0) :
    deningerGammaSixAdjacentDefectQuotient ε (deningerGammaSixIntegralTailOperator k l M w)
      (deningerGammaSixIntegralTailOperator k l (M + 1) w) =
      deningerGammaSixSuccessorRatio w * (Complex.ofReal ((6 : ℝ) ^ (-ε))) *
        (deningerGammaSixDeattenuatedDefect k l (M + 1) w ε /
          deningerGammaSixDeattenuatedDefect k l M w ε) := by
  have hN := deningerGammaSixSuccessorNormalizer_ne_zero M w
  have hN1 := deningerGammaSixSuccessorNormalizer_ne_zero 1 w
  have he : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  have hb : (Complex.ofReal ((6 : ℝ) ^ (-(M : ℝ) * ε))) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 6) (-(M : ℝ) * ε)))
  have hg : (Complex.ofReal ((6 : ℝ) ^ (-ε))) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 6) (-ε)))
  unfold deningerGammaSixAdjacentDefectQuotient deningerGammaSixDeattenuatedDefect
  rw [deningerGammaSixSuccessorNormalizer_next, deningerGammaSixAttenuation_next, Complex.ofReal_mul]
  unfold deningerGammaSixSuccessorRatio
  have hfield (a b n t e x y : ℂ) (hn : n ≠ 0) (ht : t ≠ 0)
      (he : e ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
      a / b = t⁻¹ * y * ((n * t * a / e^(2 : ℕ) / (x*y)) / (n*b/e^(2 : ℕ)/x)) := by
    by_cases hb : b = 0
    · simp only [hb, mul_zero, zero_div, div_zero]
    · field_simp
  exact hfield _ _ _ _ _ _ _ hN hN1 he hb hg

/-- Actual adjacent-depth defects recover the complex successor ratio without knowing the spectral parameter. -/
theorem tendsto_deningerGammaSixAdjacentDefectQuotient
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (hc : iteratedDeriv k XiC w * iteratedDeriv l XiC w ≠ 0)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M) :
    Tendsto (fun M => deningerGammaSixAdjacentDefectQuotient (ε M)
      (deningerGammaSixIntegralTailOperator k l M w)
      (deningerGammaSixIntegralTailOperator k l (M + 1) w)) atTop
      (𝓝 (deningerGammaSixSuccessorRatio w)) := by
  have ht := (tendsto_deningerGammaSixDeattenuatedDefect_next k l hw hrw ε hε hpos).div
    (tendsto_deningerGammaSixDeattenuatedDefect k l hw hrw ε hε hpos)
    (deningerGammaSixTailBoundaryLimit_ne_zero k l hrw hc)
  have hg : Tendsto (fun M => Complex.ofReal ((6 : ℝ) ^ (-ε M))) atTop (𝓝 1) := by
    have hcont : ContinuousAt (fun x : ℝ => (6 : ℝ) ^ (-x)) 0 := by fun_prop (disch := positivity)
    simpa only [Function.comp_def, neg_zero, Real.rpow_zero, Complex.ofReal_one] using
      (hcont.tendsto.comp hε).ofReal
  have hlim := (hg.const_mul (deningerGammaSixSuccessorRatio w)).mul ht
  simp only [div_self (deningerGammaSixTailBoundaryLimit_ne_zero k l hrw hc), mul_one] at hlim
  apply hlim.congr'
  filter_upwards [hpos] with M he
  exact (deningerGammaSixAdjacentDefectQuotient_eq k l M w (ne_of_gt he)).symm

/-- The modulus of the recovered complex ratio retains the original horizontal anchor. -/
theorem norm_deningerGammaSixSuccessorRatio (w : ℂ) :
    ‖deningerGammaSixSuccessorRatio w‖ =
      ((mobiusSuccessor 6 : ℝ) / 6) ^ (-(mobiusThetaCenteredParameter w).re) := by
  have hb := lt_trans zero_lt_one one_lt_deningerGammaSixSuccessorBase
  rw [deningerGammaSixSuccessorRatio, norm_inv,
    mobiusThetaSuccessorSpectralNormalizer, Nat.cast_one, one_mul]
  change (‖(((mobiusSuccessor 6 : ℝ) / 6 : ℝ) : ℂ) ^ mobiusThetaCenteredParameter w‖)⁻¹ = _
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hb, Real.rpow_neg hb.le]

/-- A single real exponent, fixed by the two native depth bases. -/
def deningerGammaSixPhysicalDecoderExponent : ℝ :=
  2 * Real.log 6 / Real.log ((mobiusSuccessor 6 : ℝ) / 6)

theorem deningerGammaSixPhysicalDecoderExponent_pos :
    0 < deningerGammaSixPhysicalDecoderExponent := by
  exact div_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
    (Real.log_pos one_lt_deningerGammaSixSuccessorBase)

/-- Fixed nonlinear decoder. Its only input is the measured adjacent-defect quotient. -/
def deningerGammaSixPhysicalDecoder (z : ℂ) : ℝ :=
  1 / 6 - ‖z‖ ^ deningerGammaSixPhysicalDecoderExponent

theorem continuous_deningerGammaSixPhysicalDecoder :
    Continuous deningerGammaSixPhysicalDecoder := by
  exact continuous_const.sub
    ((Real.continuous_rpow_const deningerGammaSixPhysicalDecoderExponent_pos.le).comp continuous_norm)

/-- Reexpress the existing physical BV value without moving its parameter. -/
theorem deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation_six (s : ℂ) :
    deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation 6 s =
      1 / 6 - (6 : ℝ) ^ (-2 * s.re) := by
  have hg : (deningerHalfDensityMateGain 6 s)⁻¹ = 6 * (6 : ℝ) ^ (-2*s.re) := by
    rw [deningerHalfDensityMateGain, ← Real.exp_neg,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 6)]
    simp only [Nat.cast_ofNat]
    rw [show -((2*s.re-1)*Real.log 6) = Real.log 6 + Real.log 6*(-2*s.re) by ring,
      Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 6)]
  rw [deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation, hg]
  norm_num
  ring

/-- The fixed decoder recovers the physical value at the original source parameter. -/
theorem deningerGammaSixPhysicalDecoder_successorRatio (w : ℂ) :
    deningerGammaSixPhysicalDecoder (deningerGammaSixSuccessorRatio w) =
      deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation 6 (mobiusThetaCenteredParameter w) := by
  have hb := lt_trans zero_lt_one one_lt_deningerGammaSixSuccessorBase
  have hl := (Real.log_pos one_lt_deningerGammaSixSuccessorBase).ne'
  rw [deningerGammaSixPhysicalDecoder, norm_deningerGammaSixSuccessorRatio,
    deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation_six,
    ← Real.rpow_mul hb.le, deningerGammaSixPhysicalDecoderExponent,
    Real.rpow_def_of_pos hb, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 6)]
  congr 2
  field_simp

/-- Physical boundary value reconstructed solely from adjacent actual source defects. -/
theorem tendsto_deningerGammaSixAdjacentDefect_physicalBV
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (hc : iteratedDeriv k XiC w * iteratedDeriv l XiC w ≠ 0)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M) :
    Tendsto (fun M => deningerGammaSixPhysicalDecoder
      (deningerGammaSixAdjacentDefectQuotient (ε M)
        (deningerGammaSixIntegralTailOperator k l M w)
        (deningerGammaSixIntegralTailOperator k l (M + 1) w))) atTop
      (𝓝 (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation 6 (mobiusThetaCenteredParameter w))) := by
  have h := continuous_deningerGammaSixPhysicalDecoder.continuousAt.tendsto.comp
    (tendsto_deningerGammaSixAdjacentDefectQuotient k l hw hrw hc ε hε hpos)
  simpa only [Function.comp_def, deningerGammaSixPhysicalDecoder_successorRatio] using h

/-- Every original multiplicity-top Xi source supplies the nonzero internal jet automatically. -/
theorem tendsto_deningerGammaSixAdjacentDefectQuotient_all_divisors
    (rho : XiDivisorSupport) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M) :
    Tendsto (fun M => deningerGammaSixAdjacentDefectQuotient (ε M)
      (deningerGammaSixIntegralTailOperator (xiSupportMultiplicity rho) (xiSupportMultiplicity rho) M
        (xiSpectralPointSupport rho))
      (deningerGammaSixIntegralTailOperator (xiSupportMultiplicity rho) (xiSupportMultiplicity rho) (M+1)
        (xiSpectralPointSupport rho))) atTop
      (𝓝 (deningerGammaSixSuccessorRatio (xiSpectralPointSupport rho))) := by
  have hrw : 0 < (mobiusThetaCenteredParameter (xiSpectralPointSupport rho)).re := by
    rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
    exact (xi_divisor_support_re_mem_open_unit rho).1
  exact tendsto_deningerGammaSixAdjacentDefectQuotient _ _
    (abs_im_xiSpectralPointSupport_lt_one rho) hrw
    (mul_ne_zero (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)
      (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)) ε hε hpos

/-- Apply the fixed decoder to the actual complete source at its original multiplicity and anchor. -/
def deningerGammaSixXiAdjacentPhysicalReadout (rho : XiDivisorSupport) (ε : ℝ) (M : ℕ) : ℝ :=
  deningerGammaSixPhysicalDecoder (deningerGammaSixAdjacentDefectQuotient ε
    (deningerGammaSixIntegralTailOperator (xiSupportMultiplicity rho) (xiSupportMultiplicity rho) M
      (xiSpectralPointSupport rho))
    (deningerGammaSixIntegralTailOperator (xiSupportMultiplicity rho) (xiSupportMultiplicity rho) (M+1)
      (xiSpectralPointSupport rho)))

/-- The actual source reconstructs the fixed physical BV value at every original Xi divisor. -/
theorem tendsto_deningerGammaSixXiAdjacentPhysicalReadout
    (rho : XiDivisorSupport) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M) :
    Tendsto (fun M => deningerGammaSixXiAdjacentPhysicalReadout rho (ε M) M) atTop
      (𝓝 (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation 6 (rho : ℂ))) := by
  have h := continuous_deningerGammaSixPhysicalDecoder.continuousAt.tendsto.comp
    (tendsto_deningerGammaSixAdjacentDefectQuotient_all_divisors rho ε hε hpos)
  simpa only [Function.comp_def, deningerGammaSixPhysicalDecoder_successorRatio,
    mobiusThetaCenteredParameter_xiSpectralPointSupport, deningerGammaSixXiAdjacentPhysicalReadout] using h

/-- The two actual reflected sources reconstruct the fixed Burnol conormal radial defect. -/
theorem tendsto_deningerGammaSixXiAdjacentPhysicalReadout_reflected
    (rho : XiDivisorSupport) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M) :
    Tendsto (fun M => (6 : ℝ) *
      (deningerGammaSixXiAdjacentPhysicalReadout rho (ε M) M -
        deningerGammaSixXiAdjacentPhysicalReadout (xiZeroLineConjEquiv rho) (ε M) M)) atTop
      (𝓝 (deningerBurnolActualConormalRadialReflectionDefect 6 rho)) := by
  have h := ((tendsto_deningerGammaSixXiAdjacentPhysicalReadout rho ε hε hpos).sub
    (tendsto_deningerGammaSixXiAdjacentPhysicalReadout (xiZeroLineConjEquiv rho) ε hε hpos)).const_mul 6
  rw [deningerBurnolActualConormalRadialReflectionDefect_eq_bvGreenStokes (by omega : 2 ≤ 6)]
  simpa only [xiZeroLineConjEquiv_apply, starRingEnd_apply, Nat.cast_ofNat] using h

/-- Both adjacent literal defects are unchanged by a fixed finite diagonal repair, at every regulator. -/
theorem eventually_deningerGammaSixAdjacentDefectQuotient_finite_tail_repair
    (T F : DeningerOrdinaryIntegerEnd)
    (hF : (Function.support (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a F)).Finite) :
    ∀ᶠ M : ℕ in atTop, ∀ ε : ℝ,
      deningerGammaSixAdjacentDefectQuotient ε
        (deningerOrdinaryIntegerTailProjection (6 ^ M) * (T + F))
        (deningerOrdinaryIntegerTailProjection (6 ^ (M+1)) * (T + F)) =
      deningerGammaSixAdjacentDefectQuotient ε
        (deningerOrdinaryIntegerTailProjection (6 ^ M) * T)
        (deningerOrdinaryIntegerTailProjection (6 ^ (M+1)) * T) := by
  have h := eventually_deningerOrdinaryIntegerAbelDefect_finite_tail_repair T F hF
  have hs := (tendsto_add_atTop_nat 1).eventually h
  filter_upwards [h, hs] with M hM hS
  intro ε
  unfold deningerGammaSixAdjacentDefectQuotient
  rw [hM, hS]

/-- Finite diagonal repairs preserve the reconstructed physical value at the original anchor. -/
theorem tendsto_deningerGammaSixAdjacentDefect_finite_repair_physicalBV
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (hc : iteratedDeriv k XiC w * iteratedDeriv l XiC w ≠ 0)
    (F : DeningerOrdinaryIntegerEnd)
    (hF : (Function.support (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a F)).Finite)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M) :
    Tendsto (fun M => deningerGammaSixPhysicalDecoder (deningerGammaSixAdjacentDefectQuotient (ε M)
      (deningerOrdinaryIntegerTailProjection (6 ^ M) *
        ((deningerGammaSixIntegralOperator k l w w + F) -
          (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen))
      (deningerOrdinaryIntegerTailProjection (6 ^ (M+1)) *
        ((deningerGammaSixIntegralOperator k l w w + F) -
          (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen)))) atTop
      (𝓝 (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation 6 (mobiusThetaCenteredParameter w))) := by
  have he := eventually_deningerGammaSixAdjacentDefectQuotient_finite_tail_repair
    (deningerGammaSixIntegralOperator k l w w -
      (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen) F hF
  apply (tendsto_deningerGammaSixAdjacentDefect_physicalBV k l hw hrw hc ε hε hpos).congr'
  filter_upwards [he] with M hM
  rw [show (deningerGammaSixIntegralOperator k l w w + F) -
    (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen =
      (deningerGammaSixIntegralOperator k l w w -
        (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen) + F by abel,
    hM]
  rfl

/-- Recover the literal defect from the diagnostic normalization; the original source is unchanged. -/
theorem deningerGammaSixIntegralTailOperator_defect_factor
    (k l M : ℕ) (w : ℂ) {ε : ℝ} (hε : ε ≠ 0) :
    deningerOrdinaryIntegerAbelDefect ε (6 : PNat) (deningerGammaSixIntegralTailOperator k l M w) =
      (deningerGammaSixDeattenuatedDefect k l M w ε * deningerGammaSixSuccessorRatio w ^ M *
        (ε : ℂ)^(2 : ℕ)) * Complex.ofReal ((6 : ℝ) ^ (-(M : ℝ)*ε)) := by
  have hN := deningerGammaSixSuccessorNormalizer_ne_zero M w
  have he : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  have hb : Complex.ofReal ((6 : ℝ) ^ (-(M : ℝ)*ε)) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 6) (-(M : ℝ)*ε)).ne'
  have hq : deningerGammaSixSuccessorRatio w ^ M =
      (mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ M (mobiusThetaCenteredParameter w))⁻¹ := by
    rw [deningerGammaSixSuccessorRatio, inv_pow, ← deningerGammaSixSuccessorNormalizer_pow M w]
  rw [hq, deningerGammaSixDeattenuatedDefect]
  have hf (D N e b : ℂ) (hN : N ≠ 0) (he : e ≠ 0) (hb : b ≠ 0) :
      D = ((N*D/e^(2 : ℕ)/b)*N⁻¹*e^(2 : ℕ))*b := by field_simp
  exact hf _ _ _ _ hN he hb

/-- Every actual unnormalized defect tends to zero; adjacent relative decay still carries its anchor. -/
theorem tendsto_deningerGammaSixIntegralTailOperator_defect_zero
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M) :
    Tendsto (fun M => deningerOrdinaryIntegerAbelDefect (ε M) (6 : PNat)
      (deningerGammaSixIntegralTailOperator k l M w)) atTop (𝓝 0) := by
  have hH := tendsto_deningerGammaSixDeattenuatedDefect k l hw hrw ε hε hpos
  have hq := tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    (norm_deningerGammaSixSuccessorRatio_lt_one hrw)
  have hg := ((hH.mul hq).mul (hε.ofReal.pow 2)).norm
  simp only [mul_zero, Complex.ofReal_zero, zero_pow (by omega : 2 ≠ 0), norm_zero] at hg
  apply squeeze_zero_norm' _ hg
  filter_upwards [hpos] with M he
  rw [deningerGammaSixIntegralTailOperator_defect_factor k l M w he.ne', norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 6) _)]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg M)) he.le))

/-- Both actual adjacent measurements approach the same zero pair at a common regulator. -/
theorem tendsto_deningerGammaSixIntegralTailOperator_defect_pair_zero
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M) :
    Tendsto (fun M =>
      (deningerOrdinaryIntegerAbelDefect (ε M) (6 : PNat) (deningerGammaSixIntegralTailOperator k l M w),
       deningerOrdinaryIntegerAbelDefect (ε M) (6 : PNat) (deningerGammaSixIntegralTailOperator k l (M+1) w)))
      atTop (𝓝 (0, 0)) := by
  have he := hε.comp (tendsto_sub_atTop_nat 1)
  have hp := (tendsto_sub_atTop_nat 1).eventually hpos
  have hs := (tendsto_deningerGammaSixIntegralTailOperator_defect_zero k l hw hrw
    (fun n : ℕ => ε (n-1)) he hp).comp (tendsto_add_atTop_nat 1)
  simp only [Function.comp_def, Nat.add_sub_cancel] at hs
  exact (tendsto_deningerGammaSixIntegralTailOperator_defect_zero k l hw hrw ε hε hpos).prodMk_nhds hs

/-- The zero pair has a decoder value different from every finite original physical parameter. -/
theorem deningerGammaSixPhysicalDecoder_zero_ne_physicalBV (s : ℂ) :
    deningerGammaSixPhysicalDecoder 0 ≠ deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation 6 s := by
  rw [deningerGammaSixPhysicalDecoder, norm_zero,
    Real.zero_rpow deningerGammaSixPhysicalDecoderExponent_pos.ne', sub_zero,
    deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation_six]
  have hp := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 6) (-2*s.re)
  linarith

/-- The actual Xi source witnesses discontinuity of the literal totalized quotient decoder at the zero pair. -/
theorem deningerGammaSixAdjacentPhysicalDecoder_not_continuousAt_zero
    (rho : XiDivisorSupport) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M) :
    ¬ ContinuousAt (fun p : ℂ × ℂ => deningerGammaSixPhysicalDecoder (p.2 / p.1)) (0, 0) := by
  intro hc
  have hrw : 0 < (mobiusThetaCenteredParameter (xiSpectralPointSupport rho)).re := by
    rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
    exact (xi_divisor_support_re_mem_open_unit rho).1
  have hz := hc.tendsto.comp (tendsto_deningerGammaSixIntegralTailOperator_defect_pair_zero
    (xiSupportMultiplicity rho) (xiSupportMultiplicity rho)
    (abs_im_xiSpectralPointSupport_lt_one rho) hrw ε hε hpos)
  have hp := tendsto_deningerGammaSixXiAdjacentPhysicalReadout rho ε hε hpos
  have hz' : Tendsto (fun M => deningerGammaSixXiAdjacentPhysicalReadout rho (ε M) M) atTop
      (𝓝 (deningerGammaSixPhysicalDecoder 0)) := by
    simpa only [Function.comp_def, zero_div, deningerGammaSixXiAdjacentPhysicalReadout,
      deningerGammaSixAdjacentDefectQuotient] using hz
  exact deningerGammaSixPhysicalDecoder_zero_ne_physicalBV (rho : ℂ) (tendsto_nhds_unique hz' hp)

end
end RHTower
