import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaChannelAmplitude
import GaloisForLFunctions.RHTower.Suzuki.SuzukiHalfLogScatteringKernel

/-!
# The low-frequency term of the half-log scattering asymptotic

The two frequency channels of a homogeneous Gamma solution contribute Watson terms with conjugate
phases.  Their sum is exactly the half-log scattering map:

`∫₀^A η^{-1/2}Q(η)c₊ e^{iηL} dη + ∫₀^A t^{-1/2}Q(-t)c₋ e^{-itL} dt
    = 2π L^{-1/2} β(c₊,c₋) + O(L^{-1})`.

The error is `O(L^{-1})` with a constant depending only on the channel vectors, the operator, and
the bound on the cutoff symbol; the critical `L^{-1/2}` coefficient is the scattering map itself.
-/

open Complex Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

theorem cpow_half_pi : ((Real.pi : ℂ) ^ ((1:ℂ)/2)) = ((Real.sqrt Real.pi : ℝ) : ℂ) := by
  have hcast : ((1:ℂ)/2) = (((1:ℝ)/2 : ℝ) : ℂ) := by norm_num
  rw [hcast, ← Complex.ofReal_cpow (le_of_lt Real.pi_pos), Real.sqrt_eq_rpow]

omit [CompleteSpace X] [Nontrivial X] in
/-- **The two Watson terms assemble into the half-log scattering map.** -/
theorem watson_two_channel_sum (L : ℝ) (cp cm : X) :
    (((L ^ (-(1:ℝ)/2) : ℝ) : ℂ) * (((Real.pi : ℂ) ^ ((1:ℂ)/2))
        * Complex.exp ((Real.pi/4 : ℝ) * I))) • cp
      + watsonConstConj L • cm
      = ((2 * Real.pi * L ^ (-(1:ℝ)/2) : ℝ) : ℂ) • halfLogScatter cp cm := by
  have hs : ((Real.sqrt Real.pi : ℝ) : ℂ) * ((Real.sqrt Real.pi : ℝ) : ℂ)
      = ((Real.pi : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt Real.pi_pos)]
  have hsne : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  simp only [halfLogScatter, watsonConstConj, cpow_half_pi, smul_add, smul_smul]
  have hcast2 : ((2 * Real.pi * L ^ (-(1:ℝ)/2) : ℝ) : ℂ)
      = 2 * (((Real.sqrt Real.pi : ℝ) : ℂ) * ((Real.sqrt Real.pi : ℝ) : ℂ))
        * ((L ^ (-(1:ℝ)/2) : ℝ) : ℂ) := by
    rw [hs]
    push_cast
    ring
  congr 1
  · congr 1
    rw [hcast2]
    field_simp
  · congr 1
    rw [hcast2]
    field_simp

/-- **The low-frequency term of the half-log scattering asymptotic.**  The two channels produce
the scattering map at the critical power `L^{-1/2}`, with an `O(L^{-1})` remainder whose constant
depends only on the channel vectors, the operator, and the bound on the cutoff symbol. -/
theorem norm_lowFrequency_two_channel {T : X →L[ℂ] X} (hT : IsSelfAdjoint T)
    {r Rint : ℝ → ℝ} {cp cm : X} {A L B : ℝ}
    (hA : 0 < A) (hL : 0 < L) (hR : Rint 0 = 0)
    (hRint : ∀ x : ℝ, HasDerivAt Rint (r x) x)
    (hrb : ∀ x : ℝ, |x| ≤ A → |r x| ≤ B)
    (hrc : Continuous r) :
    ‖((∫ η in (0:ℝ)..A, scaledFresnel L η • gammaChannelAmplitude Rint T cp η)
        + ∫ t in (0:ℝ)..A, scaledFresnelConj L t • gammaChannelAmplitudeNeg Rint T cm t)
      - ((2 * Real.pi * L ^ (-(1:ℝ)/2) : ℝ) : ℂ) • halfLogScatter cp cm‖
      ≤ (‖cp‖ + ‖cm‖) * (2 * A ^ (-(1:ℝ)/2) * L ^ (-(1:ℝ)))
        + (4 * ((B / 2 + ‖T‖ / 2) * (‖cp‖ + ‖cm‖)) * A ^ ((1:ℝ)/2)) / L := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg (r 0)) (hrb 0 (by simp [hA.le]))
  have hc₀0 : (0:ℝ) ≤ B / 2 + ‖T‖ / 2 := by positivity
  -- positive channel
  have hposderiv : ∀ η : ℝ, 0 < η → η ≤ A → HasDerivAt (gammaChannelAmplitude Rint T cp)
      ((I • (shiftedSymbolOp (r η / 2) T * gammaTransport Rint T η)) cp) η :=
    fun η _ _ => hasDerivAt_gammaChannelAmplitude (hRint η)
  have hposlip : ∀ η : ℝ, 0 ≤ η → η ≤ A →
      ‖gammaChannelAmplitude Rint T cp η - gammaChannelAmplitude Rint T cp 0‖
        ≤ ((B / 2 + ‖T‖ / 2) * ‖cp‖) * η := by
    intro η hη hηA
    rw [gammaChannelAmplitude_zero hR]
    refine norm_gammaChannelAmplitude_sub_le hT hR hRint (fun x hx0 hxη => ?_) hη
    exact hrb x (by rw [abs_of_nonneg hx0]; linarith)
  have hposbound : ∀ η : ℝ, 0 < η → η ≤ A →
      ‖(I • (shiftedSymbolOp (r η / 2) T * gammaTransport Rint T η)) cp‖
        ≤ (B / 2 + ‖T‖ / 2) * ‖cp‖ := by
    intro η hη hηA
    exact norm_deriv_gammaChannelAmplitude_le hT (hrb η (by rw [abs_of_nonneg hη.le]; exact hηA))
  have hposcont : ∀ v : X, ContinuousOn (fun η : ℝ =>
      (inner ℂ v ((I • (shiftedSymbolOp (r η / 2) T * gammaTransport Rint T η)) cp) : ℂ))
      (Set.Ioc 0 A) := fun v =>
    (continuous_const.inner (continuous_deriv_gammaChannelAmplitude hrc hRint)).continuousOn
  have hposint := intervalIntegrable_scaledFresnel_smul (L := L) hA
    (by positivity : (0:ℝ) ≤ (B / 2 + ‖T‖ / 2) * ‖cp‖) hposderiv hposlip
  have hpos := norm_vector_lowFrequency_asymptotic (f := gammaChannelAmplitude Rint T cp)
    (f' := fun η => (I • (shiftedSymbolOp (r η / 2) T * gammaTransport Rint T η)) cp)
    hA hL (by positivity : (0:ℝ) ≤ (B / 2 + ‖T‖ / 2) * ‖cp‖) hposderiv hposcont hposlip
    hposbound hposint
  rw [gammaChannelAmplitude_zero hR] at hpos
  -- negative channel
  have hnegderiv : ∀ t : ℝ, 0 < t → t ≤ A → HasDerivAt (gammaChannelAmplitudeNeg Rint T cm)
      (-((I • (shiftedSymbolOp (r (-t) / 2) T * gammaTransport Rint T (-t))) cm)) t :=
    fun t _ _ => hasDerivAt_gammaChannelAmplitudeNeg (hRint (-t))
  have hneglip : ∀ t : ℝ, 0 ≤ t → t ≤ A →
      ‖gammaChannelAmplitudeNeg Rint T cm t - gammaChannelAmplitudeNeg Rint T cm 0‖
        ≤ ((B / 2 + ‖T‖ / 2) * ‖cm‖) * t := by
    intro t ht htA
    rw [gammaChannelAmplitudeNeg_zero hR]
    refine norm_gammaChannelAmplitudeNeg_sub_le hT hR hRint (fun x hx1 hx2 => ?_) ht
    exact hrb x (by rw [abs_of_nonpos hx2]; linarith)
  have hnegbound : ∀ t : ℝ, 0 < t → t ≤ A →
      ‖-((I • (shiftedSymbolOp (r (-t) / 2) T * gammaTransport Rint T (-t))) cm)‖
        ≤ (B / 2 + ‖T‖ / 2) * ‖cm‖ := by
    intro t ht htA
    rw [norm_neg]
    refine norm_deriv_gammaChannelAmplitude_le hT (hrb (-t) ?_)
    rw [abs_neg, abs_of_nonneg ht.le]
    exact htA
  have hnegcont : ∀ v : X, ContinuousOn (fun t : ℝ =>
      (inner ℂ v (-((I • (shiftedSymbolOp (r (-t) / 2) T * gammaTransport Rint T (-t))) cm)) : ℂ))
      (Set.Ioc 0 A) := by
    intro v
    have hbase : Continuous (fun t : ℝ =>
        -((I • (shiftedSymbolOp (r (-t) / 2) T * gammaTransport Rint T (-t))) cm)) :=
      ((continuous_deriv_gammaChannelAmplitude hrc hRint).comp continuous_neg).neg
    exact (continuous_const.inner hbase).continuousOn
  have hneg := norm_vector_lowFrequency_asymptotic_conj (f := gammaChannelAmplitudeNeg Rint T cm)
    (f' := fun t => -((I • (shiftedSymbolOp (r (-t) / 2) T * gammaTransport Rint T (-t))) cm))
    hA hL (by positivity : (0:ℝ) ≤ (B / 2 + ‖T‖ / 2) * ‖cm‖) hnegderiv hnegcont hneglip hnegbound
  rw [gammaChannelAmplitudeNeg_zero hR] at hneg
  -- combine
  have hsum := watson_two_channel_sum (X := X) L cp cm
  have hrearrange : ((∫ η in (0:ℝ)..A, scaledFresnel L η • gammaChannelAmplitude Rint T cp η)
        + ∫ t in (0:ℝ)..A, scaledFresnelConj L t • gammaChannelAmplitudeNeg Rint T cm t)
      - ((2 * Real.pi * L ^ (-(1:ℝ)/2) : ℝ) : ℂ) • halfLogScatter cp cm
      = ((∫ η in (0:ℝ)..A, scaledFresnel L η • gammaChannelAmplitude Rint T cp η)
          - (((L ^ (-(1:ℝ)/2) : ℝ) : ℂ) * (((Real.pi : ℂ) ^ ((1:ℂ)/2))
            * Complex.exp ((Real.pi/4 : ℝ) * I))) • cp)
        + ((∫ t in (0:ℝ)..A, scaledFresnelConj L t • gammaChannelAmplitudeNeg Rint T cm t)
          - watsonConstConj L • cm) := by
    rw [← hsum]
    abel
  rw [hrearrange]
  refine le_trans (norm_add_le _ _) ?_
  have := add_le_add hpos hneg
  refine le_trans this (le_of_eq ?_)
  field_simp

end

end GaloisForLFunctions.RHTower
