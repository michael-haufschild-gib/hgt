import GaloisForLFunctions.RHTower.SuzukiHalfLogLowFrequencyTerm
import GaloisForLFunctions.HTGeometry.HighFrequencyTransportBound

/-!
# The half-log scattering asymptotic

Splitting the oscillatory inverse Fourier integral of a homogeneous Gamma solution at a fixed
frequency cutoff, the low-frequency part produces the scattering map at the critical power and the
high-frequency part is `O(1/L)` on both rays.  Hence

`∫₀^R η^{-1/2}W_L(η)c₊ dη + ∫₀^R t^{-1/2}W_L(-t)c₋ dt = 2π L^{-1/2} β(c₊,c₋) + O(L^{-1})`,

with an explicit constant.  No frequency is discarded: the high-frequency remainder carries the
whole Gamma phase and is controlled by the exact telescoping of the shifted symbol.
-/

open Complex Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {Rint r : ℝ → ℝ} {T : X →L[ℂ] X}

omit [Nontrivial X] in
/-- The frequency propagator factors as the plain oscillation times the Gamma transport. -/
theorem freqPropagator_eq_smul_gammaTransport (L : ℝ) (η : ℝ) :
    freqPropagator L Rint T η
      = Complex.exp (((η * L : ℝ)) * I) • gammaTransport Rint T η := by
  rw [gammaTransport, freqPropagator, freqPropagator, smul_smul]
  congr 1
  rw [gammaPhase, gammaPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

omit [Nontrivial X] in
/-- The positive-ray integrand of the scattering integral is the half-power kernel against the
channel amplitude. -/
theorem halfPower_smul_freqPropagator (L : ℝ) (c : X) (η : ℝ) :
    (η ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T η c)
      = scaledFresnel L η • channelAmplitude Rint T c η := by
  rw [freqPropagator_eq_smul_gammaTransport, scaledFresnel, channelAmplitude]
  show (η ^ (-(1:ℝ)/2)) • (Complex.exp (((η * L : ℝ)) * I) • (gammaTransport Rint T η c))
      = (((η ^ (-(1:ℝ)/2) : ℝ) : ℂ) * Complex.exp (((η * L : ℝ)) * I))
        • (gammaTransport Rint T η c)
  rw [← ofReal_smul_eq, smul_smul]

omit [Nontrivial X] in
/-- The reflected integrand is the conjugate half-power kernel against the reflected amplitude. -/
theorem halfPower_smul_freqPropagator_neg (L : ℝ) (c : X) (t : ℝ) :
    (t ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T (-t) c)
      = scaledFresnelConj L t • channelAmplitudeNeg Rint T c t := by
  rw [freqPropagator_eq_smul_gammaTransport, scaledFresnelConj, channelAmplitudeNeg,
    channelAmplitude]
  show (t ^ (-(1:ℝ)/2)) • (Complex.exp (((-t * L : ℝ)) * I) • (gammaTransport Rint T (-t) c))
      = (((t ^ (-(1:ℝ)/2) : ℝ) : ℂ) * Complex.exp (-(((t * L : ℝ)) * I)))
        • (gammaTransport Rint T (-t) c)
  have hexp : Complex.exp (((-t * L : ℝ)) * I) = Complex.exp (-(((t * L : ℝ)) * I)) := by
    congr 1
    push_cast
    ring
  rw [← ofReal_smul_eq, smul_smul, hexp]

/-- **The half-log scattering asymptotic.**  The truncated oscillatory inverse Fourier integral of a
homogeneous Gamma solution equals `2πL^{-1/2}β(c₊,c₋)` up to an explicit `O(L^{-1})` remainder. -/
theorem norm_halfLog_scattering_asymptotic {r' : ℝ → ℝ} (hT : IsSelfAdjoint T)
    (hR : Rint 0 = 0) {cp cm : X} {A L R B : ℝ}
    (hA : 0 < A) (hAR : A ≤ R) (hTL : ‖T‖ / 2 < L)
    (hRint : ∀ x : ℝ, HasDerivAt Rint (r x) x)
    (hrnn : ∀ x : ℝ, 0 ≤ r x)
    (hrb : ∀ x : ℝ, |x| ≤ A → |r x| ≤ B)
    (hrc : Continuous r)
    (hr' : ∀ x : ℝ, HasDerivAt r (r' x) x)
    (hr'c : Continuous r')
    (hr'pos : ∀ x : ℝ, 0 ≤ x → 0 ≤ r' x)
    (hr'neg : ∀ x : ℝ, x ≤ 0 → r' x ≤ 0) :
    ‖((∫ η in (0:ℝ)..R, (η ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T η cp))
        + ∫ t in (0:ℝ)..R, (t ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T (-t) cm))
      - ((2 * Real.pi * L ^ (-(1:ℝ)/2) : ℝ) : ℂ) • halfLogScatter cp cm‖
      ≤ ((‖cp‖ + ‖cm‖) * (2 * A ^ (-(1:ℝ)/2) * L ^ (-(1:ℝ)))
          + (4 * ((B / 2 + ‖T‖ / 2) * (‖cp‖ + ‖cm‖)) * A ^ ((1:ℝ)/2)) / L)
        + (3 * A ^ (-(1:ℝ)/2) + R ^ (-(1:ℝ)/2)) * (L - ‖T‖ / 2)⁻¹ * (‖cp‖ + ‖cm‖) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg (r 0)) (hrb 0 (by simp [hA.le]))
  have hRpos : 0 < R := lt_of_lt_of_le hA hAR
  have hc₀ : (0:ℝ) < L - ‖T‖ / 2 := by linarith
  -- continuity of the propagator and of the half-power weights
  have hWcont : Continuous (freqPropagator L Rint T) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_freqPropagator (L := L) (Rint := Rint) (r := r) T (hRint x)).continuousAt
  have hWv : ∀ v : X, Continuous (fun η => freqPropagator L Rint T η v) := fun v =>
    (ContinuousLinearMap.apply ℂ X v).continuous.comp hWcont
  have hIccAR : uIcc A R = Icc A R := uIcc_of_le hAR
  have hposAR : ∀ x ∈ uIcc A R, 0 < x := by
    intro x hx
    rw [hIccAR] at hx
    exact lt_of_lt_of_le hA hx.1
  have hacAR : ContinuousOn (fun x : ℝ => x ^ (-(1:ℝ)/2)) (uIcc A R) := by
    intro x hx
    exact (Real.continuousAt_rpow_const x (-(1:ℝ)/2)
      (Or.inl (ne_of_gt (hposAR x hx)))).continuousWithinAt
  -- the four pieces
  have hfunpos : (fun η : ℝ => (η ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T η cp))
      = fun η : ℝ => scaledFresnel L η • channelAmplitude Rint T cp η := by
    funext η
    exact halfPower_smul_freqPropagator L cp η
  have hfunneg : (fun t : ℝ => (t ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T (-t) cm))
      = fun t : ℝ => scaledFresnelConj L t • channelAmplitudeNeg Rint T cm t := by
    funext t
    exact halfPower_smul_freqPropagator_neg L cm t
  have hposlip : ∀ η : ℝ, 0 ≤ η → η ≤ A →
      ‖channelAmplitude Rint T cp η - channelAmplitude Rint T cp 0‖
        ≤ ((B / 2 + ‖T‖ / 2) * ‖cp‖) * η := by
    intro η hη hηA
    rw [channelAmplitude_zero hR]
    refine norm_channelAmplitude_sub_le hT hR hRint (fun x hx0 hxη => ?_) hη
    exact hrb x (by rw [abs_of_nonneg hx0]; linarith)
  have hneglip : ∀ t : ℝ, 0 ≤ t → t ≤ A →
      ‖channelAmplitudeNeg Rint T cm t - channelAmplitudeNeg Rint T cm 0‖
        ≤ ((B / 2 + ‖T‖ / 2) * ‖cm‖) * t := by
    intro t ht htA
    rw [channelAmplitudeNeg_zero hR]
    refine norm_channelAmplitudeNeg_sub_le hT hR hRint (fun x hx1 hx2 => ?_) ht
    exact hrb x (by rw [abs_of_nonpos hx2]; linarith)
  have hint_pos_low : IntervalIntegrable
      (fun η : ℝ => (η ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T η cp)) volume 0 A := by
    rw [hfunpos]
    exact intervalIntegrable_scaledFresnel_smul (L := L)
      (f' := fun η => (I • (shiftedSymbolOp (r η / 2) T * gammaTransport Rint T η)) cp) hA
      (by positivity) (fun η _ _ => hasDerivAt_channelAmplitude (hRint η)) hposlip
  have hint_neg_low : IntervalIntegrable
      (fun t : ℝ => (t ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T (-t) cm)) volume 0 A := by
    rw [hfunneg]
    exact intervalIntegrable_scaledFresnelConj_smul (L := L)
      (f' := fun t => -((I • (shiftedSymbolOp (r (-t) / 2) T
        * gammaTransport Rint T (-t))) cm)) hA (by positivity)
      (fun t _ _ => hasDerivAt_channelAmplitudeNeg (hRint (-t))) hneglip
  have hint_pos_high : IntervalIntegrable
      (fun η : ℝ => (η ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T η cp)) volume A R :=
    (hacAR.smul (hWv cp).continuousOn).intervalIntegrable
  have hint_neg_high : IntervalIntegrable
      (fun t : ℝ => (t ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T (-t) cm)) volume A R := by
    refine ContinuousOn.intervalIntegrable (hacAR.smul ?_)
    exact ((hWv cm).comp continuous_neg).continuousOn
  have hsplitpos := intervalIntegral.integral_add_adjacent_intervals hint_pos_low hint_pos_high
  have hsplitneg := intervalIntegral.integral_add_adjacent_intervals hint_neg_low hint_neg_high
  -- the low-frequency term
  have hlow := norm_lowFrequency_two_channel (T := T) (r := r) (Rint := Rint) (cp := cp)
    (cm := cm) (B := B) hT hA
    (lt_of_le_of_lt (by positivity : (0:ℝ) ≤ ‖T‖ / 2) hTL) hR hRint hrb hrc
  rw [← hfunpos, ← hfunneg] at hlow
  -- the high-frequency terms
  have hrAR : ∀ x ∈ uIcc A R, HasDerivAt r (r' x) x := fun x _ => hr' x
  have hrnnAR : ∀ x ∈ uIcc A R, 0 ≤ r x := fun x _ => hrnn x
  have hr'nnAR : ∀ x ∈ uIcc A R, 0 ≤ r' x := fun x hx => hr'pos x (le_of_lt (hposAR x hx))
  have hRintAR : ∀ x ∈ uIcc A R, HasDerivAt Rint (r x) x := fun x _ => hRint x
  have hhighpos := norm_integral_halfPower_freqPropagator_apply_le (T := T) hT cp hTL hA hAR
    hrAR hrnnAR hr'nnAR hr'c.continuousOn hRintAR
  have hIccneg : uIcc (-R) (-A) = Icc (-R) (-A) := uIcc_of_le (by linarith)
  have hnegAR : ∀ x ∈ uIcc (-R) (-A), x ≤ 0 := by
    intro x hx
    rw [hIccneg] at hx
    linarith [hx.2]
  have hhighneg := norm_integral_halfPower_freqPropagator_neg_apply_le (T := T) hT cm hTL hA hAR
    (fun x _ => hr' x) (fun x _ => hrnn x)
    (Or.inr fun x hx => hr'neg x (hnegAR x hx)) hr'c.continuousOn (fun x _ => hRint x)
  have hcompneg : (∫ t in A..R, (t ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T (-t) cm))
      = ∫ η in (-R)..(-A), ((-η) ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T η cm) := by
    have h := intervalIntegral.integral_comp_neg (a := A) (b := R)
      (f := fun η : ℝ => ((-η) ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T η cm))
    simpa using h
  rw [hcompneg] at hsplitneg
  -- assemble
  have hrearr : ((∫ η in (0:ℝ)..R, (η ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T η cp))
        + ∫ t in (0:ℝ)..R, (t ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T (-t) cm))
      - ((2 * Real.pi * L ^ (-(1:ℝ)/2) : ℝ) : ℂ) • halfLogScatter cp cm
      = (((∫ η in (0:ℝ)..A, (η ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T η cp))
          + ∫ t in (0:ℝ)..A, (t ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T (-t) cm))
          - ((2 * Real.pi * L ^ (-(1:ℝ)/2) : ℝ) : ℂ) • halfLogScatter cp cm)
        + ((∫ η in A..R, (η ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T η cp))
          + ∫ η in (-R)..(-A), ((-η) ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T η cm)) := by
    rw [← hsplitpos, ← hsplitneg]
    abel
  rw [hrearr]
  refine le_trans (norm_add_le _ _) ?_
  refine add_le_add hlow ?_
  refine le_trans (norm_add_le _ _) ?_
  have hsum := add_le_add hhighpos hhighneg
  refine le_trans hsum (le_of_eq ?_)
  ring

end

end GaloisForLFunctions.RHTower
