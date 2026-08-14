import GaloisForLFunctions.RHTower.SuzukiGammaHalfLineClassification
import GaloisForLFunctions.HTGeometry.ConjugateLowFrequencyAsymptotic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# The channel amplitude of a homogeneous Gamma solution

A homogeneous solution on a frequency half-line is the half-power weight times the channel
amplitude `a(η) = Q(η)c`, where `Q` is the Gamma transport.  On the cutoff region the symbol is
bounded, and then the amplitude is Lipschitz with the explicit constant `(B + ‖T‖)‖c‖/2`, has norm
at most `‖c‖`, and starts at the channel vector itself.  These are exactly the data the
low-frequency Watson asymptotic consumes.
-/

open Complex Set

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

/-- The channel amplitude carried by the half-power weight. -/
def channelAmplitude (Rint : ℝ → ℝ) (T : X →L[ℂ] X) (c : X) (η : ℝ) : X :=
  gammaTransport Rint T η c

variable {Rint r : ℝ → ℝ} {T : X →L[ℂ] X} {c : X}

omit [CompleteSpace X] [Nontrivial X] in
theorem channelAmplitude_zero (hR : Rint 0 = 0) : channelAmplitude Rint T c 0 = c := by
  rw [channelAmplitude, gammaTransport, freqPropagator_zero T hR]
  rfl

omit [Nontrivial X] in
theorem hasDerivAt_channelAmplitude {η : ℝ} (hRint : HasDerivAt Rint (r η) η) :
    HasDerivAt (channelAmplitude Rint T c)
      ((I • (shiftedSymbolOp (r η / 2) T * gammaTransport Rint T η)) c) η := by
  have hQ : HasDerivAt (gammaTransport Rint T)
      (I • (shiftedSymbolOp (r η / 2) T * gammaTransport Rint T η)) η := by
    have h := hasDerivAt_freqPropagator (L := 0) (Rint := Rint) (r := r) (η := η) T hRint
    rwa [zero_add] at h
  have hconst : HasDerivAt (fun _ : ℝ => c) (0 : X) η := hasDerivAt_const η c
  have h := hasDerivAt_clm_apply hQ hconst
  simp only [map_zero, add_zero] at h
  exact h

theorem norm_channelAmplitude_le (hT : IsSelfAdjoint T) (η : ℝ) :
    ‖channelAmplitude Rint T c η‖ ≤ ‖c‖ := by
  have h := ContinuousLinearMap.le_opNorm (gammaTransport Rint T η) c
  have hnorm : ‖gammaTransport Rint T η‖ = 1 := norm_freqPropagator hT 0 Rint η
  rw [hnorm, one_mul] at h
  exact h

/-- The generator of the amplitude is bounded by the symbol and the operator. -/
theorem norm_deriv_channelAmplitude_le (hT : IsSelfAdjoint T) {η B : ℝ} (hr : |r η| ≤ B) :
    ‖(I • (shiftedSymbolOp (r η / 2) T * gammaTransport Rint T η)) c‖
      ≤ (B / 2 + ‖T‖ / 2) * ‖c‖ := by
  have hnormQ : ‖gammaTransport Rint T η‖ = 1 := norm_freqPropagator hT 0 Rint η
  have hB : ‖shiftedSymbolOp (r η / 2) T‖ ≤ B / 2 + ‖T‖ / 2 := by
    rw [shiftedSymbolOp]
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖(((r η / 2 : ℝ)) : ℂ) • (1 : X →L[ℂ] X)‖ ≤ B / 2 := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, norm_one, mul_one]
      calc |r η / 2| = |r η| / 2 := by rw [abs_div, abs_two]
        _ ≤ B / 2 := by linarith
    have h2 : ‖((2⁻¹ : ℂ)) • T‖ ≤ ‖T‖ / 2 := by
      rw [norm_smul, show ‖(2⁻¹ : ℂ)‖ = 2⁻¹ by norm_num, inv_mul_eq_div]
    linarith
  calc ‖(I • (shiftedSymbolOp (r η / 2) T * gammaTransport Rint T η)) c‖
      ≤ ‖I • (shiftedSymbolOp (r η / 2) T * gammaTransport Rint T η)‖ * ‖c‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖shiftedSymbolOp (r η / 2) T * gammaTransport Rint T η‖ * ‖c‖ := by
        rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ (‖shiftedSymbolOp (r η / 2) T‖ * ‖gammaTransport Rint T η‖) * ‖c‖ := by
        gcongr
        exact norm_mul_le _ _
    _ = ‖shiftedSymbolOp (r η / 2) T‖ * ‖c‖ := by rw [hnormQ, mul_one]
    _ ≤ (B / 2 + ‖T‖ / 2) * ‖c‖ := by gcongr

/-- **The channel amplitude is Lipschitz on the cutoff region.** -/
theorem norm_channelAmplitude_sub_le (hT : IsSelfAdjoint T) (hR : Rint 0 = 0)
    {B : ℝ}
    (hRint : ∀ x : ℝ, HasDerivAt Rint (r x) x)
    (hr : ∀ x : ℝ, 0 ≤ x → |r x| ≤ B) {η : ℝ} (hη : 0 ≤ η) :
    ‖channelAmplitude Rint T c η - c‖ ≤ ((B / 2 + ‖T‖ / 2) * ‖c‖) * η := by
  have hconv : Convex ℝ (Icc (0:ℝ) η) := convex_Icc 0 η
  have hderiv : ∀ x ∈ Icc (0:ℝ) η, HasDerivWithinAt (channelAmplitude Rint T c)
      ((I • (shiftedSymbolOp (r x / 2) T * gammaTransport Rint T x)) c) (Icc (0:ℝ) η) x :=
    fun x _ => (hasDerivAt_channelAmplitude (hRint x)).hasDerivWithinAt
  have hbound : ∀ x ∈ Icc (0:ℝ) η,
      ‖(I • (shiftedSymbolOp (r x / 2) T * gammaTransport Rint T x)) c‖
        ≤ (B / 2 + ‖T‖ / 2) * ‖c‖ :=
    fun x hx => norm_deriv_channelAmplitude_le hT (hr x hx.1)
  have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (left_mem_Icc.mpr hη) (right_mem_Icc.mpr hη)
  rw [channelAmplitude_zero hR] at h
  rw [sub_zero] at h
  calc ‖channelAmplitude Rint T c η - c‖ ≤ (B / 2 + ‖T‖ / 2) * ‖c‖ * |η| := by
        simpa [Real.norm_eq_abs] using h
    _ = ((B / 2 + ‖T‖ / 2) * ‖c‖) * η := by rw [abs_of_nonneg hη]

/-- The channel amplitude of the negative frequency half-line, reflected to `t = -η ≥ 0`. -/
def channelAmplitudeNeg (Rint : ℝ → ℝ) (T : X →L[ℂ] X) (c : X) (t : ℝ) : X :=
  channelAmplitude Rint T c (-t)

omit [CompleteSpace X] [Nontrivial X] in
theorem channelAmplitudeNeg_zero (hR : Rint 0 = 0) : channelAmplitudeNeg Rint T c 0 = c := by
  rw [channelAmplitudeNeg, neg_zero, channelAmplitude_zero hR]

omit [Nontrivial X] in
theorem hasDerivAt_channelAmplitudeNeg {t : ℝ} (hRint : HasDerivAt Rint (r (-t)) (-t)) :
    HasDerivAt (channelAmplitudeNeg Rint T c)
      (-((I • (shiftedSymbolOp (r (-t) / 2) T * gammaTransport Rint T (-t))) c)) t := by
  have h := hasDerivAt_channelAmplitude (Rint := Rint) (r := r) (T := T) (c := c) hRint
  have hneg : HasDerivAt (fun x : ℝ => -x) (-1 : ℝ) t := (hasDerivAt_id t).neg
  have hcomp := h.scomp t hneg
  rw [neg_one_smul] at hcomp
  exact hcomp

/-- **The reflected channel amplitude is Lipschitz on the cutoff region.** -/
theorem norm_channelAmplitudeNeg_sub_le (hT : IsSelfAdjoint T) (hR : Rint 0 = 0) {B : ℝ}
    (hRint : ∀ x : ℝ, HasDerivAt Rint (r x) x)
    (hr : ∀ x : ℝ, |r x| ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    ‖channelAmplitudeNeg Rint T c t - c‖ ≤ ((B / 2 + ‖T‖ / 2) * ‖c‖) * t := by
  have hconv : Convex ℝ (Icc (0:ℝ) t) := convex_Icc 0 t
  have hderiv : ∀ x ∈ Icc (0:ℝ) t, HasDerivWithinAt (channelAmplitudeNeg Rint T c)
      (-((I • (shiftedSymbolOp (r (-x) / 2) T * gammaTransport Rint T (-x))) c))
      (Icc (0:ℝ) t) x :=
    fun x _ => (hasDerivAt_channelAmplitudeNeg (hRint (-x))).hasDerivWithinAt
  have hbound : ∀ x ∈ Icc (0:ℝ) t,
      ‖-((I • (shiftedSymbolOp (r (-x) / 2) T * gammaTransport Rint T (-x))) c)‖
        ≤ (B / 2 + ‖T‖ / 2) * ‖c‖ := by
    intro x _
    rw [norm_neg]
    exact norm_deriv_channelAmplitude_le hT (hr (-x))
  have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht)
  rw [channelAmplitudeNeg_zero hR, sub_zero] at h
  calc ‖channelAmplitudeNeg Rint T c t - c‖ ≤ (B / 2 + ‖T‖ / 2) * ‖c‖ * |t| := by
        simpa [Real.norm_eq_abs] using h
    _ = ((B / 2 + ‖T‖ / 2) * ‖c‖) * t := by rw [abs_of_nonneg ht]

omit [Nontrivial X] in
/-- The generator of the amplitude depends continuously on the frequency. -/
theorem continuous_deriv_channelAmplitude (hrc : Continuous r)
    (hRint : ∀ x : ℝ, HasDerivAt Rint (r x) x) :
    Continuous (fun η => (I • (shiftedSymbolOp (r η / 2) T * gammaTransport Rint T η)) c) := by
  have hQ : Continuous (gammaTransport Rint T) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have h := hasDerivAt_freqPropagator (L := 0) (Rint := Rint) (r := r) (η := x) T (hRint x)
    exact h.continuousAt
  have hB : Continuous (fun η : ℝ => shiftedSymbolOp (r η / 2) T) := by
    have h1 : Continuous (fun η : ℝ => (((r η / 2 : ℝ)) : ℂ)) :=
      Complex.continuous_ofReal.comp (hrc.div_const 2)
    have h2 : Continuous (fun η : ℝ => (((r η / 2 : ℝ)) : ℂ) • (1 : X →L[ℂ] X)) :=
      h1.smul continuous_const
    exact h2.sub continuous_const
  have hprod : Continuous (fun η : ℝ =>
      (I : ℂ) • (shiftedSymbolOp (r η / 2) T * gammaTransport Rint T η)) :=
    (hB.mul hQ).const_smul (I : ℂ)
  exact (ContinuousLinearMap.apply ℂ X c).continuous.comp hprod

end

end GaloisForLFunctions.RHTower
