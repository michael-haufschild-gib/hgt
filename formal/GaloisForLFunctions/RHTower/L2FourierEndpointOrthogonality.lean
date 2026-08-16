import GaloisForLFunctions.RHTower.L2MellinUnitary
import GaloisForLFunctions.RHTower.L2FourierReflection
import GaloisForLFunctions.HTGeometry.L2DerivativeFourier

/-!
# Endpoint orthogonality for bandlimited L² states

If an L²(ℝ) Fourier transform is supported in [-b, b], then its translate by 2b has
disjoint support except at the null singleton {-b}. Plancherel turns this into exact
orthogonality between a state and its modulation by frequency -2b. For a real state, taking
real parts gives vanishing of the cosine coefficient of its squared magnitude at physical
frequency 4πb.

This is a measure-theoretic endpoint theorem. No pointwise Fourier inversion or computation is
used.
-/

noncomputable section

open MeasureTheory Set FourierTransform
open scoped ENNReal

namespace RHTower
namespace MellinL2

theorem l2Reflection_additiveTranslation (a : ℝ) (f : Lp (α := ℝ) ℂ 2) :
    l2Reflection (additiveTranslationUnitary a f) =
      additiveTranslationUnitary (-a) (l2Reflection f) := by
  change Lp.compMeasurePreserving (fun x : ℝ => -x) _
      (Lp.compMeasurePreserving (realTranslationEquiv a) _ f) =
    Lp.compMeasurePreserving (realTranslationEquiv (-a)) _
      (Lp.compMeasurePreserving (fun x : ℝ => -x) _ f)
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (realTranslationEquiv a)
        (realTranslation_measurePreserving a) f)
      (Measure.measurePreserving_neg (volume : Measure ℝ)),
    (Lp.coeFn_compMeasurePreserving f (realTranslation_measurePreserving a)).comp_tendsto
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae,
    Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (fun x : ℝ => -x)
        (Measure.measurePreserving_neg (volume : Measure ℝ)) f)
      (realTranslation_measurePreserving (-a)),
    (Lp.coeFn_compMeasurePreserving f
      (Measure.measurePreserving_neg (volume : Measure ℝ))).comp_tendsto
        (realTranslation_measurePreserving (-a)).quasiMeasurePreserving.tendsto_ae]
    with x hl hla hr hra
  rw [hl, hla, hr, hra]
  change f (-x + a) = f (-(x + -a))
  congr 1
  ring

theorem l2Reflection_fourierInv (f : Lp (α := ℝ) ℂ 2) :
    l2Reflection (𝓕⁻ f) = 𝓕 f := by
  have h := l2_fourier_fourier (𝓕⁻ f)
  have hinv : 𝓕 (𝓕⁻ f : Lp ℂ 2 (volume : Measure ℝ)) = f :=
    fourier_fourierInv_eq f
  change (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) (𝓕⁻ f) = f at hinv
  rw [hinv] at h
  exact h.symm

/-- Two possibly different Fourier-band states are orthogonal after translation by the extreme
difference frequency. -/
theorem inner_additiveTranslation_two_mul_eq_zero_of_two_bandSupports
    {b : ℝ} (hb : 0 ≤ b) (u v : Lp (α := ℝ) ℂ 2)
    (hu : ∀ᵐ x : ℝ, b < |x| → u x = 0)
    (hv : ∀ᵐ x : ℝ, b < |x| → v x = 0) :
    inner ℂ u (additiveTranslationUnitary (2 * b) v) = 0 := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_eq_zero_of_ae
  have hvshift : ∀ᵐ x : ℝ, b < |x + 2 * b| → v (x + 2 * b) = 0 := by
    simpa [Function.comp_def, realTranslationEquiv] using
      (realTranslation_measurePreserving (2 * b)).quasiMeasurePreserving.ae hv
  filter_upwards [hu, hvshift, (volume : Measure ℝ).ae_ne (-b),
    Lp.coeFn_compMeasurePreserving v (realTranslation_measurePreserving (2 * b))]
    with x hx hxshift hxne htrans
  have htrans' : (additiveTranslationUnitary (2 * b) v) x = v (x + 2 * b) := by
    simpa [additiveTranslationUnitary, lpCompMeasurePreservingEquiv,
      Function.comp_def, realTranslationEquiv] using htrans
  rw [htrans']
  by_cases hout : b < |x|
  · rw [hx hout]
    simp
  · have hxb : |x| ≤ b := le_of_not_gt hout
    have hxlo : -b ≤ x := (abs_le.mp hxb).1
    have hxstrict : -b < x := lt_of_le_of_ne hxlo (Ne.symm hxne)
    have hshiftout : b < |x + 2 * b| := by
      rw [abs_of_nonneg]
      · linarith
      · linarith
    rw [hxshift hshiftout]
    simp

/-- The L² modulation law dual to fourier_additiveTranslation. -/
theorem fourier_fourierPhaseMulUnitary (a : ℝ) (f : Lp (α := ℝ) ℂ 2) :
    𝓕 (fourierPhaseMulUnitary a f) =
      additiveTranslationUnitary (-a) (𝓕 f) := by
  have htranslate := fourier_additiveTranslation a (𝓕⁻ f)
  have hphase : fourierPhaseMulUnitary a f =
      𝓕 (additiveTranslationUnitary a (𝓕⁻ f)) := by
    simpa using htranslate.symm
  calc
    𝓕 (fourierPhaseMulUnitary a f) =
        𝓕 (𝓕 (additiveTranslationUnitary a (𝓕⁻ f))) := congrArg 𝓕 hphase
    _ = l2Reflection (additiveTranslationUnitary a (𝓕⁻ f)) :=
      l2_fourier_fourier _
    _ = additiveTranslationUnitary (-a) (l2Reflection (𝓕⁻ f)) :=
      l2Reflection_additiveTranslation a _
    _ = additiveTranslationUnitary (-a) (𝓕 f) := by
      rw [l2Reflection_fourierInv]

/-- Two states with the same Fourier band are orthogonal after modulation by its extreme
difference frequency. -/
theorem inner_fourierPhaseMul_neg_two_mul_eq_zero_of_two_bandSupports
    {b : ℝ} (hb : 0 ≤ b) (u v : Lp (α := ℝ) ℂ 2)
    (hu : ∀ᵐ x : ℝ, b < |x| →
      (𝓕 u : Lp ℂ 2 (volume : Measure ℝ)) x = 0)
    (hv : ∀ᵐ x : ℝ, b < |x| →
      (𝓕 v : Lp ℂ 2 (volume : Measure ℝ)) x = 0) :
    inner ℂ u (fourierPhaseMulUnitary (-2 * b) v) = 0 := by
  rw [← MeasureTheory.Lp.inner_fourier_eq]
  rw [fourier_fourierPhaseMulUnitary]
  have hshift : -(-2 * b) = 2 * b := by ring
  rw [hshift]
  exact inner_additiveTranslation_two_mul_eq_zero_of_two_bandSupports
    hb (𝓕 u) (𝓕 v) hu hv

/-- A Fourier support in [-b,b] is orthogonal to its translate by 2b. Their possible
intersection is the singleton endpoint {-b}, which is null for Lebesgue measure. -/
theorem inner_additiveTranslation_two_mul_eq_zero_of_bandSupport
    {b : ℝ} (hb : 0 ≤ b) (v : Lp (α := ℝ) ℂ 2)
    (hv : ∀ᵐ x : ℝ, b < |x| → v x = 0) :
    inner ℂ v (additiveTranslationUnitary (2 * b) v) = 0 := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_eq_zero_of_ae
  have hvshift : ∀ᵐ x : ℝ, b < |x + 2 * b| → v (x + 2 * b) = 0 := by
    simpa [Function.comp_def, realTranslationEquiv] using
      (realTranslation_measurePreserving (2 * b)).quasiMeasurePreserving.ae hv
  filter_upwards [hv, hvshift, (volume : Measure ℝ).ae_ne (-b),
    Lp.coeFn_compMeasurePreserving v (realTranslation_measurePreserving (2 * b))]
    with x hx hxshift hxne htrans
  have htrans' : (additiveTranslationUnitary (2 * b) v) x = v (x + 2 * b) := by
    simpa [additiveTranslationUnitary, lpCompMeasurePreservingEquiv,
      Function.comp_def, realTranslationEquiv] using htrans
  rw [htrans']
  by_cases hout : b < |x|
  · rw [hx hout]
    simp
  · have hxb : |x| ≤ b := le_of_not_gt hout
    have hxlo : -b ≤ x := (abs_le.mp hxb).1
    have hxstrict : -b < x := lt_of_le_of_ne hxlo (Ne.symm hxne)
    have hshiftout : b < |x + 2 * b| := by
      rw [abs_of_nonneg]
      · linarith
      · linarith
    rw [hxshift hshiftout]
    simp

/-- A state whose Fourier transform is supported in [-b,b] is orthogonal to its modulation by
the extreme difference frequency -2b. -/
theorem inner_fourierPhaseMul_neg_two_mul_eq_zero_of_bandSupport
    {b : ℝ} (hb : 0 ≤ b) (u : Lp (α := ℝ) ℂ 2)
    (hu : ∀ᵐ x : ℝ, b < |x| → (𝓕 u : Lp ℂ 2 (volume : Measure ℝ)) x = 0) :
    inner ℂ u (fourierPhaseMulUnitary (-2 * b) u) = 0 := by
  rw [← MeasureTheory.Lp.inner_fourier_eq]
  rw [fourier_fourierPhaseMulUnitary]
  have hshift : -(-2 * b) = 2 * b := by ring
  rw [hshift]
  exact inner_additiveTranslation_two_mul_eq_zero_of_bandSupport hb (𝓕 u) hu

/-- Real endpoint form: if g has mathlib Fourier support in [-b,b], then the physical
frequency-4πb cosine coefficient of g² vanishes exactly. -/
theorem integral_sq_mul_cos_four_pi_eq_zero_of_bandSupport
    {b : ℝ} (hb : 0 ≤ b) {g : ℝ → ℝ} (hg : MemLp g 2 volume)
    (hband : ∀ᵐ ξ : ℝ, b < |ξ| →
      (𝓕 (GaloisForLFunctions.HTGeometry.ofRealLp (hg.toLp g)) :
        Lp ℂ 2 (volume : Measure ℝ)) ξ = 0) :
    ∫ x : ℝ, g x ^ 2 * Real.cos (4 * Real.pi * b * x) = 0 := by
  let uR : Lp ℝ 2 (volume : Measure ℝ) := hg.toLp g
  let uC : Lp ℂ 2 (volume : Measure ℝ) :=
    GaloisForLFunctions.HTGeometry.ofRealLp uR
  have hinner : inner ℂ uC (fourierPhaseMulUnitary (-2 * b) uC) = 0 := by
    apply inner_fourierPhaseMul_neg_two_mul_eq_zero_of_bandSupport hb uC
    simpa [uC, uR] using hband
  rw [MeasureTheory.L2.inner_def] at hinner
  have hint := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) uC
    (fourierPhaseMulUnitary (-2 * b) uC)
  have hreal : (∫ x : ℝ, RCLike.re
      (inner ℂ (uC x) ((fourierPhaseMulUnitary (-2 * b) uC) x))) = 0 := by
    rw [integral_re hint, hinner]
    rfl
  have hae : ∀ᵐ x : ℝ,
      RCLike.re (inner ℂ (uC x) ((fourierPhaseMulUnitary (-2 * b) uC) x)) =
        g x ^ 2 * Real.cos (4 * Real.pi * b * x) := by
    filter_upwards [
      GaloisForLFunctions.HTGeometry.coeFn_ofRealLp uR,
      hg.coeFn_toLp,
      fourierPhaseMulAux_ae (-2 * b) uC]
      with x huC huR hphase
    change RCLike.re (inner ℂ (uC x) (fourierPhaseMulAux (-2 * b) uC x)) = _
    rw [hphase, huC, huR]
    simp only [RCLike.inner_apply', starRingEnd_apply, fourierPhase,
      Real.fourierChar_apply]
    simp [Complex.mul_re, Complex.exp_re, Complex.exp_im]
    ring_nf
  calc
    (∫ x : ℝ, g x ^ 2 * Real.cos (4 * Real.pi * b * x)) =
        ∫ x : ℝ, RCLike.re
          (inner ℂ (uC x) ((fourierPhaseMulUnitary (-2 * b) uC) x)) :=
      integral_congr_ae (hae.mono fun _ hx => hx.symm)
    _ = 0 := hreal

/-- Real bilinear endpoint form: the extreme cosine coefficient of the product of two states
with the same Fourier band vanishes. -/
theorem integral_mul_mul_cos_four_pi_eq_zero_of_two_bandSupports
    {b : ℝ} (hb : 0 ≤ b) {g h : ℝ → ℝ}
    (hg : MemLp g 2 volume) (hh : MemLp h 2 volume)
    (hbandg : ∀ᵐ ξ : ℝ, b < |ξ| →
      (𝓕 (GaloisForLFunctions.HTGeometry.ofRealLp (hg.toLp g)) :
        Lp ℂ 2 (volume : Measure ℝ)) ξ = 0)
    (hbandh : ∀ᵐ ξ : ℝ, b < |ξ| →
      (𝓕 (GaloisForLFunctions.HTGeometry.ofRealLp (hh.toLp h)) :
        Lp ℂ 2 (volume : Measure ℝ)) ξ = 0) :
    ∫ x : ℝ, (g x * h x) * Real.cos (4 * Real.pi * b * x) = 0 := by
  let uR : Lp ℝ 2 (volume : Measure ℝ) := hg.toLp g
  let vR : Lp ℝ 2 (volume : Measure ℝ) := hh.toLp h
  let uC : Lp ℂ 2 (volume : Measure ℝ) :=
    GaloisForLFunctions.HTGeometry.ofRealLp uR
  let vC : Lp ℂ 2 (volume : Measure ℝ) :=
    GaloisForLFunctions.HTGeometry.ofRealLp vR
  have hinner : inner ℂ uC (fourierPhaseMulUnitary (-2 * b) vC) = 0 := by
    apply inner_fourierPhaseMul_neg_two_mul_eq_zero_of_two_bandSupports hb uC vC
    · simpa [uC, uR] using hbandg
    · simpa [vC, vR] using hbandh
  rw [MeasureTheory.L2.inner_def] at hinner
  have hint := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) uC
    (fourierPhaseMulUnitary (-2 * b) vC)
  have hreal : (∫ x : ℝ, RCLike.re
      (inner ℂ (uC x) ((fourierPhaseMulUnitary (-2 * b) vC) x))) = 0 := by
    rw [integral_re hint, hinner]
    rfl
  have hae : ∀ᵐ x : ℝ,
      RCLike.re (inner ℂ (uC x) ((fourierPhaseMulUnitary (-2 * b) vC) x)) =
        (g x * h x) * Real.cos (4 * Real.pi * b * x) := by
    filter_upwards [
      GaloisForLFunctions.HTGeometry.coeFn_ofRealLp uR,
      GaloisForLFunctions.HTGeometry.coeFn_ofRealLp vR,
      hg.coeFn_toLp,
      hh.coeFn_toLp,
      fourierPhaseMulAux_ae (-2 * b) vC]
      with x huC hvC huR hvR hphase
    change RCLike.re (inner ℂ (uC x) (fourierPhaseMulAux (-2 * b) vC x)) = _
    rw [hphase, huC, hvC, huR, hvR]
    simp only [RCLike.inner_apply', starRingEnd_apply, fourierPhase,
      Real.fourierChar_apply]
    simp [Complex.mul_re, Complex.exp_re, Complex.exp_im]
    ring_nf
  calc
    (∫ x : ℝ, (g x * h x) * Real.cos (4 * Real.pi * b * x)) =
        ∫ x : ℝ, RCLike.re
          (inner ℂ (uC x) ((fourierPhaseMulUnitary (-2 * b) vC) x)) :=
      integral_congr_ae (hae.mono fun _ hx => hx.symm)
    _ = 0 := hreal

end MellinL2
end RHTower
