/-
An unconditional Mellin--Plancherel transport on complex L².

The multiplicative source is `L²(ℝ₊, dˣx)`, encoded without a density theorem as the pushforward
of Lebesgue measure by `exp : ℝ → ℝ₊`.  Pullback by `exp` turns multiplicative scaling into additive
translation.  The mathlib Fourier transform uses the kernel `exp (-2π i t ξ)`, so the final frequency
dilation by `(2π)⁻¹` changes from `ξ` to the standard Mellin variable `s = 2πξ`.

With these conventions the source pullback `h(x) ↦ h(p x)` is carried to multiplication by

  `exp (i log(p) s) = p^(i s)`.

The positive sign is deliberate: the source action is pullback by `x ↦ p x`, while the Fourier
kernel has a negative exponent.  No abstract intertwining assumption is used: the translation
formula is first proved for Schwartz functions and extended to all of L² by density and Plancherel.
-/
import GaloisForLFunctions.RHTower.SoninEulerCornerNoncompact
import GaloisForLFunctions.RHTower.SoninL2Model
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic

noncomputable section

open MeasureTheory Set
open SchwartzMap FourierTransform
open scoped ENNReal

namespace RHTower
namespace MellinL2

variable {α β E 𝕜 : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} {q : ℝ≥0∞}
variable [NormedAddCommGroup E] [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
variable [Fact (1 ≤ q)]

/-- Pullback along a measure-preserving measurable equivalence, as an onto `Lᵖ` isometry. -/
def lpCompMeasurePreservingEquiv (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) :
    Lp E q ν ≃ₗᵢ[𝕜] Lp E q μ where
  __ := Lp.compMeasurePreservingₗᵢ 𝕜 e he
  invFun := Lp.compMeasurePreserving e.symm he.symm
  left_inv g := by
    change Lp.compMeasurePreserving e.symm he.symm
      (Lp.compMeasurePreserving e he g) = g
    rw [← Lp.compMeasurePreserving_comp_apply g he he.symm]
    simpa using Lp.compMeasurePreserving_id_apply g
  right_inv g := by
    change Lp.compMeasurePreserving e he
      (Lp.compMeasurePreserving e.symm he.symm g) = g
    rw [← Lp.compMeasurePreserving_comp_apply g he.symm he]
    simpa using Lp.compMeasurePreserving_id_apply g

/-! ### Logarithmic coordinates -/

abbrev PosReal := Set.Ioi (0 : ℝ)

def expMeasurableEquiv : ℝ ≃ᵐ PosReal :=
  Real.expOrderIso.toHomeomorph.toMeasurableEquiv

/-- Multiplicative Haar measure, defined canonically as `exp_* dt`. -/
def multiplicativeHaar : Measure PosReal :=
  Measure.map expMeasurableEquiv (volume : Measure ℝ)

theorem exp_measurePreserving :
    MeasurePreserving expMeasurableEquiv (volume : Measure ℝ) multiplicativeHaar :=
  expMeasurableEquiv.measurable.measurePreserving _

/-- Composition with `exp`, from multiplicative Haar `L²` to additive Lebesgue `L²`. -/
def expPullbackUnitary :
    Lp ℂ 2 multiplicativeHaar ≃ₗᵢ[ℂ] Lp (α := ℝ) ℂ 2 :=
  lpCompMeasurePreservingEquiv expMeasurableEquiv exp_measurePreserving

def realTranslationEquiv (a : ℝ) : ℝ ≃ᵐ ℝ :=
  (Homeomorph.addRight a).toMeasurableEquiv

theorem realTranslation_measurePreserving (a : ℝ) :
    MeasurePreserving (realTranslationEquiv a) (volume : Measure ℝ) volume := by
  simpa [realTranslationEquiv] using measurePreserving_add_right (volume : Measure ℝ) a

/-- Multiplicative scaling, defined as logarithmic translation conjugated by `exp`. -/
def positiveScaleEquiv (a : ℝ) : PosReal ≃ᵐ PosReal :=
  expMeasurableEquiv.symm.trans ((realTranslationEquiv a).trans expMeasurableEquiv)

theorem positiveScale_measurePreserving (a : ℝ) :
    MeasurePreserving (positiveScaleEquiv a) multiplicativeHaar multiplicativeHaar := by
  exact exp_measurePreserving.comp
    ((realTranslation_measurePreserving a).comp exp_measurePreserving.symm)

def positiveScaleUnitary (a : ℝ) :
    Lp ℂ 2 multiplicativeHaar ≃ₗᵢ[ℂ] Lp ℂ 2 multiplicativeHaar :=
  lpCompMeasurePreservingEquiv (positiveScaleEquiv a)
    (positiveScale_measurePreserving a)

def additiveTranslationUnitary (a : ℝ) :
    Lp (α := ℝ) ℂ 2 ≃ₗᵢ[ℂ] Lp (α := ℝ) ℂ 2 :=
  lpCompMeasurePreservingEquiv (realTranslationEquiv a)
    (realTranslation_measurePreserving a)

theorem expPullback_positiveScale (a : ℝ) (f : Lp ℂ 2 multiplicativeHaar) :
    expPullbackUnitary (positiveScaleUnitary a f) =
      additiveTranslationUnitary a (expPullbackUnitary f) := by
  change Lp.compMeasurePreserving expMeasurableEquiv exp_measurePreserving
      (Lp.compMeasurePreserving (positiveScaleEquiv a)
        (positiveScale_measurePreserving a) f) =
    Lp.compMeasurePreserving (realTranslationEquiv a)
      (realTranslation_measurePreserving a)
      (Lp.compMeasurePreserving expMeasurableEquiv exp_measurePreserving f)
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (positiveScaleEquiv a)
        (positiveScale_measurePreserving a) f)
      exp_measurePreserving,
    (Lp.coeFn_compMeasurePreserving f (positiveScale_measurePreserving a)).comp_tendsto
      exp_measurePreserving.quasiMeasurePreserving.tendsto_ae,
    Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving expMeasurableEquiv exp_measurePreserving f)
      (realTranslation_measurePreserving a),
    (Lp.coeFn_compMeasurePreserving f exp_measurePreserving).comp_tendsto
      (realTranslation_measurePreserving a).quasiMeasurePreserving.tendsto_ae
  ] with x hl hscale hr hexp
  rw [hl, hr]
  change Lp.compMeasurePreserving (positiveScaleEquiv a)
      (positiveScale_measurePreserving a) f (expMeasurableEquiv x) =
    Lp.compMeasurePreserving expMeasurableEquiv exp_measurePreserving f
      (realTranslationEquiv a x)
  rw [show Lp.compMeasurePreserving (positiveScaleEquiv a)
        (positiveScale_measurePreserving a) f (expMeasurableEquiv x) =
      f (positiveScaleEquiv a (expMeasurableEquiv x)) by
        simpa [Function.comp_apply] using hscale,
    show Lp.compMeasurePreserving expMeasurableEquiv exp_measurePreserving f
        (realTranslationEquiv a x) =
      f (expMeasurableEquiv (realTranslationEquiv a x)) by
        simpa [Function.comp_apply] using hexp]
  congr 1
  simp [positiveScaleEquiv]

/-! ### Fourier translation and phase multiplication -/

def fourierPhase (a x : ℝ) : ℂ :=
  (Real.fourierChar (a * x) : ℂ)

theorem fourierPhase_continuous (a : ℝ) : Continuous (fourierPhase a) := by
  exact continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (continuous_const.mul continuous_id))

@[simp] theorem norm_fourierPhase (a x : ℝ) : ‖fourierPhase a x‖ = 1 := by
  simp [fourierPhase]

theorem memLp_fourierPhase_mul (a : ℝ) (f : Lp (α := ℝ) ℂ 2) :
    MemLp (fun x => fourierPhase a x * f x) 2 (volume : Measure ℝ) := by
  apply (Lp.memLp f).congr_norm
  · exact (fourierPhase_continuous a).aestronglyMeasurable.mul (Lp.memLp f).1
  · filter_upwards with x
    simp

def fourierPhaseMulAux (a : ℝ) (f : Lp (α := ℝ) ℂ 2) : Lp (α := ℝ) ℂ 2 :=
  (memLp_fourierPhase_mul a f).toLp _

theorem fourierPhaseMulAux_ae (a : ℝ) (f : Lp (α := ℝ) ℂ 2) :
    fourierPhaseMulAux a f =ᵐ[volume] fun x => fourierPhase a x * f x :=
  (memLp_fourierPhase_mul a f).coeFn_toLp

def fourierPhaseMulLinear (a : ℝ) :
    Lp (α := ℝ) ℂ 2 →ₗ[ℂ] Lp (α := ℝ) ℂ 2 where
  toFun := fourierPhaseMulAux a
  map_add' f g := by
    apply Lp.ext
    filter_upwards [fourierPhaseMulAux_ae a (f + g),
      fourierPhaseMulAux_ae a f, fourierPhaseMulAux_ae a g,
      Lp.coeFn_add f g,
      Lp.coeFn_add (fourierPhaseMulAux a f) (fourierPhaseMulAux a g)]
      with x hfg hf hg hadd hout
    rw [hfg, hout]
    change fourierPhase a x * (f + g : Lp (α := ℝ) ℂ 2) x =
      fourierPhaseMulAux a f x + fourierPhaseMulAux a g x
    rw [hadd, hf, hg]
    change fourierPhase a x * (f x + g x) =
      fourierPhase a x * f x + fourierPhase a x * g x
    ring
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [fourierPhaseMulAux_ae a (c • f),
      fourierPhaseMulAux_ae a f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (fourierPhaseMulAux a f)] with x hcf hf hcin hcout
    rw [hcf, hcout]
    change fourierPhase a x * (c • f : Lp (α := ℝ) ℂ 2) x =
      c • fourierPhaseMulAux a f x
    rw [hcin, hf]
    change fourierPhase a x * (c * f x) = c * (fourierPhase a x * f x)
    ring

theorem norm_fourierPhaseMulAux (a : ℝ) (f : Lp (α := ℝ) ℂ 2) :
    ‖fourierPhaseMulAux a f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (fourierPhaseMulAux_ae a f)]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards with x
  simp

def fourierPhaseMulIsometry (a : ℝ) :
    Lp (α := ℝ) ℂ 2 →ₗᵢ[ℂ] Lp (α := ℝ) ℂ 2 where
  __ := fourierPhaseMulLinear a
  norm_map' := norm_fourierPhaseMulAux a

theorem fourierPhase_neg_mul (a x : ℝ) :
    fourierPhase (-a) x * fourierPhase a x = 1 := by
  simp [fourierPhase, Real.fourierChar_apply, ← Complex.exp_add]

/-- Unitary multiplication by the Fourier character `x ↦ exp (2π i a x)`. -/
def fourierPhaseMulUnitary (a : ℝ) :
    Lp (α := ℝ) ℂ 2 ≃ₗᵢ[ℂ] Lp (α := ℝ) ℂ 2 where
  __ := fourierPhaseMulIsometry a
  invFun := fourierPhaseMulAux (-a)
  left_inv f := by
    change fourierPhaseMulAux (-a) (fourierPhaseMulAux a f) = f
    apply Lp.ext
    filter_upwards [fourierPhaseMulAux_ae a f,
      fourierPhaseMulAux_ae (-a) (fourierPhaseMulAux a f)] with x hf hout
    rw [hout, hf, ← mul_assoc, fourierPhase_neg_mul, one_mul]
  right_inv f := by
    change fourierPhaseMulAux a (fourierPhaseMulAux (-a) f) = f
    apply Lp.ext
    filter_upwards [fourierPhaseMulAux_ae (-a) f,
      fourierPhaseMulAux_ae a (fourierPhaseMulAux (-a) f)] with x hf hout
    rw [hout, hf]
    have h := fourierPhase_neg_mul a x
    rw [← mul_assoc, mul_comm (fourierPhase a x) (fourierPhase (-a) x), h, one_mul]

def schwartzTranslate (a : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (by fun_prop : (fun x : ℝ => x + a).HasTemperateGrowth)
    (isometry_add_right a).antilipschitz

@[simp] theorem schwartzTranslate_apply (a : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzTranslate a f x = f (x + a) := rfl

theorem additiveTranslation_toLp (a : ℝ) (f : 𝓢(ℝ, ℂ)) :
    additiveTranslationUnitary a (f.toLp 2 volume) =
      (schwartzTranslate a f).toLp 2 volume := by
  change Lp.compMeasurePreserving (realTranslationEquiv a)
      (realTranslation_measurePreserving a) (f.toLp 2 volume) = _
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_compMeasurePreserving (f.toLp 2 volume)
      (realTranslation_measurePreserving a),
    (schwartzTranslate a f).coeFn_toLp (p := 2) (μ := volume),
    (f.coeFn_toLp (p := 2) (μ := volume)).comp_tendsto
      (realTranslation_measurePreserving a).quasiMeasurePreserving.tendsto_ae
  ] with x hl hr hf
  rw [hl, hr]
  change (f.toLp 2 volume) (x + a) = f (x + a)
  simpa [Function.comp_apply, realTranslationEquiv] using hf

theorem fourier_schwartzTranslate (a : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    𝓕 (schwartzTranslate a f) x = fourierPhase a x * 𝓕 f x := by
  have h := congrFun
    (Fourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure ℝ) (fun y : ℝ => f y) a) x
  rw [SchwartzMap.fourier_coe (schwartzTranslate a f), SchwartzMap.fourier_coe f]
  simpa [Real.fourier_eq, Fourier.fourierIntegral_def, fourierPhase,
    Circle.smul_def, Function.comp_apply, mul_comm] using h

theorem fourier_additiveTranslation_on_schwartz (a : ℝ) (f : 𝓢(ℝ, ℂ)) :
    𝓕 (additiveTranslationUnitary a (f.toLp 2 volume)) =
      fourierPhaseMulUnitary a (𝓕 (f.toLp 2 volume)) := by
  rw [additiveTranslation_toLp, SchwartzMap.toLp_fourier_eq,
    SchwartzMap.toLp_fourier_eq]
  change (𝓕 (schwartzTranslate a f)).toLp 2 volume =
    fourierPhaseMulAux a ((𝓕 f).toLp 2 volume)
  apply Lp.ext
  filter_upwards [
    (𝓕 (schwartzTranslate a f)).coeFn_toLp (p := 2) (μ := volume),
    fourierPhaseMulAux_ae a ((𝓕 f).toLp 2 volume),
    (𝓕 f).coeFn_toLp (p := 2) (μ := volume)
  ] with x hl hr hf
  rw [hl, hr, hf, fourier_schwartzTranslate]

/-- Plancherel extension of `Fourier(f(·+a)) = exp(2πia·) Fourier(f)` to all of `L²`. -/
theorem fourier_additiveTranslation (a : ℝ) (f : Lp (α := ℝ) ℂ 2) :
    𝓕 (additiveTranslationUnitary a f) =
      fourierPhaseMulUnitary a (𝓕 f) := by
  let P : Lp (α := ℝ) ℂ 2 → Prop := fun g =>
    𝓕 (additiveTranslationUnitary a g) =
      fourierPhaseMulUnitary a (𝓕 g)
  apply DenseRange.induction_on (p := P)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp
        (additiveTranslationUnitary a).continuous
    · exact (fourierPhaseMulUnitary a).continuous.comp
        (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).continuous
  · intro g
    exact fourier_additiveTranslation_on_schwartz a g

/-! ### Mellin normalization and the prime character -/

/-- Mellin--Fourier before rescaling the mathlib frequency by `2π`. -/
def rawMellinUnitary :
    Lp ℂ 2 multiplicativeHaar ≃ₗᵢ[ℂ] Lp (α := ℝ) ℂ 2 :=
  expPullbackUnitary.trans (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)

theorem rawMellin_positiveScale (a : ℝ) (f : Lp ℂ 2 multiplicativeHaar) :
    rawMellinUnitary (positiveScaleUnitary a f) =
      fourierPhaseMulUnitary a (rawMellinUnitary f) := by
  change 𝓕 (expPullbackUnitary (positiveScaleUnitary a f)) =
    fourierPhaseMulUnitary a (𝓕 (expPullbackUnitary f))
  rw [expPullback_positiveScale, fourier_additiveTranslation]

theorem fourierPhase_scale (a c x : ℝ) :
    fourierPhase a (c * x) = fourierPhase (a * c) x := by
  unfold fourierPhase
  congr 2
  ring

theorem dilation_fourierPhaseMul (c : ℝ) (hc : 0 < c) (a : ℝ)
    (f : Lp (α := ℝ) ℂ 2) :
    RHTower.dilationUnitary c hc (fourierPhaseMulUnitary a f) =
      fourierPhaseMulUnitary (a * c) (RHTower.dilationUnitary c hc f) := by
  change RHTower.dilation c hc (fourierPhaseMulAux a f) =
    fourierPhaseMulAux (a * c) (RHTower.dilation c hc f)
  apply Lp.ext
  have hphase_scaled := (fourierPhaseMulAux_ae a f).comp_tendsto
    (RHTower.realMul_quasiMeasurePreserving c hc.ne').tendsto_ae
  filter_upwards [RHTower.dilation_ae c hc (fourierPhaseMulAux a f),
    hphase_scaled, fourierPhaseMulAux_ae (a * c) (RHTower.dilation c hc f),
    RHTower.dilation_ae c hc f] with x hl hphase hr hf
  rw [hl, hr, hf]
  rw [show fourierPhaseMulAux a f (c * x) = fourierPhase a (c * x) * f (c * x) by
    simpa [Function.comp_apply] using hphase]
  rw [fourierPhase_scale]
  ring

def spectralNormalization : ℝ := (2 * Real.pi)⁻¹

theorem spectralNormalization_pos : 0 < spectralNormalization := by
  unfold spectralNormalization
  positivity

/-- Mellin unitary in the standard spectral coordinate, with kernel `exp (-i s log x)`. -/
def mellinUnitary :
    Lp ℂ 2 multiplicativeHaar ≃ₗᵢ[ℂ] Lp (α := ℝ) ℂ 2 :=
  rawMellinUnitary.trans
    (RHTower.dilationUnitary spectralNormalization spectralNormalization_pos)

theorem mellin_positiveScale (a : ℝ) (f : Lp ℂ 2 multiplicativeHaar) :
    mellinUnitary (positiveScaleUnitary a f) =
      fourierPhaseMulUnitary (a * spectralNormalization) (mellinUnitary f) := by
  change RHTower.dilation spectralNormalization spectralNormalization_pos
      (rawMellinUnitary (positiveScaleUnitary a f)) =
    fourierPhaseMulAux (a * spectralNormalization)
      (RHTower.dilation spectralNormalization spectralNormalization_pos
        (rawMellinUnitary f))
  rw [rawMellin_positiveScale]
  exact dilation_fourierPhaseMul spectralNormalization spectralNormalization_pos a
    (rawMellinUnitary f)

/-- The standard Mellin character `p^(i s)`, written using an exponential. -/
def mellinCharacter (p s : ℝ) : ℂ :=
  Complex.exp (((Real.log p * s : ℝ) : ℂ) * Complex.I)

theorem mellinCharacter_eq_cpow (p : ℝ) (hp : 0 < p) (s : ℝ) :
    mellinCharacter p s = (p : ℂ) ^ (Complex.I * (s : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne')]
  rw [← Complex.ofReal_log hp.le]
  unfold mellinCharacter
  congr 1
  push_cast
  ring

theorem fourierPhase_log_normalized (p s : ℝ) :
    fourierPhase (Real.log p * spectralNormalization) s = mellinCharacter p s := by
  unfold fourierPhase spectralNormalization mellinCharacter
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- At logarithmic parameter `log p`, the abstract positive scale is exactly `x ↦ p*x`. -/
theorem positiveScaleEquiv_log_apply (p : ℝ) (hp : 0 < p) (x : PosReal) :
    ((positiveScaleEquiv (Real.log p) x : PosReal) : ℝ) = p * (x : ℝ) := by
  simp [positiveScaleEquiv, realTranslationEquiv, expMeasurableEquiv,
    Real.exp_add, Real.exp_log hp]
  have hx : Real.exp (Real.expOrderIso.symm x) = (x : ℝ) :=
    congrArg Subtype.val (Real.expOrderIso.apply_symm_apply x)
  rw [hx, mul_comm]

/-- Unitary multiplication by `p^(i s)` in the standard Mellin coordinate. -/
def mellinCharacterMulUnitary (p : ℝ) :
    Lp (α := ℝ) ℂ 2 ≃ₗᵢ[ℂ] Lp (α := ℝ) ℂ 2 :=
  fourierPhaseMulUnitary (Real.log p * spectralNormalization)

theorem mellinCharacterMulUnitary_ae (p : ℝ) (f : Lp (α := ℝ) ℂ 2) :
    mellinCharacterMulUnitary p f =ᵐ[volume]
      fun s => mellinCharacter p s * f s := by
  change fourierPhaseMulAux (Real.log p * spectralNormalization) f =ᵐ[volume] _
  filter_upwards [fourierPhaseMulAux_ae
    (Real.log p * spectralNormalization) f] with s hs
  rw [hs, fourierPhase_log_normalized]

/-- The concrete Mellin intertwining identity `M(U_p f) = p^(i s) M(f)`. -/
theorem mellin_positiveDilation (p : ℝ) (hp : 0 < p)
    (f : Lp ℂ 2 multiplicativeHaar) :
    mellinUnitary (positiveScaleUnitary (Real.log p) f) =
      mellinCharacterMulUnitary p (mellinUnitary f) := by
  exact mellin_positiveScale (Real.log p) f

/-- Operator-level pullback: the `p^(i s)` multiplier conjugates to positive scaling. -/
theorem conjugateOperator_mellinCharacter (p : ℝ) (hp : 0 < p) :
    RHTower.conjugateOperator mellinUnitary.toContinuousLinearEquiv
      (mellinCharacterMulUnitary p).toLinearIsometry.toContinuousLinearMap =
    (positiveScaleUnitary (Real.log p)).toLinearIsometry.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro f
  change mellinUnitary.symm
      (mellinCharacterMulUnitary p (mellinUnitary f)) =
    positiveScaleUnitary (Real.log p) f
  apply mellinUnitary.injective
  rw [mellinUnitary.apply_symm_apply]
  exact (mellin_positiveDilation p hp f).symm

end MellinL2
end RHTower
