import GaloisForLFunctions.RHTower.L2FourierReflection
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Actual zero and odd extensions of the original negative-half-line Hilbert space. -/
open MeasureTheory Set Filter
namespace GaloisForLFunctions.HTGeometry
open RHTower
noncomputable section
abbrev NegativeLineL2 := Lp ℂ 2 (volume.restrict (Iio (0:ℝ)))

def negativeZeroExtensionFun (f : NegativeLineL2) : ℝ → ℂ := (Iio (0:ℝ)).indicator f

private theorem negativeZeroExtension_memLp (f : NegativeLineL2) :
    MemLp (negativeZeroExtensionFun f) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_Iio).mpr (Lp.memLp f)

private def negativeZeroExtensionValue (f : NegativeLineL2) : FourierRealL2 :=
  (negativeZeroExtension_memLp f).toLp _

private theorem negativeZeroExtensionValue_ae (f : NegativeLineL2) :
    negativeZeroExtensionValue f =ᵐ[volume] negativeZeroExtensionFun f :=
  (negativeZeroExtension_memLp f).coeFn_toLp

private theorem negativeZeroExtensionValue_norm (f : NegativeLineL2) :
    ‖negativeZeroExtensionValue f‖ = ‖f‖ := by
  unfold negativeZeroExtensionValue
  rw [Lp.norm_toLp,Lp.norm_def,negativeZeroExtensionFun,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Iio]

private def negativeZeroExtensionLinear : NegativeLineL2 →ₗ[ℂ] FourierRealL2 where
  toFun := negativeZeroExtensionValue
  map_add' f g := by
    apply Lp.ext
    have hi := (ae_restrict_iff' measurableSet_Iio).mp (Lp.coeFn_add f g)
    filter_upwards [negativeZeroExtensionValue_ae (f+g),negativeZeroExtensionValue_ae f,
      negativeZeroExtensionValue_ae g,Lp.coeFn_add (negativeZeroExtensionValue f)
        (negativeZeroExtensionValue g),hi] with x ho hf hg ha hi
    rw [ho,ha]
    simp only [Pi.add_apply,hf,hg]
    by_cases hx : x ∈ Iio (0:ℝ)
    · simp only [negativeZeroExtensionFun,indicator_of_mem hx]
      exact hi hx
    · simp [negativeZeroExtensionFun,hx]
  map_smul' c f := by
    apply Lp.ext
    have hi := (ae_restrict_iff' measurableSet_Iio).mp (Lp.coeFn_smul c f)
    filter_upwards [negativeZeroExtensionValue_ae (c • f),negativeZeroExtensionValue_ae f,
      Lp.coeFn_smul c (negativeZeroExtensionValue f),hi] with x ho hf hs hi
    change negativeZeroExtensionValue (c • f) x = (c • negativeZeroExtensionValue f) x
    rw [ho,hs]
    simp only [Pi.smul_apply,smul_eq_mul,hf]
    by_cases hx : x ∈ Iio (0:ℝ)
    · simp only [negativeZeroExtensionFun,indicator_of_mem hx]
      exact hi hx
    · simp [negativeZeroExtensionFun,hx]

/-- Isometric zero extension in the actual L² quotient, with no representative hypothesis. -/
def negativeZeroExtension : NegativeLineL2 →L[ℂ] FourierRealL2 :=
  negativeZeroExtensionLinear.mkContinuous 1 (by
    intro f
    change ‖negativeZeroExtensionValue f‖ ≤ 1*‖f‖
    simpa using (negativeZeroExtensionValue_norm f).le)

theorem negativeZeroExtension_ae (f : NegativeLineL2) :
    negativeZeroExtension f =ᵐ[volume] negativeZeroExtensionFun f := negativeZeroExtensionValue_ae f

theorem negativeZeroExtension_norm (f : NegativeLineL2) : ‖negativeZeroExtension f‖ = ‖f‖ :=
  negativeZeroExtensionValue_norm f

/-- The source-faithful odd extension fixes the negative half-line and reflects its sign. -/
def negativeOddExtension : NegativeLineL2 →L[ℂ] FourierRealL2 :=
  negativeZeroExtension-l2Reflection.comp negativeZeroExtension

theorem negativeOddExtension_apply (f : NegativeLineL2) :
    negativeOddExtension f = negativeZeroExtension f-l2Reflection (negativeZeroExtension f) := rfl

theorem negativeOddExtension_norm_le (f : NegativeLineL2) : ‖negativeOddExtension f‖ ≤ 2*‖f‖ := by
  rw [negativeOddExtension_apply]
  calc
    _ ≤ ‖negativeZeroExtension f‖+‖l2Reflection (negativeZeroExtension f)‖ := norm_sub_le _ _
    _ = 2*‖f‖ := by
      change ‖negativeZeroExtension f‖+‖l2ReflectionIsometry (negativeZeroExtension f)‖ = _
      rw [l2ReflectionIsometry.norm_map,negativeZeroExtension_norm]
      ring

/-- Odd extension is an exact negative eigenvector of spatial reflection. -/
theorem negativeOddExtension_reflection (f : NegativeLineL2) :
    l2Reflection (negativeOddExtension f) = -negativeOddExtension f := by
  have he (g : FourierRealL2) : l2Reflection (l2Reflection g) = g := by
    apply Lp.ext
    have h₀ : l2Reflection g =ᵐ[volume] (fun x : ℝ => g (-x)) :=
      Lp.coeFn_compMeasurePreserving g (Measure.measurePreserving_neg (volume : Measure ℝ))
    have h₁ : l2Reflection (l2Reflection g) =ᵐ[volume] (fun x : ℝ => l2Reflection g (-x)) :=
      Lp.coeFn_compMeasurePreserving (l2Reflection g)
      (Measure.measurePreserving_neg (volume : Measure ℝ))
    have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h₀
    filter_upwards [h₁,hn] with x hx hn
    simpa only [Function.comp_apply,neg_neg] using hx.trans hn
  rw [negativeOddExtension_apply,map_sub,he]
  abel

/-- The odd extension retains the original negative-ray function almost everywhere. -/
theorem negativeOddExtension_ae_negative (f : NegativeLineL2) :
    negativeOddExtension f =ᵐ[volume.restrict (Iio (0:ℝ))] f := by
  have he := negativeZeroExtension_ae f
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae he
  have hr : l2Reflection (negativeZeroExtension f) =ᵐ[volume]
      (fun x : ℝ => negativeZeroExtension f (-x)) :=
    Lp.coeFn_compMeasurePreserving (negativeZeroExtension f)
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hh := Lp.coeFn_sub (negativeZeroExtension f) (l2Reflection (negativeZeroExtension f))
  filter_upwards [he.filter_mono (ae_mono Measure.restrict_le_self),
    hn.filter_mono (ae_mono Measure.restrict_le_self),hr.filter_mono (ae_mono Measure.restrict_le_self),
    hh.filter_mono (ae_mono Measure.restrict_le_self),ae_restrict_mem measurableSet_Iio] with x he hn hr hh hx
  change (negativeZeroExtension f-l2Reflection (negativeZeroExtension f)) x = f x
  rw [hh]
  change negativeZeroExtension f x-l2Reflection (negativeZeroExtension f) x = f x
  rw [he,hr,hn]
  change x < 0 at hx
  simp [negativeZeroExtensionFun,hx,show ¬ -x < 0 by linarith]

end
end GaloisForLFunctions.HTGeometry
