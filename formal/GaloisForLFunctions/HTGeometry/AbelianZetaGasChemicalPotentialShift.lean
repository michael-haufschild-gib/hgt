import GaloisForLFunctions.HTGeometry.ConstitutiveGlobalFormationInformationProperness
import GaloisForLFunctions.HTGeometry.GeometricModeChirality

/-!
# The chemical-potential shift of the abelian zeta gas, mode by mode

The corpus already carries the fugacity shift `τ ↦ τ + u` and its least-mode ratio law.  This
module supplies the **general mode** law: at every prime-depth mode the shift is exactly the
Esscher tilt of that mode's geometric ratio at jump size `log p`, so every mode of the gas is a
geometric formation mode in the sense of `GeometricModeChirality`.  It also identifies the
zero-occupation normalizer as the exponential of the summed mode log partitions.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- **The fugacity shift is the mode Esscher tilt.**  At every prime-depth mode, shifting the
chemical potential by `u` multiplies the geometric ratio by `p^{−u} = e^{−u log p}`. -/
theorem ratio_fugacityShiftParameters (θ : AbelianZetaParameters) (u : ℝ) (hu : 0 ≤ u)
    (m : AbelianZetaMode) :
    (fugacityShiftParameters θ u hu).ratio m
      = modeRatio (θ.ratio m) (Real.log ((m.1 : ℕ) : ℝ)) u := by
  have hp : (0:ℝ) < ((m.1 : ℕ) : ℝ) := by exact_mod_cast m.1.prop.pos
  simp only [AbelianZetaParameters.ratio, AbelianZetaParameters.exponent, modeRatio,
    fugacityShiftParameters_sigma, fugacityShiftParameters_tau]
  rw [← Real.exp_log hp, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  rw [Real.log_exp]
  ring

/-- The zero-occupation normalizer is the exponential of the summed mode log partitions. -/
theorem coe_nnNormalizer_eq_exp (θ : AbelianZetaConvergentParameters) :
    ((θ.nnNormalizer : ℝ≥0) : ℝ)
      = Real.exp (∑' m : AbelianZetaMode,
          Real.log (1 - θ.toAbelianZetaParameters.ratio m)) := by
  have hpos : ∀ m : AbelianZetaMode, 0 < (1 - θ.toAbelianZetaParameters.ratio m) := fun m =>
    sub_pos.mpr (θ.toAbelianZetaParameters.ratio_lt_one m)
  have hlog : Summable (fun m : AbelianZetaMode =>
      Real.log (1 - θ.toAbelianZetaParameters.ratio m)) := by
    simpa only [sub_eq_add_neg] using
      Real.summable_log_one_add_of_summable θ.summable_ratio.neg
  set A : ℝ≥0 := ⟨Real.exp (∑' m : AbelianZetaMode,
    Real.log (1 - θ.toAbelianZetaParameters.ratio m)), Real.exp_nonneg _⟩ with hA
  have hreal : HasProd (fun m : AbelianZetaMode => ((θ.nnZeroFactor m : ℝ≥0) : ℝ))
      ((A : ℝ≥0) : ℝ) := by
    apply Real.hasProd_of_hasSum_log
    · intro m; exact hpos m
    · exact hlog.hasSum
  have hnn : HasProd θ.nnZeroFactor A :=
    (NNReal.isClosedEmbedding_coe.isInducing.hasProd_iff
      (g := NNReal.toRealHom.toMonoidHom) θ.nnZeroFactor A).mp hreal
  rw [AbelianZetaConvergentParameters.nnNormalizer, hnn.tprod_eq, hA]
  rfl

/-- **The gas log partition is the sum of the geometric-mode log partitions.** -/
theorem neg_log_nnNormalizer_eq_tsum_modeLogPartition
    (θ : AbelianZetaConvergentParameters) (u : ℝ) (hu : 0 ≤ u) :
    -Real.log (((fugacityShiftConv θ u hu).nnNormalizer : ℝ≥0) : ℝ)
      = ∑' m : AbelianZetaMode,
          modeLogPartition (θ.toAbelianZetaParameters.ratio m)
            (Real.log ((m.1 : ℕ) : ℝ)) u := by
  rw [coe_nnNormalizer_eq_exp, Real.log_exp, ← tsum_neg]
  refine tsum_congr fun m => ?_
  rw [modeLogPartition, ← ratio_fugacityShiftParameters θ.toAbelianZetaParameters u hu m]
  rfl

end GaloisForLFunctions.HTGeometry
