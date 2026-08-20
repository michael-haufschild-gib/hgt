import GaloisForLFunctions.HTGeometry.AbelianZetaGas.RelativeEntropy
import GaloisForLFunctions.HTGeometry.GeometricModeChirality

/-!
# The chemical-potential shift of the abelian zeta gas

Shifting the chemical potential `τ ↦ τ + t` multiplies every geometric mode ratio by `p^{-t}`, so
each mode of the gas becomes an Esscher tilt of itself at jump size `log p`.  The zero-occupation
normalizer is the exponential of the summed mode log partitions, so the gas log partition is the
sum of the geometric-mode log partitions.
-/

open MeasureTheory
open scoped NNReal ENNReal
namespace GaloisForLFunctions.HTGeometry

open AbelianZetaParameters AbelianZetaConvergentParameters

/-- The chemical-potential shift of a convergent parameter point. -/
def shiftTau (θ : AbelianZetaConvergentParameters) (t : ℝ) (ht : 0 ≤ t) :
    AbelianZetaConvergentParameters where
  sigma := θ.sigma
  tau := θ.tau + t
  sigma_pos := θ.sigma_pos
  tau_nonneg := by have := θ.tau_nonneg; linarith
  firstDepth := by have := θ.firstDepth; linarith

theorem ratio_shiftTau (θ : AbelianZetaConvergentParameters) (t : ℝ) (ht : 0 ≤ t)
    (m : AbelianZetaMode) :
    (shiftTau θ t ht).toAbelianZetaParameters.ratio m
      = modeRatio (θ.toAbelianZetaParameters.ratio m) (Real.log ((m.1 : ℕ) : ℝ)) t := by
  have hp : (0:ℝ) < ((m.1 : ℕ) : ℝ) := by exact_mod_cast m.1.prop.pos
  simp only [AbelianZetaParameters.ratio, AbelianZetaParameters.exponent, modeRatio, shiftTau]
  rw [← Real.exp_log hp]
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  congr 1
  rw [Real.log_exp]
  ring

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
  have hreal : HasProd (fun m : AbelianZetaMode => ((θ.nnZeroFactor m : ℝ≥0) : ℝ)) ((A : ℝ≥0) : ℝ) := by
    apply Real.hasProd_of_hasSum_log
    · intro m
      exact hpos m
    · exact hlog.hasSum
  have hnn : HasProd θ.nnZeroFactor A :=
    (NNReal.isClosedEmbedding_coe.isInducing.hasProd_iff
      (g := NNReal.toRealHom.toMonoidHom) θ.nnZeroFactor A).mp hreal
  rw [AbelianZetaConvergentParameters.nnNormalizer, hnn.tprod_eq, hA]
  rfl

theorem log_nnNormalizer (θ : AbelianZetaConvergentParameters) :
    Real.log ((θ.nnNormalizer : ℝ≥0) : ℝ)
      = ∑' m : AbelianZetaMode, Real.log (1 - θ.toAbelianZetaParameters.ratio m) := by
  rw [coe_nnNormalizer_eq_exp, Real.log_exp]

end GaloisForLFunctions.HTGeometry
