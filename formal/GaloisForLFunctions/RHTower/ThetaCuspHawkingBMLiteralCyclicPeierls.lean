import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralPeierlsPhysicalFrequency
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularGoursat
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularMeanGrowth

/-!
# Literal cyclic Peierls core

This module packages only identities realized by the actual full theta-circle
field.  The bulk field is the physical-frequency two-leg metric; the causal
kernel is the original direct-minus-image onset kernel.  The latter is
reciprocal in its two radial slots, which is the geometric cyclic identity
needed before the source-event pairing can be antisymmetrized.

Proof-chain role:
`literal two-leg bulk equation + cyclic full causal kernel -> admitted
retarded-minus-advanced pairing -> cap/contact equality -> HB causal cut`.
The admission and cap/contact steps are intentionally not claimed here.
-/

namespace RHTower.D4BMLiteralCyclicPeierls

open GaloisForLFunctions.HTGeometry
open D4BMHorizon D4BMFundamentalScalarMetric D4BMModularCore
open D4BMMetricReconstruction
open D4BMCausalKernel D4BMFullAngularReconstruction D4BMFullAngularGoursat
open D4BMFullAngularGrowth D4BMFullAngularCircle D4BMNativeCircle
open D4BMLiteralPeierlsPhysicalFrequency D4BMLiteralPeierlsStream

noncomputable section
set_option autoImplicit false

private theorem invariant_swap (h x y : ℝ) :
    invariant h x y = invariant h y x := by
  unfold invariant
  ring

private theorem invariant_image_swap (h x y : ℝ) :
    invariant h x (-y) = invariant h y (-x) := by
  simp only [invariant, Real.sinh_neg, Real.cosh_neg]
  ring

private theorem causal_radius_le_time (h x y : ℝ) (hc : |x - y| ≤ h) :
    Real.arcosh (invariant h x y) ≤ h := by
  have hz := invariant_causal ⟨h, x, y, hc⟩
  have hd := Real.arcosh_nonneg hz
  have hh := (abs_nonneg (x - y)).trans hc
  have hb := invariant_le_cosh_time h x y
  rw [← Real.cosh_arcosh hz] at hb
  simpa only [abs_of_nonneg hd, abs_of_nonneg hh] using Real.cosh_le_cosh.mp hb

/-- The full direct-minus-image causal kernel is reciprocal in its two radial
arguments.  Both causal gates and the reflected image are literal. -/
theorem angularDirichletKernel_cyclic (q : XiZeroCopy) (branch : Bool)
    (h x y X k : ℝ) :
    angularDirichletKernel q branch h x y X k =
      angularDirichletKernel q branch h y x X k := by
  unfold angularDirichletKernel
  rw [invariant_swap h x y, invariant_image_swap h x y]
  rw [abs_sub_comm x y, add_comm x y]

/-- The actual onset-pulse kernel inherits the same cyclic radial reciprocity,
without replacing either causal arm by a modal or trace proxy. -/
theorem onsetDirichletKernel_cyclic (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (τ t h x y X k : ℝ) :
    onsetDirichletKernel q branch a τ t h x y X k =
      onsetDirichletKernel q branch a τ t h y x X k := by
  unfold onsetDirichletKernel
  rw [invariant_swap h x y, invariant_image_swap h x y]
  rw [abs_sub_comm x y, add_comm x y]

/-- The literal full direct-minus-image circle kernel has a strict causal
growth exponent.  Its exponent is below the physical clock exponent; no modal
replacement, truncated source, or cap renormalization occurs in this bound. -/
theorem angularDirichletKernel_strict_growth (q : XiZeroCopy) (branch : Bool)
    (X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h x y : ℝ, 0 ≤ h →
      ‖angularDirichletKernel q branch h x y X k‖ ≤
        C * Real.exp (strictGrowthExponent q * h) := by
  obtain ⟨C, hC, hmean⟩ := angularMean_strict_growth q branch X k
  have hgamma : 0 ≤ strictGrowthExponent q := by
    linarith [(sourceGrowthExponent_bounds q).1, (strictGrowthExponent_bounds q).1]
  refine ⟨C, hC, fun h x y hh => ?_⟩
  have cone_bound (z : ℝ) :
      ‖if |x - z| ≤ h then
          angularMean q branch (Real.arcosh (invariant h x z)) X k else 0‖ ≤
        C * Real.exp (strictGrowthExponent q * h) := by
    split_ifs with hc
    · have hz := invariant_causal ⟨h, x, z, hc⟩
      have hd : 0 ≤ Real.arcosh (invariant h x z) := Real.arcosh_nonneg hz
      have hm := hmean (Real.arcosh (invariant h x z)) hd
      have hvalue : ‖angularMean q branch (Real.arcosh (invariant h x z)) X k‖ ≤
          C * Real.exp (strictGrowthExponent q * Real.arcosh (invariant h x z)) :=
        (le_add_of_nonneg_right (norm_nonneg _)).trans hm
      exact hvalue.trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
          (causal_radius_le_time h x z hc) hgamma)) hC)
    · simp only [norm_zero]
      positivity
  have hdirect := cone_bound y
  have himage := cone_bound (-y)
  simp only [sub_neg_eq_add] at himage
  unfold angularDirichletKernel
  rw [norm_div, Complex.norm_ofNat]
  exact (div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)).trans (by linarith)

/-- Literal cyclic Peierls core: the physical polarized metric obeys its full
Einstein equation and the exact full causal onset kernel is reciprocal. -/
theorem literalCyclicPeierls_core (q : XiZeroCopy) (branch : Bool)
    (p : D4BMBackground.ExteriorPoint) (a d : ℂ) (i j : Fin 4)
    (τ t h x y X k : ℝ) :
    (CoordinateMetricTwoJet.Linearization.cosmological
        (D4BMBackground.jet (p.val 1) (p.val 3))
        (ofMetricField (forcedMetricBilinear q branch a d) p.val) (-3) i j +
      literalMixedSourceBilinear q branch (p.val 1)
        (envelope (physicalRate q branch) a p.val)
        (envelope (physicalRate q branch) d p.val) (angularPoint p.val) i j = 0) ∧
    onsetDirichletKernel q branch a τ t h x y X k =
      onsetDirichletKernel q branch a τ t h y x X k := by
  exact ⟨forcedMetricBilinear_cosmological_source q branch p a d i j,
    onsetDirichletKernel_cyclic q branch a τ t h x y X k⟩

end

end RHTower.D4BMLiteralCyclicPeierls
