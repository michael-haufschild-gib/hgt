import GaloisForLFunctions.RHTower.XiShiftedHardEdgeParabolicNyquistAlias

/-!
# Parabolic Nyquist parity law for Route U

The quadratic divisor shell does not inherit the pointwise dyadic `(1,1)` parity law.  Its fine
Cayley phase sits at the coarse Nyquist wall.  After exact alias folding, the coarse-even channel
converges to half the Fourier profile at `-4 / u`; the full fine channel escapes to infinite
frequency and vanishes; therefore the odd channel converges to the negative half-profile.

This premise-free theorem identifies the ultraviolet parity line as `(1,-1)`.  It supplies the
local shell law needed before any Riemann--von Mangoldt summation or logarithmic renormalization.
-/

open scoped BigOperators SchwartzMap FourierTransform
open Complex Filter MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

theorem routeUComplexHardEdgePeriodizationAt_sub_aliasPeriod
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (r : ℝ) (z : ℂ) :
    routeUComplexHardEdgePeriodizationAt n f r
        (z - (routeUHardEdgeAliasPeriod r : ℂ)) =
      routeUComplexHardEdgePeriodizationAt n f r z := by
  rw [routeUComplexHardEdgePeriodizationAt,
    routeUComplexHardEdgePeriodizationAt]
  congr 1
  apply tsum_congr
  intro j
  congr 1
  have hmesh := routeUHardEdgeMesh_mul_aliasPeriod r
  have harg :
      Complex.I * (z - (routeUHardEdgeAliasPeriod r : ℂ)) *
          (((routeUHardEdgeMesh r * (j : ℝ) : ℝ) : ℂ)) =
        Complex.I * z *
            (((routeUHardEdgeMesh r * (j : ℝ) : ℝ) : ℂ)) +
          ((-j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    have hmeshC :
        (routeUHardEdgeMesh r : ℂ) *
            (routeUHardEdgeAliasPeriod r : ℂ) =
          (2 * Real.pi : ℝ) := by
      exact_mod_cast hmesh
    rw [show (((routeUHardEdgeMesh r * (j : ℝ) : ℝ) : ℂ)) =
        (routeUHardEdgeMesh r : ℂ) * (j : ℂ) by push_cast; ring]
    rw [show ((-j : ℤ) : ℂ) = -(j : ℂ) by push_cast; ring]
    calc
      Complex.I * (z - (routeUHardEdgeAliasPeriod r : ℂ)) *
          ((routeUHardEdgeMesh r : ℂ) * (j : ℂ)) =
        Complex.I * z * ((routeUHardEdgeMesh r : ℂ) * (j : ℂ)) -
          (j : ℂ) *
            ((routeUHardEdgeMesh r : ℂ) *
              (routeUHardEdgeAliasPeriod r : ℂ)) * Complex.I := by ring
      _ = Complex.I * z * ((routeUHardEdgeMesh r : ℂ) * (j : ℂ)) +
          -(j : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hmeshC]
        push_cast
        ring
  rw [harg, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Fine Cayley phase on the quadratic shell, viewed as a complex frequency. -/
def routeUDyadicParabolicComplexPhase
    (u : RouteUPositiveParabolicScale) (k : ℕ) : ℂ :=
  routeUComplexHardEdgePhase (routeUDyadicFineIndex k : ℝ)
    (routeUDyadicParabolicHeight u k : ℂ)

/-- Parabolic fine phase folded into the coarse alias chart. -/
def routeUDyadicParabolicComplexFoldedPhase
    (u : RouteUPositiveParabolicScale) (k : ℕ) : ℂ :=
  routeUDyadicParabolicComplexPhase u k -
    (routeUHardEdgeAliasPeriod (k : ℝ) : ℂ)

theorem routeUDyadicParabolicComplexFoldedPhase_eq_ofReal
    (u : RouteUPositiveParabolicScale) (k : ℕ) :
    routeUDyadicParabolicComplexFoldedPhase u k =
      (routeUDyadicParabolicFoldedPhase u k : ℂ) := by
  rw [routeUDyadicParabolicComplexFoldedPhase,
    routeUDyadicParabolicComplexPhase,
    routeUDyadicParabolicFoldedPhase,
    routeUComplexHardEdgePhase_ofReal]
  push_cast
  rfl

/-- Coarse-even polyphase sample on the quadratic spectral shell. -/
def routeUDyadicParabolicEvenSample
    (n : ℕ) (f : SchwartzMap ℝ ℂ)
    (u : RouteUPositiveParabolicScale) (k : ℕ) : ℂ :=
  (1 / 2 : ℂ) *
    routeUComplexHardEdgePeriodizationAt n f (k : ℝ)
      (routeUDyadicParabolicComplexPhase u k)

/-- The coarse-even channel retains half of the Fourier profile at the finite folded coordinate. -/
theorem tendsto_routeUDyadicParabolicEvenSample
    (n : ℕ) (f : SchwartzMap ℝ ℂ)
    (u : RouteUPositiveParabolicScale) :
    Tendsto (routeUDyadicParabolicEvenSample n f u) atTop
      (nhds ((1 / 2 : ℂ) *
        routeUComplexPositiveFourierExtension n f
          ((-4 / (u : ℝ) : ℝ) : ℂ))) := by
  let z : ℕ → ℂ := routeUDyadicParabolicComplexFoldedPhase u
  let z₀ : ℂ := ((-4 / (u : ℝ) : ℝ) : ℂ)
  let C : ℝ := routeUComplexHardEdgeUniformAliasTailConstant n f 0
  have hz : Tendsto z atTop (nhds z₀) := by
    have hreal := (Complex.continuous_ofReal.tendsto (-4 / (u : ℝ))).comp
      (tendsto_routeUDyadicParabolicFoldedPhase u)
    dsimp only [z, z₀]
    exact hreal.congr' (Eventually.of_forall fun k =>
      (routeUDyadicParabolicComplexFoldedPhase_eq_ofReal u k).symm)
  have hzIm : ∀ k, |(z k).im| ≤ 1 := by
    intro k
    rw [show z k = (routeUDyadicParabolicFoldedPhase u k : ℂ) by
      exact routeUDyadicParabolicComplexFoldedPhase_eq_ofReal u k]
    simp
  have hcentral : Tendsto
      (fun k : ℕ => routeUComplexPositiveFourierExtension n f (z k)) atTop
      (nhds (routeUComplexPositiveFourierExtension n f z₀)) :=
    tendsto_routeUComplexPositiveFourierExtension_of_tendsto n f z z₀ hz hzIm
  have hperiod : Tendsto
      (fun k : ℕ => routeUHardEdgeAliasPeriod (k : ℝ)) atTop atTop := by
    have hmul := Tendsto.const_mul_atTop Real.pi_pos
      tendsto_routeUHardEdgeMass_natCast_atTop
    simpa only [routeUHardEdgeAliasPeriod] using hmul
  have hperiodHalf : Tendsto
      (fun k : ℕ => routeUHardEdgeAliasPeriod (k : ℝ) / 2) atTop atTop := by
    have hmul := Tendsto.const_mul_atTop (by positivity : 0 < (1 / 2 : ℝ)) hperiod
    simpa only [one_div, inv_mul_eq_div] using hmul
  have hzRe : Tendsto (fun k : ℕ => |(z k).re|) atTop (nhds |z₀.re|) :=
    (continuous_abs.tendsto _).comp ((Complex.reCLM.continuous.tendsto _).comp hz)
  have hzReBound : ∀ᶠ k : ℕ in atTop, |(z k).re| < |z₀.re| + 1 :=
    hzRe.eventually (Iio_mem_nhds (lt_add_one _))
  have hperiodBound : ∀ᶠ k : ℕ in atTop,
      |z₀.re| + 1 ≤ routeUHardEdgeAliasPeriod (k : ℝ) / 2 :=
    (tendsto_atTop.1 hperiodHalf) (|z₀.re| + 1)
  have hphaseWindow : ∀ᶠ k : ℕ in atTop,
      |(z k).re| ≤ routeUHardEdgeAliasPeriod (k : ℝ) / 2 := by
    filter_upwards [hzReBound, hperiodBound] with k hk hK
    exact hk.le.trans hK
  have hperiodSq : Tendsto
      (fun k : ℕ => routeUHardEdgeAliasPeriod (k : ℝ) ^ (2 : ℕ)) atTop atTop := by
    simpa only [pow_two] using hperiod.atTop_mul_atTop₀ hperiod
  have hbound : Tendsto
      (fun k : ℕ => C / routeUHardEdgeAliasPeriod (k : ℝ) ^ (2 : ℕ))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hperiodSq
  have htail : Tendsto
      (fun k : ℕ => routeUComplexHardEdgeAliasTail n f (k : ℝ) (z k))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ hbound
    filter_upwards [hphaseWindow] with k hk
    simpa only [C,
      GaloisForLFunctions.RHTower.ccmRationalArchimedeanDecayExponent,
      Nat.zero_add, Nat.mul_one] using
      (norm_routeUComplexHardEdgeAliasTail_uniform_le n f (k : ℝ) (z k)
        (hzIm k) hk 0)
  have hfolded : Tendsto
      (fun k : ℕ => routeUComplexHardEdgePeriodizationAt n f (k : ℝ) (z k))
      atTop (nhds (routeUComplexPositiveFourierExtension n f z₀)) := by
    have hsum := hcentral.add htail
    simpa only [add_zero] using hsum.congr'
      (by
        filter_upwards [hphaseWindow] with k hk
        exact (routeUComplexHardEdgePeriodizationAt_eq_extension_add_tail
          n f (k : ℝ) (z k) hk).symm)
  have horiginal : Tendsto
      (fun k : ℕ => routeUComplexHardEdgePeriodizationAt n f (k : ℝ)
        (routeUDyadicParabolicComplexPhase u k))
      atTop (nhds (routeUComplexPositiveFourierExtension n f z₀)) :=
    hfolded.congr'
      (Eventually.of_forall fun k => by
        simpa only [z, routeUDyadicParabolicComplexFoldedPhase] using
          (routeUComplexHardEdgePeriodizationAt_sub_aliasPeriod n f
            (k : ℝ) (routeUDyadicParabolicComplexPhase u k)))
  change Tendsto (fun k : ℕ => (1 / 2 : ℂ) *
      routeUComplexHardEdgePeriodizationAt n f (k : ℝ)
        (routeUDyadicParabolicComplexPhase u k)) atTop _
  simpa only [z₀] using tendsto_const_nhds.mul horiginal

/-- Full fine-lattice sample on the quadratic spectral shell. -/
def routeUDyadicParabolicFullSample
    (n : ℕ) (f : SchwartzMap ℝ ℂ)
    (u : RouteUPositiveParabolicScale) (k : ℕ) : ℂ :=
  routeUComplexHardEdgePeriodizationAt n f
    (routeUDyadicFineIndex k : ℝ) (routeUDyadicParabolicComplexPhase u k)

/-- The full fine channel escapes to infinite frequency on the parabolic shell. -/
theorem tendsto_routeUDyadicParabolicFullSample_zero
    (n : ℕ) (f : SchwartzMap ℝ ℂ)
    (u : RouteUPositiveParabolicScale) :
    Tendsto (routeUDyadicParabolicFullSample n f u) atTop (nhds 0) := by
  let p : ℕ → ℂ := routeUDyadicParabolicComplexPhase u
  let z : ℕ → ℂ := routeUDyadicParabolicComplexFoldedPhase u
  let z₀ : ℂ := ((-4 / (u : ℝ) : ℝ) : ℂ)
  let D : ℝ := routeUComplexTiltUniformDecay n f 1
  let C : ℝ := routeUComplexHardEdgeUniformAliasTailConstant n f 0
  let x : ℕ → ℝ := fun k => -(p k).re / (2 * Real.pi)
  have hz : Tendsto z atTop (nhds z₀) := by
    have hreal := (Complex.continuous_ofReal.tendsto (-4 / (u : ℝ))).comp
      (tendsto_routeUDyadicParabolicFoldedPhase u)
    dsimp only [z, z₀]
    exact hreal.congr' (Eventually.of_forall fun k =>
      (routeUDyadicParabolicComplexFoldedPhase_eq_ofReal u k).symm)
  have hzRe : Tendsto (fun k : ℕ => (z k).re) atTop (nhds z₀.re) :=
    (Complex.reCLM.continuous.tendsto _).comp hz
  have hperiod : Tendsto
      (fun k : ℕ => routeUHardEdgeAliasPeriod (k : ℝ)) atTop atTop := by
    have hmul := Tendsto.const_mul_atTop Real.pi_pos
      tendsto_routeUHardEdgeMass_natCast_atTop
    simpa only [routeUHardEdgeAliasPeriod] using hmul
  have hpRe : Tendsto (fun k : ℕ => (p k).re) atTop atTop := by
    have hsum := hperiod.atTop_add hzRe
    exact hsum.congr'
      (Eventually.of_forall fun k => by
        dsimp only [p, z, routeUDyadicParabolicComplexFoldedPhase]
        simp only [Complex.sub_re, Complex.ofReal_re]
        ring)
  have hscaled : Tendsto
      (fun k : ℕ => (p k).re / (2 * Real.pi)) atTop atTop := by
    have hmul := Tendsto.const_mul_atTop
      (by positivity : 0 < (1 / (2 * Real.pi) : ℝ)) hpRe
    convert hmul using 1
    funext k
    ring
  have hxAbs : Tendsto (fun k : ℕ => |x k|) atTop atTop := by
    have habs := Filter.tendsto_abs_atTop_atTop.comp hscaled
    convert habs using 1
    funext k
    simp only [Function.comp_apply, x, abs_div, abs_neg]
  have hkg : Tendsto (fun k : ℕ => kgFreq (x k)) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hxAbs
    exact Eventually.of_forall fun k => abs_le_kgFreq_real (x k)
  have hkgSq : Tendsto (fun k : ℕ => kgFreq (x k) ^ (2 : ℕ)) atTop atTop :=
    (tendsto_pow_atTop (n := 2) (by norm_num)).comp hkg
  have hcentralBound : Tendsto
      (fun k : ℕ => D / kgFreq (x k) ^ (2 : ℕ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hkgSq
  have hpIm : ∀ k, |(p k).im| ≤ 1 := by
    intro k
    rw [show p k =
        (routeUHardEdgePhase (routeUDyadicFineIndex k : ℝ)
          (routeUDyadicParabolicHeight u k) : ℂ) by
      dsimp only [p, routeUDyadicParabolicComplexPhase]
      exact routeUComplexHardEdgePhase_ofReal _ _]
    simp
  have hcentral : Tendsto
      (fun k : ℕ => routeUComplexPositiveFourierExtension n f (p k))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_
      hcentralBound
    exact Eventually.of_forall fun k => by
      have hdecay := routeUComplexPositiveFourierExtension_uniform_decay
        n f (z := p k) (hpIm k) 1
      apply (le_div_iff₀ (pow_pos (kgFreq_pos (x k)) 2)).2
      calc
        ‖routeUComplexPositiveFourierExtension n f (p k)‖ *
            kgFreq (x k) ^ (2 : ℕ) =
          kgFreq (x k) ^ (2 : ℕ) *
            ‖routeUComplexPositiveFourierExtension n f (p k)‖ := by ring
        _ ≤ D := by simpa only [x, D, Nat.mul_one] using hdecay
  have hperiodFine : Tendsto
      (fun k : ℕ => routeUHardEdgeAliasPeriod
        (routeUDyadicFineIndex k : ℝ)) atTop atTop :=
    hperiod.comp tendsto_routeUDyadicFineIndex_atTop
  have hperiodFineSq : Tendsto
      (fun k : ℕ => routeUHardEdgeAliasPeriod
        (routeUDyadicFineIndex k : ℝ) ^ (2 : ℕ)) atTop atTop := by
    simpa only [pow_two] using hperiodFine.atTop_mul_atTop₀ hperiodFine
  have htailBound : Tendsto
      (fun k : ℕ => C / routeUHardEdgeAliasPeriod
        (routeUDyadicFineIndex k : ℝ) ^ (2 : ℕ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hperiodFineSq
  have hphaseWindow : ∀ k,
      |(p k).re| ≤ routeUHardEdgeAliasPeriod
        (routeUDyadicFineIndex k : ℝ) / 2 := by
    intro k
    dsimp only [p, routeUDyadicParabolicComplexPhase]
    exact abs_routeUComplexHardEdgePhase_re_le_half_aliasPeriod _ _
  have htail : Tendsto
      (fun k : ℕ => routeUComplexHardEdgeAliasTail n f
        (routeUDyadicFineIndex k : ℝ) (p k)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_
      htailBound
    exact Eventually.of_forall fun k => by
      simpa only [C,
        GaloisForLFunctions.RHTower.ccmRationalArchimedeanDecayExponent,
        Nat.zero_add, Nat.mul_one] using
        (norm_routeUComplexHardEdgeAliasTail_uniform_le n f
          (routeUDyadicFineIndex k : ℝ) (p k) (hpIm k) (hphaseWindow k) 0)
  have hsum := hcentral.add htail
  change Tendsto (fun k : ℕ => routeUComplexHardEdgePeriodizationAt n f
    (routeUDyadicFineIndex k : ℝ) (p k)) atTop (nhds 0)
  simpa only [zero_add] using hsum.congr'
    (Eventually.of_forall fun k =>
      (routeUComplexHardEdgePeriodizationAt_eq_extension_add_tail n f
        (routeUDyadicFineIndex k : ℝ) (p k) (hphaseWindow k)).symm)

/-- Odd polyphase channel, defined by exact fine-minus-even recombination. -/
def routeUDyadicParabolicOddSample
    (n : ℕ) (f : SchwartzMap ℝ ℂ)
    (u : RouteUPositiveParabolicScale) (k : ℕ) : ℂ :=
  routeUDyadicParabolicFullSample n f u k -
    routeUDyadicParabolicEvenSample n f u k

/-- The odd channel carries the opposite half-profile on every positive parabolic shell. -/
theorem tendsto_routeUDyadicParabolicOddSample
    (n : ℕ) (f : SchwartzMap ℝ ℂ)
    (u : RouteUPositiveParabolicScale) :
    Tendsto (routeUDyadicParabolicOddSample n f u) atTop
      (nhds (-(1 / 2 : ℂ) *
        routeUComplexPositiveFourierExtension n f
          ((-4 / (u : ℝ) : ℝ) : ℂ))) := by
  have hsub := (tendsto_routeUDyadicParabolicFullSample_zero n f u).sub
    (tendsto_routeUDyadicParabolicEvenSample n f u)
  convert hsub using 1
  · funext k
    rfl
  · ring

/-- Ultraviolet parabolic shells converge to the antisymmetric `(1,-1)` parity line. -/
theorem tendsto_routeUDyadicParabolicParityPair
    (n : ℕ) (f : SchwartzMap ℝ ℂ)
    (u : RouteUPositiveParabolicScale) :
    Tendsto (fun k : ℕ =>
      (routeUDyadicParabolicEvenSample n f u k,
        routeUDyadicParabolicOddSample n f u k)) atTop
      (nhds
        ((1 / 2 : ℂ) * routeUComplexPositiveFourierExtension n f
            ((-4 / (u : ℝ) : ℝ) : ℂ),
          -(1 / 2 : ℂ) * routeUComplexPositiveFourierExtension n f
            ((-4 / (u : ℝ) : ℝ) : ℂ))) := by
  simpa only [nhds_prod_eq] using
    (tendsto_routeUDyadicParabolicEvenSample n f u).prodMk
      (tendsto_routeUDyadicParabolicOddSample n f u)

end RHTower
