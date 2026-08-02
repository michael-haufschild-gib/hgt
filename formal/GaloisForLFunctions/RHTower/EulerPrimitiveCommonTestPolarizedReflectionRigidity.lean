import GaloisForLFunctions.RHTower.EulerPrimitiveCommonTestPolarizedChainSource
import GaloisForLFunctions.RHTower.CCMFirstClockPrimitivePromotedExteriorSource
import GaloisForLFunctions.RHTower.DeningerCalderonWittSingularGammaTransgression
import GaloisForLFunctions.RHTower.XiSourceModularTypeSuperselectionLaw

/-!
# Finite-energy rigidity of the polarized reflection boundary

The primitive-current common test has two reflected continuations
`exp (-a t)` and `exp (a t)`.  Before scalar trace their reflection-odd
difference is retained in both source channels.  Its Hardy-tail energy
density is

`(1 - exp (-t)) * (exp (a t) - exp (-a t))^2`.

This module proves an exact source-side admission theorem:

```text
reflection-odd common-test profile has finite Hardy-tail energy
  ↔ modular displacement a is zero.
```

For every nonzero displacement the density itself tends to infinity, so
the obstruction is stronger than failure of bounded continuation or
finite-Rees moderation.  The reflected profile does not land in the
polarized source Hilbert leg at all.

Local rigidity uses no Xi divisor, zero-location statement, Ward premise,
or RH hypothesis.  Final section instantiates displacement at the existing
Xi boundary fracture and records the exact remaining global landing law.
-/

open Filter MeasureTheory Set

namespace RHTower

noncomputable section

/-- Hardy-tail energy density of the reflected common-test difference. -/
def eulerPrimitiveBoundaryReflectionOddTailEnergyDensity
    (a t : ℝ) : ℝ :=
  eulerPrimitiveBoundaryTailWeight t *
    (Real.exp (a * t) - Real.exp (-a * t)) ^ 2

/-- Difference of the two reflected common-test continuations before
scalar trace. -/
def eulerPrimitiveBoundaryPolarizedReflectionOddProfile
    (a : ℝ) : EulerPrimitiveBoundaryPolarizedFeature :=
  (fun t =>
      (eulerPrimitiveBoundaryPolarizedTest ((-a : ℝ) : ℂ)).1 t -
        (eulerPrimitiveBoundaryPolarizedTest (a : ℂ)).1 t,
    fun t =>
      (eulerPrimitiveBoundaryPolarizedTest ((-a : ℝ) : ℂ)).2 t -
        (eulerPrimitiveBoundaryPolarizedTest (a : ℂ)).2 t)

/--
Singular source-pointed fracture vector.  Its head is the fixed
pole-centered Fisher score; its tail is the full reflected common-test
difference.  The critical fibre therefore retains the four-unit source
score while every transverse displacement is tested before trace.
-/
def eulerPrimitiveBoundaryFractureAugmentedSource
    (a : ℝ) : EulerPrimitiveBoundaryPolarizedFeature :=
  (eulerPrimitiveBoundaryPolarizedScore.1,
    (eulerPrimitiveBoundaryPolarizedReflectionOddProfile a).2)

@[simp]
theorem eulerPrimitiveBoundaryFractureAugmentedSource_zero :
    eulerPrimitiveBoundaryFractureAugmentedSource 0 =
      eulerPrimitiveBoundaryPolarizedScore := by
  apply Prod.ext
  · rfl
  · funext t
    simp [eulerPrimitiveBoundaryFractureAugmentedSource,
      eulerPrimitiveBoundaryPolarizedReflectionOddProfile,
      eulerPrimitiveBoundaryPolarizedTest,
      eulerPrimitiveBoundaryPolarizedScore]

/--
Four is the exact norm square of the unique zero-displacement source
fibre.
-/
theorem eulerPrimitiveBoundaryFractureAugmentedSource_zero_pairing :
    eulerPrimitiveBoundaryPolarizedPairing
        (eulerPrimitiveBoundaryFractureAugmentedSource 0)
        (eulerPrimitiveBoundaryFractureAugmentedSource 0) =
      4 := by
  rw [eulerPrimitiveBoundaryFractureAugmentedSource_zero,
    eulerPrimitiveBoundaryPolarizedPairing_score_score]

theorem eulerPrimitiveBoundaryPolarizedReflectionOddProfile_apply
    (a t : ℝ) :
    (eulerPrimitiveBoundaryPolarizedReflectionOddProfile a).1 t =
        ((Real.exp (a * t) - Real.exp (-a * t) : ℝ) : ℂ) ∧
      (eulerPrimitiveBoundaryPolarizedReflectionOddProfile a).2 t =
        ((Real.exp (a * t) - Real.exp (-a * t) : ℝ) : ℂ) := by
  constructor <;>
    simp only [eulerPrimitiveBoundaryPolarizedReflectionOddProfile,
      eulerPrimitiveBoundaryPolarizedTest]
  all_goals
    rw [show
      -(((-a : ℝ) : ℂ)) * (t : ℂ) = ((a * t : ℝ) : ℂ) by
        push_cast
        ring,
      show
        -((a : ℂ)) * (t : ℂ) = ((-a * t : ℝ) : ℂ) by
          push_cast
          ring]
    rw [← Complex.ofReal_exp, ← Complex.ofReal_exp]
    push_cast
    rfl

theorem
    eulerPrimitiveBoundaryPolarizedReflectionOddProfile_tailEnergyDensity
    (a t : ℝ) :
    eulerPrimitiveBoundaryTailWeight t *
        Complex.normSq
          ((eulerPrimitiveBoundaryPolarizedReflectionOddProfile a).2 t) =
      eulerPrimitiveBoundaryReflectionOddTailEnergyDensity a t := by
  rw [
    (eulerPrimitiveBoundaryPolarizedReflectionOddProfile_apply a t).2,
    Complex.normSq_ofReal]
  simp [eulerPrimitiveBoundaryReflectionOddTailEnergyDensity, pow_two]

theorem eulerPrimitiveBoundaryReflectionOddTailEnergyDensity_nonneg
    (a t : ℝ) (ht : 0 ≤ t) :
    0 ≤ eulerPrimitiveBoundaryReflectionOddTailEnergyDensity a t := by
  unfold eulerPrimitiveBoundaryReflectionOddTailEnergyDensity
  exact mul_nonneg
    (by
      rw [eulerPrimitiveBoundaryTailWeight]
      exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))
    (sq_nonneg _)

private theorem
    tendsto_eulerPrimitiveBoundaryReflectionOddTailEnergyDensity_atTop_of_pos
    {a : ℝ} (ha : 0 < a) :
    Tendsto
      (eulerPrimitiveBoundaryReflectionOddTailEnergyDensity a)
      atTop atTop := by
  have hpos :
      Tendsto (fun t : ℝ => Real.exp (a * t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop ha)
  have hzero :
      Tendsto (fun t : ℝ => Real.exp (-a * t)) atTop (nhds 0) := by
    exact Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith : -a < 0))
  have hdiff :
      Tendsto
        (fun t : ℝ => Real.exp (a * t) - Real.exp (-a * t))
        atTop atTop := by
    simpa only [sub_eq_add_neg] using hpos.atTop_add hzero.neg
  have hsq :
      Tendsto
        (fun t : ℝ =>
          (Real.exp (a * t) - Real.exp (-a * t)) ^ 2)
        atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (n := 2) (by norm_num)).comp hdiff
  have htail :
      Tendsto eulerPrimitiveBoundaryTailWeight atTop (nhds 1) := by
    unfold eulerPrimitiveBoundaryTailWeight
    have hneg : Tendsto (fun t : ℝ => -t) atTop atBot :=
      tendsto_neg_atTop_atBot
    simpa using
      tendsto_const_nhds.sub (Real.tendsto_exp_atBot.comp hneg)
  have htailLower :
      ∀ᶠ t : ℝ in atTop,
        (1 / 2 : ℝ) ≤ eulerPrimitiveBoundaryTailWeight t :=
    (htail.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1)).mono
      fun _ h => h.le
  apply tendsto_atTop_mono' atTop
    (htailLower.mono fun t ht => by
      unfold eulerPrimitiveBoundaryReflectionOddTailEnergyDensity
      exact mul_le_mul_of_nonneg_right ht (sq_nonneg _))
  exact hsq.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)

theorem
    tendsto_eulerPrimitiveBoundaryReflectionOddTailEnergyDensity_atTop
    {a : ℝ} (ha : a ≠ 0) :
    Tendsto
      (eulerPrimitiveBoundaryReflectionOddTailEnergyDensity a)
      atTop atTop := by
  rcases lt_or_gt_of_ne ha with haNeg | haPos
  · have h :=
      tendsto_eulerPrimitiveBoundaryReflectionOddTailEnergyDensity_atTop_of_pos
        (a := -a) (neg_pos.mpr haNeg)
    have heq :
        eulerPrimitiveBoundaryReflectionOddTailEnergyDensity a =
          eulerPrimitiveBoundaryReflectionOddTailEnergyDensity (-a) := by
      funext t
      unfold eulerPrimitiveBoundaryReflectionOddTailEnergyDensity
      ring_nf
    rwa [heq]
  · exact
      tendsto_eulerPrimitiveBoundaryReflectionOddTailEnergyDensity_atTop_of_pos
        haPos

theorem
    not_integrableOn_eulerPrimitiveBoundaryReflectionOddTailEnergyDensity
    {a : ℝ} (ha : a ≠ 0) :
    ¬ IntegrableOn
      (eulerPrimitiveBoundaryReflectionOddTailEnergyDensity a)
      (Ioi 0) := by
  intro hint
  have hevent :
      ∀ᶠ t : ℝ in atTop,
        1 ≤ eulerPrimitiveBoundaryReflectionOddTailEnergyDensity a t :=
    (tendsto_eulerPrimitiveBoundaryReflectionOddTailEnergyDensity_atTop ha).eventually_ge_atTop 1
  obtain ⟨T, hT⟩ := eventually_atTop.1 hevent
  let U : ℝ := max T 0
  have hrestrict :
      IntegrableOn
        (eulerPrimitiveBoundaryReflectionOddTailEnergyDensity a)
        (Ioi U) := by
    apply hint.mono_set
    intro t ht
    exact lt_of_le_of_lt (le_max_right T 0) ht
  have hconst :
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi U) := by
    change Integrable
      (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioi U))
    change Integrable
      (eulerPrimitiveBoundaryReflectionOddTailEnergyDensity a)
      (volume.restrict (Ioi U)) at hrestrict
    apply MeasureTheory.Integrable.mono hrestrict
      continuous_const.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hlower :
        1 ≤ eulerPrimitiveBoundaryReflectionOddTailEnergyDensity a t :=
      hT t (le_trans (le_max_left T 0) ht.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1),
      Real.norm_eq_abs,
      abs_of_nonneg
        (eulerPrimitiveBoundaryReflectionOddTailEnergyDensity_nonneg a t
          (le_trans (le_max_right T 0) ht.le))]
    exact hlower
  simp [integrableOn_const_iff] at hconst

theorem
    integrableOn_eulerPrimitiveBoundaryReflectionOddTailEnergyDensity_iff
    (a : ℝ) :
    IntegrableOn
        (eulerPrimitiveBoundaryReflectionOddTailEnergyDensity a)
        (Ioi 0) ↔
      a = 0 := by
  constructor
  · intro h
    by_contra ha
    exact
      not_integrableOn_eulerPrimitiveBoundaryReflectionOddTailEnergyDensity
        ha h
  · rintro rfl
    have hzero :
        eulerPrimitiveBoundaryReflectionOddTailEnergyDensity 0 =
          fun _ : ℝ => 0 := by
      funext t
      simp [eulerPrimitiveBoundaryReflectionOddTailEnergyDensity]
    rw [hzero]
    exact integrableOn_zero

/--
The reflected source pair lands in the actual Hardy-tail Hilbert leg
exactly at zero modular displacement.
-/
theorem
    integrableOn_eulerPrimitiveBoundaryPolarizedReflectionOddProfile_tail_iff
    (a : ℝ) :
    IntegrableOn
        (fun t : ℝ =>
          eulerPrimitiveBoundaryTailWeight t *
            Complex.normSq
              ((eulerPrimitiveBoundaryPolarizedReflectionOddProfile a).2 t))
        (Ioi 0) ↔
      a = 0 := by
  simpa only [
    eulerPrimitiveBoundaryPolarizedReflectionOddProfile_tailEnergyDensity]
    using
      integrableOn_eulerPrimitiveBoundaryReflectionOddTailEnergyDensity_iff a

/--
The singular augmented source has an admissible Hardy tail exactly in its
four-unit critical fibre.
-/
theorem
    integrableOn_eulerPrimitiveBoundaryFractureAugmentedSource_tail_iff
    (a : ℝ) :
    IntegrableOn
        (fun t : ℝ =>
          eulerPrimitiveBoundaryTailWeight t *
            Complex.normSq
              ((eulerPrimitiveBoundaryFractureAugmentedSource a).2 t))
        (Ioi 0) ↔
      a = 0 := by
  exact
    integrableOn_eulerPrimitiveBoundaryPolarizedReflectionOddProfile_tail_iff
      a

/-! ## Prime/depth-labelled exterior source -/

/--
Reflection-odd common test multiplied by the literal promoted
prime/depth exterior amplitude.  Multiplication occurs before any scalar
trace, so both source labels and their exterior incidence remain present.
-/
def xiGammaEulerPrimitivePolarizedReflectionOddCommonTest
    (a : ℝ) (i j : Nat.Primes × ℕ) :
    EulerPrimitiveBoundaryPolarizedFeature :=
  let c : ℂ := xiGammaEulerPrimitiveExteriorCell 0 i j
  let x := eulerPrimitiveBoundaryPolarizedReflectionOddProfile a
  (fun t => c * x.1 t, fun t => c * x.2 t)

theorem
    xiGammaEulerPrimitivePolarizedReflectionOddCommonTest_tailEnergyDensity
    (a : ℝ) (i j : Nat.Primes × ℕ) (t : ℝ) :
    eulerPrimitiveBoundaryTailWeight t *
        Complex.normSq
          ((xiGammaEulerPrimitivePolarizedReflectionOddCommonTest
            a i j).2 t) =
      xiGammaEulerPrimitiveExteriorCell 0 i j ^ 2 *
        eulerPrimitiveBoundaryReflectionOddTailEnergyDensity a t := by
  simp only [xiGammaEulerPrimitivePolarizedReflectionOddCommonTest,
    Complex.normSq_mul, Complex.normSq_ofReal]
  calc
    _ = xiGammaEulerPrimitiveExteriorCell 0 i j ^ 2 *
        (eulerPrimitiveBoundaryTailWeight t *
          Complex.normSq
            ((eulerPrimitiveBoundaryPolarizedReflectionOddProfile a).2 t)) := by
      ring
    _ = _ := by
      rw [
        eulerPrimitiveBoundaryPolarizedReflectionOddProfile_tailEnergyDensity]

theorem
    xiGammaEulerPrimitiveExteriorCell_ne_zero_of_halfHeight_ne
    (i j : Nat.Primes × ℕ)
    (hheight :
      xiGammaEulerBoundaryHalfHeight i.1 i.2 ≠
        xiGammaEulerBoundaryHalfHeight j.1 j.2) :
    xiGammaEulerPrimitiveExteriorCell 0 i j ≠ 0 := by
  unfold xiGammaEulerPrimitiveExteriorCell
  exact mul_ne_zero
    (mul_ne_zero
      (xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 i).ne'
      (xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 j).ne')
    (sub_ne_zero.mpr hheight)

/--
Every nondegenerate literal prime/depth exterior cell has finite
reflection-odd Hardy-tail energy exactly at zero modular displacement.
The primitive promotion changes only the positive prefactor and cannot
hide an off-line fracture.
-/
theorem
    integrableOn_xiGammaEulerPrimitivePolarizedReflectionOddCommonTest_tail_iff
    (a : ℝ) (i j : Nat.Primes × ℕ)
    (hheight :
      xiGammaEulerBoundaryHalfHeight i.1 i.2 ≠
        xiGammaEulerBoundaryHalfHeight j.1 j.2) :
    IntegrableOn
        (fun t : ℝ =>
          eulerPrimitiveBoundaryTailWeight t *
            Complex.normSq
              ((xiGammaEulerPrimitivePolarizedReflectionOddCommonTest
                a i j).2 t))
        (Ioi 0) ↔
      a = 0 := by
  let c := xiGammaEulerPrimitiveExteriorCell 0 i j
  have hc : c ≠ 0 :=
    xiGammaEulerPrimitiveExteriorCell_ne_zero_of_halfHeight_ne i j hheight
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  rw [show
    (fun t : ℝ =>
      eulerPrimitiveBoundaryTailWeight t *
        Complex.normSq
          ((xiGammaEulerPrimitivePolarizedReflectionOddCommonTest
            a i j).2 t)) =
      fun t : ℝ =>
        c ^ 2 *
          eulerPrimitiveBoundaryReflectionOddTailEnergyDensity a t by
      funext t
      exact
        xiGammaEulerPrimitivePolarizedReflectionOddCommonTest_tailEnergyDensity
          a i j t]
  constructor
  · intro h
    apply
      (integrableOn_eulerPrimitiveBoundaryReflectionOddTailEnergyDensity_iff
        a).1
    have hscaled := h.const_mul (c ^ 2)⁻¹
    change Integrable
      (fun t : ℝ =>
        (c ^ 2)⁻¹ *
          (c ^ 2 *
            eulerPrimitiveBoundaryReflectionOddTailEnergyDensity a t))
      (volume.restrict (Ioi 0)) at hscaled
    change Integrable
      (eulerPrimitiveBoundaryReflectionOddTailEnergyDensity a)
      (volume.restrict (Ioi 0))
    apply hscaled.congr
    filter_upwards with t
    · field_simp [hc2]
  · intro ha
    have h :=
      (integrableOn_eulerPrimitiveBoundaryReflectionOddTailEnergyDensity_iff
        a).2 ha
    exact h.const_mul (c ^ 2)

/-! ## Exact Xi-fracture landing boundary -/

/-- Actual polarized source profile at the Xi duality-adjunction
fracture. -/
def xiPrimitiveBoundaryFractureReflectionOddProfile (rho : ℂ) :
    EulerPrimitiveBoundaryPolarizedFeature :=
  eulerPrimitiveBoundaryPolarizedReflectionOddProfile
    (xiNearbyPoleDualityAdjunctionFracture rho).re

/--
Four-unit augmented source fibre at the actual Xi boundary fracture.
-/
def xiPrimitiveBoundaryFractureAugmentedSource (rho : ℂ) :
    EulerPrimitiveBoundaryPolarizedFeature :=
  eulerPrimitiveBoundaryFractureAugmentedSource
    (xiNearbyPoleDualityAdjunctionFracture rho).re

/--
Literal promoted prime/depth exterior common test evaluated at the Xi
duality-adjunction fracture.
-/
def xiGammaEulerPrimitivePolarizedFractureCommonTest
    (rho : ℂ) (i j : Nat.Primes × ℕ) :
    EulerPrimitiveBoundaryPolarizedFeature :=
  xiGammaEulerPrimitivePolarizedReflectionOddCommonTest
    (xiNearbyPoleDualityAdjunctionFracture rho).re i j

/--
A point of the critical strip has a finite-energy reflected source profile
exactly when its real part is on the critical line.
-/
theorem
    integrableOn_xiPrimitiveBoundaryFractureReflectionOddProfile_tail_iff
    (rho : ℂ) :
    IntegrableOn
        (fun t : ℝ =>
          eulerPrimitiveBoundaryTailWeight t *
            Complex.normSq
              ((xiPrimitiveBoundaryFractureReflectionOddProfile rho).2 t))
        (Ioi 0) ↔
      rho.re = 1 / 2 := by
  rw [xiPrimitiveBoundaryFractureReflectionOddProfile,
    integrableOn_eulerPrimitiveBoundaryPolarizedReflectionOddProfile_tail_iff]
  rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  simp
  constructor <;> intro h <;> linarith

theorem
    integrableOn_xiPrimitiveBoundaryFractureAugmentedSource_tail_iff
    (rho : ℂ) :
    IntegrableOn
        (fun t : ℝ =>
          eulerPrimitiveBoundaryTailWeight t *
            Complex.normSq
              ((xiPrimitiveBoundaryFractureAugmentedSource rho).2 t))
        (Ioi 0) ↔
      rho.re = 1 / 2 := by
  rw [xiPrimitiveBoundaryFractureAugmentedSource,
    integrableOn_eulerPrimitiveBoundaryFractureAugmentedSource_tail_iff]
  rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  simp
  constructor <;> intro h <;> linarith

/--
On the critical line the actual Xi-fracture source fibre is literally the
four-unit score, not merely a vector with the same scalar norm.
-/
theorem xiPrimitiveBoundaryFractureAugmentedSource_eq_score
    {rho : ℂ} (hrho : rho.re = 1 / 2) :
    xiPrimitiveBoundaryFractureAugmentedSource rho =
      eulerPrimitiveBoundaryPolarizedScore := by
  rw [xiPrimitiveBoundaryFractureAugmentedSource]
  have hzero :
      (xiNearbyPoleDualityAdjunctionFracture rho).re = 0 := by
    rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
    simp [hrho]
  rw [hzero, eulerPrimitiveBoundaryFractureAugmentedSource_zero]

theorem xiPrimitiveBoundaryFractureAugmentedSource_pairing_eq_four
    {rho : ℂ} (hrho : rho.re = 1 / 2) :
    eulerPrimitiveBoundaryPolarizedPairing
        (xiPrimitiveBoundaryFractureAugmentedSource rho)
        (xiPrimitiveBoundaryFractureAugmentedSource rho) =
      4 := by
  rw [xiPrimitiveBoundaryFractureAugmentedSource_eq_score hrho,
    eulerPrimitiveBoundaryPolarizedPairing_score_score]

/--
On every nondegenerate promoted prime/depth exterior cell, finite-energy
landing of the actual fracture common test is exactly critical-line
placement.
-/
theorem
    integrableOn_xiGammaEulerPrimitivePolarizedFractureCommonTest_tail_iff
    (rho : ℂ) (i j : Nat.Primes × ℕ)
    (hheight :
      xiGammaEulerBoundaryHalfHeight i.1 i.2 ≠
        xiGammaEulerBoundaryHalfHeight j.1 j.2) :
    IntegrableOn
        (fun t : ℝ =>
          eulerPrimitiveBoundaryTailWeight t *
            Complex.normSq
              ((xiGammaEulerPrimitivePolarizedFractureCommonTest
                rho i j).2 t))
        (Ioi 0) ↔
      rho.re = 1 / 2 := by
  rw [xiGammaEulerPrimitivePolarizedFractureCommonTest,
    integrableOn_xiGammaEulerPrimitivePolarizedReflectionOddCommonTest_tail_iff
      _ i j hheight]
  rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  simp
  constructor <;> intro h <;> linarith

/--
Every Xi divisor fibre lands in the finite-energy polarized source
boundary.  This predicate names the remaining global landing assertion;
its local analytic content is no longer hidden.
-/
def XiPrimitiveBoundaryFractureFiniteEnergy : Prop :=
  ∀ rho : XiDivisorSupport,
    IntegrableOn
      (fun t : ℝ =>
        eulerPrimitiveBoundaryTailWeight t *
          Complex.normSq
            ((xiPrimitiveBoundaryFractureReflectionOddProfile
              (rho : ℂ)).2 t))
      (Ioi 0)

/--
Global finite-energy landing law on one fixed nondegenerate,
prime/depth-labelled exterior cell.
-/
def XiPrimitiveBoundaryLabeledFractureFiniteEnergy
    (i j : Nat.Primes × ℕ) : Prop :=
  ∀ rho : XiDivisorSupport,
    IntegrableOn
      (fun t : ℝ =>
        eulerPrimitiveBoundaryTailWeight t *
          Complex.normSq
            ((xiGammaEulerPrimitivePolarizedFractureCommonTest
              (rho : ℂ) i j).2 t))
      (Ioi 0)

theorem
    xiPrimitiveBoundaryFractureFiniteEnergy_iff_boundaryCharacterNeutral :
    XiPrimitiveBoundaryFractureFiniteEnergy ↔
      XiBoundaryCharacterNeutral := by
  constructor
  · intro h rho
    have hre :=
      (integrableOn_xiPrimitiveBoundaryFractureReflectionOddProfile_tail_iff
        (rho : ℂ)).1 (h rho)
    exact
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
        (rho : ℂ)).2 hre
  · intro h rho
    apply
      (integrableOn_xiPrimitiveBoundaryFractureReflectionOddProfile_tail_iff
        (rho : ℂ)).2
    exact
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
        (rho : ℂ)).1 (h rho)

/--
The exact source-Hilbert landing statement is equivalent to RH.  This is
not used as a premise above: it records the precise remaining global
scientific obligation after the unconditional local rigidity theorem.
-/
theorem xiPrimitiveBoundaryFractureFiniteEnergy_iff_riemannHypothesis :
    XiPrimitiveBoundaryFractureFiniteEnergy ↔
      RiemannHypothesis := by
  rw [xiPrimitiveBoundaryFractureFiniteEnergy_iff_boundaryCharacterNeutral,
    xiBoundaryCharacterNeutral_iff_riemannHypothesis]

/--
For every nondegenerate literal exterior cell, its global finite-energy
landing law is exactly RH.  Unlike a scalar divisor coordinate, the
predicate retains the selected prime and valuation-depth labels before
trace.
-/
theorem
    xiPrimitiveBoundaryLabeledFractureFiniteEnergy_iff_riemannHypothesis
    (i j : Nat.Primes × ℕ)
    (hheight :
      xiGammaEulerBoundaryHalfHeight i.1 i.2 ≠
        xiGammaEulerBoundaryHalfHeight j.1 j.2) :
    XiPrimitiveBoundaryLabeledFractureFiniteEnergy i j ↔
      RiemannHypothesis := by
  rw [← xiBoundaryCharacterNeutral_iff_riemannHypothesis]
  constructor
  · intro h rho
    apply
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
        (rho : ℂ)).2
    exact
      (integrableOn_xiGammaEulerPrimitivePolarizedFractureCommonTest_tail_iff
        (rho : ℂ) i j hheight).1 (h rho)
  · intro h rho
    apply
      (integrableOn_xiGammaEulerPrimitivePolarizedFractureCommonTest_tail_iff
        (rho : ℂ) i j hheight).2
    exact
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
        (rho : ℂ)).1 (h rho)

/--
Distinct primes at one common valuation depth automatically give a
nondegenerate polarized reflection-odd source cell.  Thus its local
finite-energy law has no residual height-separation premise.
-/
theorem
    integrableOn_xiGammaEulerPrimitivePolarizedReflectionOddCommonTest_sameDepth_tail_iff
    (a : ℝ) {p q : Nat.Primes} (hpq : p ≠ q) (n : ℕ) :
    IntegrableOn
        (fun t : ℝ =>
          eulerPrimitiveBoundaryTailWeight t *
            Complex.normSq
              ((xiGammaEulerPrimitivePolarizedReflectionOddCommonTest
                a (p, n) (q, n)).2 t))
        (Ioi 0) ↔
      a = 0 :=
  integrableOn_xiGammaEulerPrimitivePolarizedReflectionOddCommonTest_tail_iff
    a (p, n) (q, n)
      (xiGammaEulerBoundaryHalfHeight_ne_of_primes_ne_sameDepth hpq n)

/--
The actual Xi-fracture common test on every distinct-prime same-depth cell
lands in finite Hardy-tail energy exactly on the critical line.
-/
theorem
    integrableOn_xiGammaEulerPrimitivePolarizedFractureCommonTest_sameDepth_tail_iff
    (rho : ℂ) {p q : Nat.Primes} (hpq : p ≠ q) (n : ℕ) :
    IntegrableOn
        (fun t : ℝ =>
          eulerPrimitiveBoundaryTailWeight t *
            Complex.normSq
              ((xiGammaEulerPrimitivePolarizedFractureCommonTest
                rho (p, n) (q, n)).2 t))
        (Ioi 0) ↔
      rho.re = 1 / 2 :=
  integrableOn_xiGammaEulerPrimitivePolarizedFractureCommonTest_tail_iff
    rho (p, n) (q, n)
      (xiGammaEulerBoundaryHalfHeight_ne_of_primes_ne_sameDepth hpq n)

/--
Every distinct-prime same-depth labeled exterior cell is independently a
complete finite-energy criterion for RH; no auxiliary source-height
nondegeneracy hypothesis remains.
-/
theorem
    xiPrimitiveBoundaryLabeledFractureFiniteEnergy_sameDepth_iff_riemannHypothesis
    {p q : Nat.Primes} (hpq : p ≠ q) (n : ℕ) :
    XiPrimitiveBoundaryLabeledFractureFiniteEnergy (p, n) (q, n) ↔
      RiemannHypothesis :=
  xiPrimitiveBoundaryLabeledFractureFiniteEnergy_iff_riemannHypothesis
    (p, n) (q, n)
      (xiGammaEulerBoundaryHalfHeight_ne_of_primes_ne_sameDepth hpq n)

/--
One fixed source cell already detects the global landing law: the
prime-two/prime-three depth-zero polarized boundary has finite energy on
every Xi divisor fibre exactly when RH holds.
-/
theorem
    xiPrimitiveBoundaryLabeledFractureFiniteEnergy_primeTwoThree_iff_riemannHypothesis
    :
    XiPrimitiveBoundaryLabeledFractureFiniteEnergy
        (⟨2, Nat.prime_two⟩, 0)
        (⟨3, Nat.prime_three⟩, 0) ↔
      RiemannHypothesis := by
  apply
    xiPrimitiveBoundaryLabeledFractureFiniteEnergy_sameDepth_iff_riemannHypothesis
      (n := 0)
  intro h
  have hval := congrArg (fun r : Nat.Primes => (r : ℕ)) h
  norm_num at hval

end

end RHTower
