import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularSourceReflection
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularCausalPeierlsPairing
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGeneralTemporalTransposition
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWCompletedCTPOriginalCapLiftBridge

/-!
# PW-B literal ordered CTP source-domain transport

The full two-event direct-minus-image source is transported through the
source-based affine null chart. Both original physical-event restrictions and
the translated image causal face remain explicit. Fubini and the exact
Jacobian identify the completed CTP numerator with the nested null integral;
the existing cap/lift normal form then shows that both lift defects survive.

This closes source-domain transport, not the noncompact Goursat
transposition-to-current, fixed-grade PW magnitude, or all-divisor extinction.
-/

open MeasureTheory Set
open scoped ENNReal

namespace RHTower.D4BMPWOrderedCTPNullTransport
open D4BMFullSourceReciprocity D4BMGeneralTemporalTransposition
open D4BMFullAngularSourceReflection D4BMFullAngularReconstruction
open D4BMFullAngularCircle D4BMModularCore D4BMJointSource

noncomputable section
set_option autoImplicit false

private theorem event_integral_null_chart (s y : ℝ) (F : Event → ℂ) :
    (∫ p : Event, F p ∂eventMeasure) =
      (1 / 2 : ℂ) * ∫ z : ℝ × ℝ,
        (Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ)).indicator F (pastVertex s y z) := by
  let S : Set Event := Ioi 0 ×ˢ Iio 0
  have hmap := integral_pastVertex s y (S.indicator F)
  have hevent : (∫ p : Event, F p ∂eventMeasure) =
      ∫ p : Event, S.indicator F p := by
    rw [eventMeasure, Measure.prod_restrict, ← Measure.volume_eq_prod,
      integral_indicator (measurableSet_Ioi.prod measurableSet_Iio)]
  rw [hevent]
  change (∫ p : Event, S.indicator F p) =
    (1 / 2 : ℂ) * ∫ z : ℝ × ℝ, S.indicator F (pastVertex s y z)
  linear_combination -hmap / 2

private theorem direct_gate_local (u v : ℝ) :
    |(u - v) / 2| ≤ (u + v) / 2 ↔ 0 ≤ u ∧ 0 ≤ v := by
  rw [abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

private theorem image_gate_local (y u v : ℝ) :
    |2 * y + (u - v) / 2| ≤ (u + v) / 2 ↔
      0 ≤ u + 2 * y ∧ 0 ≤ v - 2 * y := by
  rw [abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

private theorem kernel_null (q : XiZeroCopy) (branch : Bool)
    (y u v X k : ℝ) :
    angularDirichletKernel q branch ((u + v) / 2)
      (y + (u - v) / 2) y X k =
      ((if 0 ≤ u ∧ 0 ≤ v then
          angularMean q branch (Real.arcosh
            (D4BMCausalKernel.invariant ((u + v) / 2) (y + (u - v) / 2) y)) X k
          else 0) -
        (if 0 ≤ u + 2 * y ∧ 0 ≤ v - 2 * y then
          angularMean q branch (Real.arcosh
            (D4BMCausalKernel.invariant ((u + v) / 2) (y + (u - v) / 2) (-y))) X k
          else 0)) / 2 := by
  simp only [angularDirichletKernel, add_sub_cancel_left]
  rw [show y + (u - v) / 2 + y = 2 * y + (u - v) / 2 by ring]
  simp only [direct_gate_local, image_gate_local]

/-- Full two-leg source in the direct null chart, with the original physical
event wedge and both shifted causal gates retained. -/
def nullSourcePairDensity (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) (r z : Event) : ℂ :=
  let p := pastVertex r.1 r.2 z
  if 0 < p.1 ∧ p.2 < 0 then
    timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
      (((if 0 ≤ z.1 ∧ 0 ≤ z.2 then
          angularMean q branch (Real.arcosh
            (D4BMCausalKernel.invariant ((z.1 + z.2) / 2) p.2 r.2)) X k
          else 0) -
        (if 0 ≤ z.1 + 2 * r.2 ∧ 0 ≤ z.2 - 2 * r.2 then
          angularMean q branch (Real.arcosh
            (D4BMCausalKernel.invariant ((z.1 + z.2) / 2) p.2 (-r.2))) X k
          else 0)) / 2) *
      timeReducedCoefficient (physicalRate q c) d r.1 r.2
  else 0

private theorem nullSourcePairDensity_eq_indicator (q : XiZeroCopy)
    (branch b c : Bool) (a d : ℂ) (X k : ℝ) (r z : Event) :
    nullSourcePairDensity q branch b c a d X k r z =
      (Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ)).indicator
        (fun p => fullCircleSourcePairDensity q branch b c a d X k (p,r))
        (pastVertex r.1 r.2 z) := by
  let p := pastVertex r.1 r.2 z
  by_cases hp : 0 < p.1 ∧ p.2 < 0
  · have hmem : p ∈ Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ) := hp
    rw [Set.indicator_of_mem hmem]
    have hdelay : r.1 - p.1 = (z.1 + z.2) / 2 := by
      dsimp [p, pastVertex]
      ring
    have hradius : p.2 = r.2 + (z.1 - z.2) / 2 := rfl
    unfold nullSourcePairDensity fullCircleSourcePairDensity
    rw [if_pos hp, hdelay, hradius, kernel_null]
  · have hnot : p ∉ Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ) := hp
    rw [Set.indicator_of_notMem hnot]
    exact if_neg hp

theorem fullCircleSourcePair_inner_null (q : XiZeroCopy)
    (branch b c : Bool) (a d : ℂ) (X k : ℝ) (r : Event) :
    (∫ p : Event, fullCircleSourcePairDensity q branch b c a d X k (p,r)
      ∂eventMeasure) =
      (1 / 2 : ℂ) * ∫ z : Event,
        nullSourcePairDensity q branch b c a d X k r z := by
  rw [event_integral_null_chart]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun z => (nullSourcePairDensity_eq_indicator q branch b c a d X k r z).symm)

theorem fullCircleSourcePair_double_null (q : XiZeroCopy)
    (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    (∫ z : Event × Event, fullCircleSourcePairDensity q branch b c a d X k z
      ∂eventMeasure.prod eventMeasure) =
      ∫ r : Event, (1 / 2 : ℂ) *
        (∫ z : Event, nullSourcePairDensity q branch b c a d X k r z)
        ∂eventMeasure := by
  have hi : Integrable (fullCircleSourcePairDensity q branch b c a d X k)
      (eventMeasure.prod eventMeasure) := by
    exact D4BMFullAngularCausalPeierls.fullSourcePairDensity_integrable q branch b c a d X k
  calc
    _ = ∫ r : Event, ∫ p : Event,
        fullCircleSourcePairDensity q branch b c a d X k (p,r)
        ∂eventMeasure ∂eventMeasure :=
          integral_prod_symm (μ := eventMeasure) (ν := eventMeasure) _ hi
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun r => fullCircleSourcePair_inner_null q branch b c a d X k r)

/-- Exact original direct-minus-image ordered CTP source, now in its physical
nonseparable null chart. -/
def orderedNullBranch (q : XiZeroCopy) (branch : Bool)
    (a : ℂ) (X k : ℝ) : ℂ :=
  (∫ r : Event, (1 / 2 : ℂ) *
      (∫ z : Event, nullSourcePairDensity q branch false true a a X k r z)
      ∂eventMeasure) -
    ∫ r : Event, (1 / 2 : ℂ) *
      (∫ z : Event, nullSourcePairDensity q branch true false a a X k r z)
      ∂eventMeasure

theorem fullCircleCrossBranchCausalPair_eq_orderedNullBranch (q : XiZeroCopy)
    (branch : Bool) (a : ℂ) (X k : ℝ) :
    fullCircleCrossBranchCausalPair q branch a X k =
      orderedNullBranch q branch a X k := by
  unfold fullCircleCrossBranchCausalPair orderedNullBranch
  rw [fullCircleSourcePair_double_null, fullCircleSourcePair_double_null]

theorem fullCircleCrossBranchSymmetricCausalPair_eq_orderedNull
    (q : XiZeroCopy) (a : ℂ) (X k : ℝ) :
    fullCircleCrossBranchSymmetricCausalPair q a X k =
      orderedNullBranch q true a X k + orderedNullBranch q false a X k := by
  unfold fullCircleCrossBranchSymmetricCausalPair
  rw [fullCircleCrossBranchCausalPair_eq_orderedNullBranch,
    fullCircleCrossBranchCausalPair_eq_orderedNullBranch]

/-- The null-chart transport retains the original cap and both full-minus-native
lift defects: no image leg or physical boundary contact is dropped. -/
theorem orderedNull_completed_eq_original_cap_lift
    (q : XiZeroCopy) (a : ℂ) (X k : ℝ) :
    orderedNullBranch q true a X k + orderedNullBranch q false a X k =
      2 * RHTower.pwbOriginalNativeCapFunctional q a X k +
        D4BMLiteralCyclicPeierlsLiftDefect.causalSourceLiftDefect
          q true true false a a X k +
        D4BMLiteralCyclicPeierlsLiftDefect.causalSourceLiftDefect
          q false true false a a X k := by
  rw [← fullCircleCrossBranchSymmetricCausalPair_eq_orderedNull]
  exact RHTower.pwb_completedCTP_original_cap_lift_exact q a X k

end
end RHTower.D4BMPWOrderedCTPNullTransport
