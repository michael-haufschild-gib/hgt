import GaloisForLFunctions.HTGeometry.TopologicallyAdmittedHahnLabel
import GaloisForLFunctions.HTGeometry.TopologicallyAdmittedFellerAdmission

/-!
# Event marginals, timing ambiguity, and hidden clock state

Gebbie, arXiv:2608.22497v2, Propositions 1--3 distinguish an event law from a
joint event/timing law and from its observable projection. The corpus's finite
channels admit an injectively parameterized family of compatible timing laws.
For arbitrary joint finite laws, the exact information omitted by both marginals
is a signed residual with zero row and column sums. A deterministic two-phase
clock also exhibits failure of state-only transition closure.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
noncomputable section

namespace FiniteProbabilityLaw
variable {Y Z : Type*} [Fintype Y] [Fintype Z]

/-- Event marginal of an actual finite joint law. -/
def eventMarginal (p : FiniteProbabilityLaw (Y × Z)) : FiniteProbabilityLaw Y where
  prob y := ∑ z, p.prob (y, z)
  nonneg y := Finset.sum_nonneg fun z _ => p.nonneg (y, z)
  sum_prob := by rw [← Fintype.sum_prod_type]; exact p.sum_prob

/-- Timing marginal of the same joint law. -/
def timingMarginal (p : FiniteProbabilityLaw (Y × Z)) : FiniteProbabilityLaw Z where
  prob z := ∑ y, p.prob (y, z)
  nonneg z := Finset.sum_nonneg fun y _ => p.nonneg (y, z)
  sum_prob := by rw [Finset.sum_comm, ← Fintype.sum_prod_type]; exact p.sum_prob

/-- Independent event/timing completion, one canonical choice among compatible laws. -/
def independentTiming (p : FiniteProbabilityLaw Y) (q : FiniteProbabilityLaw Z) :
    FiniteProbabilityLaw (Y × Z) where
  prob yz := p.prob yz.1 * q.prob yz.2
  nonneg yz := mul_nonneg (p.nonneg _) (q.nonneg _)
  sum_prob := by simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, q.sum_prob, mul_one]; exact p.sum_prob

/-- The part of the joint law that neither marginal records. -/
def timingCorrelation (p : FiniteProbabilityLaw (Y × Z)) (y : Y) (z : Z) : ℝ :=
  p.prob (y, z) - p.eventMarginal.prob y * p.timingMarginal.prob z

/-- Every event row of the correlation residual has zero total mass. -/
theorem timingCorrelation_row (p : FiniteProbabilityLaw (Y × Z)) (y : Y) :
    ∑ z, p.timingCorrelation y z = 0 := by
  simp only [timingCorrelation, Finset.sum_sub_distrib, ← Finset.mul_sum,
    p.timingMarginal.sum_prob, mul_one, eventMarginal, sub_self]

/-- Every timing column of the same residual has zero total mass. -/
theorem timingCorrelation_column (p : FiniteProbabilityLaw (Y × Z)) (z : Z) :
    ∑ y, p.timingCorrelation y z = 0 := by
  simp only [timingCorrelation, Finset.sum_sub_distrib, ← Finset.sum_mul,
    p.eventMarginal.sum_prob, one_mul, timingMarginal, sub_self]

/-- Marginals plus the zero-marginal residual reconstruct the entire joint law. -/
theorem timingCorrelation_reconstruct (p : FiniteProbabilityLaw (Y × Z)) :
    p.prob = fun yz =>
      (p.eventMarginal.independentTiming p.timingMarginal).prob yz +
        p.timingCorrelation yz.1 yz.2 := by
  funext yz
  simp only [timingCorrelation, independentTiming]
  ring

/-- The residual is precisely the covariance of every separated event/timing probe. -/
theorem timingCorrelation_covariance (p : FiniteProbabilityLaw (Y × Z))
    (f : Y → ℝ) (g : Z → ℝ) :
    (∑ y, ∑ z, p.prob (y, z) * f y * g z) -
      (∑ y, p.eventMarginal.prob y * f y) * (∑ z, p.timingMarginal.prob z * g z) =
      ∑ y, ∑ z, p.timingCorrelation y z * f y * g z := by
  simp only [timingCorrelation, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- Independence is equivalent to vanishing of every entry of the omitted residual. -/
theorem timingCorrelation_zero_iff (p : FiniteProbabilityLaw (Y × Z)) :
    (∀ y z, p.timingCorrelation y z = 0) ↔
      p.prob = (p.eventMarginal.independentTiming p.timingMarginal).prob := by
  simp only [timingCorrelation, sub_eq_zero, funext_iff, independentTiming]
  exact ⟨fun h yz => h yz.1 yz.2, fun h y z => h (y, z)⟩
end FiniteProbabilityLaw

namespace FiniteChannel
variable {X Y : Type*} [Fintype Y]

/-- A waiting time taking two positive labels, with independently variable timing mass. -/
def twoClockLift (K : FiniteChannel X Y) (θ : unitInterval) : FiniteChannel X (Y × Bool) where
  weight x yb := K.weight x yb.1 * (if yb.2 then (θ : ℝ) else 1 - (θ : ℝ))
  weight_nonneg x yb := mul_nonneg (K.weight_nonneg _ _)
    (by split_ifs; exact θ.property.1; exact sub_nonneg.mpr θ.property.2)
  row_sum x := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true,
      if_false, if_true]
    have h (y : Y) : K.weight x y * (θ : ℝ) + K.weight x y * (1 - (θ : ℝ)) = K.weight x y := by ring
    simp_rw [h]
    exact K.row_sum x

/-- Every timing parameter preserves exactly the same event channel. -/
theorem twoClockLift_eventMarginal (K : FiniteChannel X Y) (θ : unitInterval)
    (x : X) (y : Y) :
    (∑ b : Bool, (K.twoClockLift θ).weight x (y, b)) = K.weight x y := by
  simp only [twoClockLift, Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]
  ring

/-- The timing parameter is recovered by a single timing event. -/
theorem twoClockLift_timingMarginal (K : FiniteChannel X Y) (θ : unitInterval) (x : X) :
    (∑ y, (K.twoClockLift θ).weight x (y, true)) = (θ : ℝ) := by
  simp only [twoClockLift, if_true, ← Finset.sum_mul, K.row_sum, one_mul]

/-- Compatible timing remains freely identifiable after the event law is fixed. -/
theorem twoClockLift_injective (K : FiniteChannel X Y) (x : X) :
    Function.Injective K.twoClockLift := by
  intro θ η h
  apply Subtype.ext
  have hmass := congrArg (fun J : FiniteChannel X (Y × Bool) => ∑ y, J.weight x (y, true)) h
  simpa only [twoClockLift_timingMarginal] using hmass

/-- Event-only data cannot select a unique compatible joint law. -/
theorem exists_distinct_compatible_timing (K : FiniteChannel X Y) (x : X) :
    ∃ J₀ J₁ : FiniteChannel X (Y × Bool), J₀ ≠ J₁ ∧
      (∀ x y, (∑ b : Bool, J₀.weight x (y, b)) = K.weight x y) ∧
      (∀ x y, (∑ b : Bool, J₁.weight x (y, b)) = K.weight x y) := by
  refine ⟨K.twoClockLift 0, K.twoClockLift 1, ?_, K.twoClockLift_eventMarginal 0,
    K.twoClockLift_eventMarginal 1⟩
  exact fun h => zero_ne_one ((K.twoClockLift_injective x) h)

/-- Adding independent timing preserves the full signed decision current up to its timing factor. -/
theorem twoClockLift_push_current [Fintype X] (K : FiniteChannel X Y)
    (E : FiniteBinaryExperiment X) (θ : unitInterval) (y : Y) (b : Bool) :
    ((K.twoClockLift θ).push E).current (y, b) =
      (K.push E).current y * (if b then (θ : ℝ) else 1 - (θ : ℝ)) := by
  simp only [push_current, twoClockLift, ← mul_assoc, ← Finset.sum_mul]

/-- Independent timing adds no information for discriminating the two event laws. -/
theorem twoClockLift_push_tv [Fintype X] (K : FiniteChannel X Y)
    (E : FiniteBinaryExperiment X) (θ : unitInterval) :
    ((K.twoClockLift θ).push E).tv = (K.push E).tv := by
  simp only [FiniteBinaryExperiment.tv, Fintype.sum_prod_type,
    Fintype.sum_bool, twoClockLift_push_current, Bool.false_eq_true, if_false, if_true,
    abs_mul, abs_of_nonneg θ.property.1,
    abs_of_nonneg (sub_nonneg.mpr θ.property.2)]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  ring

end FiniteChannel

/-- A two-phase clock: first age in place, then jump and reset age. -/
def delayedBinaryEventStep (s : Bool × Bool) : Bool × Bool :=
  if s.2 then (!s.1, false) else (s.1, true)

/-- A deterministic event model can fail to close after its clock phase is forgotten. -/
theorem delayedBinaryEventStep_no_stateOnly_closure :
    ¬ ∃ f : Bool → Bool, Prod.fst ∘ delayedBinaryEventStep = f ∘ Prod.fst := by
  rintro ⟨f, h⟩
  have h₀ := congrFun h (false, false)
  have h₁ := congrFun h (false, true)
  simp only [Function.comp_apply, delayedBinaryEventStep, Bool.false_eq_true,
    if_false, if_true, Bool.not_false] at h₀ h₁
  exact Bool.false_ne_true (h₀.trans h₁.symm)

end
end GaloisForLFunctions.HTGeometry
