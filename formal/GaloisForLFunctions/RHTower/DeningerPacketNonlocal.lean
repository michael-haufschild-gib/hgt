import GaloisForLFunctions.RHTower.DeningerPacketAverage
import GaloisForLFunctions.RHTower.DeningerTransversePartition
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The packet average is not a local operation

Evaluating the packet average uses the values of a function on the whole packet: two continuous
functions agreeing on a proper clopen piece can have different averages.  So the average is not an
endomorphism of an ordinary sheaf, whose value on a piece of a disjoint clopen decomposition is
determined by the restriction to that piece.

Consequently the kernel of the average is not trivial: a clopen piece of intermediate mass gives a
nonconstant mode of vanishing average, which survives in the packet coefficient.

* `deningerPacketAv_indicator` : the average of a clopen indicator is its mass.
* `deningerPacketAv_not_local` : the average is not determined by a proper clopen restriction.
* `deningerPacketAv_ker_ne_bot` : the kernel of the average contains a nonzero mode.
-/

namespace RHTower

open MeasureTheory Set

section Nonlocal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- The indicator of a clopen set as a continuous function. -/
noncomputable def deningerClopenFun {D : Set X} (hD : IsClopen D) : C(X, ℝ) :=
  ⟨D.indicator fun _ => (1 : ℝ), deningerClopenIndicator_continuous hD⟩

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
@[simp] theorem deningerClopenFun_apply {D : Set X} (hD : IsClopen D) (x : X) :
    deningerClopenFun hD x = D.indicator (fun _ => (1 : ℝ)) x := rfl

/-- **The average of a clopen indicator is its mass.** -/
theorem deningerPacketAv_indicator {D : Set X} (hD : IsClopen D) :
    deningerPacketAv μ (deningerClopenFun hD) = μ.real D := by
  show (∫ x, D.indicator (fun _ => (1 : ℝ)) x ∂μ) = μ.real D
  rw [integral_indicator_const (1 : ℝ) hD.isClosed.measurableSet, smul_eq_mul, mul_one]

/-- **The average is not a local operation.**  Two continuous functions agreeing on a proper clopen
piece can have different averages, so the average is not an endomorphism of an ordinary sheaf. -/
theorem deningerPacketAv_not_local {D : Set X} (hD : IsClopen D) (hlt : μ.real D < 1) :
    ∃ f g : C(X, ℝ), (∀ x ∈ D, f x = g x)
      ∧ deningerPacketAv μ f ≠ deningerPacketAv μ g := by
  refine ⟨0, deningerClopenFun hD.compl, fun x hx => ?_, ?_⟩
  · show (0 : ℝ) = Dᶜ.indicator (fun _ => (1 : ℝ)) x
    rw [Set.indicator_of_notMem (by simpa using hx)]
  · rw [map_zero, deningerPacketAv_indicator, measureReal_compl hD.isClosed.measurableSet, probReal_univ]
    intro h
    exact absurd h.symm (ne_of_gt (by linarith))

/-- **The kernel of the average contains a nonzero mode.**  A clopen piece of intermediate mass
gives a nonconstant function of vanishing average. -/
theorem deningerPacketAv_ker_ne_bot {D : Set X} (hD : IsClopen D) (hpos : 0 < μ.real D)
    (hlt : μ.real D < 1) :
    ∃ f : C(X, ℝ), deningerPacketAv μ f = 0 ∧ f ≠ 0 := by
  refine ⟨deningerClopenFun hD - deningerPacketIncl (μ.real D), ?_, ?_⟩
  · rw [map_sub, deningerPacketAv_indicator, deningerPacketAv_incl, sub_self]
  · have hne : D.Nonempty := by
      by_contra hempty
      rw [not_nonempty_iff_eq_empty] at hempty
      rw [hempty] at hpos
      simp at hpos
    obtain ⟨x, hx⟩ := hne
    intro hzero
    have hval : (deningerClopenFun hD - deningerPacketIncl (μ.real D) : C(X, ℝ)) x = 0 := by
      rw [hzero]
      rfl
    rw [ContinuousMap.sub_apply, deningerClopenFun_apply, Set.indicator_of_mem hx,
      deningerPacketIncl_apply] at hval
    linarith

end Nonlocal

end RHTower
