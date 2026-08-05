import GaloisForLFunctions.HTGeometry.ObserverReturnTemporalMetricLaw

/-!
# Nondegenerate observer temporal metrics exist

The return-metric law assumes that the gap family separates temporal coordinates: only the zero
shift is annihilated by every visible gap.  That is exactly injectivity of the coordinate action,
and it holds as soon as the gap family contains a coordinate readout — an observer whose gap
vector is the `k`-th coordinate functional, for every `k`.

The identity gap family is such a system, so the law is not vacuous; a gap family that is
identically zero fails it as soon as there is a nonzero shift, so the hypothesis is not free.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **A coordinate readout makes the temporal metric nondegenerate.**  If some observer reads each
coordinate on its own, no nonzero shift can be invisible. -/
theorem observerTemporalMetricNondegenerate_of_coordinateReadout
    {J κ : Type*} [Fintype κ] [DecidableEq κ]
    (gap : J → κ → ℝ) (ι : κ → J)
    (h : ∀ k k', gap (ι k) k' = if k = k' then 1 else 0) :
    ObserverTemporalMetricNondegenerate gap := by
  intro theta hzero
  funext k
  have hk := hzero (ι k)
  rw [observerTemporalCoordinateAction] at hk
  have hsum : ∑ k', gap (ι k) k' * theta k' = theta k := by
    rw [Finset.sum_congr rfl fun k' _ => by rw [h k k']]
    simp
  rw [hsum] at hk
  simpa using hk

/-- The identity gap family is nondegenerate. -/
theorem observerTemporalMetricNondegenerate_id {κ : Type*} [Fintype κ] [DecidableEq κ] :
    ObserverTemporalMetricNondegenerate (fun k k' : κ => if k = k' then (1 : ℝ) else 0) :=
  observerTemporalMetricNondegenerate_of_coordinateReadout _ id fun _ _ => rfl

/-- Nondegeneracy is a real condition: a blind gap family fails it whenever a nonzero shift
exists. -/
theorem not_observerTemporalMetricNondegenerate_zero
    {J κ : Type*} [Fintype κ] [Nonempty κ] :
    ¬ ObserverTemporalMetricNondegenerate (fun _ : J => fun _ : κ => (0 : ℝ)) := by
  intro h
  have hzero : (fun _ : κ => (1 : ℝ)) = 0 := by
    refine h _ fun j => ?_
    rw [observerTemporalCoordinateAction]
    simp
  have := congrFun hzero (Classical.arbitrary κ)
  norm_num at this

end

end GaloisForLFunctions.HTGeometry
