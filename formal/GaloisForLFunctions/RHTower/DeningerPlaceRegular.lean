import GaloisForLFunctions.RHTower.DeningerPlaceMeasure

/-!
# The counting measure of a discrete space is regular, and the scale over the places

In a discrete space every set is open, so outer regularity is trivial, and every finite set is
compact, so a set of infinite counting measure is approximated from inside by finite subsets of
arbitrarily large cardinality.  The counting measure is therefore regular, which is the last
hypothesis needed for the test space to be dense in `L²`.

Collecting the pieces: over the space of places of a number field the test space maps densely and
continuously into the completion of the `ℓ¹` — that is, the height — seminorm, and that completion
maps densely into `L²`, with the composite the canonical embedding.

* `deningerCount_regular` : **the counting measure of a discrete space is regular.**
* `deningerPlaceScale` : **the scale of test space, height completion and `L²` over the places.**
-/

namespace RHTower

open MeasureTheory NumberField

section CountRegular

variable {X : Type*} [TopologicalSpace X] [DiscreteTopology X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
theorem deningerCount_outerRegular : (Measure.count : Measure X).OuterRegular := by
  constructor
  intro A _ r hr
  exact ⟨A, subset_rfl, isOpen_discrete A, hr⟩

theorem deningerCount_innerRegular :
    (Measure.count : Measure X).InnerRegularWRT IsCompact IsOpen := by
  intro U _ r hr
  by_cases hfin : U.Finite
  · exact ⟨U, subset_rfl, hfin.isCompact, hr⟩
  · have hinf : U.Infinite := hfin
    have hrne : r ≠ ⊤ := hr.ne_top
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hrne
    obtain ⟨t, htU, htcard⟩ := hinf.exists_subset_card_eq n
    refine ⟨(t : Set X), htU, t.finite_toSet.isCompact, ?_⟩
    rw [Measure.count_apply_finite _ t.finite_toSet]
    have hcard : t.finite_toSet.toFinset.card = n := by
      rw [Finset.finite_toSet_toFinset, htcard]
    rw [hcard]
    exact hn

/-- **The counting measure of a discrete space is regular.** -/
theorem deningerCount_regular : (Measure.count : Measure X).Regular := by
  haveI : IsFiniteMeasureOnCompacts (Measure.count : Measure X) := by
    constructor
    intro s hs
    rw [Measure.count_apply_finite s hs.finite_of_discrete]
    exact ENNReal.natCast_lt_top _
  haveI := deningerCount_outerRegular (X := X)
  exact ⟨deningerCount_innerRegular⟩

end CountRegular

section PlaceScale

variable (K : Type*) [Field K] [NumberField K]

instance : (Measure.count : Measure (DeningerPlace K)).Regular := deningerCount_regular

/-- **The scale over the places of a number field**: the test space maps densely into the
completion of the height seminorm, which maps densely into `L²`, and the composite is the
canonical embedding. -/
theorem deningerPlaceScale :
    DenseRange (deningerSeminormMkC (deningerL1Seminorm K)) ∧
      DenseRange (deningerSeminormFactorC (deningerPlaceToL2_norm_le K)) ∧
      ∀ g, deningerSeminormFactorC (deningerPlaceToL2_norm_le K)
          (deningerSeminormMkC (deningerL1Seminorm K) g)
        = deningerTestToL2 (Measure.count : Measure (DeningerPlace K)) g :=
  deningerTestScale_three_step (Measure.count : Measure (DeningerPlace K))
    (deningerPlaceToL2_norm_le K)

end PlaceScale

end RHTower
