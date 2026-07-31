import GaloisForLFunctions.HTGeometry.ProjectiveHorizonMinorFamily

/-!
# Minor ratios and the rank-one horizon field

Ratios of the minor observables of a covector span are again observables of that span, and they are
the normalised quantities of the moving-frame picture: the rank-`(r+1)` minor divided by the rank-`r`
minor is the transverse jet with its span component removed.

For an elementary span the horizon field visibly contains the tower of the chart denominator
together with the positive-order chart jets, while the zeroth-order chart coordinates are moved by
the chart translations.  The elementary horizon field therefore sits strictly between those two
descriptions.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## Minor ratios -/

/-- The normalised transverse jet of a span: the rank-`(r+1)` minor divided by the rank-`r`
minor. -/
def jetMinorRatio (t : Finset n) (k : n) : HomogeneousJetField n K :=
  jetDet (insert k t) / jetDet t

/-- **Minor ratios are observables.**  The normalised transverse jets of a span lie in its horizon
field. -/
theorem jetMinorRatio_mem_horizonField (t : Finset n) (k : n) :
    jetMinorRatio (K := K) t k ∈ horizonField (K := K) (↑t : Set n) :=
  div_mem (jetDet_insert_mem_horizonField k) (jetDet_mem_horizonField t)

/-! ## The elementary horizon field -/

/-- Observables of an elementary span visible by inspection: the tower of the chart denominator and
the positive-order chart jets. -/
def chartHorizonGenerators (i : n) (K : Type*) [Field K] : Set (HomogeneousJetField n K) :=
  (Set.range fun l : ℕ => freeCoordinate K (n × ℕ) (i, l)) ∪ chartTailGenerators i K

/-- **Lower description of the elementary horizon field.**  The chart-denominator tower and the
positive-order chart jets are all observables of `ker e_i^*`. -/
theorem chartHorizonGenerators_adjoin_le_horizonField (i : n) :
    IntermediateField.adjoin K (chartHorizonGenerators i K) ≤
      horizonField (K := K) {i} := by
  rw [IntermediateField.adjoin_le_iff]
  rintro f (⟨l, rfl⟩ | hf)
  · exact freeCoordinate_mem_horizonField_self i l
  · exact chartTailField_le_horizonField i (IntermediateField.subset_adjoin K _ hf)

/-- **The zeroth-order chart coordinates are not observables.**  A chart translation moves them, so
the horizon field of `ker e_i^*` is strictly smaller than the chart field. -/
theorem affineCoord_notMem_horizonField {i k : n} (hk : k ≠ i) :
    affineCoord (K := K) i k ∉ horizonField (K := K) {i} := by
  intro hmem
  have hfix := (mem_horizonField_iff'.1 hmem) _ (chartUnitTranslation_mem (K := K) hk)
  rw [linearJetAction_affineCoord_of_mem hk (chartUnitTranslation_mem (K := K) hk),
    chartUnitTranslation_inv_apply hk k hk, if_pos rfl, map_one] at hfix
  exact one_ne_zero (add_eq_left.1 hfix)

/-- The elementary horizon field is a proper subfield of the homogeneous jet field. -/
theorem horizonField_singleton_ne_top [Nontrivial n] (i : n) :
    horizonField (K := K) {i} ≠ ⊤ := by
  obtain ⟨k, hk⟩ := exists_ne i
  intro hcon
  exact affineCoord_notMem_horizonField (K := K) hk (hcon ▸ trivial)

end

end GaloisForLFunctions.HTGeometry
