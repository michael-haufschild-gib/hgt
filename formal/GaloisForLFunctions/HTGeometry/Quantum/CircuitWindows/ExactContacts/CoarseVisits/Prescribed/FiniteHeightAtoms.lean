import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.PrefixProbability

/-! # Positive-probability values of a finite random set of heights -/

open Filter MeasureTheory Set Topology
namespace GaloisForLFunctions.HTGeometry.ExactContacts.CoarseVisits.Prescribed
noncomputable section

/-- Only finitely many points can occur with probability bounded below
in an almost surely finite random set. No bound on its mean size is needed. -/
theorem finite_frequent_heights {Ω Y : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Ω → Set Y) (hm : ∀ y, MeasurableSet {x | y ∈ S x})
    (hfin : ∀ᵐ x ∂μ, (S x).Finite) {p : ℝ} (hp : 0 < p) :
    {y | p ≤ μ.real {x | y ∈ S x}}.Finite := by
  classical
  let B := {y | p ≤ μ.real {x | y ∈ S x}}
  by_contra h
  let f := Set.Infinite.natEmbedding B h
  let y (j : ℕ) := (f j).val
  have hinj : Function.Injective y := Subtype.val_injective.comp f.injective
  have hmiss : ∀ᵐ x ∂μ, ∀ᶠ j : ℕ in atTop, y j ∉ S x := by
    filter_upwards [hfin] with x hx
    obtain ⟨M,hM⟩ := (hx.preimage hinj.injOn).bddAbove
    filter_upwards [eventually_gt_atTop M] with j hj
    exact fun he => hj.not_ge (hM he)
  have hlim := PrescribedTimes.ShortWindows.probability_vanishes μ (fun j => {x | y j ∈ S x})
    (fun j => hm (y j)) hmiss
  obtain ⟨j,hj⟩ := (hlim.eventually_lt_const hp).exists
  exact hj.not_ge (f j).property

/-- At most countably many levels can occur with positive probability. -/
theorem countable_height_atoms {Ω Y : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Ω → Set Y) (hm : ∀ y, MeasurableSet {x | y ∈ S x})
    (hfin : ∀ᵐ x ∂μ, (S x).Finite) : {y | 0 < μ.real {x | y ∈ S x}}.Countable := by
  let A (j : ℕ) := {y | 1/((j:ℝ)+1) ≤ μ.real {x | y ∈ S x}}
  have hA (j : ℕ) : (A j).Countable :=
    (finite_frequent_heights μ S hm hfin (by positivity : 0 < 1/((j:ℝ)+1))).countable
  apply (countable_iUnion hA).mono
  intro y hy
  obtain ⟨j,hj⟩ := exists_nat_one_div_lt hy
  exact mem_iUnion.mpr ⟨j,hj.le⟩

#print axioms countable_height_atoms
end
end GaloisForLFunctions.HTGeometry.ExactContacts.CoarseVisits.Prescribed
