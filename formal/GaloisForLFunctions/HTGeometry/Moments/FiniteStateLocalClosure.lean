import GaloisForLFunctions.HTGeometry.Moments.FiniteStateLeadingMinors

/-!
# Bounded state dimension survives local approximation

Finite-coordinate approximation by responses of uniformly bounded dimension
produces an exact finite-state realization. Each oversized leading determinant
vanishes by continuity; the leading-minor criterion supplies the realization.
The transition matrices themselves need not converge or remain bounded.
-/

open Filter Topology

namespace HTGeometry.FiniteHankel

/-- Pointwise limits of uniformly bounded state dimension admit an exact realization
with no increase in dimension. -/
theorem stateSpace_of_fixedDimension_tendsto
    {K : Type*} [NormedField K] {B : ℕ} {s : ℕ → ℕ → K} {target : ℕ → K}
    (hs : ∀ j, ∃ d ≤ B, AlgebraicStateSpaceDimensionAtMost d (s j))
    (hconv : Tendsto s atTop (nhds target)) :
    ∃ d ≤ B, AlgebraicStateSpaceDimensionAtMost d target := by
  apply (leading_tail_zero_iff_stateSpace target B).mp
  intro n hn
  have hmatrix : Tendsto
      (fun j => Matrix.of fun r c : Fin n => s j (r.val + c.val)) atTop
      (nhds (Matrix.of fun r c : Fin n => target (r.val + c.val))) := by
    apply tendsto_pi_nhds.mpr
    intro r
    apply tendsto_pi_nhds.mpr
    intro c
    exact (tendsto_pi_nhds.mp hconv) (r.val + c.val)
  have hdet : Tendsto (fun j => leadingDet (s j) n) atTop (nhds (leadingDet target n)) :=
    continuous_id.matrix_det.continuousAt.tendsto.comp hmatrix
  have hzero : Tendsto (fun j => leadingDet (s j) n) atTop (nhds 0) := by
    refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun j => ?_)
    obtain ⟨d, hd, hdim⟩ := hs j
    exact (leading_tail_zero_of_stateSpace hdim n (by omega)).symm
  exact tendsto_nhds_unique hdet hzero

/-- Separate finite-window approximants of one bounded dimension yield an exact finite-state
model of the entire sequence. -/
theorem stateSpace_of_fixedDimension_localClosure
    {K : Type*} [NormedField K] {B : ℕ} {target : ℕ → K}
    (h : FixedAlgebraicStateSpaceDimensionLocalClosure B target) :
    ∃ d ≤ B, AlgebraicStateSpaceDimensionAtMost d target := by
  have happ : ∀ j : ℕ, ∃ A : Matrix (Fin B) (Fin B) K, ∃ input output : Fin B → K,
      ∀ n < j + 1, dist (algebraicStateSpaceResponse A input output n) (target n) <
        1 / ((j : ℝ) + 1) := by
    intro j
    exact h (j + 1) (1 / ((j : ℝ) + 1)) (by positivity)
  choose A input output happrox using happ
  let approx : ℕ → ℕ → K :=
    fun j => algebraicStateSpaceResponse (A j) (input j) (output j)
  apply stateSpace_of_fixedDimension_tendsto
    (s := approx) (fun j => ⟨B, le_rfl, A j, input j, output j, rfl⟩)
  apply tendsto_pi_nhds.mpr
  intro n
  rw [Metric.tendsto_atTop]
  intro ε hε
  have herr : ∀ᶠ j : ℕ in atTop, 1 / ((j : ℝ) + 1) < ε :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hε)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp herr
  refine ⟨max J n, fun j hj => ?_⟩
  exact (happrox j n (by omega)).trans (hJ j (le_trans (le_max_left _ _) hj))

/-- Allowing arbitrarily accurate finite-window fits does not enlarge bounded finite memory. -/
theorem bounded_localClosure_iff_stateSpace
    {K : Type*} [NormedField K] (B : ℕ) (target : ℕ → K) :
    (∃ d ≤ B, FixedAlgebraicStateSpaceDimensionLocalClosure d target) ↔
      ∃ d ≤ B, AlgebraicStateSpaceDimensionAtMost d target := by
  constructor
  · rintro ⟨d, hd, h⟩
    obtain ⟨e, he, hs⟩ := stateSpace_of_fixedDimension_localClosure h
    exact ⟨e, he.trans hd, hs⟩
  · rintro ⟨d, hd, h⟩
    exact ⟨d, hd, fixedAlgebraicStateSpaceDimensionLocalClosure_of_dimensionAtMost h⟩

#print axioms stateSpace_of_fixedDimension_tendsto
#print axioms bounded_localClosure_iff_stateSpace

end HTGeometry.FiniteHankel
