import GaloisForLFunctions.HTGeometry.ProjectiveHorizonChartBasisIndependence

/-!
# The chart change of variables is an isomorphism

The chart transcendence basis is algebraically independent and generates, so evaluating the free
rational coordinate field at it is both injective and surjective.  The homogeneous jet field is
therefore isomorphic, over the constants, to a free rational coordinate field on the same index,
by an isomorphism carrying each coordinate to the corresponding chart datum: the denominator tower
to itself and the remaining coordinates to the affine chart jets.

This is the exact sense in which one affine chart is a coordinate system for the projective source.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## Evaluation at the chart basis -/

/-- Evaluation of the free coordinate model at the chart transcendence basis. -/
def basisEvalPoly (i : n) : MvPolynomial (n × ℕ) K →ₐ[K] HomogeneousJetField n K :=
  MvPolynomial.aeval (chartBasis i)

omit [Fintype n] in
@[simp]
theorem basisEvalPoly_X (i : n) (p : n × ℕ) :
    basisEvalPoly (K := K) i (MvPolynomial.X p) = chartBasis i p := by
  simp [basisEvalPoly]

omit [Fintype n] in
theorem basisEvalPoly_injective (i : n) :
    Function.Injective (basisEvalPoly (K := K) i) :=
  algebraicIndependent_chartBasis i

/-- The chart change of variables on the free rational coordinate field. -/
def basisEval (i : n) :
    FreeCoordinateRationalField K (n × ℕ) →ₐ[K] HomogeneousJetField n K :=
  { IsFractionRing.lift (basisEvalPoly_injective (K := K) i) with
    commutes' := fun c => by
      show IsFractionRing.lift (basisEvalPoly_injective (K := K) i)
        (algebraMap K (FreeCoordinateRationalField K (n × ℕ)) c) = _
      rw [IsScalarTower.algebraMap_apply K (MvPolynomial (n × ℕ) K)
          (FreeCoordinateRationalField K (n × ℕ)),
        IsFractionRing.lift_algebraMap]
      exact (basisEvalPoly i).commutes c }

omit [Fintype n] in
@[simp]
theorem basisEval_algebraMap (i : n) (p : MvPolynomial (n × ℕ) K) :
    basisEval i (algebraMap (MvPolynomial (n × ℕ) K)
        (FreeCoordinateRationalField K (n × ℕ)) p) = basisEvalPoly i p :=
  IsFractionRing.lift_algebraMap (basisEvalPoly_injective (K := K) i) p

omit [Fintype n] in
@[simp]
theorem basisEval_freeCoordinate (i : n) (p : n × ℕ) :
    basisEval (K := K) i (freeCoordinate K (n × ℕ) p) = chartBasis i p := by
  rw [freeCoordinate, basisEval_algebraMap, basisEvalPoly_X]

omit [Fintype n] in
theorem basisEval_injective (i : n) : Function.Injective (basisEval (K := K) i) :=
  (basisEval (K := K) i).toRingHom.injective

/-! ## Surjectivity -/

omit [Fintype n] in
theorem chartAdaptedGenerators_subset_fieldRange (i : n) :
    chartAdaptedGenerators i K ⊆ ((basisEval (K := K) i).fieldRange : Set _) := by
  rintro f (⟨l, rfl⟩ | ⟨k, l, rfl⟩)
  · refine ⟨freeCoordinate K (n × ℕ) (i, l), ?_⟩
    show basisEval (K := K) i (freeCoordinate K (n × ℕ) (i, l)) =
      freeCoordinate K (n × ℕ) (i, l)
    rw [basisEval_freeCoordinate, chartBasis, if_pos rfl]
  · by_cases hk : k = i
    · rw [hk, affineJet_self]
      split
      · exact (basisEval (K := K) i).fieldRange.one_mem
      · exact (basisEval (K := K) i).fieldRange.zero_mem
    · refine ⟨freeCoordinate K (n × ℕ) (k, l), ?_⟩
      show basisEval (K := K) i (freeCoordinate K (n × ℕ) (k, l)) = affineJet i k l
      rw [basisEval_freeCoordinate, chartBasis, if_neg hk]

omit [Fintype n] in
theorem basisEval_surjective (i : n) : Function.Surjective (basisEval (K := K) i) := by
  have hrange : (basisEval (K := K) i).fieldRange = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← chartAdaptedGenerators_adjoin_eq_top (K := K) i, IntermediateField.adjoin_le_iff]
    exact chartAdaptedGenerators_subset_fieldRange i
  intro f
  have hmem : f ∈ (basisEval (K := K) i).fieldRange := by rw [hrange]; trivial
  exact hmem

/-- **Chart coordinate isomorphism.**  One affine chart is a coordinate system: the homogeneous jet
field is isomorphic over the constants to the free rational coordinate field, by the map sending the
denominator tower to itself and every other coordinate to the corresponding affine chart jet. -/
def chartBasisEquiv (i : n) :
    FreeCoordinateRationalField K (n × ℕ) ≃ₐ[K] HomogeneousJetField n K :=
  AlgEquiv.ofBijective (basisEval i) ⟨basisEval_injective i, basisEval_surjective i⟩

omit [Fintype n] in
@[simp]
theorem chartBasisEquiv_freeCoordinate (i : n) (p : n × ℕ) :
    chartBasisEquiv (K := K) i (freeCoordinate K (n × ℕ) p) = chartBasis i p :=
  basisEval_freeCoordinate i p

end

end GaloisForLFunctions.HTGeometry
