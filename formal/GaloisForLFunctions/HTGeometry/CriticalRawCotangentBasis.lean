import GaloisForLFunctions.HTGeometry.CriticalSchurRamifies
import GaloisForLFunctions.HTGeometry.KaehlerAnnihilatorDeterminant
import GaloisForLFunctions.HTGeometry.CriticalSchurCoordinateAdjoin

/-!
# The raw coordinate cotangent basis, and the Kähler different at the Schur place

The differentials of the raw horizon coordinates span the cotangent module of the source Schur
valuation ring: the reciprocal coordinates have `dY = -Y² dX`, the Schur coordinates are
polynomials in the raw and reciprocal coordinates, and the Schur coordinates carry the coordinate
cotangent basis.  A spanning family of the size of a basis is a basis, so

```text
criticalRawBlockCotangentBasis                   the raw differentials, as a basis
criticalSchur_annihilator_kaehler_eq_maximalIdeal
    ** Ann (Ω[source Schur place ⁄ observation Schur place]) = the maximal ideal **
```

the last statement because in that basis the coordinate matrix of the observation differentials is
the observation Jacobian itself, whose determinant is a uniformizer.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open KaehlerDifferential IsLocalRing MvPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

/-- The coordinate cotangent basis of a localization of a polynomial ring is the family of
differentials of the variables. -/
theorem localizationCotangentBasis_apply
    (k : Type*) [CommRing k] {σ : Type*} [Finite σ]
    (T : Type*) [CommRing T] [Algebra (MvPolynomial σ k) T] [Algebra k T]
    [IsScalarTower k (MvPolynomial σ k) T]
    (S : Submonoid (MvPolynomial σ k)) [IsLocalization S T] (i : σ) :
    localizationCotangentBasis k T S i
      = KaehlerDifferential.D k T (algebraMap (MvPolynomial σ k) T (MvPolynomial.X i)) := by
  classical
  apply (localizationCotangentBasis k T S).repr.injective
  ext j
  rw [Module.Basis.repr_self, localizationCotangentBasis_repr_D_algebraMap]
  by_cases hij : j = i
  · subst hij
    simp
  · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hij), map_zero, Finsupp.single_apply,
      if_neg (Ne.symm hij)]

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

omit [Fact (1 < m)] [Fact (1 < n)] in
theorem criticalSchurSourceCotangentBasis_apply (i : Fin (m + n - 1 + 1)) :
    criticalSchurSourceCotangentBasis K (Fact.out : 0 < m) (Fact.out : 0 < n) i
      = KaehlerDifferential.D K
          (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
          (algebraMap (criticalSchurSourceRing K m n)
            (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
            (MvPolynomial.X i)) :=
  localizationCotangentBasis_apply K _ _ i

/-- The `B`-span of the differentials of the raw source coordinates. -/
def criticalRawSpan :
    Submodule (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      Ω[criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)⁄K] :=
  Submodule.span _ (Set.range (criticalRawDifferential K (m := m) (n := n)))

omit [Fact (1 < m)] [Fact (1 < n)] in
theorem D_criticalSourceRawIntegral_mem (i : Fin (m + n)) :
    KaehlerDifferential.D K
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        (criticalSourceRawIntegral K (Fact.out : 0 < m) (Fact.out : 0 < n) i)
      ∈ criticalRawSpan K (m := m) (n := n) := by
  refine Submodule.subset_span ⟨finSumFinEquiv.symm i, ?_⟩
  show KaehlerDifferential.D K _
      (criticalSourceRawIntegral K (Fact.out : 0 < m) (Fact.out : 0 < n)
        (finSumFinEquiv (finSumFinEquiv.symm i))) = _
  rw [Equiv.apply_symm_apply]

omit [Fact (1 < m)] [Fact (1 < n)] in
theorem D_criticalSourceRawPolynomialIntegral_coeff_mem (k : ℕ) :
    KaehlerDifferential.D K
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        ((criticalSourceRawPolynomialIntegral K (Fact.out : 0 < m) (Fact.out : 0 < n)).coeff k)
      ∈ criticalRawSpan K (m := m) (n := n) := by
  by_cases hk : k < m + n
  · rw [criticalSourceRawPolynomialIntegral_coeff K (Fact.out : 0 < m) (Fact.out : 0 < n) k hk]
    exact D_criticalSourceRawIntegral_mem K ⟨k, hk⟩
  · have hzero : (criticalSourceRawPolynomialIntegral K (Fact.out : 0 < m)
        (Fact.out : 0 < n)).coeff k = 0 := by
      classical
      rw [criticalSourceRawPolynomialIntegral, Polynomial.finsetSum_coeff]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
    rw [hzero, map_zero]
    exact Submodule.zero_mem _

omit [Fact (1 < m)] [Fact (1 < n)] in
theorem D_criticalSourceRecipIntegral_mem (i : Fin (m + n)) :
    KaehlerDifferential.D K
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        (criticalSourceRecipIntegral K (Fact.out : 0 < m) (Fact.out : 0 < n) i)
      ∈ criticalRawSpan K (m := m) (n := n) := by
  rw [← criticalSourceRecipPolynomialIntegral_coeff K (Fact.out : 0 < m) (Fact.out : 0 < n)
    (i : ℕ) i.isLt]
  rw [D_criticalSourceRecipPolynomialIntegral_coeff K (Fact.out : 0 < m) (Fact.out : 0 < n)
    (i : ℕ) i.isLt]
  refine Submodule.neg_mem _ (Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ ?_)
  exact D_criticalSourceRawPolynomialIntegral_coeff_mem K x.2

/-- The source Schur valuation ring inside the source field, as a `K`-algebra map. -/
def criticalSchurSourceInclusion :
    criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) →ₐ[K]
      criticalSourceField K m n :=
  { (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)).subtype with
    commutes' := fun c =>
      coe_algebraMap_ground_criticalSchurSourceValuation K (Fact.out : 0 < m)
        (Fact.out : 0 < n) c }

omit [Fact (1 < m)] [Fact (1 < n)] in
@[simp] theorem criticalSchurSourceInclusion_apply
    (x : criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :
    criticalSchurSourceInclusion K x = (x : criticalSourceField K m n) := rfl

omit [Fact (1 < m)] [Fact (1 < n)] in
theorem criticalSchurSourceInclusion_injective :
    Function.Injective (criticalSchurSourceInclusion K (m := m) (n := n)) :=
  Subtype.val_injective

/-- The elements of the source Schur valuation ring whose differentials lie in the raw span. -/
def criticalRawVanishing :
    Subalgebra K (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :=
  cotangentVanishingSubalgebra (R := K)
    (A := criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
    (B := criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
    (criticalRawSpan K (m := m) (n := n))

omit [Fact (1 < m)] [Fact (1 < n)] in
theorem mem_criticalRawVanishing_iff
    (x : criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :
    x ∈ criticalRawVanishing K (m := m) (n := n) ↔
      KaehlerDifferential.D K
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) x
        ∈ criticalRawSpan K (m := m) (n := n) := Iff.rfl

omit [Fact (1 < m)] [Fact (1 < n)] in
theorem criticalSourceCoordinateSet_subset_vanishing :
    criticalSourceCoordinateSet K m n ⊆
      ((criticalRawVanishing K (m := m) (n := n)).map
        (criticalSchurSourceInclusion K (m := m) (n := n)) :
        Subalgebra K (criticalSourceField K m n)) := by
  rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · exact ⟨criticalSourceRawIntegral K (Fact.out : 0 < m) (Fact.out : 0 < n) i,
      (mem_criticalRawVanishing_iff K _).mpr (D_criticalSourceRawIntegral_mem K i), rfl⟩
  · exact ⟨criticalSourceRecipIntegral K (Fact.out : 0 < m) (Fact.out : 0 < n) i,
      (mem_criticalRawVanishing_iff K _).mpr (D_criticalSourceRecipIntegral_mem K i), rfl⟩

omit [Fact (1 < m)] [Fact (1 < n)] in
/-- Every Schur coordinate has its differential in the raw span. -/
theorem criticalSchurCoordinate_mem_criticalRawVanishing (i : Fin (m + n - 1 + 1)) :
    algebraMap (criticalSchurSourceRing K m n)
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        (MvPolynomial.X i)
      ∈ criticalRawVanishing K (m := m) (n := n) := by
  have hadj : Algebra.adjoin K (criticalSourceCoordinateSet K m n) ≤
      (criticalRawVanishing K (m := m) (n := n)).map
        (criticalSchurSourceInclusion K (m := m) (n := n)) :=
    Algebra.adjoin_le (criticalSourceCoordinateSet_subset_vanishing K)
  have hmem := hadj (criticalSourceSchurCoordinates_mem_adjoin K
    (Fact.out : 0 < m) (Fact.out : 0 < n) i)
  obtain ⟨v, hv, hveq⟩ := hmem
  have hcoe : (algebraMap (criticalSchurSourceRing K m n)
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (MvPolynomial.X i) : criticalSourceField K m n)
      = criticalSourceSchurCoordinates K (Fact.out : 0 < m) (Fact.out : 0 < n) i := by
    rw [coe_algebraMap_criticalSchurSourceValuation K (Fact.out : 0 < m) (Fact.out : 0 < n)]
    simp
  have : v = algebraMap (criticalSchurSourceRing K m n)
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (MvPolynomial.X i) :=
    criticalSchurSourceInclusion_injective K (hveq.trans hcoe.symm)
  rwa [this] at hv

omit [Fact (1 < m)] [Fact (1 < n)] in
/-- **The raw differentials span the cotangent module of the source Schur valuation ring.** -/
theorem criticalRawSpan_eq_top : criticalRawSpan K (m := m) (n := n) = ⊤ := by
  rw [eq_top_iff, ← (criticalSchurSourceCotangentBasis K (Fact.out : 0 < m)
    (Fact.out : 0 < n)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [criticalSchurSourceCotangentBasis_apply K i]
  exact criticalSchurCoordinate_mem_criticalRawVanishing K i

/-- The raw coordinate cotangent basis of the source Schur valuation ring, in block order. -/
def criticalRawBlockCotangentBasis :
    Module.Basis (Fin m ⊕ Fin n)
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      Ω[criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)⁄K] :=
  basisOfSpanningOfBasis (criticalSchurBlockCotangentBasis K)
    (criticalRawDifferential K (m := m) (n := n))
    (le_of_eq (criticalRawSpan_eq_top K).symm)

@[simp] theorem coe_criticalRawBlockCotangentBasis :
    ⇑(criticalRawBlockCotangentBasis K (m := m) (n := n))
      = criticalRawDifferential K (m := m) (n := n) :=
  coe_basisOfSpanningOfBasis _ _ _

/-- **The Kähler different at the Schur place is the maximal ideal.**  The Jacobian determinant of
the horizon map is a uniformizer of the source Schur valuation ring, so it generates the whole
annihilator of the relative differentials. -/
theorem criticalSchur_annihilator_kaehler_eq_maximalIdeal :
    Module.annihilator
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        Ω[criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)⁄
          criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)]
      = maximalIdeal
          (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) := by
  refine annihilator_kaehler_eq_maximalIdeal (criticalRawBlockCotangentBasis K)
    (criticalObservationBlockCoord K) (criticalObservationJacobian K)
    (criticalSchur_hgen_block K) ?_ ?_
  · intro s
    simp only [coe_criticalRawBlockCotangentBasis]
    cases s with
    | inl s' => exact criticalObservationJacobian_hvw_inl K s'
    | inr s' => exact criticalObservationJacobian_hvw_inr K s'
  · rw [det_criticalObservationJacobian K]
    exact irreducible_criticalSchurJacobianDetElement K (Fact.out : 1 < m) (Fact.out : 1 < n)

end

end GaloisForLFunctions.HTGeometry
