import GaloisForLFunctions.HTGeometry.Critical.Schur.ConormalDirection
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower

/-!
# The observation cotangent basis, and the conormal vector of the branch

The observation Schur valuation ring is formally étale over the observation coordinate ring — it is
a localization of a localization — so its Kähler differentials carry the observation coordinates as
a basis.  In that basis and the raw basis upstairs, the matrix of the cotangent map is exactly the
observation Jacobian:

```text
formallyEtaleCotangentBasis                     the general coordinate basis
criticalObservationBlockCotangentBasis          the observation coordinates, in block order
criticalObservationJacobian_repr                the cotangent map has the Jacobian as its matrix
D_algebraMap_eq_sum_blockCoord
criticalSchur_jacobian_conormal_mem_maximalIdeal
    ** the coordinate vector of the differential of a non-unit of the observation Schur place is
       killed by the Jacobian modulo the maximal ideal upstairs **
```

The last statement is the ramification statement `(R)` read as a linear-algebra fact: the conormal
line of the branch is spanned by the differential of a uniformizer of the observation Schur place,
which is defined over the observation side and therefore the same at every point of the fibre.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open KaehlerDifferential IsLocalRing MvPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

/-- The coordinate basis of the Kähler differentials of any formally étale algebra over a
polynomial ring. -/
noncomputable def formallyEtaleCotangentBasis
    (k : Type*) [CommRing k] {σ : Type*} [Finite σ]
    (T : Type*) [CommRing T] [Algebra (MvPolynomial σ k) T] [Algebra k T]
    [IsScalarTower k (MvPolynomial σ k) T] [Algebra.FormallyEtale (MvPolynomial σ k) T] :
    Module.Basis σ T Ω[T⁄k] :=
  ((KaehlerDifferential.mvPolynomialBasis k σ).baseChange T).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (MvPolynomial σ k) T)

theorem formallyEtaleCotangentBasis_repr_D_algebraMap
    (k : Type*) [CommRing k] {σ : Type*} [Finite σ]
    (T : Type*) [CommRing T] [Algebra (MvPolynomial σ k) T] [Algebra k T]
    [IsScalarTower k (MvPolynomial σ k) T] [Algebra.FormallyEtale (MvPolynomial σ k) T]
    (r : MvPolynomial σ k) (i : σ) :
    (formallyEtaleCotangentBasis k T).repr
        (KaehlerDifferential.D k T (algebraMap (MvPolynomial σ k) T r)) i =
      algebraMap (MvPolynomial σ k) T (MvPolynomial.pderiv i r) := by
  simp [formallyEtaleCotangentBasis,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Module.Basis.baseChange_repr_tmul, Algebra.smul_def]

theorem formallyEtaleCotangentBasis_apply
    (k : Type*) [CommRing k] {σ : Type*} [Finite σ]
    (T : Type*) [CommRing T] [Algebra (MvPolynomial σ k) T] [Algebra k T]
    [IsScalarTower k (MvPolynomial σ k) T] [Algebra.FormallyEtale (MvPolynomial σ k) T]
    (i : σ) :
    formallyEtaleCotangentBasis k T i
      = KaehlerDifferential.D k T (algebraMap (MvPolynomial σ k) T (MvPolynomial.X i)) := by
  classical
  apply (formallyEtaleCotangentBasis (σ := σ) k T).repr.injective
  ext j
  rw [Module.Basis.repr_self, formallyEtaleCotangentBasis_repr_D_algebraMap]
  by_cases hij : j = i
  · subst hij
    simp
  · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hij), map_zero, Finsupp.single_apply,
      if_neg (Ne.symm hij)]

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

instance criticalObservationRingChartRing_formallyEtale :
    Algebra.FormallyEtale (criticalObservationRing K m n) (criticalObservationChartRing K m n) :=
  Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (criticalObservationMarked K (m := m) (n := n)))

instance criticalChartObservationSchur_formallyEtale :
    Algebra.FormallyEtale (criticalObservationChartRing K m n)
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :=
  Algebra.FormallyEtale.of_isLocalization
    (criticalSchurChartUnder K (m := m) (n := n)).primeCompl

instance criticalObservationRingSchur_formallyEtale :
    Algebra.FormallyEtale (criticalObservationRing K m n)
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :=
  Algebra.FormallyEtale.comp (criticalObservationRing K m n)
    (criticalObservationChartRing K m n)
    (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))

instance criticalObservationRingSchurGroundTower :
    IsScalarTower K (criticalObservationRing K m n)
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) := by
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  rw [IsScalarTower.algebraMap_apply K (criticalObservationChartRing K m n)
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)),
    IsScalarTower.algebraMap_apply K (criticalObservationRing K m n)
      (criticalObservationChartRing K m n),
    ← IsScalarTower.algebraMap_apply (criticalObservationRing K m n)
      (criticalObservationChartRing K m n)
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))]

/-- The coordinate cotangent basis of the observation Schur valuation ring. -/
def criticalObservationSchurCotangentBasis :
    Module.Basis (Fin n ⊕ Fin m)
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      Ω[criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)⁄K] :=
  formallyEtaleCotangentBasis K _

theorem criticalObservationSchurCotangentBasis_apply (s : Fin n ⊕ Fin m) :
    criticalObservationSchurCotangentBasis K (m := m) (n := n) s
      = KaehlerDifferential.D K
          (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
          (criticalObservationCoordSchur K s) :=
  formallyEtaleCotangentBasis_apply K _ s

/-- The observation cotangent basis in block order. -/
def criticalObservationBlockCotangentBasis :
    Module.Basis (Fin m ⊕ Fin n)
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      Ω[criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)⁄K] :=
  (criticalObservationSchurCotangentBasis K (m := m) (n := n)).reindex
    (Equiv.sumComm (Fin n) (Fin m))

theorem criticalObservationBlockCotangentBasis_apply (s : Fin m ⊕ Fin n) :
    criticalObservationBlockCotangentBasis K (m := m) (n := n) s
      = KaehlerDifferential.D K
          (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
          (criticalObservationBlockCoord K s) := by
  have hre : criticalObservationBlockCotangentBasis K (m := m) (n := n) s
      = criticalObservationSchurCotangentBasis K ((Equiv.sumComm (Fin n) (Fin m)).symm s) :=
    Module.Basis.reindex_apply _ _ _
  rw [hre, criticalObservationSchurCotangentBasis_apply K]
  rfl

/-- In the raw basis, the differential of an observation coordinate has the observation Jacobian
column as its coordinates. -/
theorem criticalObservationJacobian_repr (s t : Fin m ⊕ Fin n) :
    (criticalRawBlockCotangentBasis K (m := m) (n := n)).repr
        (KaehlerDifferential.D K
          (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
          (algebraMap
            (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
            (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
            (criticalObservationBlockCoord K s))) t
      = criticalObservationJacobian K t s := by
  classical
  have hvw : KaehlerDifferential.D K
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (algebraMap
        (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        (criticalObservationBlockCoord K s))
      = ∑ i, criticalObservationJacobian K i s •
          criticalRawBlockCotangentBasis K (m := m) (n := n) i := by
    simp only [coe_criticalRawBlockCotangentBasis]
    cases s with
    | inl s' => exact criticalObservationJacobian_hvw_inl K s'
    | inr s' => exact criticalObservationJacobian_hvw_inr K s'
  rw [hvw, map_sum, Finset.sum_apply']
  rw [Finset.sum_eq_single t]
  · rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
  · intro i _ hi
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
      if_neg hi, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ t) h

/-- Expansion of the differential of an element of the observation Schur place in the observation
coordinate differentials, pushed to the source. -/
theorem D_algebraMap_eq_sum_blockCoord
    (δ : criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :
    KaehlerDifferential.D K
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        (algebraMap
          (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
          (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) δ)
      = ∑ s, algebraMap
          (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
          (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
          ((criticalObservationBlockCotangentBasis K (m := m) (n := n)).repr
            (KaehlerDifferential.D K
              (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
                (Fact.out : 0 < n)) δ) s) •
          KaehlerDifferential.D K
            (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
            (algebraMap
              (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
              (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
              (criticalObservationBlockCoord K s)) := by
  have hsum := (criticalObservationBlockCotangentBasis K (m := m) (n := n)).sum_repr
    (KaehlerDifferential.D K
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) δ)
  have hmap := congrArg (KaehlerDifferential.map K K
    (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
    (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))) hsum
  rw [KaehlerDifferential.map_D, map_sum] at hmap
  rw [← hmap]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [LinearMap.map_smul, criticalObservationBlockCotangentBasis_apply K,
    KaehlerDifferential.map_D, ← IsScalarTower.algebraMap_smul
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))]

/-- **The conormal vector.**  The coordinates of the differential of a non-unit of the observation
Schur place are killed by the observation Jacobian modulo the maximal ideal of the source Schur
place. -/
theorem criticalSchur_jacobian_conormal_mem_maximalIdeal
    (δ : criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
    (hδ : δ ∈ maximalIdeal
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)))
    (t : Fin m ⊕ Fin n) :
    ∑ s, criticalObservationJacobian K t s *
        algebraMap
          (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
          (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
          ((criticalObservationBlockCotangentBasis K (m := m) (n := n)).repr
            (KaehlerDifferential.D K
              (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
                (Fact.out : 0 < n)) δ) s)
      ∈ maximalIdeal
          (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) := by
  have hkey := criticalSchur_repr_D_observation_mem_maximalIdeal K δ hδ t
  rw [D_algebraMap_eq_sum_blockCoord K δ, map_sum, Finset.sum_apply'] at hkey
  refine (Finset.sum_congr rfl fun s _ => ?_ : (_ : criticalSchurSourceValuationSubring K
    (Fact.out : 0 < m) (Fact.out : 0 < n)) = _) ▸ hkey
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, criticalObservationJacobian_repr K,
    mul_comm]

end

end GaloisForLFunctions.HTGeometry
