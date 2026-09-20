import GaloisForLFunctions.HTGeometry.CriticalSheetJacobianCorankOne
import GaloisForLFunctions.HTGeometry.CriticalObservationConormalBase
import GaloisForLFunctions.HTGeometry.CriticalObservationCotangentBasis

/-!
# One conormal vector for all singular sheets

The conormal direction of the branch is defined over the observation side, and every geometric
sheet restricts to the identity there.  So a single nonzero vector of the residue field of the
normal closure lies in the kernel of the reduced observation Jacobian at *every* singular reduced
state.  Together with corank one this pins that kernel down to the line it spans.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 1000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- The lift of a sheet agrees with the canonical map on the observation valuation ring. -/
theorem criticalSheetSourceSchurLift_algebraMap_observation
    (σ : criticalGeometricSheet K m n)
    (hsing : criticalSheetChartToNormalSchur K σ
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n)))
    (a : criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :
    criticalSheetSourceSchurLift K σ hsing
        (algebraMap (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n))
          (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) a)
      = criticalSchurObservationValuationToNormalClosure K (Fact.out : 0 < m)
          (Fact.out : 0 < n) a := by
  apply Subtype.ext
  rw [criticalSheetSourceSchurLift_coe K σ hsing]
  show σ (algebraMap (criticalObservationField K m n) (criticalSourceField K m n)
      (a : criticalObservationField K m n)) = _
  rw [σ.commutes]
  rfl

/-- The conormal vector of the branch, read in the residue field of the normal closure. -/
noncomputable def criticalNormalSchurConormalVector
    (δ : criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :
    Fin m ⊕ Fin n → IsLocalRing.ResidueField
      (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :=
  fun s => IsLocalRing.residue _
    (criticalSchurObservationValuationToNormalClosure K (Fact.out : 0 < m) (Fact.out : 0 < n)
      ((criticalObservationBlockCotangentBasis K (m := m) (n := n)).repr
        (KaehlerDifferential.D K
          (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
            (Fact.out : 0 < n)) δ) s))

/-- **The conormal vector lies in the kernel at every singular sheet.** -/
theorem criticalSheet_jacobian_mulVec_conormal
    (σ : criticalGeometricSheet K m n)
    (hsing : criticalSheetChartToNormalSchur K σ
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n)))
    (δ : criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
    (hδ : δ ∈ maximalIdeal (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
      (Fact.out : 0 < n))) :
    ((criticalObservationJacobian K (m := m) (n := n)).map
        ((IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n))).comp (criticalSheetSourceSchurLift K σ hsing))).mulVec
      (criticalNormalSchurConormalVector K δ) = 0 := by
  have hfm : 0 < m := Fact.out
  have hfn : 0 < n := Fact.out
  funext t
  have hsum := criticalSchur_jacobian_conormal_mem_maximalIdeal K δ hδ t
  set f := (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K hfm
    hfn)).comp (criticalSheetSourceSchurLift K σ hsing) with hf
  have key : ∀ s : Fin m ⊕ Fin n,
      f (criticalObservationJacobian K (m := m) (n := n) t s) *
          criticalNormalSchurConormalVector K δ s
        = f (criticalObservationJacobian K (m := m) (n := n) t s *
          algebraMap
            (criticalSchurObservationValuationSubring K hfm hfn)
            (criticalSchurSourceValuationSubring K hfm hfn)
            ((criticalObservationBlockCotangentBasis K (m := m) (n := n)).repr
              (KaehlerDifferential.D K
                (criticalSchurObservationValuationSubring K hfm
                  hfn) δ) s)) := by
    intro s
    rw [map_mul]
    congr 1
    rw [criticalNormalSchurConormalVector, hf, RingHom.comp_apply,
      criticalSheetSourceSchurLift_algebraMap_observation K σ hsing]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply]
  rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => key s), ← map_sum, hf,
    RingHom.comp_apply]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr
    (criticalSheetSourceSchurLift_mem_maximalIdeal K σ hsing hsum)

/-- **The conormal vector is nonzero.** -/
theorem exists_criticalNormalSchurConormalVector_ne_zero :
    ∃ δ : criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n),
      δ ∈ maximalIdeal (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n)) ∧ criticalNormalSchurConormalVector K δ ≠ 0 := by
  have hfm : 0 < m := Fact.out
  have hfn : 0 < n := Fact.out
  obtain ⟨δ, hδ, s, hs⟩ := exists_mem_maximalIdeal_repr_D_notMem_maximalIdeal K (m := m) (n := n)
  refine ⟨δ, hδ, fun hcon => ?_⟩
  have hzero : criticalNormalSchurConormalVector K δ s = 0 := by rw [hcon]; rfl
  rw [criticalNormalSchurConormalVector] at hzero
  have hunit : IsUnit ((criticalObservationBlockCotangentBasis K (m := m) (n := n)).repr
      (KaehlerDifferential.D K
        (criticalSchurObservationValuationSubring K hfm hfn) δ) s) :=
    IsLocalRing.notMem_maximalIdeal.mp hs
  exact (IsLocalRing.notMem_maximalIdeal.mpr (hunit.map _))
    ((IsLocalRing.residue_eq_zero_iff _).mp hzero)

end

end GaloisForLFunctions.HTGeometry
