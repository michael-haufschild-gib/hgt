import GaloisForLFunctions.HTGeometry.CriticalObservationChartRing
import GaloisForLFunctions.HTGeometry.CriticalSchurCoordinateAdjoin
import GaloisForLFunctions.HTGeometry.CriticalSchurObservationSourceAlgebra
import GaloisForLFunctions.HTGeometry.CriticalSchurMarkedUnits

/-!
# The chart algebra sits inside the Schur valuation ring

Every horizon coordinate is integral at the Schur place, the observation coordinate ring lands
there, and the marked product is a unit there, so the whole chart ring — and therefore the chart
algebra it generates — lies in the Schur valuation ring.  This exhibits the Schur local ring as an
overring of a ring finite over the chart ring, which is what the height computation needs.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)]

instance criticalObservationRingGroundTower :
    IsScalarTower K (criticalObservationRing K m n) (criticalSourceField K m n) := by
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  rw [IsScalarTower.algebraMap_apply (criticalObservationRing K m n)
      (criticalObservationField K m n) (criticalSourceField K m n),
    ← IsScalarTower.algebraMap_apply K (criticalObservationRing K m n)
      (criticalObservationField K m n),
    ← IsScalarTower.algebraMap_apply K (criticalObservationField K m n)
      (criticalSourceField K m n)]

omit [IsAlgClosed K] in
/-- The horizon coordinates are integral at the Schur place. -/
theorem criticalSourceCoordinateSet_subset_schur :
    criticalSourceCoordinateSet K m n ⊆
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) :
        Set (criticalSourceField K m n)) := by
  rintro x ((⟨j, rfl⟩) | (⟨j, rfl⟩))
  · exact criticalSourceRaw_mem_sourceValuationSubring K Fact.out Fact.out j
  · exact criticalSourceRecip_mem_sourceValuationSubring K Fact.out Fact.out j

/-- The observation coordinate ring is integral at the Schur place. -/
theorem observationRing_mem_schur (p : criticalObservationRing K m n) :
    algebraMap (criticalObservationRing K m n) (criticalSourceField K m n) p ∈
      criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have hC : (MvPolynomial.C a : criticalObservationRing K m n)
          = algebraMap K (criticalObservationRing K m n) a := rfl
      rw [hC, ← IsScalarTower.algebraMap_apply K (criticalObservationRing K m n)
        (criticalSourceField K m n),
        ← coe_algebraMap_ground_criticalSchurSourceValuation K Fact.out Fact.out a]
      exact Subtype.property _
  | add p q hp hq => rw [map_add]; exact Subring.add_mem _ hp hq
  | mul_X p s hp =>
      rw [map_mul]
      refine Subring.mul_mem _ hp ?_
      cases s with
      | inl i =>
          rw [algebraMap_criticalObservationRing_X_inl K]
          exact criticalSourceRaw_mem_sourceValuationSubring K Fact.out Fact.out _
      | inr j =>
          rw [algebraMap_criticalObservationRing_X_inr K]
          exact criticalSourceRecip_mem_sourceValuationSubring K Fact.out Fact.out _

/-- The marked product is a unit at the Schur place. -/
theorem isUnit_algebraMap_marked_schur (hm : 1 < m) (hn : 1 < n) :
    IsUnit (⟨algebraMap (criticalObservationRing K m n) (criticalSourceField K m n)
      (criticalObservationMarked K),
      observationRing_mem_schur K _⟩ :
      criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) := by
  have hraw := isUnit_criticalSourceRaw_marked_sourceValuationSubring K hm hn
  have hrec := isUnit_criticalSourceRecip_marked_sourceValuationSubring K hm hn
  have hmul := hraw.mul hrec
  refine (isUnit_iff_exists_inv.mpr ?_)
  obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp hmul
  refine ⟨u, ?_⟩
  apply Subtype.ext
  have := congrArg (Subtype.val (p := fun x : criticalSourceField K m n =>
    x ∈ criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))) hu
  rw [← this]
  show algebraMap (criticalObservationRing K m n) (criticalSourceField K m n)
      (criticalObservationMarked K) * (u : criticalSourceField K m n) = _
  rw [criticalObservationMarked, map_mul, algebraMap_criticalObservationRing_X_inl,
    algebraMap_criticalObservationRing_X_inr]
  congr 2

/-- **The chart ring is integral at the Schur place.** -/
theorem chartRing_mem_schur (hm : 1 < m) (hn : 1 < n)
    (z : criticalObservationChartRing K m n) :
    algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n) z ∈
      criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) := by
  obtain ⟨⟨p, s⟩, hs⟩ := IsLocalization.surj
    (M := Submonoid.powers (criticalObservationMarked K (m := m) (n := n))) z
  obtain ⟨k, hk⟩ := s.2
  have hsu : IsUnit (⟨algebraMap (criticalObservationRing K m n) (criticalSourceField K m n)
      ((s : criticalObservationRing K m n)), observationRing_mem_schur K _⟩ :
      criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) := by
    have heq : (⟨algebraMap (criticalObservationRing K m n) (criticalSourceField K m n)
        ((s : criticalObservationRing K m n)), observationRing_mem_schur K _⟩ :
        criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        = (⟨algebraMap (criticalObservationRing K m n) (criticalSourceField K m n)
          (criticalObservationMarked K), observationRing_mem_schur K _⟩ :
          criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) ^ k := by
      apply Subtype.ext
      show algebraMap (criticalObservationRing K m n) (criticalSourceField K m n)
        ((s : criticalObservationRing K m n)) = _
      rw [← hk, map_pow]
      rfl
    rw [heq]
    exact (isUnit_algebraMap_marked_schur K hm hn).pow k
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hsu
  have hvE : algebraMap (criticalObservationRing K m n) (criticalSourceField K m n)
      ((s : criticalObservationRing K m n)) * (v : criticalSourceField K m n) = 1 :=
    congrArg Subtype.val hv
  have hsE := congrArg (algebraMap (criticalObservationChartRing K m n)
    (criticalSourceField K m n)) hs
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hsE
  have hz : algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n) z
      = algebraMap (criticalObservationRing K m n) (criticalSourceField K m n) p *
        (v : criticalSourceField K m n) := by
    have h2 := congrArg (fun x : criticalSourceField K m n => x * (v : criticalSourceField K m n))
      hsE
    simp only at h2
    rw [mul_assoc, hvE, mul_one] at h2
    exact h2
  rw [hz]
  exact Subring.mul_mem _ (observationRing_mem_schur K p) v.property

/-- The Schur valuation ring as a chart-ring subalgebra. -/
noncomputable def criticalSchurSourceSubalgebra (hm : 1 < m) (hn : 1 < n) :
    Subalgebra (criticalObservationChartRing K m n) (criticalSourceField K m n) where
  __ := (criticalSchurSourceValuationSubring K (Fact.out : 0 < m)
    (Fact.out : 0 < n)).toSubring
  algebraMap_mem' := chartRing_mem_schur K hm hn

/-- **The chart algebra is integral at the Schur place.** -/
theorem criticalSourceChartAlgebra_le_schur (hm : 1 < m) (hn : 1 < n) :
    criticalSourceChartAlgebra K (m := m) (n := n) ≤ criticalSchurSourceSubalgebra K hm hn := by
  refine Algebra.adjoin_le ?_
  intro x hx
  exact criticalSourceCoordinateSet_subset_schur K hx

end

end GaloisForLFunctions.HTGeometry
