import GaloisForLFunctions.HTGeometry.FisherOneCornerCoareaTransform

/-!
# Height-preserving replication cannot evacuate a spectral cutoff diagonal

Replicating every atom into `k` orthogonal copies can dilute an algebraic
diagonal chosen by an unrelated linear order.  It does not change a physical
one-corner cutoff whose projection is determined by height: all replicas of
one atom cross every height threshold together.

The theorem below is exact at every finite replication depth.  After the
probability of each copy is divided by `k`, the `k²` replica pairs cancel that
normalization and leave the complete one-corner coarea density unchanged.
Thus a cofinal replica limit cannot remove any collision from the actual
spectral-cutoff field unless the replicas acquire distinct physical heights.
-/

open scoped BigOperators

open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Probability of a height-preserving replica atom. -/
def fisherHeightReplicaProbability
    {ι : Type*} (k : ℕ) (p : ι → ℝ) (q : Fin k × ι) : ℝ :=
  p q.2 / k

/-- Every copy of one atom has the same physical height. -/
def fisherHeightReplicaCoordinate
    {ι : Type*} (h : ι → ℝ) (q : Fin k × ι) : ℝ :=
  h q.2

/-- Two replicas of the same atom can never straddle a physical height
cutoff, regardless of their replica labels. -/
theorem not_fisherHeightReplicaCoordinate_straddles_same_atom
    {ι : Type*} {k : ℕ} (h : ι → ℝ) (u : ℝ)
    (r s : Fin k) (i : ι) :
    ¬(fisherHeightReplicaCoordinate h (s, i) < u ∧
      u ≤ fisherHeightReplicaCoordinate h (r, i)) := by
  simp only [fisherHeightReplicaCoordinate]
  exact fun hcross => (not_lt_of_ge hcross.2) hcross.1

/-- **Height-replica coarea invariance.**  Orthogonally replicating each
atom with unchanged height and probability `p/k` leaves the complete
physical one-corner Fisher density unchanged at every cutoff. -/
theorem finiteFisherOneCornerCoareaDensity_heightReplica
    {ι : Type*} [Fintype ι]
    (k : ℕ) (hk : 0 < k) (p h : ι → ℝ) (m u : ℝ) :
    finiteFisherOneCornerCoareaDensity
        (fisherHeightReplicaProbability k p)
        (fisherHeightReplicaCoordinate h) m u =
      finiteFisherOneCornerCoareaDensity p h m u := by
  simp only [finiteFisherOneCornerCoareaDensity,
    finiteFisherPairAmplitudeSq, fisherHeightReplicaProbability,
    fisherHeightReplicaCoordinate, Fintype.sum_prod_type,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs
  · field_simp [hkR]
  · ring

/-- The complete integrated physical coarea energy is likewise invariant
under every finite height-preserving replication. -/
theorem integral_finiteFisherOneCornerCoareaDensity_heightReplica
    {ι : Type*} [Fintype ι]
    (k : ℕ) (hk : 0 < k) (p h : ι → ℝ) (m : ℝ) :
    (∫ u : ℝ in Set.Ioi 0,
      finiteFisherOneCornerCoareaDensity
        (fisherHeightReplicaProbability k p)
        (fisherHeightReplicaCoordinate h) m u) =
      ∫ u : ℝ in Set.Ioi 0,
        finiteFisherOneCornerCoareaDensity p h m u := by
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun u =>
    finiteFisherOneCornerCoareaDensity_heightReplica k hk p h m u

end GaloisForLFunctions.HTGeometry
