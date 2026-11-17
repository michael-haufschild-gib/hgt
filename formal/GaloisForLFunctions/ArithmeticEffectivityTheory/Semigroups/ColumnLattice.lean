import GaloisForLFunctions.ArithmeticEffectivityTheory.Semigroups.ColumnJoin

/-!
# Exact genus loss under additive fusion

The drop from the union threshold to the joined threshold measures the
fusion defect. Its sum gives an exact genus balance; the lattice inequality
is an equality precisely when the set union already equals the additive join.
-/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.ArithmeticEffectivityTheory.ResidueColumns

/-- Missing exponents filled by additive fusion, counted column by column. -/
def fusionDefect (m : ℕ) (k l j : ℕ → ℕ) : ℕ :=
  ∑ r ∈ Finset.range (m + 1), (min (k r) (l r) - j r)

/-- The genus loss is exactly the total threshold drop below the union. -/
theorem genus_fusion_balance (m : ℕ) (k l j : ℕ → ℕ)
    (hj : ∀ r < m + 1, j r ≤ min (k r) (l r)) :
    genus m (fun r => max (k r) (l r)) + genus m j + fusionDefect m k l j =
      genus m k + genus m l := by
  unfold genus fusionDefect
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have h := hj r (Finset.mem_range.mp hr)
  omega

/-- Equality in the genus lattice inequality holds exactly when fusion adds no exponent beyond the union. -/
theorem genus_fusion_equality_iff (m : ℕ) (k l j : ℕ → ℕ)
    (hj : ∀ r < m + 1, j r ≤ min (k r) (l r)) :
    genus m (fun r => max (k r) (l r)) + genus m j = genus m k + genus m l ↔
      carrier m j = carrier m k ∪ carrier m l := by
  have hbalance := genus_fusion_balance m k l j hj
  have he : genus m (fun r => max (k r) (l r)) + genus m j = genus m k + genus m l ↔
      fusionDefect m k l j = 0 := by omega
  rw [he, fusionDefect, Finset.sum_eq_zero_iff, ← carrier_min, carrier_eq_iff]
  constructor
  · intro h r hr
    have hz := h r (Finset.mem_range.mpr hr)
    have hle := hj r hr
    omega
  · intro h r hr
    rw [h r (Finset.mem_range.mp hr), Nat.sub_self]

/-- A joined threshold cannot exceed either original threshold. -/
theorem joinThreshold_le_min (m : ℕ) (S T : AddSubmonoid ℕ)
    (hS : m + 1 ∈ S) (hT : m + 1 ∈ T) (C D : ℕ)
    (hC : ∀ n, C ≤ n → n ∈ S) (hD : ∀ n, D ≤ n → n ∈ T) (r : ℕ) :
    joinThreshold m S T C hC r ≤ min (thresholdAt m S C hC r) (thresholdAt m T D hD r) := by
  apply le_min
  · apply (thresholdAt_mem_iff m (S ⊔ T) (AddSubmonoid.mem_sup_left hS) C
      (fun n hn => AddSubmonoid.mem_sup_left (hC n hn)) _ _).mp
    exact AddSubmonoid.mem_sup_left ((thresholdAt_mem_iff m S hS C hC _ _).mpr le_rfl)
  · apply (thresholdAt_mem_iff m (S ⊔ T) (AddSubmonoid.mem_sup_left hS) C
      (fun n hn => AddSubmonoid.mem_sup_left (hC n hn)) _ _).mp
    exact AddSubmonoid.mem_sup_right ((thresholdAt_mem_iff m T hT D hD _ _).mpr le_rfl)

/-- Additive fusion can only decrease the total genus relative to the intersection balance. -/
theorem join_genus_submodular (m : ℕ) (S T : AddSubmonoid ℕ)
    (hS : m + 1 ∈ S) (hT : m + 1 ∈ T) (C D : ℕ)
    (hC : ∀ n, C ≤ n → n ∈ S) (hD : ∀ n, D ≤ n → n ∈ T) :
    genus m (fun r => max (thresholdAt m S C hC r) (thresholdAt m T D hD r)) +
        genus m (joinThreshold m S T C hC) ≤
      genus m (thresholdAt m S C hC) + genus m (thresholdAt m T D hD) := by
  have h := genus_fusion_balance m (thresholdAt m S C hC) (thresholdAt m T D hD)
    (joinThreshold m S T C hC) (fun r _ => joinThreshold_le_min m S T hS hT C D hC hD r)
  omega

/-- The join/intersection genus inequality is sharp exactly when the set union is already additive. -/
theorem join_genus_equality_iff_union (m : ℕ) (S T : AddSubmonoid ℕ)
    (hS : m + 1 ∈ S) (hT : m + 1 ∈ T) (C D : ℕ)
    (hC : ∀ n, C ≤ n → n ∈ S) (hD : ∀ n, D ≤ n → n ∈ T) :
    genus m (fun r => max (thresholdAt m S C hC r) (thresholdAt m T D hD r)) +
        genus m (joinThreshold m S T C hC) =
      genus m (thresholdAt m S C hC) + genus m (thresholdAt m T D hD) ↔
      ((S ⊔ T : AddSubmonoid ℕ) : Set ℕ) = (S : Set ℕ) ∪ (T : Set ℕ) := by
  have h := genus_fusion_equality_iff m (thresholdAt m S C hC) (thresholdAt m T D hD)
    (joinThreshold m S T C hC) (fun r _ => joinThreshold_le_min m S T hS hT C D hC hD r)
  rw [← thresholdAt_carrier m S hS C hC, ← thresholdAt_carrier m T hT D hD] at h
  change _ ↔ carrier m (thresholdAt m (S ⊔ T) C
    (fun n hn => AddSubmonoid.mem_sup_left (hC n hn))) = _ at h
  rw [← thresholdAt_carrier m (S ⊔ T) (AddSubmonoid.mem_sup_left hS) C
    (fun n hn => AddSubmonoid.mem_sup_left (hC n hn))] at h
  exact h

#print axioms join_genus_submodular
#print axioms join_genus_equality_iff_union
#print axioms genus_fusion_balance
#print axioms genus_fusion_equality_iff
end GaloisForLFunctions.ArithmeticEffectivityTheory.ResidueColumns
