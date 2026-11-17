import GaloisForLFunctions.ArithmeticEffectivityTheory.Semigroups.ColumnLattice

/-!
# The exact number of gaps filled by fusion

Partitioning the original union gaps identifies the threshold defect with newly admitted exponents.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticEffectivityTheory.ResidueColumns

/-- Exponents present after fusion but absent from both original spectra. -/
def fusionGaps (m : ℕ) (k l j : ℕ → ℕ) : Set ℕ :=
  carrier m j \ (carrier m k ∪ carrier m l)

instance fusionGapsFintype (m : ℕ) (k l j : ℕ → ℕ) :
    Fintype (fusionGaps m k l j) := by
  classical
  let f : fusionGaps m k l j → {n : ℕ // n ∉ carrier m (fun r => min (k r) (l r))} :=
    fun n => ⟨n.val, by rw [carrier_min]; exact n.property.2⟩
  refine Fintype.ofInjective f ?_
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : {n : ℕ // n ∉ carrier m (fun r => min (k r) (l r))} => z.val) h

/-- Union gaps split into surviving gaps and newly filled gaps. -/
private def gapPartitionEquiv (m : ℕ) (k l j : ℕ → ℕ)
    (hj : ∀ r < m + 1, j r ≤ min (k r) (l r)) :
    {n : ℕ // n ∉ carrier m (fun r => min (k r) (l r))} ≃
      ({n : ℕ // n ∉ carrier m j} ⊕ fusionGaps m k l j) := by
  classical
  have hsub : carrier m (fun r => min (k r) (l r)) ⊆ carrier m j :=
    (subset_iff m _ _).mpr hj
  refine {
    toFun := fun n => if hn : n.val ∈ carrier m j then
      Sum.inr ⟨n.val, hn, by rw [← carrier_min]; exact n.property⟩ else Sum.inl ⟨n.val, hn⟩
    invFun := fun n => match n with
      | Sum.inl n => ⟨n.val, fun hn => n.property (hsub hn)⟩
      | Sum.inr n => ⟨n.val, by rw [carrier_min]; exact n.property.2⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro n
    dsimp only
    split_ifs <;> rfl
  · intro n
    cases n with
    | inl n => simp only [dif_neg n.property]
    | inr n => simp only [dif_pos n.property.1]

/-- The threshold-drop defect is the exact number of exponents newly created by fusion. -/
theorem card_fusionGaps (m : ℕ) (k l j : ℕ → ℕ)
    (hj : ∀ r < m + 1, j r ≤ min (k r) (l r)) :
    Fintype.card (fusionGaps m k l j) = fusionDefect m k l j := by
  have hc := Fintype.card_congr (gapPartitionEquiv m k l j hj)
  rw [Fintype.card_sum, card_gaps, card_gaps] at hc
  have hg : genus m (fun r => min (k r) (l r)) = genus m j + fusionDefect m k l j := by
    unfold genus fusionDefect
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    exact (Nat.add_sub_of_le (hj r (Finset.mem_range.mp hr))).symm
  omega

/-- The same count applies to the actual additive join, with the threshold bound discharged. -/
theorem card_join_fusionGaps (m : ℕ) (S T : AddSubmonoid ℕ)
    (hS : m + 1 ∈ S) (hT : m + 1 ∈ T) (C D : ℕ)
    (hC : ∀ n, C ≤ n → n ∈ S) (hD : ∀ n, D ≤ n → n ∈ T) :
    Fintype.card (fusionGaps m (thresholdAt m S C hC) (thresholdAt m T D hD)
      (joinThreshold m S T C hC)) =
      fusionDefect m (thresholdAt m S C hC) (thresholdAt m T D hD)
        (joinThreshold m S T C hC) :=
  card_fusionGaps m _ _ _ (fun r _ => joinThreshold_le_min m S T hS hT C D hC hD r)

#print axioms card_join_fusionGaps

#print axioms card_fusionGaps
end GaloisForLFunctions.ArithmeticEffectivityTheory.ResidueColumns
