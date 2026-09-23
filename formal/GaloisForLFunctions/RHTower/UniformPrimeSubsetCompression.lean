import GaloisForLFunctions.RHTower.UniformPrimeSubsetBooleanInversion

/-!
# Associative residual compression for finite label energy

Processing a core and then a packet is exactly equivalent to replacing the
atomic source by its core-residual fibres and processing the packet there.
Consequently, full residual parity orientation at a core controls every finite
future Boolean energy jet at that core.
-/

noncomputable section
open Finset
namespace RHTower

/-- Residualizing by two processed packets is associative after the first
packet is compressed into its residual fibres. -/
theorem subsetLabelFibre_union_eq_compressed
    {α ι : Type*} [DecidableEq α] (U : Finset α) (I : Finset ι)
    (a : ι → Finset α) (c : ι → ℝ)
    (ha : ∀ i ∈ I, a i ⊆ U) (P B R : Finset α) :
    subsetLabelFibre I a c (P ∪ B) R =
      subsetLabelFibre U.powerset (fun Q : Finset α => Q)
        (fun Q => subsetLabelFibre I a c P Q) B R := by
  unfold subsetLabelFibre
  change (∑ i ∈ I, if a i \ (P ∪ B) = R then c i else 0) =
    ∑ Q ∈ U.powerset,
      if Q \ B = R then (∑ i ∈ I, if a i \ P = Q then c i else 0) else 0
  have hswap :
      (∑ Q ∈ U.powerset,
        if Q \ B = R then (∑ i ∈ I, if a i \ P = Q then c i else 0) else 0) =
      ∑ i ∈ I, ∑ Q ∈ U.powerset,
        if Q \ B = R then (if a i \ P = Q then c i else 0) else 0 := by
    calc
      _ = ∑ Q ∈ U.powerset, ∑ i ∈ I,
          if Q \ B = R then (if a i \ P = Q then c i else 0) else 0 := by
            apply sum_congr rfl
            intro Q hQ
            rw [Finset.sum_ite_irrel]
            simp
      _ = _ := by rw [sum_comm]
  rw [hswap]
  apply sum_congr rfl
  intro i hi
  have hm : a i \ P ∈ U.powerset :=
    mem_powerset.mpr (sdiff_subset.trans (ha i hi))
  rw [sum_eq_single (a i \ P)]
  · have hs : a i \ (P ∪ B) = (a i \ P) \ B := by
      ext x
      simp only [mem_sdiff, mem_union]
      tauto
    rw [hs]
    simp
  · intro Q hQ hne
    have hq : a i \ P ≠ Q := Ne.symm hne
    simp [hq]
  · exact fun hn => (hn hm).elim

/-- Processing `P ∪ B` is the label energy of the source compressed at `P`
and then processed by `B`. -/
theorem subsetLabelEnergy_union_eq_compressed
    {α ι : Type*} [DecidableEq α] (U : Finset α) (I : Finset ι)
    (a : ι → Finset α) (c : ι → ℝ)
    (ha : ∀ i ∈ I, a i ⊆ U) (P B : Finset α) :
    subsetLabelEnergy U I a c (P ∪ B) =
      subsetLabelEnergy U U.powerset (fun Q : Finset α => Q)
        (fun Q => subsetLabelFibre I a c P Q) B := by
  unfold subsetLabelEnergy
  apply sum_congr rfl
  intro R hR
  rw [subsetLabelFibre_union_eq_compressed U I a c ha P B R]

/-- Full parity orientation of residual fibres controls every finite future
Boolean energy jet at that core. -/
theorem subsetLabelEnergy_booleanAlternating_union_nonneg_of_fibreParity
    {α ι : Type*} [DecidableEq α] (U : Finset α) (I : Finset ι)
    (a : ι → Finset α) (c : ι → ℝ)
    (ha : ∀ i ∈ I, a i ⊆ U) (P A : Finset α)
    (hparity : ∀ R ∈ U.powerset,
      0 ≤ (-1 : ℝ) ^ R.card * subsetLabelFibre I a c P R) :
    0 ≤ ∑ B ∈ A.powerset, (-1 : ℝ) ^ B.card *
      subsetLabelEnergy U I a c (P ∪ B) := by
  simp_rw [subsetLabelEnergy_union_eq_compressed U I a c ha P]
  exact subsetLabelEnergy_booleanAlternating_nonneg_of_parity
    U U.powerset (fun Q : Finset α => Q)
    (fun Q => subsetLabelFibre I a c P Q)
    (fun Q hQ => mem_powerset.mp hQ)
    hparity A

end RHTower
