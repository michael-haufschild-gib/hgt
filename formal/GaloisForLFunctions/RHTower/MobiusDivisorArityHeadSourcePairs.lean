import GaloisForLFunctions.RHTower.MobiusDivisorArityHeadCharge

/-!
# Literal source-pair form of arity-head charge

The arity energy completed by its head square has one exact signed source-pair
kernel. Its one-prime increment is the corresponding literal source-pair
correlation across adjacent unprocessed labels. These are identities only:
they retain the unresolved signed cancellation problem without an estimate.
-/

noncomputable section
open Finset
open scoped symmDiff
namespace RHTower

/-- The completed arity-head energy is one literal signed source-pair kernel.
The rank-one term is exactly the processed-label boundary contribution. -/
theorem mobiusDivisorArityHeadEnergy_eq_pairs (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorArityHeadEnergy M P =
      ∑ d ∈ mobiusDivisorSelectionIndices M, ∑ e ∈ mobiusDivisorSelectionIndices M,
        if d.primeFactors ∆ e.primeFactors ⊆ P then
          (((d.primeFactors \ P).card : ℝ) +
            if d.primeFactors \ P = ∅ then 1 else 0) *
              mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M e
        else 0 := by
  have hiff (S T P : Finset ℕ) : S \ P = T \ P ↔ S ∆ T ⊆ P := by
    simp only [Finset.ext_iff, mem_sdiff, subset_iff, mem_symmDiff]
    constructor
    · intro h x hx
      by_contra hn
      have := h x
      tauto
    · intro h x
      constructor
      · rintro ⟨hx, hp⟩
        refine ⟨?_, hp⟩
        by_contra ht
        exact hp (h (Or.inl ⟨hx, ht⟩))
      · rintro ⟨hx, hp⟩
        refine ⟨?_, hp⟩
        by_contra hs
        exact hp (h (Or.inr ⟨hx, hs⟩))
  have hhead : (mobiusDivisorSelectionFibre M P ∅)^2 =
      ∑ d ∈ mobiusDivisorSelectionIndices M, ∑ e ∈ mobiusDivisorSelectionIndices M,
        if d.primeFactors ∆ e.primeFactors ⊆ P ∧ d.primeFactors \ P = ∅ then
          mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M e
        else 0 := by
    unfold mobiusDivisorSelectionFibre subsetLabelFibre
    simp only [sq, Finset.sum_mul_sum]
    apply sum_congr rfl
    intro d hd
    apply sum_congr rfl
    intro e he
    by_cases hdP : d.primeFactors \ P = ∅
    · by_cases heP : e.primeFactors \ P = ∅
      · have hsymm : d.primeFactors ∆ e.primeFactors ⊆ P :=
          (hiff _ _ _).mp (by rw [hdP, heP])
        simp [hdP, heP, hsymm]
      · have hnsymm : ¬d.primeFactors ∆ e.primeFactors ⊆ P := by
          intro h
          apply heP
          have heq := (hiff _ _ _).mpr h
          simpa [hdP] using heq.symm
        simp [hdP, heP, hnsymm]
    · simp [hdP]
  unfold mobiusDivisorArityHeadEnergy
  rw [mobiusDivisorArityEnergy_eq_pairs, hhead, ← Finset.sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  rw [← Finset.sum_add_distrib]
  apply sum_congr rfl
  intro e he
  by_cases hsymm : d.primeFactors ∆ e.primeFactors ⊆ P
  · by_cases hzero : d.primeFactors \ P = ∅ <;>
      simp [hsymm, hzero]
  · simp [hsymm]

/-- The coupled charge is the literal signed pair correlation between adjacent
unprocessed prime labels. -/
theorem mobiusDivisorArityHeadCharge_eq_pairs (M : ℕ) (P : Finset ℕ) (p : ℕ) :
    mobiusDivisorArityHeadCharge M P p =
      2 * ∑ d ∈ mobiusDivisorSelectionIndices M, ∑ e ∈ mobiusDivisorSelectionIndices M,
        if p ∉ d.primeFactors \ P ∧ e.primeFactors \ P = insert p (d.primeFactors \ P) then
          (((d.primeFactors \ P).card : ℝ) +
            if d.primeFactors \ P = ∅ then 1 else 0) *
              mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M e
        else 0 := by
  classical
  let U := mobiusDivisorSelectionPrimes M
  let I := mobiusDivisorSelectionIndices M
  have hlabels (d : ℕ) (hd : d ∈ I) : d.primeFactors ⊆ U := by
    obtain ⟨hdI, hsquarefree⟩ := mem_filter.mp hd
    obtain ⟨hd1, hdM⟩ := mem_Icc.mp hdI
    intro q hq
    have hqbound := Nat.le_of_mem_primeFactors hq
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), (Nat.mem_primeFactors.mp hq).1⟩
  have hdelta :
      (∑ R ∈ (U.erase p).powerset,
        (if R = ∅ then 1 else 0) * mobiusDivisorSelectionFibre M P R *
          mobiusDivisorSelectionFibre M P (insert p R)) =
        mobiusDivisorSelectionFibre M P ∅ * mobiusDivisorSelectionFibre M P {p} := by
    rw [sum_eq_single ∅]
    · simp
    · intro R hR hne
      simp [hne]
    · simp
  have hcombined : mobiusDivisorArityHeadCharge M P p =
      2 * ∑ R ∈ (U.erase p).powerset,
        ((R.card : ℝ) + if R = ∅ then 1 else 0) *
          mobiusDivisorSelectionFibre M P R *
            mobiusDivisorSelectionFibre M P (insert p R) := by
    unfold mobiusDivisorArityHeadCharge mobiusDivisorArityCharge
    calc
      _ = 2 * ((∑ R ∈ (U.erase p).powerset,
          (R.card : ℝ) * mobiusDivisorSelectionFibre M P R *
            mobiusDivisorSelectionFibre M P (insert p R)) +
          mobiusDivisorSelectionFibre M P ∅ * mobiusDivisorSelectionFibre M P {p}) := by ring
      _ = 2 * ((∑ R ∈ (U.erase p).powerset,
          (R.card : ℝ) * mobiusDivisorSelectionFibre M P R *
            mobiusDivisorSelectionFibre M P (insert p R)) +
          ∑ R ∈ (U.erase p).powerset,
            (if R = ∅ then 1 else 0) * mobiusDivisorSelectionFibre M P R *
              mobiusDivisorSelectionFibre M P (insert p R)) := by rw [hdelta]
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        apply congrArg (fun x : ℝ => 2 * x)
        apply sum_congr rfl
        intro R hR
        ring
  have hcollapse (d e : ℕ) (hd : d ∈ I) (he : e ∈ I) :
      (∑ R ∈ (U.erase p).powerset,
        ((R.card : ℝ) + if R = ∅ then 1 else 0) *
          (if d.primeFactors \ P = R then mobiusDivisorDilationChannel M d else 0) *
          (if e.primeFactors \ P = insert p R then mobiusDivisorDilationChannel M e else 0)) =
      if p ∉ d.primeFactors \ P ∧ e.primeFactors \ P = insert p (d.primeFactors \ P) then
        (((d.primeFactors \ P).card : ℝ) + if d.primeFactors \ P = ∅ then 1 else 0) *
          mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M e
      else 0 := by
    by_cases hpD : p ∈ d.primeFactors \ P
    · have hzero : ∀ R ∈ (U.erase p).powerset,
        (if d.primeFactors \ P = R then mobiusDivisorDilationChannel M d else 0) = 0 := by
          intro R hR
          have hpR : p ∉ R := by
            intro hpR
            exact (mem_erase.mp (mem_powerset.mp hR hpR)).1 rfl
          by_cases h : d.primeFactors \ P = R
          · exact (hpR (h ▸ hpD)).elim
          · simp [h]
      rw [sum_eq_zero (fun R hR => by simp [hzero R hR])]
      simp [hpD]
    · by_cases hE : e.primeFactors \ P = insert p (d.primeFactors \ P)
      · have hmem : d.primeFactors \ P ∈ (U.erase p).powerset := by
          apply mem_powerset.mpr
          intro q hq
          apply mem_erase.mpr
          refine ⟨?_, (hlabels d hd) (sdiff_subset hq)⟩
          intro hpq
          exact hpD (hpq ▸ hq)
        rw [sum_eq_single (d.primeFactors \ P)]
        · have hcondition : p ∉ d.primeFactors \ P ∧
              e.primeFactors \ P = insert p (d.primeFactors \ P) := ⟨hpD, hE⟩
          rw [if_pos rfl, if_pos hE, if_pos hcondition]
        · intro R hR hne
          have hR : d.primeFactors \ P ≠ R := Ne.symm hne
          simp [hR]
        · exact fun hn => (hn hmem).elim
      · simp [hpD, hE]
        apply sum_eq_zero
        intro R hR
        by_cases hD : d.primeFactors \ P = R
        · have hR : ¬e.primeFactors \ P = insert p R := by
            intro h
            apply hE
            rw [hD]
            exact h
          simp [hR]
        · simp [hD]
  rw [hcombined]
  apply congrArg (fun x : ℝ => 2 * x)
  unfold mobiusDivisorSelectionFibre subsetLabelFibre
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ e ∈ I, ∑ R ∈ (U.erase p).powerset, ∑ d ∈ I,
        (((R.card : ℝ) + if R = ∅ then 1 else 0) *
          (if d.primeFactors \ P = R then mobiusDivisorDilationChannel M d else 0) *
          (if e.primeFactors \ P = insert p R then mobiusDivisorDilationChannel M e else 0)) := by
        rw [Finset.sum_comm]
    _ = ∑ e ∈ I, ∑ d ∈ I, ∑ R ∈ (U.erase p).powerset,
        (((R.card : ℝ) + if R = ∅ then 1 else 0) *
          (if d.primeFactors \ P = R then mobiusDivisorDilationChannel M d else 0) *
          (if e.primeFactors \ P = insert p R then mobiusDivisorDilationChannel M e else 0)) := by
        apply sum_congr rfl
        intro e he
        rw [Finset.sum_comm]
    _ = ∑ d ∈ I, ∑ e ∈ I, ∑ R ∈ (U.erase p).powerset,
        (((R.card : ℝ) + if R = ∅ then 1 else 0) *
          (if d.primeFactors \ P = R then mobiusDivisorDilationChannel M d else 0) *
          (if e.primeFactors \ P = insert p R then mobiusDivisorDilationChannel M e else 0)) := by
        rw [Finset.sum_comm]
    _ = _ := by
        apply sum_congr rfl
        intro d hd
        apply sum_congr rfl
        intro e he
        exact hcollapse d e hd he

end RHTower
