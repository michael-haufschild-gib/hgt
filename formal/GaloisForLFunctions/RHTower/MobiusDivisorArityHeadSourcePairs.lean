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

/-- On the empty processed core, squarefree source support makes every adjacent
residual-label pair uniquely a literal prime shift.  The cutoff condition is
retained exactly: only `p*d` still inside the source index set contributes. -/
private lemma empty_adjacent_eq_prime_mul {M p d e : ℕ}
    (hd : d ∈ mobiusDivisorSelectionIndices M)
    (he : e ∈ mobiusDivisorSelectionIndices M)
    (hpD : p ∉ d.primeFactors)
    (hlabel : e.primeFactors = insert p d.primeFactors) :
    e = p * d := by
  have hds : Squarefree d := (mem_filter.mp hd).2
  have hes : Squarefree e := (mem_filter.mp he).2
  calc
    e = ∏ q ∈ e.primeFactors, q := (Nat.prod_primeFactors_of_squarefree hes).symm
    _ = ∏ q ∈ insert p d.primeFactors, q := by rw [hlabel]
    _ = p * ∏ q ∈ d.primeFactors, q := prod_insert hpD
    _ = p * d := by rw [Nat.prod_primeFactors_of_squarefree hds]

/-- The empty-core completed charge is exactly one signed, cutoff-truncated
prime-shift correlation.  Its arity factor is the source squarefree rank, with
the separate empty-label boundary contribution retained. -/
theorem mobiusDivisorArityHeadCharge_empty_eq_prime_shift (M : ℕ) {p : ℕ}
    (hp : p.Prime) :
    mobiusDivisorArityHeadCharge M ∅ p =
      2 * ∑ d ∈ mobiusDivisorSelectionIndices M,
        if p ∉ d.primeFactors ∧ p * d ∈ mobiusDivisorSelectionIndices M then
          ((d.primeFactors.card : ℝ) + if d.primeFactors = ∅ then 1 else 0) *
            mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M (p * d)
        else 0 := by
  rw [mobiusDivisorArityHeadCharge_eq_pairs]
  simp only [sdiff_empty]
  congr 1
  apply sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := by
    have := (mem_Icc.mp (mem_filter.mp hd).1).1
    omega
  have hlabel_mul : (p * d).primeFactors = insert p d.primeFactors := by
    rw [Nat.primeFactors_mul hp.ne_zero hd0, hp.primeFactors, singleton_union]
  change
    (∑ e ∈ mobiusDivisorSelectionIndices M,
      if p ∉ d.primeFactors ∧ e.primeFactors = insert p d.primeFactors then
        ((d.primeFactors.card : ℝ) + if d.primeFactors = ∅ then 1 else 0) *
          mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M e
      else 0) =
    if p ∉ d.primeFactors ∧ p * d ∈ mobiusDivisorSelectionIndices M then
      ((d.primeFactors.card : ℝ) + if d.primeFactors = ∅ then 1 else 0) *
        mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M (p * d)
    else 0
  by_cases hpD : p ∉ d.primeFactors
  · by_cases hpd : p * d ∈ mobiusDivisorSelectionIndices M
    · rw [if_pos (And.intro hpD hpd)]
      let f : ℕ → ℝ := fun e =>
        if p ∉ d.primeFactors ∧ e.primeFactors = insert p d.primeFactors then
          ((d.primeFactors.card : ℝ) + if d.primeFactors = ∅ then 1 else 0) *
            mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M e
        else 0
      change (∑ e ∈ mobiusDivisorSelectionIndices M, f e) = _
      have hpoint : f (p * d) =
          ((d.primeFactors.card : ℝ) + if d.primeFactors = ∅ then 1 else 0) *
            mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M (p * d) := by
        dsimp [f]
        rw [if_pos (And.intro hpD hlabel_mul)]
      exact (sum_eq_single
        (s := mobiusDivisorSelectionIndices M) (f := f) (p * d)
        (by
          intro e he hne
          have hzero : ¬(p ∉ d.primeFactors ∧
              e.primeFactors = insert p d.primeFactors) := by
            intro h
            exact hne (empty_adjacent_eq_prime_mul hd he h.1 h.2)
          dsimp [f]
          rw [if_neg hzero])
        (by intro hnot; exact (hnot hpd).elim)).trans hpoint
    · have houter : ¬(p ∉ d.primeFactors ∧ p * d ∈ mobiusDivisorSelectionIndices M) :=
          fun h => hpd h.2
      rw [if_neg houter]
      apply sum_eq_zero
      intro e he
      by_cases hcond : p ∉ d.primeFactors ∧
          e.primeFactors = insert p d.primeFactors
      · have heq := empty_adjacent_eq_prime_mul hd he hcond.1 hcond.2
        exact (hpd (heq ▸ he)).elim
      · rw [if_neg hcond]
  · have houter : ¬(p ∉ d.primeFactors ∧ p * d ∈ mobiusDivisorSelectionIndices M) :=
        fun h => hpD h.1
    rw [if_neg houter]
    apply sum_eq_zero
    intro e he
    have hinner : ¬(p ∉ d.primeFactors ∧
        e.primeFactors = insert p d.primeFactors) := fun h => hpD h.1
    rw [if_neg hinner]

/-- Squarefree source labels determine their source indices. -/
private lemma selection_primeFactors_injective {M d e : ℕ}
    (hd : d ∈ mobiusDivisorSelectionIndices M)
    (he : e ∈ mobiusDivisorSelectionIndices M)
    (h : d.primeFactors = e.primeFactors) : d = e := by
  have hds : Squarefree d := (mem_filter.mp hd).2
  have hes : Squarefree e := (mem_filter.mp he).2
  calc
    d = ∏ q ∈ d.primeFactors, q := (Nat.prod_primeFactors_of_squarefree hds).symm
    _ = ∏ q ∈ e.primeFactors, q := by rw [h]
    _ = e := Nat.prod_primeFactors_of_squarefree hes

/-- The empty-core completed entrance energy is a positive source diagonal:
signs have already squared away before any prime is inserted. -/
theorem mobiusDivisorArityHeadEnergy_empty_eq_diagonal (M : ℕ) :
    mobiusDivisorArityHeadEnergy M ∅ =
      ∑ d ∈ mobiusDivisorSelectionIndices M,
        ((d.primeFactors.card : ℝ) + if d.primeFactors = ∅ then 1 else 0) *
          (mobiusDivisorDilationChannel M d)^2 := by
  rw [mobiusDivisorArityHeadEnergy_eq_pairs]
  simp only [sdiff_empty]
  apply sum_congr rfl
  intro d hd
  have hiff (e : ℕ) : d.primeFactors ∆ e.primeFactors ⊆ ∅ ↔
      e.primeFactors = d.primeFactors := by
    rw [subset_empty, symmDiff_eq_empty]
    exact eq_comm
  let f : ℕ → ℝ := fun e =>
    if d.primeFactors ∆ e.primeFactors ⊆ ∅ then
      ((d.primeFactors.card : ℝ) + if d.primeFactors = ∅ then 1 else 0) *
        mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M e
    else 0
  change (∑ e ∈ mobiusDivisorSelectionIndices M, f e) = _
  have hpoint : f d =
      ((d.primeFactors.card : ℝ) + if d.primeFactors = ∅ then 1 else 0) *
        (mobiusDivisorDilationChannel M d)^2 := by
    dsimp [f]
    rw [if_pos (by simp)]
    ring
  exact (sum_eq_single
    (s := mobiusDivisorSelectionIndices M) (f := f) d
    (by
      intro e he hne
      have hzero : ¬d.primeFactors ∆ e.primeFactors ⊆ ∅ := by
        intro hsub
        have heq : d.primeFactors = e.primeFactors := (hiff e).mp hsub |>.symm
        exact hne (selection_primeFactors_injective (d := d) (e := e) hd he heq).symm
      dsimp [f]
      rw [if_neg hzero])
    (by intro hnot; exact (hnot hd).elim)).trans hpoint

end RHTower
