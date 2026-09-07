import GaloisForLFunctions.RHTower.MobiusDivisorPrimeFibreHomothety
import GaloisForLFunctions.RHTower.SignedScalarMergeOrder

/-!
# The square-root terminal phase of prime selection

After processing all primes whose squares are below the cutoff, every active
source label is empty or singleton. The remaining signed singleton fibres
form a scalar merger problem, with a complete adaptive order attaining the
larger endpoint energy. No bound on either endpoint is assumed or proved.
-/

noncomputable section
open Finset
namespace RHTower

/-- Primes that must be processed to make every remaining active label scalar. -/
def mobiusDivisorSmallSelectionPrimes (M : ℕ) : Finset ℕ :=
  (mobiusDivisorSelectionPrimes M).filter (fun p => p*p<M)

/-- Two unprocessed prime factors cannot both remain after the square-root threshold. -/
theorem mobiusDivisorSelectionLabel_card_le_one (M : ℕ) (P : Finset ℕ)
    (hP : mobiusDivisorSmallSelectionPrimes M ⊆ P)
    (d : ℕ) (hd : d ∈ mobiusDivisorSelectionIndices M) :
    (d.primeFactors \ P).card ≤ 1 := by
  apply card_le_one.mpr
  intro p hp q hq
  obtain ⟨hpD,hpP⟩ := mem_sdiff.mp hp
  obtain ⟨hqD,hqP⟩ := mem_sdiff.mp hq
  obtain ⟨hd1,hdM⟩ := mem_Icc.mp (mem_filter.mp hd).1
  obtain ⟨hpPrime,hpd,_⟩ := Nat.mem_primeFactors.mp hpD
  obtain ⟨hqPrime,hqd,_⟩ := Nat.mem_primeFactors.mp hqD
  have hpM : p<M := by have := Nat.le_of_mem_primeFactors hpD; omega
  have hqM : q<M := by have := Nat.le_of_mem_primeFactors hqD; omega
  have hpp : M ≤ p*p := by
    by_contra hn
    exact hpP (hP (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr hpM,hpPrime⟩,by omega⟩))
  have hqq : M ≤ q*q := by
    by_contra hn
    exact hqP (hP (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr hqM,hqPrime⟩,by omega⟩))
  by_contra hpq
  have hdvd := ((Nat.coprime_primes hpPrime hqPrime).mpr hpq).mul_dvd_of_dvd_of_dvd hpd hqd
  have hprod := Nat.le_of_dvd hd1 hdvd
  rcases le_total p q with hpq|hqp
  · have := Nat.mul_le_mul_left p hpq
    omega
  · have := Nat.mul_le_mul_right q hqp
    omega

/-- Every nonscalar retained fibre vanishes throughout the terminal phase. -/
theorem mobiusDivisorSelectionFibre_eq_zero_of_card_gt_one (M : ℕ) (P R : Finset ℕ)
    (hP : mobiusDivisorSmallSelectionPrimes M ⊆ P) (hR : 1<R.card) :
    mobiusDivisorSelectionFibre M P R=0 := by
  unfold mobiusDivisorSelectionFibre subsetLabelFibre
  apply sum_eq_zero
  intro d hd
  have hne : d.primeFactors \ P ≠ R := by
    intro he
    have := mobiusDivisorSelectionLabel_card_le_one M P hP d hd
    rw [he] at this
    omega
  simp [hne]

private theorem processed_singleton_zero (M : ℕ) (P : Finset ℕ) (p : ℕ) (hp : p ∈ P) :
    mobiusDivisorSelectionFibre M P {p}=0 := by
  unfold mobiusDivisorSelectionFibre subsetLabelFibre
  apply sum_eq_zero
  intro d hd
  have hne : d.primeFactors \ P ≠ {p} := by
    intro he
    have hm : p ∈ d.primeFactors \ P := he.symm ▸ mem_singleton_self p
    exact (mem_sdiff.mp hm).2 hp
  simp [hne]

private theorem terminal_fibre_sum (M : ℕ) (P : Finset ℕ)
    (hP : mobiusDivisorSmallSelectionPrimes M ⊆ P) (f : ℝ → ℝ) (hf : f 0=0) :
    (∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset,f (mobiusDivisorSelectionFibre M P R))=
      f (mobiusDivisorSelectionFibre M P ∅)+
        ∑ p ∈ mobiusDivisorSelectionPrimes M \ P,f (mobiusDivisorSelectionFibre M P {p}) := by
  rw [sum_powerset_of_card_le_one_support _ _ (fun R _ hR => by
    rw [mobiusDivisorSelectionFibre_eq_zero_of_card_gt_one M P R hP hR,hf])]
  congr 1
  symm
  apply sum_subset sdiff_subset
  intro p hp hn
  have hpP : p ∈ P := by simpa [hp] using hn
  rw [processed_singleton_zero M P p hpP,hf]

/-- The literal retained energy is exactly the head square plus remaining singleton squares. -/
theorem mobiusDivisorSelectionEnergy_terminal (M : ℕ) (P : Finset ℕ)
    (hP : mobiusDivisorSmallSelectionPrimes M ⊆ P) :
    mobiusDivisorSelectionEnergy M P = (mobiusDivisorSelectionFibre M P ∅)^2+
      ∑ p ∈ mobiusDivisorSelectionPrimes M \ P,(mobiusDivisorSelectionFibre M P {p})^2 := by
  exact terminal_fibre_sum M P hP (fun x => x^2) (by simp)

/-- The head and remaining singleton leaves retain the complete signed arithmetic source. -/
theorem mobiusDivisorSelectionHead_add_terminal_leaves (M : ℕ) (P : Finset ℕ)
    (hP : mobiusDivisorSmallSelectionPrimes M ⊆ P) :
    mobiusDivisorSelectionFibre M P ∅+
      (∑ p ∈ mobiusDivisorSelectionPrimes M \ P,mobiusDivisorSelectionFibre M P {p}) =
      ∑ d ∈ Icc 1 M,mobiusDivisorDilationChannel M d := by
  exact (terminal_fibre_sum M P hP id rfl).symm.trans
    (mobiusDivisorSelectionFibre_sum M P)

/-- Processing other terminal primes leaves a surviving singleton coefficient unchanged. -/
theorem mobiusDivisorSelectionFibre_singleton_union_terminal (M : ℕ) (P R : Finset ℕ)
    (hP : mobiusDivisorSmallSelectionPrimes M ⊆ P) (p : ℕ) :
    mobiusDivisorSelectionFibre M (P ∪ R) {p} =
      if p ∈ R then 0 else mobiusDivisorSelectionFibre M P {p} := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert q R hqR ih =>
    rw [union_insert,mobiusDivisorSelectionFibre_insert]
    by_cases hqp : q=p
    · subst q
      simp
    · have hz : mobiusDivisorSelectionFibre M (P ∪ R) (insert q {p})=0 := by
        apply mobiusDivisorSelectionFibre_eq_zero_of_card_gt_one M (P ∪ R) _
          (hP.trans subset_union_left)
        simp [card_insert_of_notMem, hqp]
      simp [hqp,hz,ih,Ne.symm hqp]

/-- Terminal head accumulation is the exact sum of its initially retained signed leaves. -/
theorem mobiusDivisorSelectionHead_union_terminal (M : ℕ) (P R : Finset ℕ)
    (hP : mobiusDivisorSmallSelectionPrimes M ⊆ P) :
    mobiusDivisorSelectionFibre M (P ∪ R) ∅ = mobiusDivisorSelectionFibre M P ∅+
      ∑ p ∈ R,mobiusDivisorSelectionFibre M P {p} := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert p R hpR ih =>
    rw [union_insert,mobiusDivisorSelectionFibre_insert]
    simp only [notMem_empty,if_false,insert_empty_eq]
    rw [mobiusDivisorSelectionFibre_singleton_union_terminal M P R hP p,if_neg hpR,
      ih,sum_insert hpR]
    ring

/-- The entire terminal prime-subset energy is the literal signed scalar energy. -/
theorem mobiusDivisorSelectionEnergy_union_terminal (M : ℕ) (P R : Finset ℕ)
    (hP : mobiusDivisorSmallSelectionPrimes M ⊆ P) :
    mobiusDivisorSelectionEnergy M (P ∪ R) =
      scalarSubsetMergeEnergy (fun p => mobiusDivisorSelectionFibre M P {p})
        (mobiusDivisorSelectionFibre M P ∅) (mobiusDivisorSelectionPrimes M \ P) R := by
  rw [mobiusDivisorSelectionEnergy_terminal M (P ∪ R) (hP.trans subset_union_left),
    mobiusDivisorSelectionHead_union_terminal M P R hP,scalarSubsetMergeEnergy]
  congr 1
  have he : mobiusDivisorSelectionPrimes M \ (P ∪ R)=(mobiusDivisorSelectionPrimes M \ P) \ R := by
    ext p
    simp
    tauto
  rw [he]
  apply sum_congr rfl
  intro p hp
  rw [mobiusDivisorSelectionFibre_singleton_union_terminal M P R hP p,
    if_neg (mem_sdiff.mp hp).2]

/-- Every terminal state admits a complete prime order below the larger actual endpoint energy. -/
theorem exists_mobiusDivisorTerminalPrimeOrder (M : ℕ) (P : Finset ℕ)
    (hP : mobiusDivisorSmallSelectionPrimes M ⊆ P) :
    ∃ l : List ℕ,l.Nodup ∧ l.toFinset=mobiusDivisorSelectionPrimes M \ P ∧ ∀ k : ℕ,
      mobiusDivisorSelectionEnergy M (P ∪ (l.take k).toFinset) ≤
        max (mobiusDivisorSelectionEnergy M P)
          ((∑ d ∈ Icc 1 M,mobiusDivisorDilationChannel M d)^2) := by
  obtain ⟨l,hl,hset,hbound⟩ := exists_scalarSubsetMergeOrder
    (fun p => mobiusDivisorSelectionFibre M P {p}) (mobiusDivisorSelectionFibre M P ∅)
    (mobiusDivisorSelectionPrimes M \ P)
  refine ⟨l,hl,hset,fun k => ?_⟩
  rw [mobiusDivisorSelectionEnergy_union_terminal M P _ hP]
  have hk := hbound k
  rw [← mobiusDivisorSelectionEnergy_terminal M P hP,
    mobiusDivisorSelectionHead_add_terminal_leaves M P hP] at hk
  exact hk

/-- The sharp terminal ceiling criterion retains both actual endpoints. -/
theorem exists_mobiusDivisorTerminalPrimeOrder_iff (M : ℕ) (P : Finset ℕ)
    (hP : mobiusDivisorSmallSelectionPrimes M ⊆ P) (B : ℝ) :
    (∃ l : List ℕ,l.Nodup ∧ l.toFinset=mobiusDivisorSelectionPrimes M \ P ∧ ∀ k : ℕ,
      mobiusDivisorSelectionEnergy M (P ∪ (l.take k).toFinset) ≤ B) ↔
      mobiusDivisorSelectionEnergy M P ≤ B ∧
        (∑ d ∈ Icc 1 M,mobiusDivisorDilationChannel M d)^2 ≤ B := by
  constructor
  · rintro ⟨l,hl,hset,hbound⟩
    constructor
    · simpa using hbound 0
    · have hk := hbound l.length
      simp only [List.take_length,hset] at hk
      rw [mobiusDivisorSelectionEnergy_union_terminal M P _ hP] at hk
      simpa [scalarSubsetMergeEnergy,mobiusDivisorSelectionHead_add_terminal_leaves M P hP] using hk
  · rintro ⟨hi,hf⟩
    obtain ⟨l,hl,hset,hbound⟩ := exists_mobiusDivisorTerminalPrimeOrder M P hP
    exact ⟨l,hl,hset,fun k => (hbound k).trans (max_le hi hf)⟩

/-- Unconditionally, the canonical square-root stage has an endpoint-optimal terminal order. -/
theorem exists_mobiusDivisorSquareRootTerminalOrder (M : ℕ) :
    ∃ l : List ℕ,l.Nodup ∧
      l.toFinset=mobiusDivisorSelectionPrimes M \ mobiusDivisorSmallSelectionPrimes M ∧ ∀ k : ℕ,
      mobiusDivisorSelectionEnergy M (mobiusDivisorSmallSelectionPrimes M ∪ (l.take k).toFinset) ≤
        max (mobiusDivisorSelectionEnergy M (mobiusDivisorSmallSelectionPrimes M))
          ((∑ d ∈ Icc 1 M,mobiusDivisorDilationChannel M d)^2) := by
  exact exists_mobiusDivisorTerminalPrimeOrder M (mobiusDivisorSmallSelectionPrimes M) Subset.rfl
end RHTower

