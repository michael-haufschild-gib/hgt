import GaloisForLFunctions.RHTower.MobiusDivisorHeadNeutralization
import GaloisForLFunctions.RHTower.Sieve.TruncatedMoebius

/-!
# Oriented initial balancing and arbitrary one-prime extension

Stopping below the original head preserves every retained Möbius parity.
Consequently every next prime contracts energy, even when inserted anywhere
inside the chosen late-prime block. Source mass supplies this construction
unconditionally along every sufficiently large cutoff in the cofinal family.
-/
noncomputable section
open Finset Filter Topology
namespace RHTower

/-- A covered nonnegative target admits a selection below it with at most one maximum weight left over. -/
theorem exists_mass_cover_below_with_bounded_residual {α : Type*} [DecidableEq α]
    (U : Finset α) (w : α → ℝ) (a h : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hw : ∀ p ∈ U,0 ≤ w p ∧ w p ≤ a) (hcover : h ≤ ∑ p ∈ U,w p) :
    ∃ L ⊆ U,0 ≤ h-(∑ p ∈ L,w p) ∧ h-(∑ p ∈ L,w p) ≤ a := by
  by_cases hsmall : h ≤ a
  · exact ⟨∅,empty_subset _,by simpa using hh,by simpa using hsmall⟩
  · obtain ⟨L,hLU,h0,h1,_⟩ := exists_mass_cover_with_square_reserve U w a ha (h-a)
      (by linarith) hw (by linarith)
    exact ⟨L,hLU,by linarith,by linarith⟩

/-- Every original retained fibre has its literal squarefree Möbius parity. -/
theorem mobiusDivisorSelectionFibre_empty_parity_nonneg (M : ℕ) (R : Finset ℕ) :
    0 ≤ (-1:ℝ)^R.card*mobiusDivisorSelectionFibre M ∅ R := by
  unfold mobiusDivisorSelectionFibre subsetLabelFibre
  simp only [sdiff_empty]
  rw [mul_sum]
  apply sum_nonneg
  intro d hd
  by_cases he : d.primeFactors=R
  · rw [if_pos he,mobiusDivisorDilationChannel_eq_moebius_unsigned]
    have hmu := congrArg (fun z : ℤ => (z:ℝ))
      (Sieve.moebius_eq_neg_one_pow_card_primeFactors (mem_filter.mp hd).2)
    push_cast at hmu
    rw [he] at hmu
    rw [hmu]
    have h := mul_nonneg (sq_nonneg ((-1:ℝ)^R.card)) (divisorUnsignedDilationChannel_nonneg M d)
    nlinarith only [h]
  · simp [he]

/-- Consuming only late primes preserves the Möbius parity of every nonempty retained fibre. -/
theorem mobiusDivisorSelectionFibre_late_parity_nonneg (M : ℕ) (L : Finset ℕ)
    (hL : ∀ p ∈ L,p.Prime ∧ p<M ∧ M≤2*p) (R : Finset ℕ) (hR : R≠∅) :
    0 ≤ (-1:ℝ)^R.card*mobiusDivisorSelectionFibre M L R := by
  revert hL R
  induction L using Finset.induction_on with
  | empty =>
    intro hL R hR
    exact mobiusDivisorSelectionFibre_empty_parity_nonneg M R
  | @insert p L hpL ih =>
    intro hL R hR
    obtain ⟨hp,hpM,hMp⟩ := hL p (mem_insert_self p L)
    rw [mobiusDivisorSelectionFibre_insert_late_prime hp hpM hMp L R hpL,if_neg hR]
    by_cases hRp : R={p}
    · simp [hRp]
    · rw [if_neg hRp]
      exact ih (fun q hq => hL q (mem_insert_of_mem hq)) R hR

/-- Full retained Möbius parity makes every available prime merger contract complete energy. -/
theorem mobiusDivisorSelectionEnergy_insert_le_of_parity_nonneg
    (M : ℕ) (P : Finset ℕ) {q : ℕ} (hq : q.Prime) (hqM : q<M) (hqP : q ∉ P)
    (hparity : ∀ R : Finset ℕ,0 ≤ (-1:ℝ)^R.card*mobiusDivisorSelectionFibre M P R) :
    mobiusDivisorSelectionEnergy M (insert q P) ≤ mobiusDivisorSelectionEnergy M P := by
  have hsum : (∑ R ∈ ((mobiusDivisorSelectionPrimes M).erase q).powerset,
      mobiusDivisorSelectionFibre M P R*mobiusDivisorSelectionFibre M P (insert q R)) ≤ 0 := by
    apply sum_nonpos
    intro R hR
    have hqR : q ∉ R := by
      intro hm
      have := mem_powerset.mp hR hm
      simp at this
    have hsquare : ((-1:ℝ)^R.card)^(2 : ℕ)=1 := by
      calc
        _ = ((-1:ℝ)^(2 : ℕ))^R.card := by
          rw [← pow_mul,← pow_mul,Nat.mul_comm R.card 2]
        _ = 1 := by norm_num
    have hnext := hparity (insert q R)
    rw [card_insert_of_notMem hqR,pow_succ] at hnext
    have hprod := mul_nonneg (hparity R) hnext
    have heq : ((-1:ℝ)^R.card*mobiusDivisorSelectionFibre M P R)*
        ((-1:ℝ)^R.card*(-1)*mobiusDivisorSelectionFibre M P (insert q R)) =
        -(mobiusDivisorSelectionFibre M P R*mobiusDivisorSelectionFibre M P (insert q R)) := by
      calc
        _ = -((-1:ℝ)^R.card)^(2 : ℕ)*(mobiusDivisorSelectionFibre M P R*
          mobiusDivisorSelectionFibre M P (insert q R)) := by ring
        _ = _ := by rw [hsquare]; ring
    rw [heq] at hprod
    linarith only [hprod]
  have h := mobiusDivisorSelectionEnergy_insert_cross hq M P hqM hqP
  linarith only [h,hsum]

/-- After any late-only state with nonnegative head, every available prime still contracts energy. -/
theorem mobiusDivisorSelectionEnergy_insert_le_after_late_primes
    (M : ℕ) (L : Finset ℕ) (hL : ∀ p ∈ L,p.Prime ∧ p<M ∧ M≤2*p)
    (hh : 0 ≤ mobiusDivisorSelectionFibre M L ∅)
    {q : ℕ} (hq : q.Prime) (hqM : q<M) (hqL : q ∉ L) :
    mobiusDivisorSelectionEnergy M (insert q L) ≤ mobiusDivisorSelectionEnergy M L := by
  apply mobiusDivisorSelectionEnergy_insert_le_of_parity_nonneg M L hq hqM hqL
  intro R
  by_cases hR : R=∅
  · simpa [hR] using hh
  · exact mobiusDivisorSelectionFibre_late_parity_nonneg M L hL R hR

/-- Source mass supplies a nonnegative small head and contraction of every one-prime extension at every intermediate subset. -/
theorem exists_mobiusDivisorInitialOrientedPrimeExtension (M : ℕ) (U : Finset ℕ)
    (hU : ∀ p ∈ U,p.Prime ∧ p<M ∧ M≤2*p)
    (hcover : mobiusDivisorSelectionFibre M ∅ ∅ ≤ ∑ p ∈ U,divisorUnsignedDilationChannel M p) :
    ∃ L ⊆ U,
      (0 ≤ mobiusDivisorSelectionFibre M L ∅ ∧ mobiusDivisorSelectionFibre M L ∅ ≤ Real.sqrt M) ∧
      (mobiusDivisorSelectionFibre M L ∅)^(2 : ℕ) ≤ M ∧
      mobiusDivisorSelectionEnergy M L ≤ mobiusDivisorNonemptyEnergy M ∅+M ∧
      ∀ R ⊆ L,mobiusDivisorSelectionEnergy M R ≤ mobiusDivisorSelectionEnergy M ∅ ∧
        ∀ q : ℕ,q.Prime → q<M → q ∉ R →
          mobiusDivisorSelectionEnergy M (insert q R) ≤ mobiusDivisorSelectionEnergy M R := by
  obtain ⟨L,hLU,h0,h1⟩ := exists_mass_cover_below_with_bounded_residual U
    (divisorUnsignedDilationChannel M) (Real.sqrt M) (mobiusDivisorSelectionFibre M ∅ ∅)
    (Real.sqrt_nonneg _) (mobiusDivisorSelectionHead_empty_nonneg M)
    (fun p hp => ⟨divisorUnsignedDilationChannel_nonneg M p,
      divisorUnsignedDilationChannel_late_le_sqrt (hU p hp).1.pos (hU p hp).2.1 (hU p hp).2.2⟩) hcover
  have hL : ∀ p ∈ L,p.Prime ∧ p<M ∧ M≤2*p := fun p hp => hU p (hLU hp)
  have hhead : mobiusDivisorSelectionFibre M L ∅ = mobiusDivisorSelectionFibre M ∅ ∅-
      ∑ p ∈ L,divisorUnsignedDilationChannel M p := by
    have h := mobiusDivisorSelectionHead_union_late_primes M ∅ L hL (by simp)
    simp only [empty_union] at h
    rw [h,sub_eq_add_neg,← sum_neg_distrib]
    congr 1
    apply sum_congr rfl
    intro p hp
    rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,ArithmeticFunction.moebius_apply_prime (hL p hp).1]
    push_cast
    ring
  rw [← hhead] at h0 h1
  have hHsq : (mobiusDivisorSelectionFibre M L ∅)^(2 : ℕ) ≤ M := by
    have hprod := mul_nonneg (show 0 ≤ Real.sqrt M-mobiusDivisorSelectionFibre M L ∅ by linarith only [h1])
      (show 0 ≤ Real.sqrt M+mobiusDivisorSelectionFibre M L ∅ by linarith [Real.sqrt_nonneg (M:ℝ)])
    nlinarith only [hprod,Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) M)]
  have hV := mobiusDivisorNonemptyEnergy_union_late_primes_le M ∅ L hL (by simp)
  simp only [empty_union] at hV
  have henergy : mobiusDivisorSelectionEnergy M L ≤ mobiusDivisorNonemptyEnergy M ∅+M := by
    unfold mobiusDivisorNonemptyEnergy at hV ⊢
    linarith only [hV,hHsq]
  refine ⟨L,hLU,⟨h0,h1⟩,hHsq,henergy,?_⟩
  intro R hRL
  have hR : ∀ p ∈ R,p.Prime ∧ p<M ∧ M≤2*p := fun p hp => hL p (hRL hp)
  have hheadR : 0 ≤ mobiusDivisorSelectionFibre M R ∅ := by
    have he : R ∪ (L \ R)=L := union_sdiff_of_subset hRL
    have hd := mobiusDivisorSelectionHead_union_late_primes_le M R (L \ R)
      (fun p hp => hL p (mem_sdiff.mp hp).1)
      (fun p hp => (mem_sdiff.mp hp).2)
    rw [he] at hd
    exact h0.trans hd
  constructor
  · have h := mobiusDivisorSelectionEnergy_union_late_primes_le_of_head_nonneg M ∅ R hR
      (by simp) (by simpa using hheadR)
    simpa only [empty_union] using h
  · intro q hq hqM hqR
    exact mobiusDivisorSelectionEnergy_insert_le_after_late_primes M R hR hheadR hq hqM hqR

/-- Unconditionally, a square-root-sized nonnegative initial head permits every one-prime interleaving within the original diagonal. -/
theorem eventually_exists_mobiusDivisorInitialOrientedPrimeExtension :
    ∀ᶠ N : ℕ in atTop,∃ L ⊆ mobiusDivisorActiveLatePrimes (4*N),
      (0 ≤ mobiusDivisorSelectionFibre (4*N) L ∅ ∧
        mobiusDivisorSelectionFibre (4*N) L ∅ ≤ Real.sqrt (4*N:ℕ)) ∧
      (mobiusDivisorSelectionFibre (4*N) L ∅)^(2 : ℕ) ≤ (4*N:ℕ) ∧
      mobiusDivisorSelectionEnergy (4*N) L ≤ mobiusDivisorNonemptyEnergy (4*N) ∅+(4*N:ℕ) ∧
      ∀ R ⊆ L,mobiusDivisorSelectionEnergy (4*N) R ≤ mobiusDivisorSelectionEnergy (4*N) ∅ ∧
        ∀ q : ℕ,q.Prime → q<4*N → q ∉ R →
          mobiusDivisorSelectionEnergy (4*N) (insert q R) ≤ mobiusDivisorSelectionEnergy (4*N) R := by
  filter_upwards [eventually_mobiusDivisorLatePrimeMass_covers_initial_head] with N hcover
  rw [← sum_mobiusDivisorActiveLatePrimes] at hcover
  exact exists_mobiusDivisorInitialOrientedPrimeExtension (4*N) _
    (fun _ hp => mem_mobiusDivisorActiveLatePrimes hp) hcover
end RHTower
