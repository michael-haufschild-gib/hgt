import GaloisForLFunctions.RHTower.MobiusDivisorBernoulliPrimeEnergy
import GaloisForLFunctions.RHTower.DivisorUnsignedChannelPositivity

/-!
# Isolated late-prime fibres of the actual divisor source

If `M ≤ 2*p` and `p<M`, the only active arithmetic label containing the prime
`p` is `p` itself. Processing it adds its nonpositive coefficient to the
empty-cofactor head and removes its singleton fibre. The exact energy change
is twice the product of that coefficient and the current head.
-/

noncomputable section
open Finset
namespace RHTower

private theorem late_prime_label_is_singleton {M p n : ℕ}
    (hn : n ∈ mobiusDivisorSelectionIndices M) (hM : M ≤ 2*p)
    (hpn : p ∈ n.primeFactors) : n=p := by
  have hnM := mem_Icc.mp (mem_filter.mp hn).1
  obtain ⟨hp,hpd,hn0⟩ := Nat.mem_primeFactors.mp hpn
  obtain ⟨k,hk⟩ := hpd
  have hk0 : 1 ≤ k := by
    by_contra h
    have hkz : k=0 := by omega
    rw [hkz,Nat.mul_zero] at hk
    omega
  have hk1 : k=1 := by
    by_contra hne
    have hkle : 2 ≤ k := by omega
    have hmul := Nat.mul_le_mul_left p hkle
    omega
  simpa only [hk1,Nat.mul_one] using hk

/-- Every retained fibre containing a late prime is its isolated singleton or zero. -/
theorem mobiusDivisorSelectionFibre_late_prime {M p : ℕ} (hp : p.Prime)
    (hpM : p<M) (hM : M ≤ 2*p) (P R : Finset ℕ) (hpP : p ∉ P) (hpR : p ∈ R) :
    mobiusDivisorSelectionFibre M P R =
      if R={p} then mobiusDivisorDilationChannel M p else 0 := by
  have hpi : p ∈ mobiusDivisorSelectionIndices M := by
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.pos,by omega⟩,hp.squarefree⟩
  unfold mobiusDivisorSelectionFibre subsetLabelFibre
  rw [sum_eq_single p]
  · have he : p.primeFactors \ P = {p} := by simp [hp.primeFactors,hpP]
    rw [he]
    by_cases h : R={p}
    · simp [h]
    · simp [h,Ne.symm h]
  · intro n hn hnp
    have hne : n.primeFactors \ P ≠ R := by
      intro he
      have hpn : p ∈ n.primeFactors := (mem_sdiff.mp (he.symm ▸ hpR)).1
      exact hnp (late_prime_label_is_singleton hn hM hpn)
    rw [if_neg hne]
  · exact fun hn => (hn hpi).elim

/-- Every prime coefficient has nonpositive sign by actual unsigned channel positivity. -/
theorem mobiusDivisorDilationChannel_late_prime_nonpos {p : ℕ} (hp : p.Prime) (M : ℕ) :
    mobiusDivisorDilationChannel M p ≤ 0 := by
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,ArithmeticFunction.moebius_apply_prime hp]
  simpa using neg_nonpos.mpr (divisorUnsignedDilationChannel_nonneg M p)

/-- An isolated late-prime merger changes only the empty and singleton fibres. -/
theorem mobiusDivisorSelectionFibre_insert_late_prime {M p : ℕ} (hp : p.Prime)
    (hpM : p<M) (hM : M ≤ 2*p) (P R : Finset ℕ) (hpP : p ∉ P) :
    mobiusDivisorSelectionFibre M (insert p P) R =
      if R=∅ then mobiusDivisorSelectionFibre M P ∅+mobiusDivisorDilationChannel M p
      else if R={p} then 0 else mobiusDivisorSelectionFibre M P R := by
  have hsingle := mobiusDivisorSelectionFibre_late_prime hp hpM hM P {p} hpP (mem_singleton_self p)
  simp only [if_true] at hsingle
  rw [mobiusDivisorSelectionFibre_insert]
  by_cases hR0 : R=∅
  · simp [hR0,hsingle]
  by_cases hRp : R={p}
  · simp [hRp]
  by_cases hpR : p ∈ R
  · rw [if_pos hpR,if_neg hR0,if_neg hRp,
      mobiusDivisorSelectionFibre_late_prime hp hpM hM P R hpP hpR,if_neg hRp]
  · have hne : insert p R ≠ {p} := by
      intro he
      apply hR0
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxp : x=p := mem_singleton.mp (he ▸ mem_insert_of_mem hx)
      exact hpR (hxp ▸ hx)
    rw [if_neg hpR,if_neg hR0,if_neg hRp,
      mobiusDivisorSelectionFibre_late_prime hp hpM hM P (insert p R) hpP (mem_insert_self p R),
      if_neg hne,add_zero]

/-- The exact empty-cofactor head update for an unprocessed late prime. -/
theorem mobiusDivisorSelectionHead_insert_late_prime {M p : ℕ} (hp : p.Prime)
    (hpM : p<M) (hM : M ≤ 2*p) (P : Finset ℕ) (hpP : p ∉ P) :
    mobiusDivisorSelectionFibre M (insert p P) ∅ =
      mobiusDivisorSelectionFibre M P ∅+mobiusDivisorDilationChannel M p := by
  simp only [mobiusDivisorSelectionFibre_insert_late_prime hp hpM hM P ∅ hpP,if_true]

/-- The exact late-prime energy change retains its signed head overlap. -/
theorem mobiusDivisorSelectionEnergy_insert_late_prime {M p : ℕ} (hp : p.Prime)
    (hpM : p<M) (hM : M ≤ 2*p) (P : Finset ℕ) (hpP : p ∉ P) :
    mobiusDivisorSelectionEnergy M (insert p P)-mobiusDivisorSelectionEnergy M P =
      2*mobiusDivisorSelectionFibre M P ∅*mobiusDivisorDilationChannel M p := by
  have hpU : p ∈ mobiusDivisorSelectionPrimes M := mem_filter.mpr ⟨mem_range.mpr hpM,hp⟩
  have hsingle := mobiusDivisorSelectionFibre_late_prime hp hpM hM P {p} hpP (mem_singleton_self p)
  simp only [if_true] at hsingle
  change (∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset, (mobiusDivisorSelectionFibre M (insert p P) R)^(2 : ℕ))-
    (∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset, (mobiusDivisorSelectionFibre M P R)^(2 : ℕ))=_
  rw [← sum_sub_distrib]
  have he : ∀ R : Finset ℕ,
      (mobiusDivisorSelectionFibre M (insert p P) R)^(2 : ℕ)-(mobiusDivisorSelectionFibre M P R)^(2 : ℕ) =
      (if R=∅ then 2*mobiusDivisorSelectionFibre M P ∅*mobiusDivisorDilationChannel M p+
        (mobiusDivisorDilationChannel M p)^(2 : ℕ) else 0) -
      (if R={p} then (mobiusDivisorDilationChannel M p)^(2 : ℕ) else 0) := by
    intro R
    rw [mobiusDivisorSelectionFibre_insert_late_prime hp hpM hM P R hpP]
    by_cases hR0 : R=∅
    · simp [hR0]
      ring
    by_cases hRp : R={p}
    · simp [hRp,hsingle]
    · simp [hR0,hRp]
  simp_rw [he]
  rw [sum_sub_distrib]
  simp [hpU]

end RHTower
