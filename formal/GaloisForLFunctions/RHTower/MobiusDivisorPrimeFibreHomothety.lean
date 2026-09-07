import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeFibres
import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleConvergence
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Prime homothety of the retained divisor source

For a prime `p>N`, the fibres containing an unprocessed `p` at cutoff `p*N`
are exact reflected square-root-scaled copies of the retained source at
cutoff `N`. The ensuing prime merger subtracts that copy from every other
fibre. Its energy change is the complete mixed inner product of the two
source fields, with no sign or cancellation assumption.
-/

noncomputable section
open Finset
namespace RHTower

/-- Extend the retained fibre to the full arithmetic interval; all added coefficients vanish. -/
theorem mobiusDivisorSelectionFibre_eq_sum_Icc (M : ℕ) (P R : Finset ℕ) :
    mobiusDivisorSelectionFibre M P R =
      ∑ d ∈ Icc 1 M,if d.primeFactors \ P=R then mobiusDivisorDilationChannel M d else 0 := by
  unfold mobiusDivisorSelectionFibre subsetLabelFibre
  calc
    _ = ∑ d ∈ Icc 1 (M-1),if d.primeFactors \ P=R then mobiusDivisorDilationChannel M d else 0 := by
      rw [mobiusDivisorSelectionIndices,sum_filter]
      apply sum_congr rfl
      intro d hd
      by_cases hs : Squarefree d
      · simp [hs]
      · have hz : mobiusDivisorDilationChannel M d=0 := by
          simp [mobiusDivisorDilationChannel,ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
        simp [hs,hz]
    _ = _ := by
      apply sum_subset
      · intro d hd
        obtain ⟨hl,hu⟩ := mem_Icc.mp hd
        exact mem_Icc.mpr ⟨hl,by omega⟩
      · intro d hd hn
        have heq : d=M := by simp only [mem_Icc] at hd hn; omega
        subst d
        have hz : mobiusDivisorDilationChannel M M=0 := by
          have hM : 0<M := (mem_Icc.mp hd).1
          simp [mobiusDivisorDilationChannel,Icc_eq_empty_of_lt (by omega : M-1<M)]
        simp [hz]

/-- An unprocessed new prime carries an exact reflected copy of every smaller-cutoff fibre. -/
theorem mobiusDivisorSelectionFibre_mul_prime {N p : ℕ} (hp : p.Prime) (hNp : N<p)
    (P R : Finset ℕ) (hpP : p ∉ P) (hpR : p ∉ R) :
    mobiusDivisorSelectionFibre (p*N) P (insert p R) =
      -Real.sqrt p*mobiusDivisorSelectionFibre N P R := by
  rw [mobiusDivisorSelectionFibre_eq_sum_Icc,mobiusDivisorSelectionFibre_eq_sum_Icc]
  have hrestrict : (∑ n ∈ Icc 1 (p*N),
      if n.primeFactors \ P=insert p R then mobiusDivisorDilationChannel (p*N) n else 0) =
      ∑ n ∈ (Icc 1 (p*N)).filter (fun n => p ∣ n),
        if n.primeFactors \ P=insert p R then mobiusDivisorDilationChannel (p*N) n else 0 := by
    rw [sum_filter]
    apply sum_congr rfl
    intro n hn
    by_cases hpn : p ∣ n
    · simp [hpn]
    · have hne : n.primeFactors \ P ≠ insert p R := by
        intro he
        have hm : p ∈ n.primeFactors := (mem_sdiff.mp (he.symm ▸ mem_insert_self p R)).1
        exact hpn (Nat.mem_primeFactors.mp hm).2.1
      simp [hpn,hne]
  rw [hrestrict,sum_Icc_filter_dvd_reindex p (p*N) hp.pos,Nat.mul_div_cancel_left N hp.pos, mul_sum]
  apply sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  have hpndvd : ¬p ∣ n := by
    intro h
    have := Nat.le_of_dvd (mem_Icc.mp hn).1 h
    have := (mem_Icc.mp hn).2
    omega
  have hc : p.Coprime n := hp.coprime_iff_not_dvd.mpr hpndvd
  have hpn : p ∉ n.primeFactors := fun h => hpndvd (Nat.mem_primeFactors.mp h).2.1
  have hlabel : (p*n).primeFactors \ P=insert p (n.primeFactors \ P) := by
    rw [Nat.primeFactors_mul hp.ne_zero hn0,hp.primeFactors]
    ext q
    simp only [mem_sdiff,mem_union,mem_singleton,mem_insert]
    constructor
    · rintro ⟨hq,hqP⟩
      rcases hq with hq|hq
      · exact Or.inl hq
      · exact Or.inr ⟨hq,hqP⟩
    · rintro (hq|hq)
      · subst q
        exact ⟨Or.inl rfl,hpP⟩
      · exact ⟨Or.inr hq.1,hq.2⟩
  have heq : insert p (n.primeFactors \ P)=insert p R ↔ n.primeFactors \ P=R := by
    constructor
    · intro he
      ext q
      by_cases hq : q=p
      · subst q
        simp [hpn,hpR]
      · have h := Finset.ext_iff.mp he q
        simpa [hq] using h
    · intro he
      rw [he]
  rw [hlabel]
  by_cases he : n.primeFactors \ P=R
  · rw [if_pos (heq.mpr he),if_pos he,mobiusDivisorDilationChannel_mul_coprime hc,
      ArithmeticFunction.moebius_apply_prime hp]
    push_cast
    ring
  · rw [if_neg (fun h => he (heq.mp h)),if_neg he,mul_zero]

/-- The new prime singleton is the reflected smaller-cutoff head. -/
theorem mobiusDivisorSelectionFibre_mul_prime_singleton {N p : ℕ} (hp : p.Prime) (hNp : N<p)
    (P : Finset ℕ) (hpP : p ∉ P) :
    mobiusDivisorSelectionFibre (p*N) P {p} = -Real.sqrt p*mobiusDivisorSelectionFibre N P ∅ := by
  simpa only [insert_empty_eq] using mobiusDivisorSelectionFibre_mul_prime hp hNp P ∅ hpP (by simp)

/-- Processing every active source prime concentrates the complete signed sum at the empty label. -/
theorem mobiusDivisorSelectionFibre_of_all_source_primes_processed (N : ℕ) (P R : Finset ℕ)
    (hP : mobiusDivisorSelectionPrimes N ⊆ P) :
    mobiusDivisorSelectionFibre N P R =
      if R=∅ then (∑ n ∈ Icc 1 N,mobiusDivisorDilationChannel N n) else 0 := by
  have he : ∀ n ∈ mobiusDivisorSelectionIndices N,n.primeFactors \ P=∅ := by
    intro n hn
    apply sdiff_eq_empty_iff_subset.mpr
    intro q hq
    apply hP
    have hnN := mem_Icc.mp (mem_filter.mp hn).1
    have hqn := Nat.le_of_mem_primeFactors hq
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),(Nat.mem_primeFactors.mp hq).1⟩
  by_cases hR : R=∅
  · subst R
    have hsum := mobiusDivisorSelectionFibre_sum N P
    have hz : ∀ R : Finset ℕ,R ≠ ∅ → mobiusDivisorSelectionFibre N P R=0 := by
      intro R hR
      unfold mobiusDivisorSelectionFibre subsetLabelFibre
      apply sum_eq_zero
      intro n hn
      simp [he n hn,Ne.symm hR]
    rw [sum_eq_single ∅] at hsum
    · simpa using hsum
    · intro R hR hne
      exact hz R hne
    · simp
  · rw [if_neg hR]
    unfold mobiusDivisorSelectionFibre subsetLabelFibre
    apply sum_eq_zero
    intro n hn
    simp [he n hn,Ne.symm hR]

/-- A fully merged smaller source becomes one isolated singleton at the dilated cutoff. -/
theorem mobiusDivisorSelectionFibre_mul_prime_of_all_small_primes_processed {N p : ℕ}
    (hp : p.Prime) (hNp : N<p) (P : Finset ℕ) (hpP : p ∉ P)
    (hP : mobiusDivisorSelectionPrimes N ⊆ P) :
    mobiusDivisorSelectionFibre (p*N) P {p} =
      -Real.sqrt p*(∑ n ∈ Icc 1 N,mobiusDivisorDilationChannel N n) := by
  rw [mobiusDivisorSelectionFibre_mul_prime_singleton hp hNp P hpP,
    mobiusDivisorSelectionFibre_of_all_source_primes_processed N P ∅ hP,if_pos rfl]

/-- Exact two-cutoff source update after processing the new prime. -/
theorem mobiusDivisorSelectionFibre_insert_mul_prime {N p : ℕ} (hp : p.Prime) (hNp : N<p)
    (P R : Finset ℕ) (hpP : p ∉ P) (hpR : p ∉ R) :
    mobiusDivisorSelectionFibre (p*N) (insert p P) R =
      mobiusDivisorSelectionFibre (p*N) P R-Real.sqrt p*mobiusDivisorSelectionFibre N P R := by
  rw [mobiusDivisorSelectionFibre_insert,if_neg hpR,
    mobiusDivisorSelectionFibre_mul_prime hp hNp P R hpP hpR]
  ring

/-- The head update retains the exact smaller-cutoff signed head. -/
theorem mobiusDivisorSelectionHead_insert_mul_prime {N p : ℕ} (hp : p.Prime) (hNp : N<p)
    (P : Finset ℕ) (hpP : p ∉ P) :
    mobiusDivisorSelectionFibre (p*N) (insert p P) ∅ =
      mobiusDivisorSelectionFibre (p*N) P ∅-Real.sqrt p*mobiusDivisorSelectionFibre N P ∅ :=
  mobiusDivisorSelectionFibre_insert_mul_prime hp hNp P ∅ hpP (by simp)

/-- The prime energy change is the complete mixed inner product of the two retained sources. -/
theorem mobiusDivisorSelectionEnergy_insert_mul_prime {N p : ℕ} (hp : p.Prime) (hNp : N<p)
    (hN : 2 ≤ N) (P : Finset ℕ) (hpP : p ∉ P) :
    mobiusDivisorSelectionEnergy (p*N) (insert p P)-mobiusDivisorSelectionEnergy (p*N) P =
      (-2*Real.sqrt p)*∑ R ∈ ((mobiusDivisorSelectionPrimes (p*N)).erase p).powerset,
        mobiusDivisorSelectionFibre (p*N) P R*mobiusDivisorSelectionFibre N P R := by
  let U := mobiusDivisorSelectionPrimes (p*N)
  have hpU : p ∈ U := by
    apply mem_filter.mpr
    exact ⟨mem_range.mpr (by nlinarith [hp.pos]),hp⟩
  have hsplit (f : Finset ℕ → ℝ) : (∑ R ∈ U.powerset,f R) =
      (∑ R ∈ (U.erase p).powerset,f R)+(∑ R ∈ (U.erase p).powerset,f (insert p R)) := by
    conv_lhs => rw [← insert_erase hpU]
    exact sum_powerset_insert (notMem_erase p U) f
  have hpR (R : Finset ℕ) (hR : R ∈ (U.erase p).powerset) : p ∉ R := by
    intro h
    have := (mem_powerset.mp hR) h
    simp at this
  have hz : (∑ R ∈ (U.erase p).powerset,(mobiusDivisorSelectionFibre (p*N) (insert p P) (insert p R))^2)=0 := by
    apply sum_eq_zero
    intro R hR
    rw [mobiusDivisorSelectionFibre_insert]
    simp
  have ha : (∑ R ∈ (U.erase p).powerset,(mobiusDivisorSelectionFibre (p*N) (insert p P) R)^2) =
      ∑ R ∈ (U.erase p).powerset,
        (mobiusDivisorSelectionFibre (p*N) P R-Real.sqrt p*mobiusDivisorSelectionFibre N P R)^2 := by
    apply sum_congr rfl
    intro R hR
    rw [mobiusDivisorSelectionFibre_insert_mul_prime hp hNp P R hpP (hpR R hR)]
  have hc : (∑ R ∈ (U.erase p).powerset,(mobiusDivisorSelectionFibre (p*N) P (insert p R))^2) =
      ∑ R ∈ (U.erase p).powerset,(-Real.sqrt p*mobiusDivisorSelectionFibre N P R)^2 := by
    apply sum_congr rfl
    intro R hR
    rw [mobiusDivisorSelectionFibre_mul_prime hp hNp P R hpP (hpR R hR)]
  change (∑ R ∈ U.powerset,(mobiusDivisorSelectionFibre (p*N) (insert p P) R)^2)-
    (∑ R ∈ U.powerset,(mobiusDivisorSelectionFibre (p*N) P R)^2)=_
  rw [hsplit,hsplit,hz,add_zero,ha,hc,← sum_add_distrib,← sum_sub_distrib,mul_sum]
  apply sum_congr rfl
  intro R hR
  ring

end RHTower
