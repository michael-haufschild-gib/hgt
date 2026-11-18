import GaloisForLFunctions.CountingHolography.Sections.ThePrimeLatticeOfFactorialEntropy

/-! # Prime coordinates of the joint factorial image

A pair of positive rational numbers is specified by its finitely supported
integer prime valuations. Below the horizon the entropy valuation at p is a
multiple of p, while a prime at the horizon ties the two valuations together.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset

/-- Logarithmic value of a finite prime-exponent vector. -/
def primeLogValue := Finsupp.linearCombination ℤ (fun p : Nat.Primes => Real.log (p:ℕ))

private abbrev Exponents := Nat.Primes →₀ ℤ

private def allowed (L : ℕ) : AddSubgroup (Exponents × Exponents) where
  carrier := {v | ∀ p : Nat.Primes,
    ((L < p → v.1 p=0 ∧ v.2 p=0) ∧ ((p:ℤ) ∣ v.2 p) ∧ ((p:ℕ)=L → v.2 p=(p:ℤ)*v.1 p))}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb p
    obtain ⟨h₁,h₂,h₃⟩ := ha p
    obtain ⟨h₄,h₅,h₆⟩ := hb p
    refine ⟨fun hp => ?_,dvd_add h₂ h₅,fun hp => ?_⟩
    · simp [(h₁ hp).1,(h₁ hp).2,(h₄ hp).1,(h₄ hp).2]
    · simp [h₃ hp,h₆ hp,mul_add]
  neg_mem' := by
    intro a ha p
    obtain ⟨h₁,h₂,h₃⟩ := ha p
    refine ⟨fun hp => ?_,dvd_neg.mpr h₂,fun hp => ?_⟩
    · simp [(h₁ hp).1,(h₁ hp).2]
    · simp [h₃ hp]

private def readPair : Exponents × Exponents →+ ℝ×ℝ :=
  primeLogValue.toAddMonoidHom.prodMap primeLogValue.toAddMonoidHom

private theorem readPair_injective : Function.Injective readPair := by
  have hi : Function.Injective primeLogValue := logPrime_linearIndependent_int
  intro a b h
  exact Prod.ext (hi (congrArg Prod.fst h)) (hi (congrArg Prod.snd h))

private theorem basis_allowed {L : ℕ} (p : Nat.Primes) {u v : ℤ} (hp : (p:ℕ) ≤ L)
    (hd : (p:ℤ) ∣ v) (ht : (p:ℕ)=L → v=(p:ℤ)*u) :
    ((Finsupp.single p u,Finsupp.single p v) : Exponents × Exponents) ∈ allowed L := by
  intro q
  by_cases he : p=q
  · subst q
    simpa only [Finsupp.single_eq_same] using
      And.intro (fun h => (hp.not_gt h).elim : L < p → u=0 ∧ v=0) (And.intro hd ht)
  · simp [Finsupp.single_apply,he]

private theorem readings_have_coordinates (L : ℕ) :
    factorialPrimeReadings L ⊆ (allowed L).map readPair := by
  have axis (p : Nat.Primes) (u v : ℤ) (hp : (p:ℕ) ≤ L) (hd : (p:ℤ) ∣ v)
      (ht : (p:ℕ)=L → v=(p:ℤ)*u) :
      ((u:ℝ)*Real.log (p:ℕ),(v:ℝ)*Real.log (p:ℕ)) ∈ (allowed L).map readPair := by
    refine ⟨_,basis_allowed p hp hd ht,?_⟩
    simp [readPair,primeLogValue,zsmul_eq_mul]
  rintro z (⟨p,hp,hlt,rfl | rfl⟩ | ⟨hL,rfl⟩)
  · simpa using axis ⟨p,hp⟩ 1 0 hlt.le (dvd_zero _) (fun h => (hlt.ne h).elim)
  · simpa using axis ⟨p,hp⟩ 0 (p:ℤ) hlt.le (dvd_refl _) (fun h => (hlt.ne h).elim)
  · simpa using axis ⟨L,hL⟩ 1 (L:ℤ) le_rfl (dvd_refl _) (fun _ => (mul_one _).symm)

private theorem sum_log_value {S : Finset Nat.Primes} (a : Exponents) (hS : a.support ⊆ S) :
    (∑ p ∈ S, (a p:ℝ)*Real.log (p:ℕ)) = primeLogValue a := by
  unfold primeLogValue
  rw [Finsupp.linearCombination_apply,Finsupp.sum]
  simp only [zsmul_eq_mul]
  exact (Finset.sum_subset hS fun p _ hp => by rw [Finsupp.notMem_support_iff.mp hp]; simp).symm

/-- A finite pair of prime-exponent vectors is attained exactly under the
divisibility conditions at the interior primes and the top-prime tie. -/
theorem factorialJointImage_iff_prime_coordinates {L : ℕ} (hL : 10 ≤ L) (a b : Nat.Primes →₀ ℤ) :
    (primeLogValue a,primeLogValue b) ∈ factorialJointImage L ↔
      ∀ p : Nat.Primes, (L < p → a p=0 ∧ b p=0) ∧
        ((p:ℤ) ∣ b p) ∧ ((p:ℕ)=L → b p=(p:ℤ)*a p) := by
  let J := factorialJointImage L
  have hc : factorialPrimeReadings L ⊆ J := by
    rw [show J=factorialJointImage L from rfl,factorialJointImage_eq_prime_readings hL]
    exact AddSubgroup.subset_closure
  constructor
  · intro h
    rw [factorialJointImage_eq_prime_readings hL] at h
    have hz := ((allowed L).map readPair).closure_le.mpr (readings_have_coordinates L) h
    obtain ⟨y,hy,he⟩ := hz
    have hpair : y=(a,b) := readPair_injective he
    exact hpair ▸ hy
  intro hab
  let S := a.support ∪ b.support
  have hp (p : Nat.Primes) :
      ((a p:ℝ)*Real.log (p:ℕ),(b p:ℝ)*Real.log (p:ℕ)) ∈ J := by
    obtain ⟨hzero,⟨k,hk⟩,htop⟩ := hab p
    rcases lt_trichotomy (p:ℕ) L with h | h | h
    · have h₁ := J.zsmul_mem (hc (Or.inl ⟨p,p.property,h,Or.inl rfl⟩)) (a p)
      have h₂ := J.zsmul_mem (hc (Or.inl ⟨p,p.property,h,Or.inr rfl⟩)) k
      simpa [hk,Prod.smul_mk,Prod.mk_add_mk,zsmul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using
        J.add_mem h₁ h₂
    · have hpr : L.Prime := h ▸ p.property
      have h₁ := J.zsmul_mem (hc (Or.inr ⟨hpr,rfl⟩)) (a p)
      simpa [← h,htop h,Prod.smul_mk,zsmul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using h₁
    · rw [(hzero h).1,(hzero h).2,Int.cast_zero,zero_mul]
      exact J.zero_mem
  have hsum := J.sum_mem (t := S) (f := fun p => ((a p:ℝ)*Real.log (p:ℕ),(b p:ℝ)*Real.log (p:ℕ)))
    fun p _ => hp p
  convert hsum using 1
  exact Prod.ext (by rw [Prod.fst_sum]; exact (sum_log_value a subset_union_left).symm)
    (by rw [Prod.snd_sum]; exact (sum_log_value b subset_union_right).symm)

#print axioms factorialJointImage_iff_prime_coordinates

end GaloisForLFunctions.CountingHolography.Sections
