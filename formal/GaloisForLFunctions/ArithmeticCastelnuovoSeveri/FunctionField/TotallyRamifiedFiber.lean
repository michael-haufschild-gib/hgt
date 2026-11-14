import Mathlib.NumberTheory.RamificationInertia.Basic

/-!
# A fiber consisting of one totally ramified prime

For a finite extension of Dedekind domains, if every prime above a fixed
base place has ramification index equal to the full field degree, then
there is exactly one such prime and its residue degree is one. This is
the positivity consequence of the fundamental identity `Σ e f = [L:K]`.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain
variable {A B : Type*} [CommRing A] [IsDedekindDomain A]
  [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
variable (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
  [IsScalarTower A B L] [IsScalarTower A K L] [FiniteDimensional K L]

/-- Full ramification at every prime forces a singleton fiber with residue degree one. -/
theorem singleton_primesOver_of_full_ramification (v : HeightOneSpectrum A)
    (hfull : ∀ (P : Ideal B), P.IsPrime → P.LiesOver v.asIdeal →
      v.asIdeal.ramificationIdx' P = Module.finrank K L) :
    ∃ P : Ideal B, IsDedekindDomain.primesOverFinset v.asIdeal B = {P} ∧ v.asIdeal.inertiaDeg' P = 1 := by
  classical
  letI : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (algebraMap_injective_of_field_isFractionRing A B K L)
  letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  let T := IsDedekindDomain.primesOverFinset v.asIdeal B
  let f : Ideal B → ℕ := v.asIdeal.inertiaDeg'
  have hsum : Module.finrank K L * ∑ P ∈ T, f P = Module.finrank K L := by
    rw [Finset.mul_sum]
    have h := Ideal.sum_ramification_inertia B K L v.ne_bot
    refine (Finset.sum_congr rfl fun P hP => ?_).trans h
    obtain ⟨hprime, hover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot B).mp hP
    rw [hfull P hprime hover]
  have hsum1 : ∑ P ∈ T, f P = 1 := by
    apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := K) (M := L))
    simpa only [mul_one] using hsum
  have hcard : T.card ≤ 1 := by
    suffices T.card ≤ ∑ P ∈ T, f P by exact this.trans_eq hsum1
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro P hP
    obtain ⟨_, hover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot B).mp hP
    letI := hover
    exact Nat.pos_of_ne_zero (Ideal.inertiaDeg'_ne_zero v.asIdeal P)
  have hnonempty : T.Nonempty := by
    by_contra hn
    have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.sum_empty] at hsum1
    omega
  obtain ⟨P, hP⟩ := Finset.card_eq_one.mp
    (Nat.le_antisymm hcard (Finset.card_pos.mpr hnonempty))
  exact ⟨P, hP, by simpa only [hP, Finset.sum_singleton] using hsum1⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
