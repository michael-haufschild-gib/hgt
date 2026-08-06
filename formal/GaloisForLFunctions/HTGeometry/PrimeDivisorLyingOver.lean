import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.GoingDown

/-!
# Prime divisors lie over prime divisors

For an integral extension of domains, incomparability forces a prime lying over a height-one prime
to have height one itself: a prime strictly below it contracts strictly below, hence contracts to
the zero ideal, hence is zero.  Combined with lying over, every prime divisor downstairs is
dominated by a prime divisor upstairs.

This is the surjectivity hypothesis of the eigenvolume ramification system, discharged: the map
sending a prime divisor to the prime divisor below it is onto.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
variable [Algebra R S] [Algebra.IsIntegral R S] [FaithfulSMul R S]

omit [IsDomain R] [IsDomain S] [Algebra.IsIntegral R S] in
theorem comap_bot_eq_bot : (⊥ : Ideal S).comap (algebraMap R S) = ⊥ := by
  rw [← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R S)

/-- **A prime lying over a prime divisor is a prime divisor.**  In an integral extension of
domains, a prime whose contraction has height one has height one. -/
theorem height_eq_one_of_comap_height_eq_one
    {p : Ideal S} [p.IsPrime] {q : Ideal R} [q.IsPrime]
    (hq : q.height = 1) (hpq : p.comap (algebraMap R S) = q) :
    p.height = 1 := by
  have hqbot : q ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hq
  have hpbot : p ≠ ⊥ := by
    intro h
    exact hqbot (by rw [← hpq, h, comap_bot_eq_bot])
  have hlow : 1 ≤ p.height := by
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    exact hpbot
  have hhigh : p.height ≤ ((1 : ℕ) : ℕ∞) := by
    rw [Ideal.height_le_iff]
    intro p' hp' hlt
    haveI := hp'
    have hcomap : p'.comap (algebraMap R S) < q := by
      rw [← hpq]
      exact Ideal.IsIntegral.comap_lt_comap hlt
    haveI : (p'.comap (algebraMap R S)).IsPrime := Ideal.IsPrime.comap _
    have hqle : q.height ≤ ((1 : ℕ) : ℕ∞) := by rw [hq, Nat.cast_one]
    have hlt1 : (p'.comap (algebraMap R S)).height < ((1 : ℕ) : ℕ∞) :=
      Ideal.height_le_iff.mp hqle _ inferInstance hcomap
    rw [Nat.cast_one] at hlt1
    have hzero : (p'.comap (algebraMap R S)).height = 0 := Order.lt_one_iff.mp hlt1
    have hcbot : p'.comap (algebraMap R S) = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp hzero
    have hp'bot : p' = ⊥ := Ideal.eq_bot_of_comap_eq_bot hcbot
    rw [hp'bot, Ideal.height_bot, Nat.cast_one]
    exact zero_lt_one
  rw [Nat.cast_one] at hhigh
  exact le_antisymm hhigh hlow

/-- **Every prime divisor downstairs is dominated.**  Lying over produces a prime divisor of the
extension contracting to a prescribed prime divisor of the base. -/
theorem exists_heightOne_comap_eq {q : Ideal R} [q.IsPrime] (hq : q.height = 1) :
    ∃ p : Ideal S, p.IsPrime ∧ p.height = 1 ∧ p.comap (algebraMap R S) = q := by
  obtain ⟨p, -, hp, hpq⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral q (⊥ : Ideal S)
      (by rw [comap_bot_eq_bot]; exact bot_le)
  haveI := hp
  exact ⟨p, hp, height_eq_one_of_comap_height_eq_one hq hpq, hpq⟩

/-- **The prime below a prime divisor is a prime divisor.**  Going down lifts a prime strictly
below the contraction to a prime strictly below, which must then be zero.  Together with the
converse this says that the map sending a prime divisor to the prime divisor below it is
well defined. -/
theorem under_height_eq_one_of_height_eq_one [Algebra.HasGoingDown R S]
    {p : Ideal S} [p.IsPrime] (hp : p.height = 1) :
    (Ideal.under R p).height = 1 := by
  haveI : (Ideal.under R p).IsPrime := Ideal.IsPrime.comap _
  haveI : p.LiesOver (Ideal.under R p) := ⟨rfl⟩
  have hpbot : p ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hp
  have hqbot : Ideal.under R p ≠ ⊥ := by
    intro h
    exact hpbot (Ideal.eq_bot_of_comap_eq_bot h)
  have hlow : 1 ≤ (Ideal.under R p).height := by
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    exact hqbot
  have hple : p.height ≤ ((1 : ℕ) : ℕ∞) := by rw [hp, Nat.cast_one]
  have hhigh : (Ideal.under R p).height ≤ ((1 : ℕ) : ℕ∞) := by
    rw [Ideal.height_le_iff]
    intro q' hq' hlt
    haveI := hq'
    obtain ⟨P, hPlt, hPprime, hPover⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt (p := q') (q := Ideal.under R p) p hlt
    haveI := hPprime
    haveI := hPover
    have hPlt1 : P.height < ((1 : ℕ) : ℕ∞) := Ideal.height_le_iff.mp hple _ hPprime hPlt
    rw [Nat.cast_one] at hPlt1
    have hPbot : P = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp (Order.lt_one_iff.mp hPlt1)
    have hq'bot : q' = ⊥ := by
      have hover : q' = Ideal.under R P := hPover.over
      rw [hover, hPbot]
      exact comap_bot_eq_bot
    rw [hq'bot, Ideal.height_bot, Nat.cast_one]
    exact zero_lt_one
  rw [Nat.cast_one] at hhigh
  exact le_antisymm hhigh hlow

end GaloisForLFunctions.HTGeometry
