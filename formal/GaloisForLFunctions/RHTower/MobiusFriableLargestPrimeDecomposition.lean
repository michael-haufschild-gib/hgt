import GaloisForLFunctions.RHTower.Sieve.SmoothSum

/-!
# Exact largest-prime decomposition of the Mertens function

Below the first integer seam the friable range is wide enough to make the largest-prime
factorisation *exact*.  If `X < Y²` then an integer `n ≤ X` has at most one prime factor exceeding
`Y`, and that prime divides `n` exactly once — two of them, or one squared, would already push `n`
past `Y²`.  So the pairs `(p, m)` with `Y < p ≤ X` prime and `1 ≤ m ≤ X/p` biject with the
non-friable integers of `[1, X]`, and `μ(pm) = -μ(m)` because `p ∤ m`.

Hence, with no analytic input at all,

`M(X) = M_fri(X, Y) - ∑_{Y < p ≤ X} M(X/p)`.

Each `m` occurring here is smaller than `Y`, so the inner sums are themselves complete Mertens
sums; no friability restriction survives on the right.  This is the identity separating the
zero-large-prime charge from the one-large-prime charge.
-/

namespace RHTower

open Finset Nat
open scoped ArithmeticFunction.Moebius

/-- The Mertens function `M(X) = ∑_{n ≤ X} μ(n)`. -/
def mertensM (X : ℕ) : ℤ := ∑ n ∈ Finset.Icc 1 X, μ n

/-- The friable Mertens function `M_fri(X,Y) = ∑_{n ≤ X, P⁺(n) ≤ Y} μ(n)`. -/
def mertensFriable (X Y : ℕ) : ℤ := ∑ n ∈ Sieve.smoothUpTo (Nat.primesLE Y) X, μ n

/-- The primes of the window `(Y, X]`. -/
def largePrimes (X Y : ℕ) : Finset ℕ := {p ∈ Nat.primesLE X | Y < p}

theorem mem_largePrimes {X Y p : ℕ} : p ∈ largePrimes X Y ↔ (p ≤ X ∧ p.Prime) ∧ Y < p := by
  rw [largePrimes, Finset.mem_filter, Nat.mem_primesLE]

/-- Friability of `n` is exactly the bound on its prime factors. -/
theorem mem_smoothUpTo_iff {X Y n : ℕ} :
    n ∈ Sieve.smoothUpTo (Nat.primesLE Y) X ↔ (1 ≤ n ∧ n ≤ X) ∧ ∀ p ∈ n.primeFactors, p ≤ Y := by
  rw [Sieve.mem_smoothUpTo]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun p hp => (Nat.mem_primesLE.1 (h2 hp)).1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun p hp => Nat.mem_primesLE.2 ⟨h2 p hp, Nat.prime_of_mem_primeFactors hp⟩⟩

/-- Below the first seam an integer has at most one prime factor above the cut, to the first
power. -/
theorem eq_of_two_large_primes {X Y n p q : ℕ} (hn : n ≤ X) (hXY : X < Y * Y)
    (hp : p ∈ n.primeFactors) (hq : q ∈ n.primeFactors) (hpY : Y < p) (hqY : Y < q) : p = q := by
  by_contra hne
  have hn0 : n ≠ 0 := by
    intro h
    rw [h] at hp
    simp at hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hdvd : p * q ∣ n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hpprime hqprime).2 hne)
      (Nat.dvd_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hq)
  have hle : p * q ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
  have : Y * Y < p * q := Nat.mul_lt_mul_of_lt_of_lt hpY hqY
  omega

/-- **Exact largest-prime decomposition.**  For `X < Y²` the Mertens function splits into its
friable part and the one-large-prime part, with no error. -/
theorem mertensM_eq_mertensFriable_sub (X Y : ℕ) (hXY : X < Y * Y) :
    mertensM X = mertensFriable X Y - ∑ p ∈ largePrimes X Y, mertensM (X / p) := by
  classical
  set A : Finset ℕ := Sieve.smoothUpTo (Nat.primesLE Y) X with hA
  have hAfilter : A = {n ∈ Finset.Icc 1 X | ∀ p ∈ n.primeFactors, p ≤ Y} := by
    ext n
    rw [hA, mem_smoothUpTo_iff, Finset.mem_filter, Finset.mem_Icc]
  set B : Finset ℕ := {n ∈ Finset.Icc 1 X | ¬ ∀ p ∈ n.primeFactors, p ≤ Y} with hB
  have hsplit : mertensM X = mertensFriable X Y + ∑ n ∈ B, μ n := by
    rw [mertensM, mertensFriable, ← hA, hAfilter, hB]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  set S : Finset ((_ : ℕ) × ℕ) :=
    (largePrimes X Y).sigma fun p => Finset.Icc 1 (X / p) with hS
  have hkey : ∑ n ∈ B, μ n = ∑ x ∈ S, (-(μ x.2) : ℤ) := by
    refine (Finset.sum_bij (fun x _ => x.1 * x.2) ?_ ?_ ?_ ?_).symm
    · rintro ⟨p, m⟩ hx
      simp only [hS, Finset.mem_sigma] at hx
      obtain ⟨hp, hm⟩ := hx
      obtain ⟨⟨hpX, hpprime⟩, hpY⟩ := mem_largePrimes.1 hp
      obtain ⟨hm1, hmle⟩ := Finset.mem_Icc.1 hm
      have hppos : 0 < p := hpprime.pos
      have hle : p * m ≤ X := by
        calc p * m ≤ p * (X / p) := Nat.mul_le_mul_left p hmle
          _ ≤ X := Nat.mul_div_le X p
      have hpos : 1 ≤ p * m :=
        Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hpprime.pos.ne' (by omega))
      have hpmem : p ∈ (p * m).primeFactors :=
        Nat.mem_primeFactors.2 ⟨hpprime, Dvd.intro m rfl, by omega⟩
      refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hpos, hle⟩, ?_⟩
      intro hcon
      exact absurd (hcon p hpmem) (by omega)
    · rintro ⟨p, m⟩ hx ⟨p', m'⟩ hy hxy
      simp only [hS, Finset.mem_sigma] at hx hy
      obtain ⟨hp, hm⟩ := hx
      obtain ⟨hp', hm'⟩ := hy
      obtain ⟨⟨hpX, hpprime⟩, hpY⟩ := mem_largePrimes.1 hp
      obtain ⟨⟨hpX', hpprime'⟩, hpY'⟩ := mem_largePrimes.1 hp'
      obtain ⟨hm1, hmle⟩ := Finset.mem_Icc.1 hm
      obtain ⟨hm1', hmle'⟩ := Finset.mem_Icc.1 hm'
      have hle : p * m ≤ X := by
        calc p * m ≤ p * (X / p) := Nat.mul_le_mul_left p hmle
          _ ≤ X := Nat.mul_div_le X p
      have hn0 : p * m ≠ 0 := Nat.mul_ne_zero hpprime.pos.ne' (by omega)
      have hpmem : p ∈ (p * m).primeFactors :=
        Nat.mem_primeFactors.2 ⟨hpprime, Dvd.intro m rfl, hn0⟩
      have hp'mem : p' ∈ (p * m).primeFactors := by
        rw [hxy]
        exact Nat.mem_primeFactors.2 ⟨hpprime', Dvd.intro m' rfl, by rw [← hxy]; exact hn0⟩
      have hpp : p = p' := eq_of_two_large_primes hle hXY hpmem hp'mem hpY hpY'
      subst hpp
      have hmm : m = m' := Nat.eq_of_mul_eq_mul_left hpprime.pos hxy
      subst hmm
      rfl
    · intro n hn
      obtain ⟨hmem, hnot⟩ := Finset.mem_filter.1 hn
      obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.1 hmem
      obtain ⟨p, hp, hpY⟩ : ∃ p ∈ n.primeFactors, Y < p := by
        by_contra hcon
        exact hnot fun p hp => not_lt.1 fun h => hcon ⟨p, hp, h⟩
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      have hpn : p ≤ n := Nat.le_of_dvd (by omega) hpdvd
      have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpdvd
      refine ⟨⟨p, n / p⟩, ?_, hmul⟩
      simp only [hS, Finset.mem_sigma]
      refine ⟨mem_largePrimes.2 ⟨⟨by omega, hpprime⟩, by omega⟩, Finset.mem_Icc.2 ⟨?_, ?_⟩⟩
      · have : 0 < n / p := Nat.div_pos hpn hpprime.pos
        omega
      · exact Nat.div_le_div_right hnX
    · rintro ⟨p, m⟩ hx
      simp only [hS, Finset.mem_sigma] at hx
      obtain ⟨hp, hm⟩ := hx
      obtain ⟨⟨hpX, hpprime⟩, hpY⟩ := mem_largePrimes.1 hp
      obtain ⟨hm1, hmle⟩ := Finset.mem_Icc.1 hm
      have hle : p * m ≤ X := by
        calc p * m ≤ p * (X / p) := Nat.mul_le_mul_left p hmle
          _ ≤ X := Nat.mul_div_le X p
      have hnotdvd : ¬ p ∣ m := by
        intro hdvd
        obtain ⟨c, rfl⟩ := hdvd
        have hc1 : 1 ≤ c := by
          rcases Nat.eq_zero_or_pos c with rfl | h
          · simp at hm1
          · exact h
        have : p * p ≤ p * (p * c) := by
          refine Nat.mul_le_mul_left p ?_
          calc p = p * 1 := by ring
            _ ≤ p * c := Nat.mul_le_mul_left p hc1
        have hYp : Y * Y < p * p := Nat.mul_lt_mul_of_lt_of_lt hpY hpY
        omega
      have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hpprime).2 hnotdvd
      have hmulmu : μ (p * m) = μ p * μ m :=
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
      have hmup : μ p = -1 := ArithmeticFunction.moebius_apply_prime hpprime
      show (-(μ m) : ℤ) = μ (p * m)
      rw [hmulmu, hmup]
      ring
  have hsigma : ∑ x ∈ S, (-(μ x.2) : ℤ)
      = - ∑ p ∈ largePrimes X Y, mertensM (X / p) := by
    rw [hS, Finset.sum_sigma]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [mertensM, ← Finset.sum_neg_distrib]
  rw [hsplit, hkey, hsigma]
  ring

/-- The one-large-prime sector: the Möbius sum over the non-friable integers of `[1, X]`. -/
def mertensLargePrimeSector (X Y : ℕ) : ℤ :=
  ∑ n ∈ {n ∈ Finset.Icc 1 X | ¬ ∀ p ∈ n.primeFactors, p ≤ Y}, μ n

/-- The two sectors partition the Mertens function, for every cut. -/
theorem mertensM_eq_add_sector (X Y : ℕ) :
    mertensM X = mertensFriable X Y + mertensLargePrimeSector X Y := by
  classical
  have hAfilter : Sieve.smoothUpTo (Nat.primesLE Y) X
      = {n ∈ Finset.Icc 1 X | ∀ p ∈ n.primeFactors, p ≤ Y} := by
    ext n
    rw [mem_smoothUpTo_iff, Finset.mem_filter, Finset.mem_Icc]
  rw [mertensM, mertensFriable, mertensLargePrimeSector, hAfilter]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- **The one-large-prime sector is a sum of complete Mertens functions.** -/
theorem mertensLargePrimeSector_eq (X Y : ℕ) (hXY : X < Y * Y) :
    mertensLargePrimeSector X Y = - ∑ p ∈ largePrimes X Y, mertensM (X / p) := by
  have h1 := mertensM_eq_add_sector X Y
  have h2 := mertensM_eq_mertensFriable_sub X Y hXY
  linarith

/-- Below the seam the friable range is wide: `X/p < Y` for every large prime `p`. -/
theorem div_lt_of_mem_largePrimes {X Y p : ℕ} (hXY : X < Y * Y) (hp : p ∈ largePrimes X Y) :
    X / p < Y := by
  obtain ⟨⟨hpX, hpprime⟩, hpY⟩ := mem_largePrimes.1 hp
  by_contra hcon
  have hYp : Y ≤ X / p := by omega
  have h1 : X / p * p ≤ X := Nat.div_mul_le_self X p
  have h2 : Y * (Y + 1) ≤ X / p * p := Nat.mul_le_mul hYp (by omega)
  have h3 : Y * Y ≤ Y * (Y + 1) := Nat.mul_le_mul_left Y (by omega)
  omega

/-- Hence the inner sums carry no friability restriction. -/
theorem mertensFriable_div_eq {X Y p : ℕ} (hXY : X < Y * Y) (hp : p ∈ largePrimes X Y) :
    mertensFriable (X / p) Y = mertensM (X / p) := by
  classical
  have hlt := div_lt_of_mem_largePrimes hXY hp
  have hset : Sieve.smoothUpTo (Nat.primesLE Y) (X / p) = Finset.Icc 1 (X / p) := by
    ext n
    rw [mem_smoothUpTo_iff, Finset.mem_Icc]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      intro q hq
      have hqn : q ≤ n := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hq)
      omega
  rw [mertensFriable, mertensM, hset]

/-- **Card equation (20).**  The exact largest-prime decomposition with both sides friable. -/
theorem mertensM_eq_mertensFriable_sub_friable (X Y : ℕ) (hXY : X < Y * Y) :
    mertensM X = mertensFriable X Y - ∑ p ∈ largePrimes X Y, mertensFriable (X / p) Y := by
  rw [mertensM_eq_mertensFriable_sub X Y hXY]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro p hp
  exact (mertensFriable_div_eq hXY hp).symm

end RHTower
