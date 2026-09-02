import GaloisForLFunctions.RHTower.Sieve.BivariateMultiplicative

/-!
# Integral Witt ghosts: prime congruence and infinite-tail obstruction

The divisor-sum ghost sequence satisfies the exact prime-extension congruence. Consequently every
prime larger than the first nonzero ghost magnitude carries another nonzero ghost.
-/

namespace RHTower

noncomputable section

open scoped BigOperators

def integralWittGhost (c : ℕ → ℤ) (m : ℕ) : ℤ :=
  ∑ d ∈ m.divisors, (d : ℤ) * c d

/-- IWG-1: adjoining a coprime prime preserves the integral ghost modulo that prime. -/
theorem integralWittGhost_primeExtension
    (c : ℕ → ℤ) {m p : ℕ} (hp : p.Prime) (hpm : ¬p ∣ m) :
    Int.ModEq (p : ℤ) (integralWittGhost c (m * p)) (integralWittGhost c m) := by
  have hm0 : m ≠ 0 := by
    intro hm
    exact hpm (by simp [hm])
  have hcop : m.Coprime p := (hp.coprime_iff_not_dvd.mpr hpm).symm
  let e := RHTower.Sieve.coprimeDivisorsEquiv hm0 hp.ne_zero hcop
  have hsplit : integralWittGhost c (m * p) =
      ∑ a : {d // d ∈ m.divisors},
        ∑ b : {d // d ∈ p.divisors},
          ((a.1 * b.1 : ℕ) : ℤ) * c (a.1 * b.1) := by
    rw [integralWittGhost]
    have he := Fintype.sum_equiv e
      (fun ab : {d // d ∈ m.divisors} × {d // d ∈ p.divisors} =>
        ((ab.1.1 * ab.2.1 : ℕ) : ℤ) * c (ab.1.1 * ab.2.1))
      (fun z : {d // d ∈ (m * p).divisors} => (z.1 : ℤ) * c z.1)
      (fun ab => rfl)
    calc
      (∑ d ∈ (m * p).divisors, (d : ℤ) * c d) =
          ∑ z : {d // d ∈ (m * p).divisors}, (z.1 : ℤ) * c z.1 :=
        (Finset.sum_attach _ _).symm
      _ = ∑ ab : {d // d ∈ m.divisors} × {d // d ∈ p.divisors},
          ((ab.1.1 * ab.2.1 : ℕ) : ℤ) * c (ab.1.1 * ab.2.1) := he.symm
      _ = _ := Fintype.sum_prod_type _
  have hpSum (a : {d // d ∈ m.divisors}) :
      (∑ b : {d // d ∈ p.divisors},
          ((a.1 * b.1 : ℕ) : ℤ) * c (a.1 * b.1)) =
        (a.1 : ℤ) * c a.1 + (p : ℤ) * ((a.1 : ℤ) * c (a.1 * p)) := by
    rw [← Finset.sum_subtype p.divisors (fun _ => Iff.rfl)
      (fun b => ((a.1 * b : ℕ) : ℤ) * c (a.1 * b))]
    rw [show p.divisors = {1, p} from hp.divisors]
    rw [Finset.sum_insert (by simpa using hp.ne_one.symm), Finset.sum_singleton]
    simp only [Nat.mul_one]
    push_cast
    ring
  have hdecomp : integralWittGhost c (m * p) =
      integralWittGhost c m +
        (p : ℤ) * ∑ a : {d // d ∈ m.divisors}, (a.1 : ℤ) * c (a.1 * p) := by
    rw [hsplit]
    simp_rw [hpSum]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [integralWittGhost]
    rw [Finset.sum_subtype m.divisors (fun _ => Iff.rfl)
      (fun d => (d : ℤ) * c d)]
  rw [hdecomp, Int.modEq_iff_dvd]
  refine ⟨-(∑ a : {d // d ∈ m.divisors}, (a.1 : ℤ) * c (a.1 * p)), ?_⟩
  ring

/-- IWG-3: a nonzero first ghost forces every sufficiently large prime ghost to be nonzero. -/
theorem integralWittGhost_prime_ne_zero_of_natAbs_lt
    (c : ℕ → ℤ) (hg : integralWittGhost c 1 ≠ 0)
    {p : ℕ} (hp : p.Prime)
    (hlarge : (integralWittGhost c 1).natAbs < p) :
    integralWittGhost c p ≠ 0 := by
  intro hzero
  have hmod := integralWittGhost_primeExtension c (m := 1) hp hp.not_dvd_one
  simp only [one_mul] at hmod
  rw [hzero] at hmod
  have hdvd : (p : ℤ) ∣ integralWittGhost c 1 := by
    rw [Int.modEq_iff_dvd] at hmod
    simpa using hmod
  have hle := Int.natAbs_le_of_dvd_ne_zero hdvd hg
  simp only [Int.natAbs_natCast] at hle
  omega

end

end RHTower
