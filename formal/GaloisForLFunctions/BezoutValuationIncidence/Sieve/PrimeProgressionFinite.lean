import GaloisForLFunctions.BezoutValuationIncidence.Sieve.ProgressionSieve
import GaloisForLFunctions.BezoutValuationIncidence.Sieve.PrimeDeletedMass
import GaloisForLFunctions.BezoutValuationIncidence.Sieve.TruncationError

/-! # A finite prime-progression bound with an explicit sieve level

Delete the progression modulus from the sieving primes. Unit CRT remainders
and the logarithmic squarefree mass give a prime count with a polynomial
truncation error, uniformly in the residue class.
-/

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

open Finset Nat BoundingSieve
open _root_.RHTower.Sieve

/-- A prime above the sieve level avoids the deleted primorial. -/
theorem primeDeletedPrimorial_coprime_prime {p Y n : ℕ}
    (hn : n.Prime) (hYn : Y < n) :
    (primeDeletedPrimorial p Y).Coprime n := by
  apply Nat.Coprime.prod_left
  intro q hq
  have hqY := Nat.mem_primesLE.mp (mem_filter.mp hq).1
  exact (Nat.coprime_primes hqY.2 hn).mpr (_root_.ne_of_lt (hqY.1.trans_lt hYn))

/-- The progression sieve retains a fixed logarithmic mass. -/
theorem progressionSieve_primeDeleted_mass_lower {A B p a Y : ℕ}
    (hp : p.Prime) (hp8 : 8 ≤ p) (hY : 1 ≤ Y) (hlog : 14 ≤ Real.log Y) :
    Real.log Y / 16 ≤
      selbergMassLE (progressionSieve A B p a (primeDeletedPrimorial p Y)
        (primeDeletedPrimorial_squarefree p Y)) Y := by
  have hmass := primeDeletedPrimorial_reciprocal_mass_lower hp hp8 hY
  have hterms : (∑ d ∈ (primeDeletedPrimorial p Y).divisors.filter (fun d => d ≤ Y),
      1 / (d : ℝ)) ≤
      selbergMassLE (progressionSieve A B p a (primeDeletedPrimorial p Y)
        (primeDeletedPrimorial_squarefree p Y)) Y := by
    apply sum_le_sum
    intro d hd
    simpa only [one_div] using inv_le_progressionSieve_selbergTerms
      (A := A) (B := B) (p := p) (a := a) (primeDeletedPrimorial_squarefree p Y)
      (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)
  linarith only [hmass, hterms, hlog]

/-- A prime progression has the reciprocal-density main bound and a sixth-power sieve error. -/
theorem card_prime_progression_le_truncation {p X Y a : ℕ}
    (hp : p.Prime) (hp8 : 8 ≤ p) (hY : 1 ≤ Y) (hlog : 14 ≤ Real.log Y) :
    ((#{n ∈ Icc 1 X | n.Prime ∧ n ≡ a [MOD p]} : ℕ) : ℝ) ≤
      (Y : ℝ) + 16 * ((X : ℝ) / p) / Real.log Y + (Y : ℝ) ^ 6 := by
  classical
  let P := primeDeletedPrimorial p Y
  let s := progressionSieve 0 X p a P (primeDeletedPrimorial_squarefree p Y)
  let T := {n ∈ Ioc 0 X | n ≡ a [MOD p] ∧ P.Coprime n}
  have hsub : {n ∈ Icc 1 X | n.Prime ∧ n ≡ a [MOD p]} ⊆ Icc 1 Y ∪ T := by
    intro n hn
    obtain ⟨hnX, hnprime, hnmod⟩ := mem_filter.mp hn
    by_cases hnY : n ≤ Y
    · exact mem_union_left _ (mem_Icc.mpr ⟨(mem_Icc.mp hnX).1, hnY⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_Ioc.mpr
        ⟨(mem_Icc.mp hnX).1, (mem_Icc.mp hnX).2⟩,
        hnmod, primeDeletedPrimorial_coprime_prime hnprime (by omega)⟩)
  have hcount : ((#{n ∈ Icc 1 X | n.Prime ∧ n ≡ a [MOD p]} : ℕ) : ℝ) ≤
      (Y : ℝ) + T.card := by
    have h := (card_le_card hsub).trans (card_union_le _ _)
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at h
    exact_mod_cast h
  have hs := card_progression_coprime_Ioc_le_selberg
    (A := 0) (B := X) (a := a) (primeDeletedPrimorial_squarefree p Y)
    (Nat.zero_le X) hp.pos (primeDeletedPrimorial_coprime hp Y) hY
  have herr := sum_abs_selbergTruncSquared_le_pow_six s hY
  have hrough : (T.card : ℝ) ≤ ((X : ℝ) / p) / selbergMassLE s Y + (Y : ℝ) ^ 6 := by
    exact hs.trans (add_le_add (by simp only [Nat.cast_zero, sub_zero, s, P]; exact le_rfl) herr)
  have hmass := progressionSieve_primeDeleted_mass_lower
    (A := 0) (B := X) (a := a) hp hp8 hY hlog
  have hmain : ((X : ℝ) / p) / selbergMassLE s Y ≤
      16 * ((X : ℝ) / p) / Real.log Y := by
    refine (div_le_div_of_nonneg_left (by positivity)
      (by linarith only [hlog] : 0 < Real.log Y / 16) hmass).trans_eq ?_
    ring
  linarith only [hcount, hrough, hmain]

#print axioms card_prime_progression_le_truncation

end GaloisForLFunctions.BezoutValuationIncidence
