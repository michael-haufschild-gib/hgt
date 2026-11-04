import GaloisForLFunctions.BezoutValuationIncidence.Sieve.ProgressionCounts
import GaloisForLFunctions.RHTower.Sieve.IntervalSelberg

/-!
# The reciprocal Selberg sieve on an arithmetic progression

Restricting an interval to one residue class divides its total mass by the
modulus. Sieving by a coprime squarefree product preserves reciprocal local
density and unit remainders, by the Chinese remainder theorem.
-/

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

open Finset Nat BoundingSieve
open _root_.RHTower.Sieve

/-- Unit weights on one residue class, with reciprocal sieve density. -/
def progressionSieve (A B p a P : ℕ) (hP : Squarefree P) : BoundingSieve where
  support := {n ∈ Ioc A B | n ≡ a [MOD p]}
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := ((B : ℝ) - A) / p
  nu := invNat
  nu_mult := isMultiplicative_invNat
  nu_pos_of_prime := fun q hq _ => by
    rw [invNat_apply hq.ne_zero]
    have : (0 : ℝ) < q := by exact_mod_cast hq.pos
    positivity
  nu_lt_one_of_prime := fun q hq _ => by
    rw [invNat_apply hq.ne_zero]
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
    rw [inv_lt_one_iff₀]
    right
    linarith only [hq2]

/-- The sieve multiple sum is the exact intersection count. -/
theorem progressionSieve_multSum (A B p a P d : ℕ) (hP : Squarefree P) :
    (progressionSieve A B p a P hP).multSum d =
      ((#{n ∈ Ioc A B | n ≡ a [MOD p] ∧ d ∣ n} : ℕ) : ℝ) := by
  change (∑ n ∈ {n ∈ Ioc A B | n ≡ a [MOD p]}, if d ∣ n then (1 : ℝ) else 0) = _
  rw [← natCast_card_filter, filter_filter]

/-- The sifted sum counts the progression members avoiding every sieve prime. -/
theorem progressionSieve_siftedSum (A B p a P : ℕ) (hP : Squarefree P) :
    (progressionSieve A B p a P hP).siftedSum =
      ((#{n ∈ Ioc A B | n ≡ a [MOD p] ∧ P.Coprime n} : ℕ) : ℝ) := by
  change (∑ n ∈ {n ∈ Ioc A B | n ≡ a [MOD p]},
    if P.Coprime n then (1 : ℝ) else 0) = _
  rw [← natCast_card_filter, filter_filter]

/-- Every reciprocal-density remainder has absolute value at most one. -/
theorem abs_progressionSieve_rem_le {A B p a P d : ℕ} (hP : Squarefree P)
    (hAB : A ≤ B) (hp : 0 < p) (hpP : p.Coprime P) (hdP : d ∣ P) :
    |(progressionSieve A B p a P hP).rem d| ≤ 1 := by
  have hd0 : d ≠ 0 := by
    intro hd
    exact hP.ne_zero (Nat.eq_zero_of_zero_dvd (hd ▸ hdP))
  have hd : 0 < d := Nat.pos_of_ne_zero hd0
  have hcount := abs_card_progression_dvd_Ioc_sub_lt_one (a := a)
    hAB hp hd (Nat.Coprime.of_dvd_right hdP hpP)
  have he : (progressionSieve A B p a P hP).rem d =
      ((#{n ∈ Ioc A B | n ≡ a [MOD p] ∧ d ∣ n} : ℕ) : ℝ) -
        ((B : ℝ) - A) / ((p : ℝ) * d) := by
    rw [rem, progressionSieve_multSum]
    change _ - invNat d * (((B : ℝ) - A) / p) = _
    rw [invNat_apply hd0]
    ring
  rw [he]
  exact hcount.le

/-- The reciprocal Selberg terms dominate the ordinary reciprocal mass. -/
theorem inv_le_progressionSieve_selbergTerms {A B p a P d : ℕ}
    (hP : Squarefree P) (hdP : d ∣ P) :
    (d : ℝ)⁻¹ ≤ (progressionSieve A B p a P hP).selbergTerms d := by
  have hdsq : Squarefree d := hP.squarefree_of_dvd hdP
  change (d : ℝ)⁻¹ ≤ (intervalSieve 0 0 d).selbergTerms d
  exact inv_le_intervalSieve_selbergTerms 0 0 d (dvd_primorial_of_squarefree hdsq le_rfl)

/-- The truncated Selberg inequality retains only unit remainder costs. -/
theorem card_progression_coprime_Ioc_le_selberg {A B p a P Y : ℕ}
    (hP : Squarefree P) (hAB : A ≤ B) (hp : 0 < p)
    (hpP : p.Coprime P) (hY : 1 ≤ Y) :
    ((#{n ∈ Ioc A B | n ≡ a [MOD p] ∧ P.Coprime n} : ℕ) : ℝ) ≤
      (((B : ℝ) - A) / p) / selbergMassLE (progressionSieve A B p a P hP) Y +
        ∑ d ∈ P.divisors, |lambdaSquared (selbergTruncWeight (progressionSieve A B p a P hP) Y) d| := by
  let s := progressionSieve A B p a P hP
  have hbase := siftedSum_le_selbergTrunc s hY
  have herr : s.errSum (lambdaSquared (selbergTruncWeight s Y)) ≤
      ∑ d ∈ P.divisors, |lambdaSquared (selbergTruncWeight s Y) d| := by
    change (∑ d ∈ P.divisors, |lambdaSquared (selbergTruncWeight s Y) d| * |s.rem d|) ≤ _
    apply sum_le_sum
    intro d hd
    exact (mul_le_mul_of_nonneg_left
      (abs_progressionSieve_rem_le hP hAB hp hpP (Nat.dvd_of_mem_divisors hd))
      (abs_nonneg _)).trans_eq (mul_one _)
  rw [progressionSieve_siftedSum] at hbase
  exact hbase.trans (add_le_add le_rfl herr)

#print axioms abs_progressionSieve_rem_le
#print axioms card_progression_coprime_Ioc_le_selberg

end GaloisForLFunctions.BezoutValuationIncidence
