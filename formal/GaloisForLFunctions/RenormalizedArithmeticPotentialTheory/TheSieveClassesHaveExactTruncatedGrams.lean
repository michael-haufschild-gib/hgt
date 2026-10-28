import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFiniteSieveHasTheTowerFinitePart
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFiniteSieveUnitGramHasTwoHorizons

/-!
# Exact class Grams with independent cutoffs

Truncation acts on the unit coordinate after division by the supported order.
Same-class Grams are scaled unit Grams; distinct classes couple at the smaller
of their two decimated cutoffs. Polar coordinates and ordinary squared norms
follow from disjointness of the supported-order classes.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.HTGeometry
  GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.ArithmeticIntersectionTheory

/-- A class pole vector cut off at an independent horizon. -/
def sieveTruncPole (Q : Finset Nat.Primes) (d A n : ℕ) : ℝ :=
  if n ≤ A then sieveClassPole Q d n else 0

theorem sum_sieveTruncPole_mul {A N : ℕ} (hAN : A ≤ N)
    (Q : Finset Nat.Primes) (d : ℕ) (F : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, sieveTruncPole Q d A n * F n =
      ∑ n ∈ Icc 1 A, sieveClassPole Q d n * F n := by
  rw [← sum_truncate hAN]
  exact sum_congr rfl fun n _ => by
    simp only [sieveTruncPole]
    split_ifs <;> ring

/-- Each cutoff decimates independently in supported/unit coordinates. -/
theorem primeBilinear_sieveTruncPole_eq_sum {d e A B N : ℕ}
    (hd : 0 < d) (he : 0 < e) (hAN : A ≤ N) (hBN : B ≤ N)
    (Q : Finset Nat.Primes) :
    primeBilinear N (sieveTruncPole Q d A) (sieveTruncPole Q e B) =
      ∑ k ∈ sieveUnits Q (A / d), ∑ l ∈ sieveUnits Q (B / e),
        poleVector (d * k) * poleVector (e * l) * weilPrimeKernel (d * k) (e * l) := by
  have houter : primeBilinear N (sieveTruncPole Q d A) (sieveTruncPole Q e B) =
      ∑ n ∈ Icc 1 N, sieveTruncPole Q d A n *
        ∑ m ∈ Icc 1 N, sieveTruncPole Q e B m * weilPrimeKernel n m := by
    unfold primeBilinear
    refine sum_congr rfl fun n _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun m _ => by ring
  rw [houter, sum_sieveTruncPole_mul hAN, sum_sieveClassPole_mul hd]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_sieveTruncPole_mul hBN, sum_sieveClassPole_mul he, mul_sum]
  exact sum_congr rfl fun l _ => by ring

/-- Same-class Grams are rectangular unit Grams scaled by the supported order. -/
theorem primeBilinear_sieveTruncPole_self {d A B N : ℕ}
    (hd : 0 < d) (hAN : A ≤ N) (hBN : B ≤ N) (Q : Finset Nat.Primes) :
    primeBilinear N (sieveTruncPole Q d A) (sieveTruncPole Q d B) =
      sieveUnitGram Q (A / d) (B / d) / d := by
  rw [primeBilinear_sieveTruncPole_eq_sum hd hd hAN hBN, sieveUnitGram, sum_div]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_div]
  refine sum_congr rfl fun l _ => ?_
  rw [weilPrimeKernel_mul_left hd, poleVector_mul_nat, poleVector_mul_nat]
  linear_combination (poleVector k * poleVector l * weilPrimeKernel k l) * poleVector_sq d

private theorem primeBilinear_sieveTruncPole_cross_of_decimated_le
    {Q : Finset Nat.Primes} {d e A B N : ℕ}
    (hd : SieveSupported Q d) (he : SieveSupported Q e) (hde : d ≠ e)
    (hAN : A ≤ N) (hBN : B ≤ N) (hAB : A / d ≤ B / e) :
    primeBilinear N (sieveTruncPole Q d A) (sieveTruncPole Q e B) =
      poleVector d * poleVector e * weilPrimeKernel d e * sievedHarmonic Q (A / d) := by
  rw [primeBilinear_sieveTruncPole_eq_sum hd.pos he.pos hAN hBN,
    sievedHarmonic, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hkunit := (mem_filter.mp hk).2
  have hk0 : 0 < k := (mem_Icc.mp (mem_filter.mp hk).1).1
  have hkB : k ∈ sieveUnits Q (B / e) := mem_filter.mpr
    ⟨mem_Icc.mpr ⟨hk0, (mem_Icc.mp (mem_filter.mp hk).1).2.trans hAB⟩, hkunit⟩
  rw [sum_eq_single k]
  · rw [show weilPrimeKernel (d * k) (e * k) = weilPrimeKernel d e by
      simpa only [mul_comm] using weilPrimeKernel_mul_left hk0 d e,
      poleVector_mul_nat, poleVector_mul_nat]
    linear_combination (poleVector d * poleVector e * weilPrimeKernel d e) * poleVector_sq k
  · intro l hl hlk
    rw [weilPrimeKernel_sieveFactors_eq_zero hd he hkunit (mem_filter.mp hl).2
      hde (Ne.symm hlk), mul_zero]
  · exact fun h => (h hkB).elim

/-- Distinct classes couple exactly up to their common unit cutoff. -/
theorem primeBilinear_sieveTruncPole_cross
    {Q : Finset Nat.Primes} {d e A B N : ℕ}
    (hd : SieveSupported Q d) (he : SieveSupported Q e) (hde : d ≠ e)
    (hAN : A ≤ N) (hBN : B ≤ N) :
    primeBilinear N (sieveTruncPole Q d A) (sieveTruncPole Q e B) =
      poleVector d * poleVector e * weilPrimeKernel d e *
        sievedHarmonic Q (min (A / d) (B / e)) := by
  rcases le_total (A / d) (B / e) with hAB | hBA
  · rw [min_eq_left hAB]
    exact primeBilinear_sieveTruncPole_cross_of_decimated_le hd he hde hAN hBN hAB
  · rw [min_eq_right hBA, primeBilinear_comm,
      primeBilinear_sieveTruncPole_cross_of_decimated_le he hd (Ne.symm hde) hBN hAN hBA,
      weilPrimeKernel_comm e d]
    ring

/-- The polar coordinate of a truncated class is its mass in that class and zero elsewhere. -/
theorem sieveClassPolar_sieveTruncPole {Q : Finset Nat.Primes} {d e A N : ℕ}
    (hd : SieveSupported Q d) (he : SieveSupported Q e) (hAN : A ≤ N) :
    sieveClassPolar Q d N (sieveTruncPole Q e A) =
      if d = e then sieveClassMass Q d A else 0 := by
  rw [sieveClassPolar, sum_sieveTruncPole_mul hAN]
  exact sieveClassPolar_classPole hd he A

/-- Ordinary class Grams retain only the smaller cutoff inside each class. -/
theorem sum_sieveTruncPole_mul_sieveTruncPole
    {Q : Finset Nat.Primes} {d e A B N : ℕ}
    (hd : SieveSupported Q d) (he : SieveSupported Q e) (hAN : A ≤ N) (_hBN : B ≤ N) :
    (∑ n ∈ Icc 1 N, sieveTruncPole Q d A n * sieveTruncPole Q e B n) =
      if d = e then sieveClassMass Q d (min A B) else 0 := by
  by_cases hde : d = e
  · subst e
    rw [if_pos rfl]
    have hterm : ∀ n, sieveTruncPole Q d A n * sieveTruncPole Q d B n =
        if n ≤ min A B then sieveClassPole Q d n ^ 2 else 0 := by
      intro n
      simp only [sieveTruncPole, le_min_iff]
      split_ifs <;> simp_all [sq]
    rw [sum_congr rfl fun n _ => hterm n,
      sum_truncate ((min_le_left A B).trans hAN), ← sieveClassMass_eq_sum hd.pos]
  · rw [if_neg hde]
    refine sum_eq_zero fun n _ => ?_
    simp only [sieveTruncPole]
    split_ifs
    · exact sieveClassPole_mul_eq_zero hd he hde n
    all_goals ring

theorem sieveClassMass_nonneg (Q : Finset Nat.Primes) (d A : ℕ) :
    0 ≤ sieveClassMass Q d A :=
  div_nonneg (sievedHarmonic_nonneg Q _) (Nat.cast_nonneg d)

theorem sieveClassMass_le_harmonicSum (Q : Finset Nat.Primes) {d : ℕ}
    (hd : 0 < d) (A : ℕ) : sieveClassMass Q d A ≤ harmonicSum A := by
  calc
    sieveClassMass Q d A ≤ sievedHarmonic Q (A / d) :=
      div_le_self (sievedHarmonic_nonneg Q _) (by exact_mod_cast hd)
    _ ≤ harmonicSum (A / d) := sievedHarmonic_le_harmonicSum Q _
    _ ≤ harmonicSum A := harmonicSum_mono (Nat.div_le_self A d)

/-- The diagonal Euler remainder is uniform over supported orders and both
cutoffs, before density normalization. -/
theorem exists_sieveTruncPole_finitePart_bound (Q : Finset Nat.Primes)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℕ), 0 < d → ∀ A B N : ℕ, A ≤ N → B ≤ N →
      |primeBilinear N (sieveTruncPole Q d A) (sieveTruncPole Q d B) -
        sieveClassMass Q d A * sieveClassMass Q d B / sieveClassDensity Q d +
        2 * sieveEuler Q * sieveClassMass Q d (min A B)| ≤
          η * harmonicSum (min A B) + C := by
  obtain ⟨C, hC, hunit⟩ := exists_sieveUnitGram_finitePart_bound Q hη
  have hordered : ∀ (d : ℕ), 0 < d → ∀ A B N : ℕ, A ≤ B → A ≤ N → B ≤ N →
      |primeBilinear N (sieveTruncPole Q d A) (sieveTruncPole Q d B) -
        sieveClassMass Q d A * sieveClassMass Q d B / sieveClassDensity Q d +
        2 * sieveEuler Q * sieveClassMass Q d A| ≤ η * harmonicSum A + C := by
    intro d hd A B N hAB hAN hBN
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hδ : sieveDensity Q ≠ 0 := (sieveDensity_pos Q).ne'
    have hid : primeBilinear N (sieveTruncPole Q d A) (sieveTruncPole Q d B) -
        sieveClassMass Q d A * sieveClassMass Q d B / sieveClassDensity Q d +
        2 * sieveEuler Q * sieveClassMass Q d A =
      (sieveUnitGram Q (A / d) (B / d) -
        sievedHarmonic Q (A / d) * sievedHarmonic Q (B / d) / sieveDensity Q +
        2 * sieveEuler Q * sievedHarmonic Q (A / d)) / d := by
      rw [primeBilinear_sieveTruncPole_self hd hAN hBN]
      simp only [sieveClassMass, sieveClassDensity]
      field_simp
    rw [hid, abs_div, abs_of_pos hdR]
    calc
      |sieveUnitGram Q (A / d) (B / d) -
          sievedHarmonic Q (A / d) * sievedHarmonic Q (B / d) / sieveDensity Q +
          2 * sieveEuler Q * sievedHarmonic Q (A / d)| / (d : ℝ) ≤
        (η * sievedHarmonic Q (A / d) + C) / d :=
        div_le_div_of_nonneg_right (hunit _ _ (Nat.div_le_div_right hAB)) hdR.le
      _ = η * sieveClassMass Q d A + C / d := by simp only [sieveClassMass]; ring
      _ ≤ η * harmonicSum A + C := add_le_add
        (mul_le_mul_of_nonneg_left (sieveClassMass_le_harmonicSum Q hd A) hη.le)
        (div_le_self hC (by exact_mod_cast hd))
  refine ⟨C, hC, fun d hd A B N hAN hBN => ?_⟩
  rcases le_total A B with hAB | hBA
  · rw [min_eq_left hAB]
    exact hordered d hd A B N hAB hAN hBN
  · rw [min_eq_right hBA, primeBilinear_comm,
      mul_comm (sieveClassMass Q d A) (sieveClassMass Q d B)]
    exact hordered d hd B A N hBA hBN hAN

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
