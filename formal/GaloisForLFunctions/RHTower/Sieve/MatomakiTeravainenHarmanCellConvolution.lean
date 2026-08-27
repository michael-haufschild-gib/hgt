import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenHarmanCellCoefficients
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenBlockConvolution

/-!
# Rectangular Harman cells as exact sifted divisor sums

The pair and triple tuple coefficients regroup the literal nested Harman sums by tuple product.
This is an equality, not a majorization: convolving one cell coefficient with `ρ(·,z)` reproduces
the source's divisibility-conditioned pair or triple sum term by term.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- A divisor sum supported on one prescribed positive divisor is the corresponding divisibility
indicator. -/
theorem sum_divisors_eq_if_dvd
    {R : Type*} [AddCommMonoid R] (f : ℕ → R)
    {n d : ℕ} (hn : 0 < n) :
    ∑ m ∈ n.divisors, (if d = m then f (n / m) else 0) =
      if d ∣ n then f (n / d) else 0 := by
  by_cases hdvd : d ∣ n
  · rw [if_pos hdvd]
    have hdMem : d ∈ n.divisors := Nat.mem_divisors.mpr ⟨hdvd, hn.ne'⟩
    rw [Finset.sum_eq_single d]
    · simp
    · intro m hm hmd
      exact if_neg (Ne.symm hmd)
    · exact fun hnot => absurd hdMem hnot
  · rw [if_neg hdvd]
    apply Finset.sum_eq_zero
    intro m hm
    have hdm : d ≠ m := by
      intro h
      subst m
      exact hdvd (Nat.dvd_of_mem_divisors hm)
    simp [hdm]

/-- Literal pair-cell Harman sum before the finite Lemma 2.3 iteration. -/
def mtHarmanPairCellSiftSum
    (S₁ S₂ : Finset ℕ) (z n : ℕ) : ℂ :=
  ∑ q₁ ∈ S₁, ∑ q₂ ∈ S₂,
    if q₁ * q₂ ∣ n then (rho (n / q₁ / q₂) z : ℂ) else 0

/-- Regrouping an exact pair rectangle by `m=q₁q₂` gives its tuple coefficient convolved with
the source sifting function. -/
theorem mtHarmanPairCellSiftSum_eq_divisorSiftSum
    (S₁ S₂ : Finset ℕ) (z : ℕ) {n : ℕ} (hn : 0 < n) :
    mtHarmanPairCellSiftSum S₁ S₂ z n =
      mtDivisorSiftSum (mtHarmanPairCellCoefficient S₁ S₂) z n := by
  unfold mtHarmanPairCellSiftSum mtDivisorSiftSum
  simp only [mtHarmanPairCellCoefficient_eq_source_sum]
  calc
    (∑ q₁ ∈ S₁, ∑ q₂ ∈ S₂,
        if q₁ * q₂ ∣ n then (rho (n / q₁ / q₂) z : ℂ) else 0) =
      ∑ q₁ ∈ S₁, ∑ q₂ ∈ S₂, ∑ m ∈ n.divisors,
        if q₁ * q₂ = m then (rho (n / m) z : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro q₁ hq₁
      apply Finset.sum_congr rfl
      intro q₂ hq₂
      simpa only [Nat.div_div_eq_div_mul] using
        (sum_divisors_eq_if_dvd (fun k => (rho k z : ℂ)) (n := n)
          (d := q₁ * q₂) hn).symm
    _ = ∑ q₁ ∈ S₁, ∑ m ∈ n.divisors, ∑ q₂ ∈ S₂,
        if q₁ * q₂ = m then (rho (n / m) z : ℂ) else 0 :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ m ∈ n.divisors, ∑ q₁ ∈ S₁, ∑ q₂ ∈ S₂,
        if q₁ * q₂ = m then (rho (n / m) z : ℂ) else 0 := Finset.sum_comm
    _ = ∑ m ∈ n.divisors,
        (∑ q₁ ∈ S₁, ∑ q₂ ∈ S₂, if q₁ * q₂ = m then 1 else 0) *
          (rho (n / m) z : ℂ) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q₁ hq₁
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q₂ hq₂
      split_ifs <;> simp

/-- Literal triple-cell Harman sum before the finite Lemma 2.3 iteration. -/
def mtHarmanTripleCellSiftSum
    (S₁ S₂ S₃ : Finset ℕ) (z n : ℕ) : ℂ :=
  ∑ q₁ ∈ S₁, ∑ q₂ ∈ S₂, ∑ q₃ ∈ S₃,
    if q₁ * q₂ * q₃ ∣ n then (rho (n / q₁ / q₂ / q₃) z : ℂ) else 0

/-- Regrouping an exact triple rectangle by `m=q₁q₂q₃` gives its tuple coefficient convolved
with the source sifting function. -/
theorem mtHarmanTripleCellSiftSum_eq_divisorSiftSum
    (S₁ S₂ S₃ : Finset ℕ) (z : ℕ) {n : ℕ} (hn : 0 < n) :
    mtHarmanTripleCellSiftSum S₁ S₂ S₃ z n =
      mtDivisorSiftSum (mtHarmanTripleCellCoefficient S₁ S₂ S₃) z n := by
  unfold mtHarmanTripleCellSiftSum mtDivisorSiftSum
  simp only [mtHarmanTripleCellCoefficient_eq_source_sum]
  calc
    (∑ q₁ ∈ S₁, ∑ q₂ ∈ S₂, ∑ q₃ ∈ S₃,
        if q₁ * q₂ * q₃ ∣ n then (rho (n / q₁ / q₂ / q₃) z : ℂ) else 0) =
      ∑ q₁ ∈ S₁, ∑ q₂ ∈ S₂, ∑ q₃ ∈ S₃, ∑ m ∈ n.divisors,
        if q₁ * q₂ * q₃ = m then (rho (n / m) z : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro q₁ hq₁
      apply Finset.sum_congr rfl
      intro q₂ hq₂
      apply Finset.sum_congr rfl
      intro q₃ hq₃
      simpa only [Nat.div_div_eq_div_mul, Nat.mul_assoc] using
        (sum_divisors_eq_if_dvd (fun k => (rho k z : ℂ)) (n := n)
          (d := q₁ * q₂ * q₃) hn).symm
    _ = ∑ q₁ ∈ S₁, ∑ q₂ ∈ S₂, ∑ m ∈ n.divisors, ∑ q₃ ∈ S₃,
        if q₁ * q₂ * q₃ = m then (rho (n / m) z : ℂ) else 0 :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ q₁ ∈ S₁, ∑ m ∈ n.divisors, ∑ q₂ ∈ S₂, ∑ q₃ ∈ S₃,
        if q₁ * q₂ * q₃ = m then (rho (n / m) z : ℂ) else 0 :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ m ∈ n.divisors, ∑ q₁ ∈ S₁, ∑ q₂ ∈ S₂, ∑ q₃ ∈ S₃,
        if q₁ * q₂ * q₃ = m then (rho (n / m) z : ℂ) else 0 := Finset.sum_comm
    _ = ∑ m ∈ n.divisors,
        (∑ q₁ ∈ S₁, ∑ q₂ ∈ S₂, ∑ q₃ ∈ S₃,
          if q₁ * q₂ * q₃ = m then 1 else 0) * (rho (n / m) z : ℂ) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q₁ hq₁
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q₂ hq₂
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q₃ hq₃
      split_ifs <;> simp

end

end RHTower.Sieve
