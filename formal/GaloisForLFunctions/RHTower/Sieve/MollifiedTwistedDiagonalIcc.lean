import GaloisForLFunctions.RHTower.Sieve.MollifiedTwistedMeanValueError
import GaloisForLFunctions.RHTower.Sieve.TwistedDiagonalGCDReindex

/-!
# Arithmetic diagonal on an initial interval

For AFE support `Icc 1 L`, the gcd-reduced twisted ray has scale range exactly
`Icc 1 (L / max (k/g) (h/g))`.  This removes the filtered double sum from the mollified main term.
-/

open Finset Complex
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.Sieve

/-- The common scale of two positive rays stays in `Icc 1 L` exactly up to
`L / max a b`. -/
theorem pair_mul_mem_Icc_iff_mem_Icc_div_max
    {a b d L : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (a * d ∈ Finset.Icc 1 L ∧ b * d ∈ Finset.Icc 1 L) ↔
      d ∈ Finset.Icc 1 (L / max a b) := by
  simp only [Finset.mem_Icc]
  have hmax : 0 < max a b := lt_of_lt_of_le (by omega) (Nat.le_max_left a b)
  constructor
  · rintro ⟨⟨had1, hadL⟩, ⟨hbd1, hbdL⟩⟩
    have hd1 : 1 ≤ d := by
      by_contra hd
      have hd0 : d = 0 := by omega
      simp [hd0] at had1
    refine ⟨hd1, (Nat.le_div_iff_mul_le hmax).2 ?_⟩
    rcases le_total a b with hab | hba
    · rw [max_eq_right hab, mul_comm]
      exact hbdL
    · rw [max_eq_left hba, mul_comm]
      exact hadL
  · rintro ⟨hd1, hdL⟩
    have hdmax : d * max a b ≤ L := (Nat.le_div_iff_mul_le hmax).1 hdL
    have haL : a * d ≤ L := by
      calc
        a * d ≤ max a b * d := Nat.mul_le_mul_right d (Nat.le_max_left a b)
        _ = d * max a b := by ac_rfl
        _ ≤ L := hdmax
    have hbL : b * d ≤ L := by
      calc
        b * d ≤ max a b * d := Nat.mul_le_mul_right d (Nat.le_max_right a b)
        _ = d * max a b := by ac_rfl
        _ ≤ L := hdmax
    exact ⟨⟨by nlinarith, haL⟩, ⟨by nlinarith, hbL⟩⟩

/-- On a common initial interval, every mollified twisted diagonal is a
single scale sum along the gcd-reduced ray. -/
theorem mollifiedTwistedDiagonal_Icc
    (a b u v : ℕ → ℂ) (q : Finset ℕ) (L : ℕ) (sigma : ℝ)
    (hq : ∀ h ∈ q, 1 ≤ h) :
    mollifiedTwistedDiagonal a b u v (Finset.Icc 1 L) q sigma =
      ∑ h ∈ q, ∑ k ∈ q,
        (u h * (starRingEnd ℂ) (v k)) *
          (∑ d ∈ Finset.Icc 1
              (L / max (k / Nat.gcd h k) (h / Nat.gcd h k)),
            twistedCoeff a b sigma
              ((k / Nat.gcd h k) * d) ((h / Nat.gcd h k) * d)) := by
  classical
  unfold mollifiedTwistedDiagonal
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  apply twisted_diagonal_reindex_gcd
  · exact hq k hk
  · intro d
    have hkred : 1 ≤ k / Nat.gcd h k := by
      have hk0 : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one (hq k hk)
      have hg : 0 < Nat.gcd h k := Nat.gcd_pos_of_pos_right h hk0
      apply Nat.one_le_div_iff hg |>.2
      exact Nat.gcd_le_right h hk0
    have hhred : 1 ≤ h / Nat.gcd h k := by
      have hh0 : 0 < h := Nat.lt_of_lt_of_le Nat.zero_lt_one (hq h hh)
      have hg : 0 < Nat.gcd h k := Nat.gcd_pos_of_pos_left k hh0
      apply Nat.one_le_div_iff hg |>.2
      exact Nat.gcd_le_left k hh0
    exact (pair_mul_mem_Icc_iff_mem_Icc_div_max hkred hhred).symm

end RHTower.Sieve
