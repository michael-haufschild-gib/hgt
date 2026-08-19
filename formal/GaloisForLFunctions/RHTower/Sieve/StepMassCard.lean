import GaloisForLFunctions.RHTower.Sieve.BlockMassCompare

/-!
# The size of a ladder step against its harmonic mass

`Sieve/BlockMassCompare.card_geomBlock_le_mul_stepMass` gives the upper half of the comparison
between a step's size and its harmonic mass.  The lower half is recorded here for completeness; it
is the direction that shows a step's harmonic mass is not larger than its size divided by the
step's left endpoint.

Both halves hold for every subdivision — no prime counting in short intervals is involved.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **A ladder step is no smaller than its harmonic mass times its left endpoint.** -/
theorem stepMass_mul_le_card {P : Finset ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) (j : ℕ) :
    stepMass P Q η j * (Q * (1 + η) ^ j) ≤ ((geomBlock P Q (1 + η) j).card : ℝ) := by
  classical
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hQj : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
  have hterm : ∀ p ∈ geomBlock P Q (1 + η) j,
      (1 : ℝ) / (p : ℝ) ≤ 1 / (Q * (1 + η) ^ j) := by
    intro p hp
    rw [geomBlock, Finset.mem_filter] at hp
    obtain ⟨-, hlo, -⟩ := hp
    exact one_div_le_one_div_of_le hQj hlo.le
  have hsum : stepMass P Q η j
      ≤ ((geomBlock P Q (1 + η) j).card : ℝ) * (1 / (Q * (1 + η) ^ j)) := by
    rw [stepMass]
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have hmul := mul_le_mul_of_nonneg_right hsum hQj.le
  refine hmul.trans (le_of_eq ?_)
  field_simp

/-- A ladder step, as a set of naturals, sits in an interval of integers. -/
theorem geomBlock_subset_Ioc {P : Finset ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) (j : ℕ) :
    geomBlock P Q (1 + η) j
      ⊆ Finset.Ioc ⌊Q * (1 + η) ^ j⌋₊ ⌊Q * (1 + η) ^ (j + 1)⌋₊ := by
  classical
  intro p hp
  rw [geomBlock, Finset.mem_filter] at hp
  obtain ⟨-, hlo, hhi⟩ := hp
  have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
  rw [Finset.mem_Ioc]
  constructor
  · exact (Nat.floor_lt hbase.le).2 hlo
  · exact Nat.le_floor hhi

/-- **A thin ladder step has harmonic mass at most `η + 1/Pj0`.**  This is what lets the
Cauchy–Schwarz over the ladder be run with *equal* weights: the number of steps is a polylogarithm
and each step's mass is `O(η)`, so `∑_j stepMass_j² ≤ (max stepMass)·W`. -/
theorem stepMass_le {P : Finset ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) (j : ℕ) :
    stepMass P Q η j ≤ η + 1 / (Q * (1 + η) ^ j) := by
  classical
  have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hterm : ∀ p ∈ geomBlock P Q (1 + η) j, (1 : ℝ) / (p : ℝ) ≤ 1 / (Q * (1 + η) ^ j) := by
    intro p hp
    rw [geomBlock, Finset.mem_filter] at hp
    exact one_div_le_one_div_of_le hbase hp.2.1.le
  have hcard : ((geomBlock P Q (1 + η) j).card : ℝ) ≤ Q * (1 + η) ^ j * η + 1 := by
    have hsub := Finset.card_le_card (geomBlock_subset_Ioc (P := P) hQ hη j)
    have hIoc : ((Finset.Ioc ⌊Q * (1 + η) ^ j⌋₊ ⌊Q * (1 + η) ^ (j + 1)⌋₊).card : ℕ)
        = ⌊Q * (1 + η) ^ (j + 1)⌋₊ - ⌊Q * (1 + η) ^ j⌋₊ := Nat.card_Ioc _ _
    have hcast : ((geomBlock P Q (1 + η) j).card : ℝ)
        ≤ ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) := by
      have h1 : (geomBlock P Q (1 + η) j).card ≤ ⌊Q * (1 + η) ^ (j + 1)⌋₊ := by
        rw [hIoc] at hsub; omega
      exact_mod_cast h1
    have hle : ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) ≤ Q * (1 + η) ^ (j + 1) :=
      Nat.floor_le (by positivity)
    have hval : Q * (1 + η) ^ (j + 1) = Q * (1 + η) ^ j * (1 + η) := by
      rw [pow_succ]; ring
    have hfl : ((⌊Q * (1 + η) ^ j⌋₊ : ℕ) : ℝ) ≤ Q * (1 + η) ^ j := Nat.floor_le hbase.le
    have hsub' : (geomBlock P Q (1 + η) j).card
        ≤ ⌊Q * (1 + η) ^ (j + 1)⌋₊ - ⌊Q * (1 + η) ^ j⌋₊ := by rw [hIoc] at hsub; exact hsub
    have hlow : (Q * (1 + η) ^ j) - 1 ≤ ((⌊Q * (1 + η) ^ j⌋₊ : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one (Q * (1 + η) ^ j)
      linarith
    have hmono : ⌊Q * (1 + η) ^ j⌋₊ ≤ ⌊Q * (1 + η) ^ (j + 1)⌋₊ := by
      refine Nat.floor_le_floor ?_
      rw [pow_succ]
      nlinarith [hbase, hr1]
    have hdiff : ((geomBlock P Q (1 + η) j).card : ℝ)
        ≤ ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) - ((⌊Q * (1 + η) ^ j⌋₊ : ℕ) : ℝ) := by
      have hc := (Nat.cast_le (α := ℝ)).2 hsub'
      rwa [Nat.cast_sub hmono] at hc
    have hle2 : ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) ≤ Q * (1 + η) ^ j * (1 + η) := by
      rw [← hval]; exact hle
    linarith [hdiff, hle2, hlow]
  have hsum : stepMass P Q η j
      ≤ ((geomBlock P Q (1 + η) j).card : ℝ) * (1 / (Q * (1 + η) ^ j)) := by
    rw [stepMass]
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  refine hsum.trans ?_
  have hmul := mul_le_mul_of_nonneg_right hcard
    (by positivity : (0 : ℝ) ≤ 1 / (Q * (1 + η) ^ j))
  refine hmul.trans (le_of_eq ?_)
  field_simp

end

end RHTower.Sieve
