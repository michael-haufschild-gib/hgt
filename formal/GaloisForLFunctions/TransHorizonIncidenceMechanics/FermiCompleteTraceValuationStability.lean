import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiValuationDepthAndFiniteWindowStability
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ShortWindowCorrelationDefectAndIsoStateClassification
import GaloisForLFunctions.BezoutValuationIncidence.TruncatedPronicGramMatrixAndFiniteHorizonVonMangoldtApproximation
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Complete selected Fermi traces

Both pronic energies converge for every finite coefficient horizon. The finite
valuation-depth estimate therefore controls the complete selected trace in its
literal reciprocal-cell weights.
-/

open Finset
open RHTower GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- Sieve energy across all positive reciprocal cells. -/
def sieveTotalPronicEnergy (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑' m : ℕ, sievePairedPronicEnergy N c {m}

/-- Complete physical energy of the odd and four-divisible boundary readings. -/
def fermiSelectedTotalPronicEnergy (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑' m : ℕ, fermiSelectedPronicEnergy N c {m}

/-- Finite coefficient horizons make both complete pronic traces summable. -/
theorem sieve_fermi_pronic_summable (N : ℕ) (c : ℕ → ℝ) :
    Summable (fun m : ℕ => sievePairedPronicEnergy N c {m}) ∧
      Summable (fun m : ℕ => fermiSelectedPronicEnergy N c {m}) := by
  let A := ∑ d ∈ Finset.Icc 1 N, |c d|
  have hs_bound (n : ℕ) : |sieveSeq N c n ^ 2| ≤ A ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_sieveSeq_le_sum_abs N c n) 2
  have he_bound (n : ℕ) : |(2 * sieveSeq N c (n / 2) - sieveSeq N c n) ^ 2| ≤
      (3 * A) ^ 2 := by
    have h1 := abs_le.mp (abs_sieveSeq_le_sum_abs N c (n / 2))
    have h2 := abs_le.mp (abs_sieveSeq_le_sum_abs N c n)
    change -A ≤ sieveSeq N c (n / 2) ∧ sieveSeq N c (n / 2) ≤ A at h1
    change -A ≤ sieveSeq N c n ∧ sieveSeq N c n ≤ A at h2
    have h : |2 * sieveSeq N c (n / 2) - sieveSeq N c n| ≤ 3 * A :=
      abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hs := summable_div_pronicSeq_of_bounded hs_bound
  have he := summable_div_pronicSeq_of_bounded he_bound
  have hodd : Summable (fun m : ℕ =>
      sieveSeq N c (2 * m + 1) ^ 2 / (pronicSeq (2 * m + 1) : ℝ)) :=
    hs.comp_injective (i := fun m : ℕ => 2 * m + 1)
      (by intro a b h; change 2 * a + 1 = 2 * b + 1 at h; omega)
  have heven : Summable (fun m : ℕ =>
      sieveSeq N c (2 * m + 2) ^ 2 / (pronicSeq (2 * m + 2) : ℝ)) :=
    hs.comp_injective (i := fun m : ℕ => 2 * m + 2)
      (by intro a b h; change 2 * a + 2 = 2 * b + 2 at h; omega)
  have hjodd : Summable (fun m : ℕ =>
      fermiBoundaryJump N c (2 * m + 1) ^ 2 / (pronicSeq (2 * m + 1) : ℝ)) := by
    refine hodd.congr fun m => ?_
    rw [fermiBoundaryJump_odd, neg_sq]
  have hjeven : Summable (fun m : ℕ =>
      fermiBoundaryJump N c (4 * m + 4) ^ 2 / (pronicSeq (4 * m + 4) : ℝ)) := by
    have hsub := he.comp_injective (i := fun m : ℕ => 4 * m + 4)
      (by intro a b h; change 4 * a + 4 = 4 * b + 4 at h; omega)
    refine hsub.congr fun m => ?_
    change (2 * sieveSeq N c ((4 * m + 4) / 2) - sieveSeq N c (4 * m + 4)) ^ 2 /
        (pronicSeq (4 * m + 4) : ℝ) = _
    have hj := fermiBoundaryJump_even N c (2 * m + 1)
    rw [show 2 * (2 * m + 1) + 2 = 4 * m + 4 by omega,
      show 2 * m + 1 + 1 = 2 * m + 2 by omega] at hj
    rw [show (4 * m + 4) / 2 = 2 * m + 2 by omega, hj]
  constructor
  · simpa only [sievePairedPronicEnergy, Finset.sum_singleton] using hodd.add heven
  · simpa only [fermiSelectedPronicEnergy, Finset.sum_singleton] using hjodd.add hjeven

/-- Complete-trace inverse stability depends at most quadratically on dyadic horizon depth. -/
theorem sieveTotalPronicEnergy_le_depth_selected (N : ℕ) (c : ℕ → ℝ) :
    let L := Nat.log 2 N + 1
    sieveTotalPronicEnergy N c ≤
      (((L : ℝ) + 4) * ((L : ℝ) + 1)) * fermiSelectedTotalPronicEnergy N c := by
  let L := Nat.log 2 N + 1
  change (∑' m : ℕ, sievePairedPronicEnergy N c {m}) ≤
    (((L : ℝ) + 4) * ((L : ℝ) + 1)) * fermiSelectedTotalPronicEnergy N c
  have hQ (m : ℕ) : 0 ≤ fermiSelectedPronicEnergy N c {m} := by
    simp only [fermiSelectedPronicEnergy, Finset.sum_singleton]
    positivity
  apply Real.tsum_le_of_sum_range_le
    (fun m => by simp only [sievePairedPronicEnergy, Finset.sum_singleton]; positivity)
  intro M
  have hfinite := sievePairedPronicEnergy_le_depth_selected_window N M c
  have hsum := Summable.sum_le_tsum (Finset.range (2 ^ L * M))
    (fun m _ => hQ m) (sieve_fermi_pronic_summable N c).2
  have htotal : fermiSelectedPronicEnergy N c (Finset.range (2 ^ L * M)) ≤
      fermiSelectedTotalPronicEnergy N c := by
    simpa only [fermiSelectedTotalPronicEnergy, fermiSelectedPronicEnergy,
      Finset.sum_singleton] using hsum
  have hbound := hfinite.trans (mul_le_mul_of_nonneg_left htotal
    (by positivity : 0 ≤ ((L : ℝ) + 4) * ((L : ℝ) + 1)))
  simpa only [sievePairedPronicEnergy, Finset.sum_singleton] using hbound

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
