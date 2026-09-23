import GaloisForLFunctions.HTGeometry.SourcePairPositiveQuarticGradedRealification

/-!
# Finite-packet Schwarz-doubled positive quartic realification

The local `(7,5)` real graded lift is assembled over an arbitrary finite complex packet. Each
node is paired with its Schwarz conjugate, so no choice of conjugate-pair representatives or
initial conjugation-closure hypothesis is needed. The total lift preserves complete traces one
and two, while its quartic defect is the finite sum

`sum_i 100 (Im z_i)^(2 : ℕ) (6 (Re z_i)^(2 : ℕ) + 23 (Im z_i)^(2 : ℕ))`.

This charge is nonnegative and vanishes exactly when every packet node is real. Both the charge
and every graded anomaly are invariant under Schwarz conjugation and arbitrary finite reindexing.
Unlike entrywise matrix aggregation, this is a spectral-packet construction. It does not assert
the source-side vanishing law needed to select real divisors at actual theta stages.
-/

open Complex Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Total power trace of the real even packet, with two nodes over every complex node. -/
def finitePacketPositiveQuarticRealEvenMoment
    (n : ℕ) (z : ι → ℂ) : ℂ :=
  ∑ i, sourcePairPositiveQuarticRealEvenMoment n (z i).re (z i).im

/-- Total power trace of the real odd packet, with four nodes over every complex node. -/
def finitePacketPositiveQuarticRealOddMoment
    (n : ℕ) (z : ι → ℂ) : ℂ :=
  ∑ i, sourcePairPositiveQuarticRealOddMoment n (z i).im

/-- Moment of the packet after adjoining the Schwarz conjugate of every node. -/
def finitePacketSchwarzDoubledMoment
    (n : ℕ) (z : ι → ℂ) : ℂ :=
  ∑ i, sourcePairMoment n (z i).re (z i).im

/-- Complete packet-level signed power-trace defect. -/
def finitePacketPositiveQuarticGradedAnomaly
    (n : ℕ) (z : ι → ℂ) : ℂ :=
  finitePacketPositiveQuarticRealEvenMoment n z -
    finitePacketPositiveQuarticRealOddMoment n z -
      finitePacketSchwarzDoubledMoment n z

/-- Positive quartic orientation charge of a finite complex packet. -/
def finitePacketPositiveQuarticCharge (z : ι → ℂ) : ℝ :=
  ∑ i, sourcePairPositiveQuarticCharge (z i).re (z i).im

/-- The global anomaly is exactly the finite sum of local Schwarz-pair anomalies. -/
theorem finitePacketPositiveQuarticGradedAnomaly_eq_sum
    (n : ℕ) (z : ι → ℂ) :
    finitePacketPositiveQuarticGradedAnomaly n z =
      ∑ i, sourcePairPositiveQuarticGradedAnomaly n (z i).re (z i).im := by
  simp [finitePacketPositiveQuarticGradedAnomaly,
    finitePacketPositiveQuarticRealEvenMoment,
    finitePacketPositiveQuarticRealOddMoment,
    finitePacketSchwarzDoubledMoment,
    sourcePairPositiveQuarticGradedAnomaly,
    Finset.sum_sub_distrib]

/-- Complete first trace is preserved for every finite packet. -/
theorem finitePacketPositiveQuarticGradedAnomaly_one (z : ι → ℂ) :
    finitePacketPositiveQuarticGradedAnomaly 1 z = 0 := by
  rw [finitePacketPositiveQuarticGradedAnomaly_eq_sum]
  simp [sourcePairPositiveQuarticGradedAnomaly_one]

/-- Complete quadratic trace is preserved for every finite packet. -/
theorem finitePacketPositiveQuarticGradedAnomaly_two (z : ι → ℂ) :
    finitePacketPositiveQuarticGradedAnomaly 2 z = 0 := by
  rw [finitePacketPositiveQuarticGradedAnomaly_eq_sum]
  simp [sourcePairPositiveQuarticGradedAnomaly_two]

/-- The packet quartic defect is exactly its positive orientation charge. -/
theorem finitePacketPositiveQuarticGradedAnomaly_four (z : ι → ℂ) :
    finitePacketPositiveQuarticGradedAnomaly 4 z =
      (finitePacketPositiveQuarticCharge z : ℂ) := by
  rw [finitePacketPositiveQuarticGradedAnomaly_eq_sum]
  simp [sourcePairPositiveQuarticGradedAnomaly_four,
    finitePacketPositiveQuarticCharge]

theorem finitePacketPositiveQuarticCharge_nonneg (z : ι → ℂ) :
    0 ≤ finitePacketPositiveQuarticCharge z := by
  apply Finset.sum_nonneg
  intro i hi
  exact sourcePairPositiveQuarticCharge_nonneg (z i).re (z i).im

/-- Packet charge vanishes exactly when every packet node is real. -/
theorem finitePacketPositiveQuarticCharge_eq_zero_iff (z : ι → ℂ) :
    finitePacketPositiveQuarticCharge z = 0 ↔ ∀ i, (z i).im = 0 := by
  constructor
  · intro h i
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
        sourcePairPositiveQuarticCharge_nonneg (z j).re (z j).im)).mp h
      i (Finset.mem_univ i)
    exact (sourcePairPositiveQuarticCharge_eq_zero_iff (z i).re (z i).im).mp hterm
  · intro h
    apply Finset.sum_eq_zero
    intro i hi
    exact (sourcePairPositiveQuarticCharge_eq_zero_iff (z i).re (z i).im).mpr (h i)

/-- Packet charge is strictly positive exactly when the packet contains a nonreal node. -/
theorem finitePacketPositiveQuarticCharge_pos_iff (z : ι → ℂ) :
    0 < finitePacketPositiveQuarticCharge z ↔ ∃ i, (z i).im ≠ 0 := by
  constructor
  · intro h
    by_contra hall
    push Not at hall
    have hz := (finitePacketPositiveQuarticCharge_eq_zero_iff z).mpr hall
    linarith
  · rintro ⟨i, hi⟩
    have hnonneg := finitePacketPositiveQuarticCharge_nonneg z
    have hne : finitePacketPositiveQuarticCharge z ≠ 0 := by
      intro hz
      exact hi ((finitePacketPositiveQuarticCharge_eq_zero_iff z).mp hz i)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Negating the imaginary coordinate only swaps nodes within every local graded block. -/
theorem sourcePairPositiveQuarticGradedAnomaly_neg_im
    (n : ℕ) (a b : ℝ) :
    sourcePairPositiveQuarticGradedAnomaly n a (-b) =
      sourcePairPositiveQuarticGradedAnomaly n a b := by
  simp [sourcePairPositiveQuarticGradedAnomaly,
    sourcePairPositiveQuarticRealEvenMoment,
    sourcePairPositiveQuarticRealOddMoment, sourcePairMoment]
  ring

/-- The scalar charge is invariant under pointwise Schwarz conjugation. -/
theorem finitePacketPositiveQuarticCharge_conj (z : ι → ℂ) :
    finitePacketPositiveQuarticCharge (fun i => (starRingEnd ℂ) (z i)) =
      finitePacketPositiveQuarticCharge z := by
  apply Finset.sum_congr rfl
  intro i hi
  change sourcePairPositiveQuarticCharge ((starRingEnd ℂ) (z i)).re
    ((starRingEnd ℂ) (z i)).im =
    sourcePairPositiveQuarticCharge (z i).re (z i).im
  rw [Complex.conj_re, Complex.conj_im]
  simp [sourcePairPositiveQuarticCharge]

/-- Every packet anomaly is invariant under pointwise Schwarz conjugation. -/
theorem finitePacketPositiveQuarticGradedAnomaly_conj
    (n : ℕ) (z : ι → ℂ) :
    finitePacketPositiveQuarticGradedAnomaly n
        (fun i => (starRingEnd ℂ) (z i)) =
      finitePacketPositiveQuarticGradedAnomaly n z := by
  rw [finitePacketPositiveQuarticGradedAnomaly_eq_sum,
    finitePacketPositiveQuarticGradedAnomaly_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.conj_re, Complex.conj_im]
  exact sourcePairPositiveQuarticGradedAnomaly_neg_im n (z i).re (z i).im

/-- Packet charge is independent of the finite enumeration. -/
theorem finitePacketPositiveQuarticCharge_reindex
    {κ : Type*} [Fintype κ] (e : ι ≃ κ) (z : ι → ℂ) :
    finitePacketPositiveQuarticCharge (fun j : κ => z (e.symm j)) =
      finitePacketPositiveQuarticCharge z := by
  unfold finitePacketPositiveQuarticCharge
  exact Equiv.sum_comp e.symm
    (fun i : ι => sourcePairPositiveQuarticCharge (z i).re (z i).im)

/-- Every packet anomaly is independent of the finite enumeration. -/
theorem finitePacketPositiveQuarticGradedAnomaly_reindex
    {κ : Type*} [Fintype κ] (e : ι ≃ κ) (n : ℕ) (z : ι → ℂ) :
    finitePacketPositiveQuarticGradedAnomaly n (fun j : κ => z (e.symm j)) =
      finitePacketPositiveQuarticGradedAnomaly n z := by
  rw [finitePacketPositiveQuarticGradedAnomaly_eq_sum,
    finitePacketPositiveQuarticGradedAnomaly_eq_sum]
  exact Equiv.sum_comp e.symm
    (fun i : ι => sourcePairPositiveQuarticGradedAnomaly n (z i).re (z i).im)

end

end GaloisForLFunctions.HTGeometry
