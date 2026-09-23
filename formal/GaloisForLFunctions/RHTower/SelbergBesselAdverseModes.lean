import GaloisForLFunctions.RHTower.SelbergBesselBoundaryEnergy
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Int.Interval

/-!
# Exact finite adverse block of the critical cusp boundary form

For width `exp(b)` and cutoff height `exp(T)`, the actual critical Bessel seam
coefficient at nonzero integer frequency `n` is negative exactly when
`0 < |n| < exp(transition) * exp(b) / (2 * pi * exp(T))`.
The full signed adverse set and its cardinality are explicit. Finite compact
mode packets have an exact square-plus-positive-boundary-minus-debt identity.

The zero channel is omitted, not identified with a positive-frequency Bessel
mode. This is a finite-packet theorem: no infinite Fourier/Parseval passage or
Maass compact-core response is assumed. The negative seam count is unbounded
along integer periods at each fixed height; it is not a uniform rank bound.
-/

open Set MeasureTheory
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergBesselModes
open SelbergBesselSlope SelbergBesselEnergy
noncomputable section

/-- Logarithm of the nonzero Fourier frequency for period `exp(b)`. -/
def modeLog (b : ℝ) (n : ℤ) : ℝ := Real.log (2 * Real.pi) - b + Real.log (n.natAbs : ℝ)

/-- Actual outgoing Bessel coefficient, with the omitted zero channel assigned zero. -/
def seam (b T : ℝ) (n : ℤ) : ℝ := if n = 0 then 0 else outgoing (modeLog b n) T

/-- Dimensionless integer-mode threshold selected by the exact Bessel transition. -/
def radius (b T : ℝ) : ℝ := Real.exp (transition - (Real.log (2 * Real.pi) - b) - T)

/-- Largest absolute integer index with strictly negative seam coefficient. -/
def cutoff (b T : ℝ) : ℕ := Nat.ceil (radius b T) - 1

/-- All signed adverse modes, with the zero channel removed. -/
def adverse (b T : ℝ) : Finset ℤ :=
  (Finset.Icc (-(cutoff b T : ℤ)) (cutoff b T : ℤ)).erase 0

private theorem mode_natAbs_pos {n : ℤ} (hn : n ≠ 0) : 0 < (n.natAbs : ℝ) := by
  exact_mod_cast Int.natAbs_pos.mpr hn

/-- The mode threshold is strictly positive at every width and height. -/
theorem radius_pos (b T : ℝ) : 0 < radius b T := Real.exp_pos _

/-- The logarithmic parameter gives exactly `2*pi*|n|/width` for every nonzero integer. -/
theorem mode_frequency (b : ℝ) (n : {n : ℤ // n ≠ 0}) :
    Real.exp (modeLog b n) = 2 * Real.pi * |((n : ℤ) : ℝ)| / Real.exp b := by
  have hp : 0 < 2 * Real.pi := mul_pos (by linarith) Real.pi_pos
  rw [modeLog, Real.exp_add, Real.exp_sub, Real.exp_log hp,
    Real.exp_log (mode_natAbs_pos n.property)]
  have ha : ((n : ℤ).natAbs : ℝ) = |((n : ℤ) : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [ha]
  ring

/-- Exact strict sign criterion, including explicit exclusion of the zero channel. -/
theorem seam_neg_iff (b T : ℝ) (n : ℤ) :
    seam b T n < 0 ↔ n ≠ 0 ∧ (n.natAbs : ℝ) < radius b T := by
  by_cases hn : n = 0
  · simp [seam, hn]
  · rw [seam, if_neg hn, outgoing_neg_iff, and_iff_right hn]
    change Real.log (2 * Real.pi) - b + Real.log (n.natAbs : ℝ) + T < transition ↔ _
    rw [show Real.log (2 * Real.pi) - b + Real.log (n.natAbs : ℝ) + T < transition ↔
      Real.log (n.natAbs : ℝ) < transition - (Real.log (2 * Real.pi) - b) - T by
        constructor <;> intro h <;> linarith]
    exact Real.log_lt_iff_lt_exp (mode_natAbs_pos hn)

/-- The finite integer set contains exactly the negative seam coefficients. -/
theorem mem_adverse_iff (b T : ℝ) (n : ℤ) : n ∈ adverse b T ↔ seam b T n < 0 := by
  rw [adverse, Finset.mem_erase, Finset.mem_Icc, seam_neg_iff]
  have hc : 0 < Nat.ceil (radius b T) := Nat.ceil_pos.mpr (radius_pos b T)
  have habs : -(cutoff b T : ℤ) ≤ n ∧ n ≤ (cutoff b T : ℤ) ↔
      n.natAbs ≤ cutoff b T := by
    rw [← abs_le, ← Int.natCast_natAbs]
    exact Nat.cast_le
  rw [habs, ← Nat.lt_ceil]
  unfold cutoff
  omega

/-- The complete signed adverse block has exactly twice the positive cutoff many modes. -/
theorem card_adverse (b T : ℝ) : (adverse b T).card = 2 * cutoff b T := by
  have hz : (0 : ℤ) ∈ Finset.Icc (-(cutoff b T : ℤ)) (cutoff b T : ℤ) := by
    simp only [Finset.mem_Icc]
    constructor <;> omega
  rw [adverse, Finset.card_erase_of_mem hz, Int.card_Icc]
  omega

/-- Every mode outside the explicit adverse block has nonnegative seam coefficient. -/
theorem seam_nonneg_outside (b T : ℝ) (n : ℤ) :
    0 ≤ seam b T n ↔ n ∉ adverse b T := by
  rw [mem_adverse_iff, not_lt]

/-- Exact width-over-height scaling law for the adverse-mode threshold. -/
theorem radius_width_height (b T : ℝ) :
    radius b T = Real.exp transition * Real.exp b / (2 * Real.pi * Real.exp T) := by
  have hp : 0 < 2 * Real.pi := mul_pos (by linarith) Real.pi_pos
  rw [radius, show transition - (Real.log (2 * Real.pi) - b) - T =
    transition + b - (Real.log (2 * Real.pi) + T) by ring,
    Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_log hp]

/-- At fixed height every natural adverse cutoff is attained by an explicit width. -/
theorem cutoff_tuned_width (T : ℝ) (m : ℕ) :
    cutoff (Real.log (2 * Real.pi) + T - transition + Real.log ((m : ℝ) + 1)) T = m := by
  unfold cutoff radius
  rw [show transition - (Real.log (2 * Real.pi) -
      (Real.log (2 * Real.pi) + T - transition + Real.log ((m : ℝ) + 1))) - T =
    Real.log ((m : ℝ) + 1) by ring, Real.exp_log (by positivity)]
  rw [← Nat.cast_one, ← Nat.cast_add, Nat.ceil_natCast, Nat.add_sub_cancel]

/-- Every even signed adverse-block size is attained at every fixed height. -/
theorem card_adverse_tuned_width (T : ℝ) (m : ℕ) :
    (adverse (Real.log (2 * Real.pi) + T - transition + Real.log ((m : ℝ) + 1)) T).card = 2 * m := by
  rw [card_adverse, cutoff_tuned_width]

/-- The adverse block vanishes exactly when the first frequency reaches the transition. -/
theorem adverse_empty_iff (b T : ℝ) : adverse b T = ∅ ↔ radius b T ≤ 1 := by
  have hc : cutoff b T = 0 ↔ radius b T ≤ 1 := by
    rw [cutoff, Nat.sub_eq_zero_iff_le, Nat.ceil_le, Nat.cast_one]
  rw [← Finset.card_eq_zero, card_adverse, ← hc]
  omega

/-- Even along positive integer periods, adverse cutoff sizes are unbounded at fixed height. -/
theorem integer_width_cutoff_unbounded (T : ℝ) (m : ℕ) :
    ∃ N : ℕ, m < cutoff (Real.log ((N : ℝ) + 1)) T := by
  have hp : 0 < 2 * Real.pi * Real.exp T := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (((m : ℝ) + 1) * (2 * Real.pi * Real.exp T) / Real.exp transition)
  refine ⟨N, ?_⟩
  have hr : (m : ℝ) + 1 < radius (Real.log ((N : ℝ) + 1)) T := by
    rw [radius_width_height, Real.exp_log (by positivity), lt_div_iff₀ hp]
    have hh := (div_lt_iff₀ (Real.exp_pos transition)).mp hN
    nlinarith [Real.exp_pos transition]
  have hm : m + 1 < Nat.ceil (radius (Real.log ((N : ℝ) + 1)) T) := by
    rw [Nat.lt_ceil]
    simpa only [Nat.cast_add, Nat.cast_one] using hr
  unfold cutoff
  omega

/-- Nonnegative part of the finite-packet seam form. -/
def positiveForm (s : Finset ℤ) (b T : ℝ) (c : ℤ → ℝ) : ℝ :=
  ∑ n ∈ s, max (seam b T n) 0 * c n ^ (2 : ℕ)

/-- The complete adverse boundary cost on the intersection with the finite packet. -/
def debtForm (s : Finset ℤ) (b T : ℝ) (c : ℤ → ℝ) : ℝ :=
  ∑ n ∈ s.filter (fun n => n ∈ adverse b T), -seam b T n * c n ^ (2 : ℕ)

/-- Exact signed decomposition; every adverse boundary contribution is retained. -/
theorem seam_form_decomposition (s : Finset ℤ) (b T : ℝ) (c : ℤ → ℝ) :
    (∑ n ∈ s, seam b T n * c n ^ (2 : ℕ)) = positiveForm s b T c - debtForm s b T c := by
  rw [positiveForm, debtForm, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n ∈ adverse b T
  · have hneg := (mem_adverse_iff b T n).mp hn
    rw [if_pos hn, max_eq_right hneg.le]
    ring
  · have hpos := (seam_nonneg_outside b T n).mpr hn
    rw [if_neg hn, max_eq_left hpos]
    ring

/-- The retained positive boundary part is nonnegative for arbitrary real traces. -/
theorem positiveForm_nonneg (s : Finset ℤ) (b T : ℝ) (c : ℤ → ℝ) :
    0 ≤ positiveForm s b T c := by
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg (le_max_right _ _) (sq_nonneg _)

/-- The adverse cost is nonnegative for arbitrary real traces. -/
theorem debtForm_nonneg (s : Finset ℤ) (b T : ℝ) (c : ℤ → ℝ) :
    0 ≤ debtForm s b T c := by
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (neg_nonneg.mpr ((mem_adverse_iff b T n).mp (Finset.mem_filter.mp hn).2).le)
    (sq_nonneg _)

/-- Strict cost occurs exactly when the packet trace meets an adverse mode nontrivially. -/
theorem debtForm_pos_iff (s : Finset ℤ) (b T : ℝ) (c : ℤ → ℝ) :
    0 < debtForm s b T c ↔ ∃ n ∈ s, n ∈ adverse b T ∧ c n ≠ 0 := by
  have hh : ∀ n ∈ s.filter (fun n => n ∈ adverse b T), 0 ≤ -seam b T n * c n ^ (2 : ℕ) := by
    intro n hn
    exact mul_nonneg (neg_nonneg.mpr ((mem_adverse_iff b T n).mp (Finset.mem_filter.mp hn).2).le)
      (sq_nonneg _)
  rw [debtForm, Finset.sum_pos_iff_of_nonneg hh]
  constructor
  · rintro ⟨n, hn, hp⟩
    refine ⟨n, (Finset.mem_filter.mp hn).1, (Finset.mem_filter.mp hn).2, ?_⟩
    intro hc
    simp [hc] at hp
  · rintro ⟨n, hn, ha, hc⟩
    refine ⟨n, Finset.mem_filter.mpr ⟨hn, ha⟩, ?_⟩
    exact mul_pos (neg_pos.mpr ((mem_adverse_iff b T n).mp ha)) (sq_pos_of_ne_zero hc)

/-- Actual finite compact-mode energy equals squares plus positive seam minus full adverse cost. -/
theorem finite_packet_energy_identity (s : Finset ℤ) (b T : ℝ) (f : ℤ → Profile) :
    (∑ n ∈ s.erase 0, ∫ t in Ioi T, excessField (f n) (modeLog b n) t) =
      (∑ n ∈ s.erase 0, ∫ t in Ioi T, squareField (f n) (modeLog b n) t) +
      positiveForm (s.erase 0) b T (fun n => f n T) -
      debtForm (s.erase 0) b T (fun n => f n T) := by
  have hid : (∑ n ∈ s.erase 0, ∫ t in Ioi T, excessField (f n) (modeLog b n) t) =
      ∑ n ∈ s.erase 0, ((∫ t in Ioi T, squareField (f n) (modeLog b n) t) +
        seam b T n * f n T ^ (2 : ℕ)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [critical_boundary_identity, seam, if_neg (Finset.mem_erase.mp hn).1]
  rw [hid, Finset.sum_add_distrib, seam_form_decomposition]
  ring

/-- All possible negative finite-packet energy is bounded by the explicit adverse trace cost. -/
theorem finite_packet_debt_bound (s : Finset ℤ) (b T : ℝ) (f : ℤ → Profile) :
    -debtForm (s.erase 0) b T (fun n => f n T) ≤
      ∑ n ∈ s.erase 0, ∫ t in Ioi T, excessField (f n) (modeLog b n) t := by
  rw [finite_packet_energy_identity]
  have hsq : 0 ≤ ∑ n ∈ s.erase 0, ∫ t in Ioi T, squareField (f n) (modeLog b n) t := by
    apply Finset.sum_nonneg
    intro n _
    exact integral_nonneg (fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  linarith [positiveForm_nonneg (s.erase 0) b T (fun n => f n T)]

end
end GaloisForLFunctions.RHTower.SelbergBesselModes
