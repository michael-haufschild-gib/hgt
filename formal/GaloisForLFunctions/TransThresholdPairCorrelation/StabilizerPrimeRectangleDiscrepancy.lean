import GaloisForLFunctions.RHTower.AdelicIntertwinerType
import GaloisForLFunctions.TransThresholdPairCorrelation.StabilizerIncompletePeriods

/-!
# Actual prime comparison for the odd-pair stabilizer

PNT gives raw mean one for distinct odd-prime logarithmic pairs. On rectangles
of odd-coordinate length Q², the conductor-Q packet has scalar mean β/2.
Thus the quarter-scaled model leaves discrepancy 7/8, while scalar two is the
unique normalization with vanishing raw discrepancy. These are full-rectangle
arithmetic means before inserting a signed aperture kernel.
-/

noncomputable section
open Finset Filter Topology

namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-- Logarithmic pair mass of distinct odd primes below the integer cutoff. -/
def oddPrimeLogRectangle (N : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesBelow N).erase 2, ∑ q ∈ ((Nat.primesBelow N).erase 2).erase p,
    Real.log (p : ℝ) * Real.log (q : ℝ)

private theorem odd_prime_log_mean :
    Tendsto (fun N : ℕ => (∑ p ∈ (Nat.primesBelow N).erase 2, Real.log (p : ℝ)) / (N : ℝ))
      atTop (𝓝 1) := by
  have hc : Tendsto (fun N : ℕ => Real.log 2 / (N : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := Real.log 2)).mul
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [mul_zero] at h
    convert h using 1
    ext n
    ring
  have h := RHTower.tendsto_sum_primesBelow_log_div.sub hc
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 2] with N hN
  have he := sum_erase_add (Nat.primesBelow N) (fun p => Real.log (p : ℝ))
    (Nat.mem_primesBelow.mpr ⟨hN, Nat.prime_two⟩)
  rw [← sub_div]
  congr 1
  exact (eq_sub_iff_add_eq.mpr he).symm

private theorem odd_prime_rectangle_eq (N : ℕ) :
    oddPrimeLogRectangle N = (∑ p ∈ (Nat.primesBelow N).erase 2, Real.log (p : ℝ)) ^ 2 -
      ∑ p ∈ (Nat.primesBelow N).erase 2, Real.log (p : ℝ) ^ 2 := by
  let S := (Nat.primesBelow N).erase 2
  have he (p : ℕ) (hp : p ∈ S) :
      (∑ q ∈ S.erase p, Real.log (p : ℝ) * Real.log (q : ℝ)) =
        Real.log (p : ℝ) * (∑ q ∈ S, Real.log (q : ℝ)) - Real.log (p : ℝ) ^ 2 := by
    have h := sum_erase_add S (fun q => Real.log (p : ℝ) * Real.log (q : ℝ)) hp
    rw [mul_sum, pow_two]
    exact eq_sub_iff_add_eq.mpr h
  unfold oddPrimeLogRectangle
  change (∑ p ∈ S, ∑ q ∈ S.erase p, Real.log (p : ℝ) * Real.log (q : ℝ)) = _
  rw [sum_congr rfl he, sum_sub_distrib, ← sum_mul]
  ring

private theorem odd_prime_log_square_bound (N : ℕ) :
    (∑ p ∈ (Nat.primesBelow N).erase 2, Real.log (p : ℝ) ^ 2) ≤
      Real.log (N : ℝ) * ∑ p ∈ (Nat.primesBelow N).erase 2, Real.log (p : ℝ) := by
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hp' := Nat.mem_primesBelow.mp (mem_of_mem_erase hp)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp'.2.one_lt.le
  have hpN : (p : ℝ) ≤ N := by exact_mod_cast hp'.1.le
  have h := mul_le_mul_of_nonneg_right (Real.log_le_log hp0 hpN) (Real.log_nonneg hp1)
  nlinarith only [h]

/-- PNT gives mean one after removing prime two and all repeated prime pairs. -/
theorem oddPrimeLogRectangle_mean :
    Tendsto (fun N : ℕ => oddPrimeLogRectangle N / (N : ℝ) ^ 2) atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hupper := hlog.mul odd_prime_log_mean
  rw [zero_mul] at hupper
  have hdiag : Tendsto (fun N : ℕ =>
      (∑ p ∈ (Nat.primesBelow N).erase 2, Real.log (p : ℝ) ^ 2) / (N : ℝ) ^ 2)
        atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · exact Eventually.of_forall fun N => div_nonneg (sum_nonneg fun p _ => sq_nonneg _) (sq_nonneg _)
    · filter_upwards [eventually_gt_atTop 0] with N hN
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      calc
        _ ≤ (Real.log (N : ℝ) * ∑ p ∈ (Nat.primesBelow N).erase 2,
            Real.log (p : ℝ)) / (N : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right (odd_prime_log_square_bound N) (sq_nonneg _)
        _ = _ := by field_simp [hNr]
  have h := (odd_prime_log_mean.pow 2).sub hdiag
  norm_num only [one_pow, sub_zero] at h
  convert h using 1
  ext N
  rw [odd_prime_rectangle_eq, sub_div, div_pow]

/-- Actual odd-prime mean minus the stabilizer mean, with conductor cutoff `n+1`
and odd-coordinate length `(n+1)²`. -/
def squareScaleStabilizerDiscrepancy (n : ℕ) (β : ℝ) : ℝ :=
  oddPrimeLogRectangle (2 * (n + 1) ^ 2) / ((2 * (n + 1) ^ 2 : ℕ) : ℝ) ^ 2 -
    distinctOddStabilizerRectangleMean (n + 1) ((n + 1) ^ 2) β

/-- The actual raw prime-pair discrepancy has limit `1−β/2` at a growing cutoff. -/
theorem squareScaleStabilizerDiscrepancy_tendsto (β : ℝ) :
    Tendsto (fun n : ℕ => squareScaleStabilizerDiscrepancy n β) atTop (𝓝 (1 - β / 2)) := by
  have hscale : Tendsto (fun n : ℕ => 2 * (n + 1) ^ 2) atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => ?_⟩
    nlinarith only [hn]
  exact (oddPrimeLogRectangle_mean.comp hscale).sub
    (distinctOddStabilizerRectangleMean_square_tendsto β)

/-- The literal quarter-scaled source leaves raw prime-pair mean discrepancy `7/8`. -/
theorem squareScaleStabilizerDiscrepancy_quarter :
    Tendsto (fun n : ℕ => squareScaleStabilizerDiscrepancy n (1 / 4)) atTop (𝓝 (7 / 8)) := by
  convert squareScaleStabilizerDiscrepancy_tendsto (1 / 4) using 1; norm_num

/-- Scalar two centers the actual raw prime rectangle at the same growing cutoff. -/
theorem squareScaleStabilizerDiscrepancy_two :
    Tendsto (fun n : ℕ => squareScaleStabilizerDiscrepancy n 2) atTop (𝓝 0) := by
  convert squareScaleStabilizerDiscrepancy_tendsto 2 using 1; norm_num

/-- Scalar two is the unique normalization with vanishing actual raw prime discrepancy. -/
theorem squareScaleStabilizerDiscrepancy_tendsto_zero_iff (β : ℝ) :
    Tendsto (fun n : ℕ => squareScaleStabilizerDiscrepancy n β) atTop (𝓝 0) ↔ β = 2 := by
  constructor
  · intro h
    have he := tendsto_nhds_unique (squareScaleStabilizerDiscrepancy_tendsto β) h
    linarith only [he]
  · rintro rfl
    exact squareScaleStabilizerDiscrepancy_two

end GaloisForLFunctions.TransThresholdPairCorrelation
