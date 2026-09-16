import GaloisForLFunctions.RHTower.CCMFUSuzukiCriticalTransportRangeNoGo

/-!
# Two-sided locality obstruction for the critical CCM-FU source

The known forward obstruction forces a cancellation block starting at a large prime to extend
at least logarithmically far.  A signed producer could in principle borrow polar mass from cells
before the prime as well.  This module closes that loophole: every contiguous nonpositive block
containing a large prime must pay the exact combined logarithmic polar span on its two sides.
Consequently every fixed two-sided radius is eventually strictly positive at primes.

The result retains the literal Mertens--polar source cell by cell.  It does not bound the
RH-bearing variation action; it proves that a prospective source-faithful transport must be
genuinely nonlocal even when both orientations are allowed.
-/

open Filter

namespace RHTower

noncomputable section

/-- A nonpositive contiguous critical source block containing a large prime must pay the
exact logarithmic polar span on both sides of that prime. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_prime_nonpos_bidirectionalBlock_forces_log_span
    {p L R : ℕ} (hp : p.Prime) (hp27 : 27 ≤ p) (hleft : L + 3 ≤ p)
    (hblock : suzukiCheckpointCriticalMertensDeviationCore (p - 2 + R) -
      suzukiCheckpointCriticalMertensDeviationCore (p - L - 3) ≤ 0) :
    Real.log (p : ℝ) / (2 * p) ≤
      (Real.log ((p - 1 : ℕ) : ℝ) - Real.log ((p - L - 1 : ℕ) : ℝ)) +
        (Real.log ((p + R : ℕ) : ℝ) - Real.log (p : ℝ)) := by
  have hprime := suzukiCheckpointCriticalMertensDeviationCore_prime_cell_lower hp hp27
  have hback := suzukiCheckpointCriticalMertensDeviationCore_forward_drift_lower
    (p - L - 3) L
  have hforward := suzukiCheckpointCriticalMertensDeviationCore_forward_drift_lower
    (p - 2) R
  rw [show p - L - 3 + L = p - 3 by omega] at hback
  rw [show p - 3 + 2 = p - 1 by omega,
    show p - L - 3 + 2 = p - L - 1 by omega] at hback
  rw [show p - 2 + R + 2 = p + R by omega,
    show p - 2 + 2 = p by omega] at hforward
  have hsum :
      -(Real.log ((p - 1 : ℕ) : ℝ) - Real.log ((p - L - 1 : ℕ) : ℝ)) +
          Real.log (p : ℝ) / (2 * p) -
          (Real.log ((p + R : ℕ) : ℝ) - Real.log (p : ℝ)) ≤
        suzukiCheckpointCriticalMertensDeviationCore (p - 2 + R) -
          suzukiCheckpointCriticalMertensDeviationCore (p - L - 3) := by
    calc
      -(Real.log ((p - 1 : ℕ) : ℝ) - Real.log ((p - L - 1 : ℕ) : ℝ)) +
            Real.log (p : ℝ) / (2 * p) -
            (Real.log ((p + R : ℕ) : ℝ) - Real.log (p : ℝ)) ≤
          (suzukiCheckpointCriticalMertensDeviationCore (p - 3) -
              suzukiCheckpointCriticalMertensDeviationCore (p - L - 3)) +
            (suzukiCheckpointCriticalMertensDeviationCore (p - 2) -
              suzukiCheckpointCriticalMertensDeviationCore (p - 3)) +
            (suzukiCheckpointCriticalMertensDeviationCore (p - 2 + R) -
              suzukiCheckpointCriticalMertensDeviationCore (p - 2)) := by
        linarith
      _ = suzukiCheckpointCriticalMertensDeviationCore (p - 2 + R) -
          suzukiCheckpointCriticalMertensDeviationCore (p - L - 3) := by ring
  linarith

/-- Exact backward logarithmic polar drift over a finite block. -/
private theorem log_suzukiCheckpointCritical_backwardBlock_drift_le
    {p L : ℕ} (hLP : L + 2 ≤ p) :
    Real.log ((p - 1 : ℕ) : ℝ) - Real.log ((p - L - 1 : ℕ) : ℝ) ≤
      (L : ℝ) / ((p - L - 1 : ℕ) : ℝ) := by
  have hdenNat : 0 < p - L - 1 := by omega
  have hnumNat : 0 < p - 1 := by omega
  have hden : (0 : ℝ) < ((p - L - 1 : ℕ) : ℝ) := by exact_mod_cast hdenNat
  have hnum : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hnumNat
  have hbasepos : (0 : ℝ) < -1 + ((p - L : ℕ) : ℝ) := by
    have hlt : (1 : ℝ) < ((p - L : ℕ) : ℝ) := by
      exact_mod_cast (show 1 < p - L by omega)
    linarith
  have hsplit : (p : ℝ) = ((p - L : ℕ) : ℝ) + L := by
    exact_mod_cast (Nat.sub_add_cancel (show L ≤ p by omega)).symm
  rw [← Real.log_div hnum.ne' hden.ne']
  calc
    Real.log (((p - 1 : ℕ) : ℝ) / ((p - L - 1 : ℕ) : ℝ)) ≤
        ((p - 1 : ℕ) : ℝ) / ((p - L - 1 : ℕ) : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hnum hden)
    _ = (L : ℝ) / ((p - L - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ p),
        Nat.cast_sub (by omega : 1 ≤ p - L)]
      push_cast
      rw [hsplit]
      have hinv : (-1 + ((p - L : ℕ) : ℝ)) *
          (-1 + ((p - L : ℕ) : ℝ))⁻¹ = 1 :=
        mul_inv_cancel₀ hbasepos.ne'
      linear_combination hinv

/-- **Quantitative bicausal locality law.** A contiguous source-faithful block that
contains a large prime and has nonpositive net Mertens--polar mass must have combined
left/right radius at least `log p / 2`. Thus not only fixed memory but every
sublogarithmic contiguous cancellation scheme is excluded. The conclusion is in
event-label coordinates, before scalar FU readout. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_prime_nonpos_bidirectionalBlock_forces_combined_log_radius
    {p L R : ℕ} (hp : p.Prime) (hp27 : 27 ≤ p) (htw : 2 * (L + 1) ≤ p)
    (hblock : suzukiCheckpointCriticalMertensDeviationCore (p - 2 + R) -
      suzukiCheckpointCriticalMertensDeviationCore (p - L - 3) ≤ 0) :
    Real.log (p : ℝ) / 2 ≤ 2 * (L : ℝ) + R := by
  have hleft : L + 3 ≤ p := by omega
  have hspan :=
    suzukiCheckpointCriticalMertensDeviationCore_prime_nonpos_bidirectionalBlock_forces_log_span
      hp hp27 hleft hblock
  have hback := log_suzukiCheckpointCritical_backwardBlock_drift_le
    (show L + 2 ≤ p by omega)
  have hforward := log_suzukiCheckpointCritical_forwardBlock_drift_le
    (p := p) (L := R) hp.one_le
  have hp0 : (0 : ℝ) < p := by positivity
  have hdenNat : 0 < p - L - 1 := by omega
  have hden : (0 : ℝ) < ((p - L - 1 : ℕ) : ℝ) := by exact_mod_cast hdenNat
  have htwR : (2 : ℝ) * ((L : ℝ) + 1) ≤ p := by
    exact_mod_cast htw
  have hdenComp : (p : ℝ) ≤ 2 * ((p - L - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ p - L), Nat.cast_sub (by omega : L ≤ p)]
    push_cast
    nlinarith [htwR]
  have hbackScale : (L : ℝ) / ((p - L - 1 : ℕ) : ℝ) ≤
      (2 * (L : ℝ)) / p := by
    apply (div_le_div_iff₀ hden hp0).2
    nlinarith [mul_le_mul_of_nonneg_left hdenComp (Nat.cast_nonneg L)]
  have hsum :
      (Real.log ((p - 1 : ℕ) : ℝ) - Real.log ((p - L - 1 : ℕ) : ℝ)) +
          (Real.log ((p + R : ℕ) : ℝ) - Real.log (p : ℝ)) ≤
        (2 * (L : ℝ) + R) / p := by
    calc
      (Real.log ((p - 1 : ℕ) : ℝ) - Real.log ((p - L - 1 : ℕ) : ℝ)) +
          (Real.log ((p + R : ℕ) : ℝ) - Real.log (p : ℝ)) ≤
          (L : ℝ) / ((p - L - 1 : ℕ) : ℝ) + (R : ℝ) / p :=
        add_le_add hback hforward
      _ ≤ (2 * (L : ℝ)) / p + (R : ℝ) / p :=
        add_le_add hbackScale le_rfl
      _ = (2 * (L : ℝ) + R) / p := by ring
  have hbound : Real.log (p : ℝ) / (2 * p) ≤ (2 * (L : ℝ) + R) / p :=
    hspan.trans hsum
  calc
    Real.log (p : ℝ) / 2 = (Real.log (p : ℝ) / (2 * p)) * p := by
      field_simp
    _ ≤ ((2 * (L : ℝ) + R) / p) * p :=
      mul_le_mul_of_nonneg_right hbound hp0.le
    _ = 2 * (L : ℝ) + R := by field_simp

/-- **Cofinal sublogarithmic bicausal obstruction.** Any varying contiguous left/right
transport schedule whose combined radius is eventually smaller than `log p / 2` leaves
strictly positive literal source on every sufficiently large prime block. This turns the
pointwise locality law into the exact rejection criterion for proposed growing-memory
transport schedules. -/
theorem eventually_prime_suzukiCheckpointCriticalMertensDeviationCore_bidirectionalBlock_pos_of_eventually_combined_radius_lt_log
    (L R : ℕ → ℕ)
    (hwidth : ∀ᶠ p : ℕ in atTop, 2 * (L p + 1) ≤ p)
    (hsmall : ∀ᶠ p : ℕ in atTop,
      2 * (L p : ℝ) + R p < Real.log (p : ℝ) / 2) :
    ∀ᶠ p : ℕ in atTop, p.Prime →
      0 < suzukiCheckpointCriticalMertensDeviationCore (p - 2 + R p) -
        suzukiCheckpointCriticalMertensDeviationCore (p - L p - 3) := by
  filter_upwards [eventually_ge_atTop (27 : ℕ), hwidth, hsmall]
    with p hp27 hpwidth hsmallp hp
  by_contra hnonpos
  have hblock : suzukiCheckpointCriticalMertensDeviationCore (p - 2 + R p) -
      suzukiCheckpointCriticalMertensDeviationCore (p - L p - 3) ≤ 0 :=
    le_of_not_gt hnonpos
  have hradius :=
    suzukiCheckpointCriticalMertensDeviationCore_prime_nonpos_bidirectionalBlock_forces_combined_log_radius
      hp hp27 hpwidth hblock
  linarith

/-- **Fixed-radius two-sided transport is impossible cofinally.**  For any fixed left and right
memory radii, every sufficiently large prime leaves strictly positive literal
Mertens--polar mass in its full two-sided block.  This closes the remaining bounded-memory
orientation loophole: a source-faithful CCM-FU cancellation mechanism must have scale-growing,
not merely bidirectional, support. -/
theorem eventually_prime_suzukiCheckpointCriticalMertensDeviationCore_bidirectionalBlock_pos
    (L R : ℕ) :
    ∀ᶠ p : ℕ in atTop, p.Prime →
      0 < suzukiCheckpointCriticalMertensDeviationCore (p - 2 + R) -
        suzukiCheckpointCriticalMertensDeviationCore (p - L - 3) := by
  have hlogReal : Tendsto (fun x : ℝ => Real.log x / 2) atTop atTop :=
    Real.tendsto_log_atTop.atTop_div_const (by norm_num)
  have hlog : Tendsto (fun p : ℕ => Real.log (p : ℝ) / 2) atTop atTop :=
    hlogReal.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_gt_atTop (2 * (L : ℝ) + R)),
    eventually_ge_atTop (27 : ℕ),
    eventually_ge_atTop (2 * (L + 1))] with p hlarge hp27 htw hp
  by_contra hnonpos
  have hblock : suzukiCheckpointCriticalMertensDeviationCore (p - 2 + R) -
      suzukiCheckpointCriticalMertensDeviationCore (p - L - 3) ≤ 0 :=
    le_of_not_gt hnonpos
  have hkey :=
    suzukiCheckpointCriticalMertensDeviationCore_prime_nonpos_bidirectionalBlock_forces_combined_log_radius
      hp hp27 htw hblock
  linarith

end

end RHTower
