import GaloisForLFunctions.RHTower.CCMFUSuzukiCriticalCellSign

/-!
# Quantitative locality obstruction for the critical FU source

The literal critical Mertens--polar increment has a positive prime atom.  This file keeps the
following cells coupled to their polar drift and proves a quantitative consequence: if the
forward block beginning at a prime `p` has nonpositive net source, it must extend for at least
`log p / 2` cells.  Thus a fixed-range signed transport cannot supply the missing FU bound.

This is a locality obstruction only.  It neither bounds the signed FU reporter nor assumes RH.
-/

open Filter

namespace RHTower

noncomputable section

/-- Every critical Mertens--polar increment dominates its negative logarithmic drift. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_succ_drift_lower (N : ℕ) :
    -(Real.log ((N + 3 : ℕ) : ℝ) - Real.log ((N + 2 : ℕ) : ℝ)) ≤
      suzukiCheckpointCriticalMertensDeviationCore (N + 1) -
        suzukiCheckpointCriticalMertensDeviationCore N := by
  rw [suzukiCheckpointCriticalMertensDeviationCore_succ_sub]
  have hvm : 0 ≤ ArithmeticFunction.vonMangoldt (N + 3) / ((N + 3 : ℕ) : ℝ) :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  linarith

/-- Over a finite forward block, all possible negative source is bounded by the exact accumulated
logarithmic polar drift. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_forward_drift_lower (N L : ℕ) :
    -(Real.log ((N + L + 2 : ℕ) : ℝ) - Real.log ((N + 2 : ℕ) : ℝ)) ≤
      suzukiCheckpointCriticalMertensDeviationCore (N + L) -
        suzukiCheckpointCriticalMertensDeviationCore N := by
  induction L with
  | zero => simp
  | succ L ih =>
      have hs := suzukiCheckpointCriticalMertensDeviationCore_succ_drift_lower (N + L)
      rw [show N + (L + 1) = N + L + 1 by omega]
      have hsum := add_le_add ih hs
      calc
        -(Real.log ((N + L + 1 + 2 : ℕ) : ℝ) - Real.log ((N + 2 : ℕ) : ℝ)) =
            -(Real.log ((N + L + 2 : ℕ) : ℝ) - Real.log ((N + 2 : ℕ) : ℝ)) +
              -(Real.log ((N + L + 3 : ℕ) : ℝ) -
                Real.log ((N + L + 2 : ℕ) : ℝ)) := by
              rw [show N + L + 1 + 2 = N + L + 3 by omega]
              ring
        _ ≤ (suzukiCheckpointCriticalMertensDeviationCore (N + L) -
              suzukiCheckpointCriticalMertensDeviationCore N) +
            (suzukiCheckpointCriticalMertensDeviationCore (N + L + 1) -
              suzukiCheckpointCriticalMertensDeviationCore (N + L)) := hsum
        _ = suzukiCheckpointCriticalMertensDeviationCore (N + L + 1) -
              suzukiCheckpointCriticalMertensDeviationCore N := by ring

/-- A forward block beginning at a large prime retains the prime atom minus exactly the following
polar drift. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_prime_forwardBlock_lower
    {p L : ℕ} (hp : p.Prime) (hp27 : 27 ≤ p) :
    Real.log (p : ℝ) / (2 * p) -
        (Real.log ((p + L : ℕ) : ℝ) - Real.log (p : ℝ)) ≤
      suzukiCheckpointCriticalMertensDeviationCore (p - 2 + L) -
        suzukiCheckpointCriticalMertensDeviationCore (p - 3) := by
  have hprime := suzukiCheckpointCriticalMertensDeviationCore_prime_cell_lower hp hp27
  have htail := suzukiCheckpointCriticalMertensDeviationCore_forward_drift_lower (p - 2) L
  rw [show p - 2 + L + 2 = p + L by omega,
    show p - 2 + 2 = p by omega] at htail
  calc
    Real.log (p : ℝ) / (2 * p) -
        (Real.log ((p + L : ℕ) : ℝ) - Real.log (p : ℝ)) =
      Real.log (p : ℝ) / (2 * p) +
        -(Real.log ((p + L : ℕ) : ℝ) - Real.log (p : ℝ)) := by ring
    _ ≤ (suzukiCheckpointCriticalMertensDeviationCore (p - 2) -
          suzukiCheckpointCriticalMertensDeviationCore (p - 3)) +
        (suzukiCheckpointCriticalMertensDeviationCore (p - 2 + L) -
          suzukiCheckpointCriticalMertensDeviationCore (p - 2)) :=
      add_le_add hprime htail
    _ = suzukiCheckpointCriticalMertensDeviationCore (p - 2 + L) -
          suzukiCheckpointCriticalMertensDeviationCore (p - 3) := by ring

/-- Exact upper bound for polar drift across a forward block. -/
theorem log_suzukiCheckpointCritical_forwardBlock_drift_le
    {p L : ℕ} (hp : 1 ≤ p) :
    Real.log ((p + L : ℕ) : ℝ) - Real.log (p : ℝ) ≤ (L : ℝ) / p := by
  have hp0 : (0 : ℝ) < p := by positivity
  have hsum0Nat : 0 < p + L := by omega
  have hsum0 : (0 : ℝ) < ((p + L : ℕ) : ℝ) := by exact_mod_cast hsum0Nat
  rw [← Real.log_div hsum0.ne' hp0.ne']
  calc
    Real.log (((p + L : ℕ) : ℝ) / p) ≤ ((p + L : ℕ) : ℝ) / p - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hsum0 hp0)
    _ = (L : ℝ) / p := by
      push_cast
      field_simp
      ring

/-- **Growing-range obstruction.** If the literal critical source has nonpositive net mass on a
forward block beginning at a large prime, that block contains at least `log p / 2` cells. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_prime_nonpos_forwardBlock_forces_log_radius
    {p L : ℕ} (hp : p.Prime) (hp27 : 27 ≤ p)
    (hblock : suzukiCheckpointCriticalMertensDeviationCore (p - 2 + L) -
      suzukiCheckpointCriticalMertensDeviationCore (p - 3) ≤ 0) :
    Real.log (p : ℝ) / 2 ≤ L := by
  have hlower := suzukiCheckpointCriticalMertensDeviationCore_prime_forwardBlock_lower
    (p := p) (L := L) hp hp27
  have hlog := log_suzukiCheckpointCritical_forwardBlock_drift_le (p := p) (L := L) hp.one_le
  have hkey : Real.log (p : ℝ) / (2 * p) ≤ (L : ℝ) / p := by
    linarith
  have hp0 : (0 : ℝ) < p := by positivity
  calc
    Real.log (p : ℝ) / 2 =
        (Real.log (p : ℝ) / (2 * p)) * p := by field_simp
    _ ≤ ((L : ℝ) / p) * p := mul_le_mul_of_nonneg_right hkey hp0.le
    _ = L := by field_simp

/-- Every fixed forward transport range eventually leaves strictly positive literal source at each
prime.  Hence no bounded-memory signed cancellation can close the FU reporter. -/
theorem eventually_prime_suzukiCheckpointCriticalMertensDeviationCore_forwardBlock_pos (L : ℕ) :
    ∀ᶠ p : ℕ in atTop, p.Prime →
      0 < suzukiCheckpointCriticalMertensDeviationCore (p - 2 + L) -
        suzukiCheckpointCriticalMertensDeviationCore (p - 3) := by
  have hlogReal : Tendsto (fun x : ℝ => Real.log x / 2) atTop atTop :=
    Real.tendsto_log_atTop.atTop_div_const (by norm_num)
  have hlog : Tendsto (fun p : ℕ => Real.log (p : ℝ) / 2) atTop atTop :=
    hlogReal.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_gt_atTop (L : ℝ)),
    eventually_ge_atTop (27 : ℕ)] with p hlarge hp27 hp
  by_contra hnonpos
  have hblock : suzukiCheckpointCriticalMertensDeviationCore (p - 2 + L) -
      suzukiCheckpointCriticalMertensDeviationCore (p - 3) ≤ 0 := le_of_not_gt hnonpos
  have hrange := suzukiCheckpointCriticalMertensDeviationCore_prime_nonpos_forwardBlock_forces_log_radius
    hp hp27 hblock
  linarith

end

end RHTower
