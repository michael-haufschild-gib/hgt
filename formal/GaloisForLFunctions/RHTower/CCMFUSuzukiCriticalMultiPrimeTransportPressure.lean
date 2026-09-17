import GaloisForLFunctions.RHTower.CCMFUSuzukiCriticalTransportRangeNoGo

/-!
# Multi-prime memory pressure for the critical CCM-FU source

The one-prime locality obstruction leaves open a growing-memory transport.
This module records the stronger source-executed constraint: if a nonpositive
forward block contains two literal prime atoms, both atoms consume its finite
logarithmic polar-drift budget.  No prime-gap estimate is assumed.
-/

namespace RHTower

noncomputable section

/-- Exact source-history decomposition of a critical forward block.  Its arithmetic side retains
every prime power, while its continuum side is the single polar logarithmic drift. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_forwardBlock_eq_vonMangoldt_sub_log
    {p : ℕ} (hp3 : 3 ≤ p) (L : ℕ) :
    suzukiCheckpointCriticalMertensDeviationCore (p - 2 + L) -
        suzukiCheckpointCriticalMertensDeviationCore (p - 3) =
      (∑ k ∈ Finset.Icc p (p + L), ArithmeticFunction.vonMangoldt k / (k : ℝ)) -
        (Real.log ((p + L : ℕ) : ℝ) - Real.log ((p - 1 : ℕ) : ℝ)) := by
  induction L with
  | zero =>
      rw [show p - 2 = p - 3 + 1 by omega,
        suzukiCheckpointCriticalMertensDeviationCore_succ_sub (p - 3),
        show p - 3 + 3 = p by omega,
        show p - 3 + 2 = p - 1 by omega]
      simp
  | succ L ih =>
      have hstep := suzukiCheckpointCriticalMertensDeviationCore_succ_sub (p - 2 + L)
      rw [show p - 2 + L + 3 = p + L + 1 by omega,
        show p - 2 + L + 2 = p + L by omega] at hstep
      calc
        suzukiCheckpointCriticalMertensDeviationCore (p - 2 + (L + 1)) -
            suzukiCheckpointCriticalMertensDeviationCore (p - 3) =
          (suzukiCheckpointCriticalMertensDeviationCore (p - 2 + L) -
              suzukiCheckpointCriticalMertensDeviationCore (p - 3)) +
            (suzukiCheckpointCriticalMertensDeviationCore (p - 2 + L + 1) -
              suzukiCheckpointCriticalMertensDeviationCore (p - 2 + L)) := by
            ring
        _ =
          ((∑ k ∈ Finset.Icc p (p + L), ArithmeticFunction.vonMangoldt k / (k : ℝ)) -
              (Real.log ((p + L : ℕ) : ℝ) - Real.log ((p - 1 : ℕ) : ℝ))) +
            (ArithmeticFunction.vonMangoldt (p + L + 1) / ((p + L + 1 : ℕ) : ℝ) -
              (Real.log ((p + L + 1 : ℕ) : ℝ) - Real.log ((p + L : ℕ) : ℝ))) := by
            rw [ih, show p - 2 + L + 1 = (p - 2 + L) + 1 by omega, hstep]
        _ =
          (∑ k ∈ Finset.Icc p (p + (L + 1)),
              ArithmeticFunction.vonMangoldt k / (k : ℝ)) -
            (Real.log ((p + (L + 1) : ℕ) : ℝ) - Real.log ((p - 1 : ℕ) : ℝ)) := by
            rw [show p + (L + 1) = p + L + 1 by omega,
              Finset.sum_Icc_succ_top (by omega)]
            ring

/-- **Finite source-history budget.** A nonpositive critical forward block can pay for no more
literal von-Mangoldt mass than its exact polar logarithmic drift. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_nonpos_forwardBlock_vonMangoldt_budget
    {p L : ℕ} (hp3 : 3 ≤ p)
    (hblock : suzukiCheckpointCriticalMertensDeviationCore (p - 2 + L) -
      suzukiCheckpointCriticalMertensDeviationCore (p - 3) ≤ 0) :
    ∑ k ∈ Finset.Icc p (p + L), ArithmeticFunction.vonMangoldt k / (k : ℝ) ≤
      Real.log ((p + L : ℕ) : ℝ) - Real.log ((p - 1 : ℕ) : ℝ) := by
  rw [suzukiCheckpointCriticalMertensDeviationCore_forwardBlock_eq_vonMangoldt_sub_log hp3 L]
    at hblock
  linarith

/-- Two distinct prime atoms inside a nonpositive forward critical-source block consume their
combined logarithmic budget.  The inequality is source-faithful: it retains both literal atoms
and every intervening polar drift. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_twoPrime_nonpos_forwardBlock_forces_log_budget
    {p q L : ℕ} (hp : p.Prime) (hq : q.Prime) (hp27 : 27 ≤ p)
    (hpq : p < q) (hqL : q ≤ p + L)
    (hblock : suzukiCheckpointCriticalMertensDeviationCore (p - 2 + L) -
      suzukiCheckpointCriticalMertensDeviationCore (p - 3) ≤ 0) :
    Real.log (p : ℝ) / (2 * p) + Real.log (q : ℝ) / (2 * q) ≤
      Real.log ((p + L : ℕ) : ℝ) - Real.log (p : ℝ) := by
  have hq27 : 27 ≤ q := by omega
  have hfirst := suzukiCheckpointCriticalMertensDeviationCore_prime_cell_lower hp hp27
  have hsecond := suzukiCheckpointCriticalMertensDeviationCore_prime_cell_lower hq hq27
  have hmiddle := suzukiCheckpointCriticalMertensDeviationCore_forward_drift_lower
    (p - 2) (q - p - 1)
  rw [show p - 2 + (q - p - 1) = q - 3 by omega,
    show q - 3 + 2 = q - 1 by omega,
    show p - 2 + 2 = p by omega] at hmiddle
  have htail := suzukiCheckpointCriticalMertensDeviationCore_forward_drift_lower
    (q - 2) (p + L - q)
  rw [show q - 2 + (p + L - q) = p - 2 + L by omega,
    show p - 2 + L + 2 = p + L by omega,
    show q - 2 + 2 = q by omega] at htail
  have hqsubpos : 0 < ((q - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < q - 1 by omega)
  have hqsub_le : ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (Nat.sub_le q 1)
  have hlogq : Real.log ((q - 1 : ℕ) : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log hqsubpos hqsub_le
  have hdecomp :
      suzukiCheckpointCriticalMertensDeviationCore (p - 2 + L) -
          suzukiCheckpointCriticalMertensDeviationCore (p - 3) =
        (suzukiCheckpointCriticalMertensDeviationCore (p - 2) -
            suzukiCheckpointCriticalMertensDeviationCore (p - 3)) +
          (suzukiCheckpointCriticalMertensDeviationCore (q - 3) -
            suzukiCheckpointCriticalMertensDeviationCore (p - 2)) +
          (suzukiCheckpointCriticalMertensDeviationCore (q - 2) -
            suzukiCheckpointCriticalMertensDeviationCore (q - 3)) +
          (suzukiCheckpointCriticalMertensDeviationCore (p - 2 + L) -
            suzukiCheckpointCriticalMertensDeviationCore (q - 2)) := by
    ring
  linarith

/-- In natural-number memory units, a nonpositive block containing two distinct primes must pay
the first prime's half-log budget plus the second prime's scale-corrected half-log budget. -/
theorem suzukiCheckpointCriticalMertensDeviationCore_twoPrime_nonpos_forwardBlock_forces_radius
    {p q L : ℕ} (hp : p.Prime) (hq : q.Prime) (hp27 : 27 ≤ p)
    (hpq : p < q) (hqL : q ≤ p + L)
    (hblock : suzukiCheckpointCriticalMertensDeviationCore (p - 2 + L) -
      suzukiCheckpointCriticalMertensDeviationCore (p - 3) ≤ 0) :
    Real.log (p : ℝ) / 2 +
      (p : ℝ) * Real.log (q : ℝ) / (2 * q) ≤ L := by
  have hbudget :=
    suzukiCheckpointCriticalMertensDeviationCore_twoPrime_nonpos_forwardBlock_forces_log_budget
      hp hq hp27 hpq hqL hblock
  have hspan := log_suzukiCheckpointCritical_forwardBlock_drift_le
    (p := p) (L := L) hp.one_le
  have hbound :
      Real.log (p : ℝ) / (2 * p) + Real.log (q : ℝ) / (2 * q) ≤ (L : ℝ) / p :=
    hbudget.trans hspan
  have hp0 : (0 : ℝ) < p := by positivity
  calc
    Real.log (p : ℝ) / 2 +
        (p : ℝ) * Real.log (q : ℝ) / (2 * q) =
        (Real.log (p : ℝ) / (2 * p) + Real.log (q : ℝ) / (2 * q)) * p := by
          field_simp
    _ ≤ ((L : ℝ) / p) * p := mul_le_mul_of_nonneg_right hbound hp0.le
    _ = L := by field_simp

end

end RHTower
