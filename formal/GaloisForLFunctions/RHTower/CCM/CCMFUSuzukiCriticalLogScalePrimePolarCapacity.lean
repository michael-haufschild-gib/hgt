import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiCriticalCellSign

/-!
# Log-scale one-prime polar capacity for the critical CCM--FU source

The critical CCM--FU source has a positive atomic contribution `log p / p` at a prime `p`.
The existing transport no-gos show that a valid source-faithful cancellation mechanism cannot
have fixed or sublogarithmic memory.  This module supplies the complementary constructive local
fact: the literal forward polar span through `ceil (2 log p)` integer cells has enough mass to
pay one marked prime atom, before any scalarization or absolute-value estimate.

This is not a global cancellation theorem.  The marked intervals attached to distinct primes
overlap, so controlling their joint allocation remains the RH-bearing problem.  The theorem
identifies that remaining problem precisely: global signed overlap control, rather than local
prime-to-polar capacity.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- Source-forced forward polar budget for one marked prime atom. -/
def ccmFUCriticalPrimeLogTransportRadius (p : ℕ) : ℕ :=
  Nat.ceil (2 * Real.log (p : ℝ))

/-- The marked transport radius is at least twice the prime's logarithmic clock. -/
theorem ccmFUCriticalPrimeLogTransportRadius_lower (p : ℕ) :
    2 * Real.log (p : ℝ) ≤ (ccmFUCriticalPrimeLogTransportRadius p : ℝ) := by
  exact Nat.le_ceil _

/-- The literal polar log span on `[p - 1, p + L]` dominates its elementary harmonic fraction.
This contains no primality input and is the capacity identity used by the marked transporter. -/
theorem ccmFUCritical_polarLogSpan_lower {p L : ℕ} (hp : 1 < p) :
    ((L : ℝ) + 1) / ((p + L : ℕ) : ℝ) ≤
      Real.log ((p + L : ℕ) : ℝ) - Real.log ((p - 1 : ℕ) : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_lt_of_lt hp)
  have hpm1 : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < p - 1 by omega)
  have hpL : (0 : ℝ) < ((p + L : ℕ) : ℝ) := by positivity
  have hratio : 0 < ((p + L : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) :=
    div_pos hpL hpm1
  have hlog := Real.one_sub_inv_le_log_of_pos hratio
  have hlogeq : Real.log (((p + L : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ)) =
      Real.log ((p + L : ℕ) : ℝ) - Real.log ((p - 1 : ℕ) : ℝ) :=
    Real.log_div hpL.ne' hpm1.ne'
  have hrewrite : (1 - (((p + L : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ))⁻¹) =
      ((L : ℝ) + 1) / ((p + L : ℕ) : ℝ) := by
    have hpred : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p)]
      norm_num
    push_cast
    rw [hpred]
    field_simp [hpL.ne', hpm1.ne']
    ring
  calc
    ((L : ℝ) + 1) / ((p + L : ℕ) : ℝ) =
        1 - (((p + L : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ))⁻¹ := hrewrite.symm
    _ ≤ Real.log (((p + L : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ)) := hlog
    _ = Real.log ((p + L : ℕ) : ℝ) - Real.log ((p - 1 : ℕ) : ℝ) := hlogeq

/-- A forward marked polar interval whose integer radius is at least `2 log p`, but at most `p`,
has enough literal polar drift to pay the full prime atom at `p`.  This is a local capacity law;
it deliberately makes no claim about other prime atoms inside the same interval. -/
theorem ccmFUCritical_primePolar_capacity_of_twoLogScale
    {p L : ℕ} (hp : 1 < p)
    (hscale : 2 * Real.log (p : ℝ) ≤ (L : ℝ))
    (hupper : L ≤ p) :
    Real.log (p : ℝ) / (p : ℝ) ≤
      Real.log ((p + L : ℕ) : ℝ) - Real.log ((p - 1 : ℕ) : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_lt_of_lt hp)
  have hpL0 : (0 : ℝ) < ((p + L : ℕ) : ℝ) := by positivity
  have hlog0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.le)
  have hpl : ((p + L : ℕ) : ℝ) ≤ 2 * (p : ℝ) := by
    push_cast
    have hupper' : (L : ℝ) ≤ p := by exact_mod_cast hupper
    linarith
  have hscale' : Real.log (p : ℝ) ≤ (L : ℝ) / 2 := by linarith
  have hkey : Real.log (p : ℝ) * ((p + L : ℕ) : ℝ) ≤
      (p : ℝ) * ((L : ℝ) + 1) := by
    calc
      Real.log (p : ℝ) * ((p + L : ℕ) : ℝ) ≤
          (L : ℝ) / 2 * ((p + L : ℕ) : ℝ) := by
            exact mul_le_mul_of_nonneg_right hscale' (by positivity)
      _ ≤
          (L : ℝ) / 2 * (2 * (p : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hpl (by positivity)
      _ = (L : ℝ) * (p : ℝ) := by ring
      _ ≤ (p : ℝ) * ((L : ℝ) + 1) := by nlinarith
  have hfrac : Real.log (p : ℝ) / (p : ℝ) ≤
      ((L : ℝ) + 1) / ((p + L : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hp0 hpL0]
    simpa [mul_comm] using hkey
  exact hfrac.trans (ccmFUCritical_polarLogSpan_lower hp)

/-- Above the first nontrivial source scale, the marked log radius stays inside the allowed
forward range. -/
theorem ccmFUCritical_twoLog_add_one_le_natCast_of_nine_le
    {p : ℕ} (hp : 9 ≤ p) :
    2 * Real.log (p : ℝ) + 1 ≤ (p : ℝ) := by
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 9) hp)
  have hp9 : (9 : ℝ) ≤ p := by exact_mod_cast hp
  have hsqrt0 : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt (p : ℝ) ^ (2 : ℕ) = (p : ℝ) := Real.sq_sqrt hp0.le
  have hsqrt3 : (3 : ℝ) ≤ Real.sqrt (p : ℝ) := by nlinarith
  have hsqrtPos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp0
  have hlogSqrt : Real.log (Real.sqrt (p : ℝ)) ≤ Real.sqrt (p : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hsqrtPos
  have hlog : Real.log (p : ℝ) = 2 * Real.log (Real.sqrt (p : ℝ)) := by
    rw [Real.log_sqrt hp0.le]
    ring
  rw [hlog]
  nlinarith

/-- The explicit marked radius is admissible for every prime-scale source cell. -/
theorem ccmFUCriticalPrimeLogTransportRadius_le
    {p : ℕ} (hp : 9 ≤ p) :
    ccmFUCriticalPrimeLogTransportRadius p ≤ p := by
  unfold ccmFUCriticalPrimeLogTransportRadius
  apply Nat.ceil_le.mpr
  have h := ccmFUCritical_twoLog_add_one_le_natCast_of_nine_le hp
  linarith

/-- Concrete one-prime construction.  A marked prime at `p ≥ 9` can be coupled to its literal
forward polar span at the source-determined radius `ceil (2 log p)` without any estimate of the
remaining prime--polar source. -/
theorem ccmFUCritical_primePolar_capacity_at_logTransportRadius
    {p : ℕ} (hp : 9 ≤ p) :
    Real.log (p : ℝ) / (p : ℝ) ≤
      Real.log ((p + ccmFUCriticalPrimeLogTransportRadius p : ℕ) : ℝ) -
        Real.log ((p - 1 : ℕ) : ℝ) := by
  apply ccmFUCritical_primePolar_capacity_of_twoLogScale
  · omega
  · exact ccmFUCriticalPrimeLogTransportRadius_lower p
  · exact ccmFUCriticalPrimeLogTransportRadius_le hp

/-- Residual signed charge of the marked one-prime/polar coupling. -/
def ccmFUCriticalPrimeLogTransportDebt (p : ℕ) : ℝ :=
  Real.log (p : ℝ) / (p : ℝ) -
    (Real.log ((p + ccmFUCriticalPrimeLogTransportRadius p : ℕ) : ℝ) -
      Real.log ((p - 1 : ℕ) : ℝ))

/-- The constructed marked coupling has nonpositive residual charge. -/
theorem ccmFUCriticalPrimeLogTransportDebt_nonpos
    {p : ℕ} (hp : 9 ≤ p) :
    ccmFUCriticalPrimeLogTransportDebt p ≤ 0 := by
  unfold ccmFUCriticalPrimeLogTransportDebt
  linarith [ccmFUCritical_primePolar_capacity_at_logTransportRadius hp]

end

end RHTower
