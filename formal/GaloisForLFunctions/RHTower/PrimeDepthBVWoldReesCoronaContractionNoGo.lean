import GaloisForLFunctions.RHTower.PrimeDepthBVWoldReesCoronaQuotient

/-!
# Adjacent-depth Rees--corona contraction no-go

The coefficient-generated Rees--corona coupling on the rational-adelic
adjacent-depth edge has an exact scalar attenuation factor

`κ_p = (1 - p⁻¹) (2 - p⁻¹) / (2 log p)`.

For every prime, `0 < κ_p < 1`.  Consequently the local coupling is a strict
contraction for every centered strip grade `|a| ≤ 1`, including every nonzero
off-critical grade.  Local Schur contractivity therefore cannot be the missing
source-geometric selector: annihilation, not contraction, is equivalent to the
zero centered rate.
-/

namespace RHTower

noncomputable section

/-- Exact attenuation of the adjacent-depth rational-adelic Rees--corona edge. -/
def primeDepthBVWoldReesCoronaAdjacentAttenuation
    (p : Nat.Primes) : ℝ :=
  (1 - (p.1 : ℝ)⁻¹) * (2 - (p.1 : ℝ)⁻¹) /
    (2 * Real.log (p.1 : ℝ))

/-- The adjacent-depth Rees coefficient is centered rate times source attenuation. -/
theorem primeDepthBVWoldReesCoronaWeight_adjacent_eq
    (a : ℝ) (p : Nat.Primes) :
    primeDepthBVWoldReesCoronaWeight a
        (ccmRationalAdelicPrimeRelativeXiCellZero p)
        (ccmRationalAdelicPrimeRelativeXiCellOne p) =
      a * primeDepthBVWoldReesCoronaAdjacentAttenuation p := by
  have hp1 : 1 < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
  have hlog : Real.log (p.1 : ℝ) ≠ 0 := (Real.log_pos hp1).ne'
  simp [primeDepthBVWoldReesCoronaWeight,
    primeDepthBVWoldReesCoronaAdjacentAttenuation,
    primeDepthBVWoldConnection,
    ccmRationalAdelicPrimeRelativeXiCellZero,
    ccmRationalAdelicPrimeRelativeXiCellOne,
    primeDepthBVFirstTraceDepthWeight_eq,
    xiGammaEulerPrimitivePrimeDepthLogClock_apply]
  field_simp [hlog]

/-- Every adjacent-depth attenuation factor is strictly positive. -/
theorem primeDepthBVWoldReesCoronaAdjacentAttenuation_pos
    (p : Nat.Primes) :
    0 < primeDepthBVWoldReesCoronaAdjacentAttenuation p := by
  have hp0 : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  have hp1 : 1 < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
  have hq0 : 0 < (p.1 : ℝ)⁻¹ := inv_pos.mpr hp0
  have hq1 : (p.1 : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hp1
  have hlog : 0 < Real.log (p.1 : ℝ) := Real.log_pos hp1
  dsimp [primeDepthBVWoldReesCoronaAdjacentAttenuation]
  exact div_pos
    (mul_pos (sub_pos.mpr hq1) (sub_pos.mpr (by linarith)))
    (mul_pos (by norm_num) hlog)

/-- Source attenuation is always strictly below one. -/
theorem primeDepthBVWoldReesCoronaAdjacentAttenuation_lt_one
    (p : Nat.Primes) :
    primeDepthBVWoldReesCoronaAdjacentAttenuation p < 1 := by
  have hp0 : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  have hp1 : 1 < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
  have hq0 : 0 < (p.1 : ℝ)⁻¹ := inv_pos.mpr hp0
  have hq1 : (p.1 : ℝ)⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hp1
  have hlog : 0 < Real.log (p.1 : ℝ) := Real.log_pos hp1
  have hlogLower :
      1 - (p.1 : ℝ)⁻¹ ≤ Real.log (p.1 : ℝ) := by
    simpa [one_div] using log_ge_one_sub_inv hp0
  have hnum :
      (1 - (p.1 : ℝ)⁻¹) * (2 - (p.1 : ℝ)⁻¹) <
        2 * Real.log (p.1 : ℝ) := by
    calc
      (1 - (p.1 : ℝ)⁻¹) * (2 - (p.1 : ℝ)⁻¹) <
          (1 - (p.1 : ℝ)⁻¹) * 2 := by nlinarith
      _ ≤ 2 * Real.log (p.1 : ℝ) := by nlinarith
  rw [primeDepthBVWoldReesCoronaAdjacentAttenuation,
    div_lt_one (by positivity)]
  exact hnum

/-- The exact source attenuation lies in the open unit interval. -/
theorem primeDepthBVWoldReesCoronaAdjacentAttenuation_mem_Ioo
    (p : Nat.Primes) :
    primeDepthBVWoldReesCoronaAdjacentAttenuation p ∈ Set.Ioo 0 1 :=
  ⟨primeDepthBVWoldReesCoronaAdjacentAttenuation_pos p,
    primeDepthBVWoldReesCoronaAdjacentAttenuation_lt_one p⟩

/-- Every centered strip grade gives a strict local Rees--corona contraction. -/
theorem abs_primeDepthBVWoldReesCoronaWeight_adjacent_lt_one
    {a : ℝ} (ha : |a| ≤ 1) (p : Nat.Primes) :
    |primeDepthBVWoldReesCoronaWeight a
        (ccmRationalAdelicPrimeRelativeXiCellZero p)
        (ccmRationalAdelicPrimeRelativeXiCellOne p)| < 1 := by
  rw [primeDepthBVWoldReesCoronaWeight_adjacent_eq, abs_mul]
  have hk0 :=
    (primeDepthBVWoldReesCoronaAdjacentAttenuation_pos p).le
  have hk1 :=
    primeDepthBVWoldReesCoronaAdjacentAttenuation_lt_one p
  rw [abs_of_nonneg hk0]
  nlinarith [abs_nonneg a]

/-- Adjacent-depth annihilation, unlike contraction, detects exactly zero centered rate. -/
theorem primeDepthBVWoldReesCoronaWeight_adjacent_eq_zero_iff
    (a : ℝ) (p : Nat.Primes) :
    primeDepthBVWoldReesCoronaWeight a
        (ccmRationalAdelicPrimeRelativeXiCellZero p)
        (ccmRationalAdelicPrimeRelativeXiCellOne p) = 0 ↔
      a = 0 := by
  rw [primeDepthBVWoldReesCoronaWeight_adjacent_eq, mul_eq_zero]
  exact or_iff_left
    (ne_of_gt (primeDepthBVWoldReesCoronaAdjacentAttenuation_pos p))

/-- Sharp nonselectivity: every nonzero strip grade gives a nonzero strict contraction. -/
theorem primeDepthBVWoldReesCorona_strictContraction_nonzero_of_strip
    {a : ℝ} (ha : |a| ≤ 1) (ha0 : a ≠ 0) (p : Nat.Primes) :
    |primeDepthBVWoldReesCoronaWeight a
        (ccmRationalAdelicPrimeRelativeXiCellZero p)
        (ccmRationalAdelicPrimeRelativeXiCellOne p)| < 1 ∧
      primeDepthBVWoldReesCoronaWeight a
        (ccmRationalAdelicPrimeRelativeXiCellZero p)
        (ccmRationalAdelicPrimeRelativeXiCellOne p) ≠ 0 := by
  exact ⟨abs_primeDepthBVWoldReesCoronaWeight_adjacent_lt_one ha p,
    (not_congr
      (primeDepthBVWoldReesCoronaWeight_adjacent_eq_zero_iff a p)).mpr ha0⟩

end


end RHTower
