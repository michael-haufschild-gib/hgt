import GaloisForLFunctions.RHTower.Sieve.GhsParameterReduction

/-!
# The number of scales, and the total error

Two of the remaining hypotheses are bookkeeping.

The number of scales is forced from above by the threshold `2^K·4·log 2 ≤ log N` and from below by
the coverage of the outer range; the largest admissible value is

```text
ghsScaleCount N := Nat.log 2 ⌊(log N)/(4 log 2)⌋ ,
```

for which `2^K ≤ (log N)/(4 log 2)` holds by `Nat.pow_log_le_self`, and hence `4^K ≤ ((log N)/(4 log 2))²`
— the form the height inequality consumes.

The three error levels are all explicit, so their common upper bound is simply their maximum:

```text
ghsTotalError N n K σ := max (uniform Perron error) (max (small-block bound) (top-block bound)) ,
```

and with it the mean value has no error hypothesis at all.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- The number of geometric scales the threshold permits. -/
def ghsScaleCount (N : ℕ) : ℕ := Nat.log 2 ⌊Real.log N / (4 * Real.log 2)⌋₊

/-- **The scale count meets the threshold.** -/
theorem two_pow_ghsScaleCount_le {N : ℕ} (hN : 16 ≤ N) :
    (2 : ℝ) ^ ghsScaleCount N * (4 * Real.log 2) ≤ Real.log N := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hNR : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog16 : Real.log 16 ≤ Real.log N := Real.log_le_log (by norm_num) hNR
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have hratio : (1 : ℝ) ≤ Real.log N / (4 * Real.log 2) := by
    rw [le_div_iff₀ (by positivity)]
    rw [h16] at hlog16
    linarith
  have hm : 1 ≤ ⌊Real.log N / (4 * Real.log 2)⌋₊ := Nat.le_floor (by exact_mod_cast hratio)
  have hpow : (2 : ℕ) ^ ghsScaleCount N ≤ ⌊Real.log N / (4 * Real.log 2)⌋₊ :=
    Nat.pow_log_le_self 2 (by omega)
  have hpowR : (2 : ℝ) ^ ghsScaleCount N ≤ (⌊Real.log N / (4 * Real.log 2)⌋₊ : ℝ) := by
    exact_mod_cast hpow
  have hfloor : ((⌊Real.log N / (4 * Real.log 2)⌋₊ : ℕ) : ℝ)
      ≤ Real.log N / (4 * Real.log 2) := Nat.floor_le (by linarith)
  rw [← le_div_iff₀ (by positivity)]
  linarith [hpowR, hfloor]

/-- **The scale count's fourth power, in the form the height inequality consumes.** -/
theorem four_pow_ghsScaleCount_le {N : ℕ} (hN : 16 ≤ N) :
    (4 : ℝ) ^ ghsScaleCount N ≤ (Real.log N / (4 * Real.log 2)) ^ 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hbase := two_pow_ghsScaleCount_le hN
  have hle : (2 : ℝ) ^ ghsScaleCount N ≤ Real.log N / (4 * Real.log 2) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ ghsScaleCount N := by positivity
  have heq : (4 : ℝ) ^ ghsScaleCount N = ((2 : ℝ) ^ ghsScaleCount N) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [heq]
  exact pow_le_pow_left₀ h0 hle 2

/-- The common upper bound for the three error levels. -/
def ghsTotalError (N n K : ℕ) (σ : ℝ) : ℝ :=
  max (ghsUniformError N n σ)
    (max ((N : ℝ) * (((Real.log ((n ^ 2 : ℕ) : ℝ) + Real.log 4)
              / Real.log ((N / n ^ 2 : ℕ) : ℝ)) * (Real.log N + Real.log 4)))
      ((N : ℝ) * (((1 / Real.log 2)
              * (Real.log (N : ℝ) - Real.log ((ghsPart N n (K + 1) : ℕ) : ℝ)
                  + mertensBlockGapConst))
            * (Real.log ((N / ghsPart N n (K + 1) : ℕ) : ℝ) + Real.log 4))))

/-- **The mean value with the error levels discharged.** -/
theorem norm_sum_Icc_le_ghs_total
    {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hcm : ∀ p q : ℕ, f (p * q) = f p * f q)
    (hf : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {N n z K : ℕ} {σ δ : ℝ} (hσ : 1 < σ) (hz : 1 ≤ z) (hδ : 0 ≤ δ)
    (hunif : ∀ y : ℝ, |y| ≤ (n : ℝ) →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn y) (Nat.primesLE z)))
    (hn : 1 ≤ n) (hne : Real.exp 4 ≤ (n : ℝ)) (hN : 2 ≤ N)
    (hPN : n ^ 2 ≤ N) (hNP : 2 ≤ N / n ^ 2)
    (hroot : n ^ 2 ≤ ghsScale N 1)
    (hK : (2 : ℝ) ^ K * (4 * Real.log 2) ≤ Real.log N)
    (hheightK : (5 / (4 * (n : ℝ))) * ((16 / 9) * 4 ^ K * (Real.log N + Real.log 4))
        ≤ 1750 * ghsShapeConst) :
    ‖∑ m ∈ Finset.Icc 1 N, f m‖
      ≤ (ghsRecursionError N
            + ((K + 2 : ℕ) : ℝ)
              * (ghsTotalError N n K σ + (1 / (2 * Real.pi))
                  * (dampedSize σ δ z N * ((N : ℝ) + 1 / 2) ^ σ
                      * ghsBlockConstOf σ ghsShapeConst))) / Real.log (N : ℝ) :=
  norm_sum_Icc_le_ghs_reduced hf1 hmul hcm hf hσ hz hδ hunif hn hne hN hPN hNP hroot hK
    hheightK (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_right _ _) (le_max_right _ _))

end RHTower.Sieve

end
