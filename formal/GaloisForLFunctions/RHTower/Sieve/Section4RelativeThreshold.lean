import GaloisForLFunctions.RHTower.Sieve.Section4ExceptionalMeasure

/-!
# The moment-method measure bound at a relative threshold

Matomäki–Radziwiłł's exceptional half thresholds the prime polynomial at a *polylogarithmic
fraction* of its trivial size, not at an absolute level.  Writing the level as `#B·θ` turns the
moment bound of `Sieve/Section4ExceptionalMeasure` into

```text
   |{|P| ≥ #B·θ}|  ≤  2(T + 4N^k(1 + log N^k))·(k/(#B·θ²))^k ,
```

whose whole content is the ratio `k/(#B·θ²)`: the moment order against the size of the block
discounted by the square of the threshold fraction.  For a block of primes near `P'` with
`log P' = (log x)^{49/50}`, the moment order `k ≈ log T/log P' = (log x)^{1/50}/2` and a threshold
`θ = (log x)^{-100}` give a measure `exp((log x)^{1/50+o(1)})` — the exponent is small because the
*threshold* is only polylogarithmic, not because the moment order is large.  That is the step a
range confined to `[1,h]` cannot perform.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **Lemma 2.5 at a relative threshold.** -/
theorem volume_blockExceptional_le_relative {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {NA k : ℕ}
    (hk : 1 ≤ k) {T θ : ℝ} (hT : 0 ≤ T) (hθ : 0 < θ) (hcard : 0 < (B.card : ℝ)) :
    volume.real (blockExceptional B moebiusCoeff NA T ((B.card : ℝ) * θ))
      ≤ 2 * (T + 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ)))
          * ((k : ℝ) / ((B.card : ℝ) * θ ^ 2)) ^ k := by
  have hV : (0 : ℝ) < (B.card : ℝ) * θ := by positivity
  have hbase := volume_blockExceptional_le (B := B) (NA := NA) (k := k) hB hk hT hV
  refine hbase.trans (le_of_eq ?_)
  have hpow : ((B.card : ℝ) * θ) ^ (2 * k) = ((B.card : ℝ)) ^ k * ((B.card : ℝ)) ^ k
      * (θ ^ 2) ^ k := by
    rw [mul_pow]
    ring
  have hne1 : ((B.card : ℝ)) ^ k ≠ 0 := by positivity
  have hne2 : (θ ^ 2) ^ k ≠ 0 := by positivity
  rw [hpow, div_pow, mul_pow]
  field_simp

/-- **The same bound in exponential form.**  The saving is `exp(−k·log(#B·θ²/k))`: the moment order
times the logarithm of the block size discounted by the square of the threshold fraction. -/
theorem volume_blockExceptional_le_exp {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {NA k : ℕ}
    (hk : 1 ≤ k) {T θ : ℝ} (hT : 0 ≤ T) (hθ : 0 < θ) (hcard : 0 < (B.card : ℝ)) :
    volume.real (blockExceptional B moebiusCoeff NA T ((B.card : ℝ) * θ))
      ≤ 2 * (T + 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ)))
          * Real.exp (-((k : ℝ) * Real.log (((B.card : ℝ) * θ ^ 2) / (k : ℝ)))) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hden : (0 : ℝ) < (B.card : ℝ) * θ ^ 2 := by positivity
  have hratio : (0 : ℝ) < (k : ℝ) / ((B.card : ℝ) * θ ^ 2) := by positivity
  refine (volume_blockExceptional_le_relative hB hk hT hθ hcard).trans (le_of_eq ?_)
  congr 1
  have hexp : ((k : ℝ) / ((B.card : ℝ) * θ ^ 2)) ^ k
      = Real.exp ((k : ℝ) * Real.log ((k : ℝ) / ((B.card : ℝ) * θ ^ 2))) := by
    rw [← Real.rpow_natCast ((k : ℝ) / ((B.card : ℝ) * θ ^ 2)) k,
      Real.rpow_def_of_pos hratio]
    ring_nf
  rw [hexp]
  congr 1
  have hlog : Real.log ((k : ℝ) / ((B.card : ℝ) * θ ^ 2))
      = -Real.log (((B.card : ℝ) * θ ^ 2) / (k : ℝ)) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  rw [hlog]
  ring

end

end RHTower.Sieve
