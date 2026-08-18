import GaloisForLFunctions.RHTower.Sieve.SiftingRangeTop
import GaloisForLFunctions.RHTower.Sieve.LogPowerLimits

/-!
# The sieve saving of the chosen sifting range

The density of the integers free of primes in `(P₁, hN]` is governed by `log P₁ / log hN`.  For
`P₁ = ⌈exp((log x)^{aβ})⌉` and `hN = ⌊exp((log x)^β)⌋` this ratio is `≍ (log x)^{−β(1−a)}`, hence
vanishes for every `a < 1`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- **The top of the sifting range has a logarithm of the expected size.** -/
theorem log_siftTop_ge {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ β - Real.log 2 ≤ Real.log ((siftTop β x : ℕ) : ℝ) := by
  have hpow : Tendsto (fun x : ℝ => (Real.log x) ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp Real.tendsto_log_atTop
  filter_upwards [eventually_le_siftTop hβ 2, hpow.eventually_ge_atTop (Real.log 2)] with x hN2 _
  have hfl : cardLength β x - 1 ≤ ((siftTop β x : ℕ) : ℝ) := by
    rw [siftTop]
    have := Nat.lt_floor_add_one (cardLength β x)
    linarith
  have hN2R : (2 : ℝ) ≤ ((siftTop β x : ℕ) : ℝ) := by exact_mod_cast hN2
  have hup : ((siftTop β x : ℕ) : ℝ) ≤ cardLength β x := by
    rw [siftTop]
    exact Nat.floor_le (cardLength_pos β x).le
  have hc2 : (2 : ℝ) ≤ cardLength β x := by linarith
  have hhalf : cardLength β x / 2 ≤ ((siftTop β x : ℕ) : ℝ) := by linarith
  have hlog : Real.log (cardLength β x / 2) ≤ Real.log ((siftTop β x : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) hhalf
  rwa [Real.log_div (ne_of_gt (cardLength_pos β x)) (by norm_num), log_cardLength] at hlog

/-- The sieve saving of the chosen range. -/
def siftRatio (a β x : ℝ) : ℝ :=
  Real.log ((siftStart (a * β) x : ℕ) : ℝ) / Real.log ((siftTop β x : ℕ) : ℝ)

theorem siftRatio_nonneg {a β : ℝ} (hβ : 0 < β) (ha0 : 0 < a) :
    ∀ᶠ x : ℝ in atTop, 0 ≤ siftRatio a β x := by
  have hpow : Tendsto (fun x : ℝ => (Real.log x) ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp Real.tendsto_log_atTop
  filter_upwards [log_siftTop_ge hβ, hpow.eventually_ge_atTop (Real.log 2 + 1),
    eventually_le_siftStart (mul_pos ha0 hβ) 1] with x hT hbig hS
  have hS1 : (1 : ℝ) ≤ ((siftStart (a * β) x : ℕ) : ℝ) := by exact_mod_cast hS
  refine div_nonneg (Real.log_nonneg hS1) ?_
  linarith [hT]

/-- **The sieve saving vanishes.** -/
theorem tendsto_siftRatio {a β : ℝ} (hβ : 0 < β) (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun x : ℝ => siftRatio a β x) atTop (𝓝 0) := by
  have hδ : (0 : ℝ) < β * (1 - a) := by
    have : (0 : ℝ) < 1 - a := by linarith
    positivity
  have hmaj : Tendsto (fun x : ℝ => 4 * (Real.log x) ^ (-(β * (1 - a)))) atTop (𝓝 0) := by
    have := (tendsto_log_rpow_neg hδ).const_mul (4 : ℝ)
    simpa using this
  have hpowB : Tendsto (fun x : ℝ => (Real.log x) ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp Real.tendsto_log_atTop
  have hpowA : Tendsto (fun x : ℝ => (Real.log x) ^ (a * β)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp Real.tendsto_log_atTop
  refine squeeze_zero' (siftRatio_nonneg hβ ha0) ?_ hmaj
  filter_upwards [log_siftTop_ge hβ, log_siftStart_le (mul_pos ha0 hβ),
    hpowB.eventually_ge_atTop (2 * Real.log 2), hpowA.eventually_ge_atTop (Real.log 2),
    Filter.eventually_gt_atTop (1 : ℝ)] with x hT hS hbigB hbigA hx1
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpowB0 : (0 : ℝ) < (Real.log x) ^ β := Real.rpow_pos_of_pos hlogx _
  have hden : (Real.log x) ^ β / 2 ≤ Real.log ((siftTop β x : ℕ) : ℝ) := by linarith
  have hden0 : (0 : ℝ) < (Real.log x) ^ β / 2 := by linarith
  have hnum : Real.log ((siftStart (a * β) x : ℕ) : ℝ) ≤ 2 * (Real.log x) ^ (a * β) := by
    linarith [hS, hbigA]
  have hnum0 : (0 : ℝ) ≤ 2 * (Real.log x) ^ (a * β) := by
    have := Real.rpow_pos_of_pos hlogx (a * β)
    linarith
  have hstep : siftRatio a β x ≤ (2 * (Real.log x) ^ (a * β)) / ((Real.log x) ^ β / 2) := by
    rw [siftRatio]
    exact div_le_div₀ hnum0 hnum hden0 hden
  refine hstep.trans (le_of_eq ?_)
  have hsplit : (Real.log x) ^ (a * β) / (Real.log x) ^ β
      = (Real.log x) ^ (-(β * (1 - a))) := by
    rw [← Real.rpow_sub hlogx]
    congr 1
    ring
  have hrw : (2 * (Real.log x) ^ (a * β)) / ((Real.log x) ^ β / 2)
      = 4 * ((Real.log x) ^ (a * β) / (Real.log x) ^ β) := by
    field_simp
    ring
  rw [hrw, hsplit]

end

end RHTower.Sieve
