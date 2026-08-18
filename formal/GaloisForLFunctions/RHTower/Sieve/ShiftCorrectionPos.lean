import GaloisForLFunctions.RHTower.Sieve.SiftingDepth

/-!
# The shift correction is positive

The sieve's shift correction is `1 − log H / (log P₁ · P₁)`, where `H` bounds the shifts.  Since
`P₁ = ⌈exp((log x)^{aβ})⌉` grows faster than any power of `log x` while `log H ≍ (log x)^β`, the
correction is at least `1/2` eventually.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- **The shift correction is at least one half.** -/
theorem shiftCorrection_ge_half {β a : ℝ} (hβ0 : 0 < β) (ha0 : 0 < a) :
    ∀ᶠ x : ℝ in atTop,
      (1 : ℝ) / 2 ≤ 1 - Real.log ⌊cardLength β x⌋₊
        / (Real.log ((siftStart (a * β) x : ℕ) : ℝ) * ((siftStart (a * β) x : ℕ) : ℝ)) := by
  have hab : (0 : ℝ) < a * β := by positivity
  have hsmall := tendsto_logLog_div_logRpow hab
  have hbig : Tendsto (fun x : ℝ => (Real.log x) ^ (a * β)) atTop atTop :=
    (tendsto_rpow_atTop hab).comp Real.tendsto_log_atTop
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1),
    Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by positivity : (0 : ℝ) < 1 / (2 * (β + 1))) hsmall,
    hbig.eventually_ge_atTop (2 * (Real.log 2 + 1))] with x hxe hx1 hsm hbg
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hll0 : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg hlog1
  have hpow0 : (0 : ℝ) < (Real.log x) ^ (a * β) := Real.rpow_pos_of_pos hlogx _
  -- `β log log x + log 2 ≤ (log x)^{aβ}`
  have hkey : β * Real.log (Real.log x) + Real.log 2 ≤ (Real.log x) ^ (a * β) := by
    rw [div_le_iff₀ hpow0] at hsm
    have hd : (0 : ℝ) < 2 * (β + 1) := by positivity
    have hnum : Real.log (Real.log x) * (2 * (β + 1)) ≤ (Real.log x) ^ (a * β) := by
      calc Real.log (Real.log x) * (2 * (β + 1))
          ≤ (1 / (2 * (β + 1)) * (Real.log x) ^ (a * β)) * (2 * (β + 1)) :=
            mul_le_mul_of_nonneg_right hsm hd.le
        _ = (Real.log x) ^ (a * β) := by field_simp
    nlinarith [hnum, hbg, hll0, hβ0]
  -- the numerator
  have hnumer : Real.log ((⌊cardLength β x⌋₊ : ℕ) : ℝ) ≤ (Real.log x) ^ β := by
    rcases Nat.eq_zero_or_pos ⌊cardLength β x⌋₊ with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      exact (Real.rpow_pos_of_pos hlogx β).le
    · have hfl : ((⌊cardLength β x⌋₊ : ℕ) : ℝ) ≤ cardLength β x :=
        Nat.floor_le (cardLength_pos β x).le
      have h0R : (0 : ℝ) < ((⌊cardLength β x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hpos
      calc Real.log ((⌊cardLength β x⌋₊ : ℕ) : ℝ) ≤ Real.log (cardLength β x) :=
            Real.log_le_log h0R hfl
        _ = (Real.log x) ^ β := log_cardLength β x
  -- the denominator
  have hP1ge : Real.exp ((Real.log x) ^ (a * β)) ≤ ((siftStart (a * β) x : ℕ) : ℝ) := by
    rw [siftStart]
    exact Nat.le_ceil _
  have hlogP1 : (1 : ℝ) ≤ Real.log ((siftStart (a * β) x : ℕ) : ℝ) := by
    have hstep : (Real.log x) ^ (a * β) ≤ Real.log ((siftStart (a * β) x : ℕ) : ℝ) := by
      calc (Real.log x) ^ (a * β) = Real.log (Real.exp ((Real.log x) ^ (a * β))) :=
            (Real.log_exp _).symm
        _ ≤ Real.log ((siftStart (a * β) x : ℕ) : ℝ) :=
            Real.log_le_log (Real.exp_pos _) hP1ge
    have hge1 : (1 : ℝ) ≤ (Real.log x) ^ (a * β) := by
      have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith [hbg, hl2]
    linarith
  have hden : 2 * (Real.log x) ^ β
      ≤ Real.log ((siftStart (a * β) x : ℕ) : ℝ) * ((siftStart (a * β) x : ℕ) : ℝ) := by
    have hexpβ : (Real.log x) ^ β = Real.exp (β * Real.log (Real.log x)) := by
      rw [Real.rpow_def_of_pos hlogx]
      congr 1
      ring
    have hstep : 2 * (Real.log x) ^ β ≤ Real.exp ((Real.log x) ^ (a * β)) := by
      rw [hexpβ, show (2 : ℝ) = Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm,
        ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith [hkey])
    have hP0 : (0 : ℝ) < ((siftStart (a * β) x : ℕ) : ℝ) := by
      have := Real.exp_pos ((Real.log x) ^ (a * β))
      linarith [hP1ge]
    nlinarith [hstep, hP1ge, hlogP1, hP0]
  have hd0 : (0 : ℝ)
      < Real.log ((siftStart (a * β) x : ℕ) : ℝ) * ((siftStart (a * β) x : ℕ) : ℝ) := by
    have hpowβ : (0 : ℝ) < (Real.log x) ^ β := Real.rpow_pos_of_pos hlogx _
    linarith [hden]
  have hratio : Real.log ((⌊cardLength β x⌋₊ : ℕ) : ℝ)
      / (Real.log ((siftStart (a * β) x : ℕ) : ℝ) * ((siftStart (a * β) x : ℕ) : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hd0 (by norm_num : (0:ℝ) < 2)]
    linarith [hnumer, hden]
  linarith [hratio]

/-- **The shift correction is positive.** -/
theorem shiftCorrection_pos {β a : ℝ} (hβ0 : 0 < β) (ha0 : 0 < a) :
    ∀ᶠ x : ℝ in atTop,
      (0 : ℝ) < 1 - Real.log ⌊cardLength β x⌋₊
        / (Real.log ((siftStart (a * β) x : ℕ) : ℝ) * ((siftStart (a * β) x : ℕ) : ℝ)) := by
  filter_upwards [shiftCorrection_ge_half hβ0 ha0] with x hx
  linarith

end

end RHTower.Sieve
