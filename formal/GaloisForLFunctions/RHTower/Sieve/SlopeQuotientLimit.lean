import GaloisForLFunctions.RHTower.Sieve.RhoLimit
import GaloisForLFunctions.RHTower.Sieve.LadderAffineBounds
import GaloisForLFunctions.RHTower.Sieve.PolyDecayLimits
import GaloisForLFunctions.RHTower.Sieve.EnergyQuotientLimit

/-!
# The ladder slope, normalised

The affine slope of the ladder majorant is negligible against the product of the fibre range, the
window length and the squared harmonic mass.  Two mechanisms combine: the annulus bound against the
number of steps, and the polynomial cofactor against the two exponential scales.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The annulus bound of the ladder is nonnegative. -/
theorem eventually_budgetRho_nonneg {A delta Ctot β γ : ℝ} (hβ0 : 0 < β) (hCtot : 0 ≤ Ctot) :
    ∀ᶠ x : ℝ in atTop, 0 ≤ budgetRho A delta Ctot β γ x := by
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), eventually_ladderWidth_ge hβ0,
    (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ)] with x hx1 hD hh1
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hD0 : (0 : ℝ) < ladderWidth β x := lt_of_lt_of_le (by positivity) hD
  have hw₀ : (0 : ℝ) < 2 * Real.pi * annulusStart β x := by
    have : (0 : ℝ) < annulusStart β x := by
      rw [annulusStart]; exact Real.rpow_pos_of_pos hlogx _
    positivity
  have hB : Real.sqrt x ≤ ((budgetB β x : ℕ) : ℝ) := sqrt_le_budgetB (β := β) x hh1
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hB0 : (0 : ℝ) < ((budgetB β x : ℕ) : ℝ) := by linarith
  have hQ0 : (0 : ℝ) < ((siftStart (γ * β) x : ℕ) : ℝ) := by
    have h1 : (1 : ℕ) ≤ siftStart (γ * β) x := Nat.one_le_ceil_iff.2 (Real.exp_pos _)
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
  have hHm : (0 : ℝ) ≤ budgetHmaj A β x := by
    rw [budgetHmaj]
    have h1 : (0 : ℝ) ≤ 1 / (2 * Real.pi * annulusStart β x) := by positivity
    have h2 : (0 : ℝ) ≤ Real.log (3 * (2 * Real.pi * budgetT β x) / 2)
        / routeTWidthPolylogLower A (2 * Real.pi * budgetT β x) := by
      refine div_nonneg ?_ (routeTWidthPolylogLower_pos A _).le
      refine Real.log_nonneg ?_
      rw [budgetT]
      have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hB1 : (1 : ℝ) ≤ ((budgetB β x : ℕ) : ℝ) :=
        Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hB0.ne'))
      nlinarith [hB1, hpi]
    linarith
  have hR0 : (0 : ℝ) ≤ relScaledMajorant Ctot (ladderWidth β x) ((Real.log x) ^ β)
      (budgetHmaj A β x) (budgetMu A delta β x) (Real.log ((siftStart (γ * β) x : ℕ) : ℝ))
      (2 * Real.pi * annulusStart β x) ((siftStart (γ * β) x : ℕ) : ℝ) :=
    relScaledMajorant_nonneg hCtot hD0 (Real.rpow_nonneg hlogx.le β) hHm hw₀ hQ0
  have hη : 0 < ladderEta β γ x := ladderEta_pos hx1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [budgetRho, ladderRho]
  have h7 : (0 : ℝ) ≤ 7 * Real.exp 9 / ((siftStart (γ * β) x : ℕ) : ℝ) := by positivity
  have hmul : (0 : ℝ) ≤ (1 + ladderEta β γ x)
      * relScaledMajorant Ctot (ladderWidth β x) ((Real.log x) ^ β) (budgetHmaj A β x)
          (budgetMu A delta β x) (Real.log ((siftStart (γ * β) x : ℕ) : ℝ))
          (2 * Real.pi * annulusStart β x) ((siftStart (γ * β) x : ℕ) : ℝ) :=
    mul_nonneg (by linarith) hR0
  have hsum : (0 : ℝ) ≤ (1 + ladderEta β γ x)
      * relScaledMajorant Ctot (ladderWidth β x) ((Real.log x) ^ β) (budgetHmaj A β x)
          (budgetMu A delta β x) (Real.log ((siftStart (γ * β) x : ℕ) : ℝ))
          (2 * Real.pi * annulusStart β x) ((siftStart (γ * β) x : ℕ) : ℝ)
      + 7 * Real.exp 9 / ((siftStart (γ * β) x : ℕ) : ℝ) := by linarith
  have hfac : (0 : ℝ) ≤ 4 / Real.log 2 := by positivity
  exact mul_nonneg hfac hsum

/-- The fibre range does not exceed twice the square root of the outer scale. -/
theorem eventually_budgetB_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop, ((budgetB β x : ℕ) : ℝ) ≤ 2 * Real.sqrt x := by
  have hratio := tendsto_cardLength_div_budgetB hβ0 hβ1
  have hmaj : Tendsto (fun x : ℝ => cardLength β x / Real.sqrt x) atTop (𝓝 0) := by
    have hsq := tendsto_cardLength_sq_div_sqrt hβ0 hβ1
    refine squeeze_zero' ?_ ?_ hsq
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
      have := Real.sqrt_pos.2 hx
      have := cardLength_pos β x
      positivity
    · filter_upwards [(tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
        Filter.eventually_gt_atTop (0 : ℝ)] with x hh1 hx
      have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
      rw [div_le_div_iff₀ hsx hsx]
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ cardLength β x)
        (by linarith : (0:ℝ) ≤ cardLength β x - 1)) hsx.le]
  filter_upwards [Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1) hmaj,
    Filter.eventually_gt_atTop (0 : ℝ)] with x hsmall hx
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
  have hh : cardLength β x ≤ Real.sqrt x := by
    rw [div_le_one hsx] at hsmall
    exact hsmall
  rw [budgetB]
  have := Nat.floor_le (by
    have := Real.sqrt_nonneg x
    have := (cardLength_pos β x).le
    linarith : (0:ℝ) ≤ Real.sqrt x + cardLength β x)
  linarith

/-- The cofactor's logarithmic ratio, in powers of the logarithm. -/
theorem eventually_cofactor_ratio_le {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγβ : γ * β < 1) :
    ∀ᶠ x : ℝ in atTop,
      Real.log ((⌊((budgetB β x : ℕ) : ℝ) * (1 + ladderEta β γ x)⌋₊ : ℕ) : ℝ)
          / Real.log ((siftStart (γ * β) x : ℕ) : ℝ)
        ≤ (Real.log x) ^ (1 - γ * β) := by
  have hab : (0 : ℝ) < γ * β := mul_pos hγ0 hβ0
  have hpowA : Tendsto (fun x : ℝ => (Real.log x) ^ (γ * β)) atTop atTop :=
    (tendsto_rpow_atTop hab).comp Real.tendsto_log_atTop
  have hzero := tendsto_ladderEta (β := β) (γ := γ) hβ0 hγβ
  filter_upwards [eventually_budgetB_le hβ0 hβ1, Filter.eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.log 4),
    Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1) hzero,
    (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
    hpowA.eventually_gt_atTop (0 : ℝ)] with x hB2 hx1 hlog4 hη1 hh1 hA0
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hη : 0 < ladderEta β γ x := ladderEta_pos hx1
  have hB : Real.sqrt x ≤ ((budgetB β x : ℕ) : ℝ) := sqrt_le_budgetB (β := β) x hh1
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hB0 : (1 : ℝ) ≤ ((budgetB β x : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ Real.sqrt x := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by linarith)
    linarith
  -- the numerator
  have hfl : (((⌊((budgetB β x : ℕ) : ℝ) * (1 + ladderEta β γ x)⌋₊ : ℕ) : ℝ))
      ≤ 4 * Real.sqrt x := by
    have := Nat.floor_le (by nlinarith [hB0, hη] :
      (0:ℝ) ≤ ((budgetB β x : ℕ) : ℝ) * (1 + ladderEta β γ x))
    nlinarith [this, hB2, hη1, hsx]
  have hfl1 : (1 : ℝ) ≤ (((⌊((budgetB β x : ℕ) : ℝ) * (1 + ladderEta β γ x)⌋₊ : ℕ) : ℝ)) := by
    have h1 : (1 : ℕ) ≤ ⌊((budgetB β x : ℕ) : ℝ) * (1 + ladderEta β γ x)⌋₊ := by
      refine Nat.one_le_floor_iff _ |>.2 ?_
      nlinarith [hB0, hη]
    exact_mod_cast h1
  have hnum : Real.log ((⌊((budgetB β x : ℕ) : ℝ) * (1 + ladderEta β γ x)⌋₊ : ℕ) : ℝ)
      ≤ Real.log x := by
    have hstep : Real.log ((⌊((budgetB β x : ℕ) : ℝ) * (1 + ladderEta β γ x)⌋₊ : ℕ) : ℝ)
        ≤ Real.log (4 * Real.sqrt x) := Real.log_le_log (by linarith) hfl
    have hval : Real.log (4 * Real.sqrt x) = Real.log 4 + Real.log x / 2 := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hsx), Real.log_sqrt (by linarith)]
    have hl4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    linarith [hstep, hval, hlog4]
  have hden : (Real.log x) ^ (γ * β) ≤ Real.log ((siftStart (γ * β) x : ℕ) : ℝ) :=
    log_siftStart_ge (γ * β) x
  have hratio : Real.log ((⌊((budgetB β x : ℕ) : ℝ) * (1 + ladderEta β γ x)⌋₊ : ℕ) : ℝ)
        / Real.log ((siftStart (γ * β) x : ℕ) : ℝ)
      ≤ Real.log x / (Real.log x) ^ (γ * β) :=
    div_le_div₀ hlogx.le hnum hA0 hden
  have hval : Real.log x / (Real.log x) ^ (γ * β) = (Real.log x) ^ (1 - γ * β) := by
    rw [Real.rpow_sub hlogx, Real.rpow_one]
  linarith [hratio, hval]

end

end RHTower.Sieve

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The step ratio squared against the number of steps. -/
theorem eventually_steps_eta_sq_le {β γ : ℝ} (hβ0 : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ * β < 1) :
    ∀ᶠ x : ℝ in atTop,
      ((ladderSteps β γ x : ℕ) : ℝ) * (ladderEta β γ x) ^ 2
        ≤ 2 * (Real.log x) ^ (γ * β - 1) := by
  filter_upwards [ladderSteps_le hβ0 hγ0 hγ1 hγβ, Filter.eventually_gt_atTop (1 : ℝ)]
    with x hL hx1
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hη : 0 < ladderEta β γ x := ladderEta_pos hx1
  have hstep : ((ladderSteps β γ x : ℕ) : ℝ) * (ladderEta β γ x) ^ 2
      ≤ (2 * (Real.log x) ^ β / ladderEta β γ x) * (ladderEta β γ x) ^ 2 :=
    mul_le_mul_of_nonneg_right hL (sq_nonneg _)
  refine hstep.trans (le_of_eq ?_)
  have hid : (2 * (Real.log x) ^ β / ladderEta β γ x) * (ladderEta β γ x) ^ 2
      = 2 * (Real.log x) ^ β * ladderEta β γ x := by
    field_simp
  rw [hid, ladderEta, mul_assoc, ← Real.rpow_add hlogx]
  congr 2
  ring

/-- The reciprocal step ratio, in powers of the logarithm. -/
theorem inv_ladderEta_eq {β γ x : ℝ} (hx1 : 1 < x) :
    1 / ladderEta β γ x = (Real.log x) ^ (β + 1 - γ * β) := by
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  rw [ladderEta, one_div, ← Real.rpow_neg hlogx.le]
  congr 1
  ring

/-- The explicit majorant of the normalised ladder slope. -/
def slopeMajorant (A delta Ctot β γ x : ℝ) : ℝ :=
  20 * Real.pi * (budgetRhoBound A delta Ctot β γ x * ((ladderSteps β γ x : ℕ) : ℝ)) ^ 2
      * (1 + 4 * (cardLength β x / ((budgetB β x : ℕ) : ℝ)))
    + 5 * Real.pi * (4 * (1 / cardLength β x)
        + 10 * ((Real.log x) ^ (2 * β + 2 - 2 * (γ * β)) / Real.sqrt x)
        + 5 * ((Real.log x) ^ (1 - γ * β) / Real.sqrt x)
        + 6 * ((Real.log x) ^ (1 - γ * β) / cardLength β x)
        + 2 * ((Real.log x) ^ (β + 2 - 2 * (γ * β)) / cardLength β x))

/-- **The majorant of the normalised ladder slope vanishes.** -/
theorem tendsto_slopeMajorant {A delta Ctot β γ : ℝ} (hβ0 : 9 / 10 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hγβ0 : 9 / 10 < γ * β) (hγβ1 : γ * β < 1) (hCtot : 0 ≤ Ctot)
    (hdelta : 0 < delta) :
    Tendsto (fun x : ℝ => slopeMajorant A delta Ctot β γ x) atTop (𝓝 0) := by
  have hβ0' : (0 : ℝ) < β := by linarith
  have hsq : Tendsto (fun x : ℝ =>
      (budgetRhoBound A delta Ctot β γ x * ((ladderSteps β γ x : ℕ) : ℝ)) ^ 2) atTop (𝓝 0) := by
    have h := tendsto_budgetRho_mul_steps (A := A) (delta := delta) (Ctot := Ctot)
      hβ0 hβ1 hγ0 hγ1 hγβ0 hγβ1 hCtot hdelta
    simpa using h.pow 2
  have hone : Tendsto (fun x : ℝ => 1 + 4 * (cardLength β x / ((budgetB β x : ℕ) : ℝ)))
      atTop (𝓝 1) := by
    have h := (tendsto_cardLength_div_budgetB hβ0' hβ1).const_mul (4 : ℝ)
    have := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).add h
    simpa using this
  have hfirst : Tendsto (fun x : ℝ =>
      20 * Real.pi * (budgetRhoBound A delta Ctot β γ x * ((ladderSteps β γ x : ℕ) : ℝ)) ^ 2
        * (1 + 4 * (cardLength β x / ((budgetB β x : ℕ) : ℝ)))) atTop (𝓝 0) := by
    have h := (hsq.const_mul (20 * Real.pi)).mul hone
    simpa using h
  have h1 := (tendsto_rpow_log_div_cardLength (β := β) hβ0' 0)
  have h1' : Tendsto (fun x : ℝ => 1 / cardLength β x) atTop (𝓝 0) :=
    tendsto_inv_cardLength hβ0'
  have h2 := tendsto_rpow_log_div_sqrt (2 * β + 2 - 2 * (γ * β))
  have h3 := tendsto_rpow_log_div_sqrt (1 - γ * β)
  have h4 := tendsto_rpow_log_div_cardLength (β := β) hβ0' (1 - γ * β)
  have h5 := tendsto_rpow_log_div_cardLength (β := β) hβ0' (β + 2 - 2 * (γ * β))
  have hsecond : Tendsto (fun x : ℝ =>
      5 * Real.pi * (4 * (1 / cardLength β x)
        + 10 * ((Real.log x) ^ (2 * β + 2 - 2 * (γ * β)) / Real.sqrt x)
        + 5 * ((Real.log x) ^ (1 - γ * β) / Real.sqrt x)
        + 6 * ((Real.log x) ^ (1 - γ * β) / cardLength β x)
        + 2 * ((Real.log x) ^ (β + 2 - 2 * (γ * β)) / cardLength β x))) atTop (𝓝 0) := by
    have hsum := ((((h1'.const_mul (4:ℝ)).add (h2.const_mul (10:ℝ))).add
      (h3.const_mul (5:ℝ))).add (h4.const_mul (6:ℝ))).add (h5.const_mul (2:ℝ))
    have := hsum.const_mul (5 * Real.pi)
    simpa using this
  have := hfirst.add hsecond
  simpa [slopeMajorant] using this

end

end RHTower.Sieve
