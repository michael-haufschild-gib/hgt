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
        ≤ 2 * (Real.log x) ^ (γ * β - 5 / 4) := by
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
    1 / ladderEta β γ x = (Real.log x) ^ (β + 5 / 4 - γ * β) := by
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

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The arithmetic of the normalised ladder slope: the annulus group collapses to the step product,
and the cofactor group to five polynomial quotients. -/
theorem slope_quotient_arith {L B Q η ρ R h W M S sx MB P1 P2 P3 : ℝ}
    (hQ1 : 1 < Q) (hη : 0 < η) (hL1 : 1 ≤ L) (hB1 : 1 ≤ B) (hh1 : 1 ≤ h)
    (hW2 : 1 ≤ W ^ 2) (hρ0 : 0 ≤ ρ) (hρR : ρ ≤ R) (hinvη : 1 / η ≤ 2 * L)
    (hsx : 0 < sx) (hsxB : sx ≤ B) (hM0 : 0 ≤ M) (hMB : M ≤ MB) (hMB0 : 0 ≤ MB)
    (hLη : L * η ^ 2 ≤ 2 * P1) (hLpoly : L ≤ 2 * P2) (hinvηP : 1 / η ≤ P3)
    (hSdef : S = L * ((1 + B) * η ^ 2 + 5) + 5 * h
      + (η * B + (1 + B) * η) * (2 / (Q * η)) + B * (2 / (Q ^ 2 * η))) :
    (4 * (5 * Real.pi / 2) * ρ ^ 2 * (2 * (L * Real.sqrt (B * h)) ^ 2 + 2 * (h / η) ^ 2)
        + 2 * (5 * Real.pi / 2) * (M * S)) / (B * h * W ^ 2)
      ≤ 20 * Real.pi * (R * L) ^ 2 * (1 + 4 * (h / B))
        + 5 * Real.pi * (4 * (MB * P1 / h) + 10 * (MB * P2 / sx) + 5 * (MB / sx)
          + 6 * (MB / h) + 2 * (MB * P3 / h)) := by
  have hh0 : (0 : ℝ) < h := by linarith
  have hB0 : (0 : ℝ) < B := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hBh : (0 : ℝ) < B * h := mul_pos hB0 hh0
  have hW20 : (0 : ℝ) < W ^ 2 := by linarith
  have hQη : (0 : ℝ) < Q * η := mul_pos hQ0 hη
  have hQ2η : (0 : ℝ) < Q ^ 2 * η := mul_pos (pow_pos hQ0 2) hη
  have hpi0 : (0 : ℝ) ≤ 20 * Real.pi := by positivity
  have hS0 : (0 : ℝ) ≤ S := by
    have h1 : (0 : ℝ) ≤ L * ((1 + B) * η ^ 2 + 5) :=
      mul_nonneg (by linarith) (by
        have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 + B) (sq_nonneg η)
        linarith)
    have h2 : (0 : ℝ) ≤ (η * B + (1 + B) * η) * (2 / (Q * η)) :=
      mul_nonneg (add_nonneg (mul_nonneg hη.le (by linarith))
        (mul_nonneg (by linarith) hη.le)) (div_nonneg (by norm_num) hQη.le)
    have h3 : (0 : ℝ) ≤ B * (2 / (Q ^ 2 * η)) :=
      mul_nonneg (by linarith) (div_nonneg (by norm_num) hQ2η.le)
    rw [hSdef]; linarith
  rw [add_div]
  have hhB : (0 : ℝ) ≤ h / B := div_nonneg hh0.le hB0.le
  have hgroup1 : 4 * (5 * Real.pi / 2) * ρ ^ 2
        * (2 * (L * Real.sqrt (B * h)) ^ 2 + 2 * (h / η) ^ 2) / (B * h * W ^ 2)
      ≤ 20 * Real.pi * (R * L) ^ 2 * (1 + 4 * (h / B)) := by
    have hsq : (L * Real.sqrt (B * h)) ^ 2 = L ^ 2 * (B * h) := by
      rw [mul_pow, Real.sq_sqrt hBh.le]
    rw [hsq]
    have hid : 4 * (5 * Real.pi / 2) * ρ ^ 2 * (2 * (L ^ 2 * (B * h)) + 2 * (h / η) ^ 2)
          / (B * h * W ^ 2)
        = 20 * Real.pi * (ρ * L) ^ 2 / W ^ 2
          + 20 * Real.pi * (ρ * (1 / η)) ^ 2 * (h / B) / W ^ 2 := by
      field_simp
      ring
    rw [hid]
    have hρL0 : (0 : ℝ) ≤ ρ * L := mul_nonneg hρ0 (by linarith)
    have hρLR : ρ * L ≤ R * L := mul_le_mul_of_nonneg_right hρR (by linarith)
    have hρL : (ρ * L) ^ 2 ≤ (R * L) ^ 2 := pow_le_pow_left₀ hρL0 hρLR 2
    have hη0 : (0 : ℝ) ≤ ρ * (1 / η) := mul_nonneg hρ0 (div_nonneg zero_le_one hη.le)
    have hρη : (ρ * (1 / η)) ^ 2 ≤ 4 * (R * L) ^ 2 := by
      have h1 : ρ * (1 / η) ≤ 2 * (R * L) := by
        have hstep : ρ * (1 / η) ≤ ρ * (2 * L) := mul_le_mul_of_nonneg_left hinvη hρ0
        have he : ρ * (2 * L) = 2 * (ρ * L) := by ring
        linarith [hstep, he, hρLR]
      have h2 := pow_le_pow_left₀ hη0 h1 2
      have h3 : (2 * (R * L)) ^ 2 = 4 * (R * L) ^ 2 := by ring
      linarith [h2, h3]
    have hp1 : 20 * Real.pi * (ρ * L) ^ 2 / W ^ 2 ≤ 20 * Real.pi * (R * L) ^ 2 := by
      have hnum : 20 * Real.pi * (ρ * L) ^ 2 ≤ 20 * Real.pi * (R * L) ^ 2 :=
        mul_le_mul_of_nonneg_left hρL hpi0
      have hnn : (0 : ℝ) ≤ 20 * Real.pi * (ρ * L) ^ 2 := mul_nonneg hpi0 (sq_nonneg _)
      have hstep : 20 * Real.pi * (ρ * L) ^ 2 / W ^ 2 ≤ 20 * Real.pi * (ρ * L) ^ 2 / 1 :=
        div_le_div_of_nonneg_left hnn (by norm_num) hW2
      rw [div_one] at hstep
      linarith
    have hp2 : 20 * Real.pi * (ρ * (1 / η)) ^ 2 * (h / B) / W ^ 2
        ≤ 20 * Real.pi * (R * L) ^ 2 * (4 * (h / B)) := by
      have hnum : 20 * Real.pi * (ρ * (1 / η)) ^ 2 ≤ 20 * Real.pi * (4 * (R * L) ^ 2) :=
        mul_le_mul_of_nonneg_left hρη hpi0
      have hval : 20 * Real.pi * (4 * (R * L) ^ 2) * (h / B)
          = 20 * Real.pi * (R * L) ^ 2 * (4 * (h / B)) := by ring
      have hmul := mul_le_mul_of_nonneg_right hnum hhB
      have hnn : (0 : ℝ) ≤ 20 * Real.pi * (ρ * (1 / η)) ^ 2 * (h / B) :=
        mul_nonneg (mul_nonneg hpi0 (sq_nonneg _)) hhB
      have hstep : 20 * Real.pi * (ρ * (1 / η)) ^ 2 * (h / B) / W ^ 2
          ≤ 20 * Real.pi * (ρ * (1 / η)) ^ 2 * (h / B) / 1 :=
        div_le_div_of_nonneg_left hnn (by norm_num) hW2
      rw [div_one] at hstep
      linarith [hstep, hmul, hval]
    have hrhs : 20 * Real.pi * (R * L) ^ 2 * (1 + 4 * (h / B))
        = 20 * Real.pi * (R * L) ^ 2 + 20 * Real.pi * (R * L) ^ 2 * (4 * (h / B)) := by ring
    linarith [hp1, hp2, hrhs]
  have hcof : 2 * (5 * Real.pi / 2) * (M * S) / (B * h * W ^ 2)
      ≤ 5 * Real.pi * (4 * (MB * P1 / h) + 10 * (MB * P2 / sx) + 5 * (MB / sx)
        + 6 * (MB / h) + 2 * (MB * P3 / h)) := by
    have hMS0 : (0 : ℝ) ≤ M * S := mul_nonneg hM0 hS0
    have hstep : 2 * (5 * Real.pi / 2) * (M * S) / (B * h * W ^ 2)
        ≤ 2 * (5 * Real.pi / 2) * (M * S) / (B * h) := by
      refine div_le_div_of_nonneg_left ?_ hBh ?_
      · exact mul_nonneg (by positivity) hMS0
      · exact le_mul_of_one_le_right hBh.le hW2
    refine hstep.trans ?_
    have hid : 2 * (5 * Real.pi / 2) * (M * S) / (B * h)
        = 5 * Real.pi * (M * (S / (B * h))) := by
      field_simp
    rw [hid]
    have hSle : S ≤ 2 * L * η ^ 2 * B + 5 * L + 5 * h + 6 * B + 2 * B * (1 / η) := by
      have hLη0 : (0 : ℝ) ≤ L * η ^ 2 := mul_nonneg (by linarith) (sq_nonneg η)
      have h1 : L * ((1 + B) * η ^ 2 + 5) ≤ 2 * L * η ^ 2 * B + 5 * L := by
        have hstep : (L * η ^ 2) * (1 + B) ≤ (L * η ^ 2) * (2 * B) :=
          mul_le_mul_of_nonneg_left (by linarith) hLη0
        calc L * ((1 + B) * η ^ 2 + 5) = (L * η ^ 2) * (1 + B) + 5 * L := by ring
          _ ≤ (L * η ^ 2) * (2 * B) + 5 * L := by linarith
          _ = 2 * L * η ^ 2 * B + 5 * L := by ring
      have h2 : (η * B + (1 + B) * η) * (2 / (Q * η)) ≤ 6 * B := by
        have hηB : η ≤ B * η := by
          have := mul_le_mul_of_nonneg_right hB1 hη.le
          linarith [this]
        have hq : (2 : ℝ) / (Q * η) ≤ 2 / (1 * η) := by
          refine div_le_div_of_nonneg_left (by norm_num) (by simpa using hη) ?_
          have := mul_le_mul_of_nonneg_right hQ1.le hη.le
          linarith [this]
        have h3B : η * B + (1 + B) * η ≤ 3 * B * η := by
          calc η * B + (1 + B) * η = 2 * (B * η) + η := by ring
            _ ≤ 2 * (B * η) + B * η := by linarith [hηB]
            _ = 3 * B * η := by ring
        have hBη0 : (0 : ℝ) ≤ 3 * B * η :=
          mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hη.le
        have hfin : (η * B + (1 + B) * η) * (2 / (Q * η)) ≤ (3 * B * η) * (2 / (1 * η)) :=
          mul_le_mul h3B hq (div_nonneg (by norm_num) hQη.le) hBη0
        have hval : (3 * B * η) * (2 / (1 * η)) = 6 * B := by field_simp; ring
        linarith [hfin, hval]
      have h3 : B * (2 / (Q ^ 2 * η)) ≤ 2 * B * (1 / η) := by
        have hQ2 : (1 : ℝ) ≤ Q ^ 2 := by nlinarith [hQ1]
        have hq : (2 : ℝ) / (Q ^ 2 * η) ≤ 2 / (1 * η) := by
          refine div_le_div_of_nonneg_left (by norm_num) (by simpa using hη) ?_
          have := mul_le_mul_of_nonneg_right hQ2 hη.le
          linarith [this]
        have hval : (2 : ℝ) / (1 * η) = 2 * (1 / η) := by field_simp
        have hstep : B * (2 / (Q ^ 2 * η)) ≤ B * (2 / (1 * η)) :=
          mul_le_mul_of_nonneg_left hq (by linarith)
        have hval2 : B * (2 / (1 * η)) = 2 * B * (1 / η) := by rw [hval]; ring
        linarith [hstep, hval2]
      rw [hSdef]; linarith
    have hSb : S / (B * h)
        ≤ 2 * (L * η ^ 2) / h + 5 * (L / B) + 5 * (1 / B) + 6 * (1 / h)
          + 2 * ((1 / η) / h) := by
      have hdiv : S / (B * h) ≤ (2 * L * η ^ 2 * B + 5 * L + 5 * h + 6 * B + 2 * B * (1 / η))
          / (B * h) := div_le_div_of_nonneg_right hSle hBh.le
      refine hdiv.trans ?_
      have hexp : (2 * L * η ^ 2 * B + 5 * L + 5 * h + 6 * B + 2 * B * (1 / η)) / (B * h)
          = 2 * (L * η ^ 2) / h + 5 * (L / B) * (1 / h) + 5 * (1 / B) + 6 * (1 / h)
            + 2 * ((1 / η) / h) := by
        field_simp
      rw [hexp]
      have hLB : (0 : ℝ) ≤ 5 * (L / B) :=
        mul_nonneg (by norm_num) (div_nonneg (by linarith) hB0.le)
      have hone : 5 * (L / B) * (1 / h) ≤ 5 * (L / B) := by
        have hinv1 : (1 : ℝ) / h ≤ 1 := by rw [div_le_one hh0]; linarith
        exact mul_le_of_le_one_right hLB hinv1
      linarith
    have hpoly : 2 * (L * η ^ 2) / h + 5 * (L / B) + 5 * (1 / B) + 6 * (1 / h)
          + 2 * ((1 / η) / h)
        ≤ 4 * (P1 / h) + 10 * (P2 / sx) + 5 * (1 / sx) + 6 * (1 / h) + 2 * (P3 / h) := by
      have hq1 : 2 * (L * η ^ 2) / h ≤ 4 * (P1 / h) := by
        have h1 : (L * η ^ 2) / h ≤ (2 * P1) / h := div_le_div_of_nonneg_right hLη hh0.le
        have h2 : (2 * P1) / h = 2 * (P1 / h) := by ring
        have h3 : 2 * (L * η ^ 2) / h = 2 * ((L * η ^ 2) / h) := by ring
        linarith [h1, h2, h3]
      have hq2 : 5 * (L / B) ≤ 10 * (P2 / sx) := by
        have hLsx : L / B ≤ L / sx := div_le_div_of_nonneg_left (by linarith) hsx hsxB
        have hLnum : L / sx ≤ (2 * P2) / sx := div_le_div_of_nonneg_right hLpoly hsx.le
        have h2 : (2 * P2) / sx = 2 * (P2 / sx) := by ring
        linarith [hLsx, hLnum, h2]
      have hq3 : 5 * (1 / B) ≤ 5 * (1 / sx) := by
        have : (1 : ℝ) / B ≤ 1 / sx := div_le_div_of_nonneg_left zero_le_one hsx hsxB
        linarith
      have hq4 : 2 * ((1 / η) / h) ≤ 2 * (P3 / h) := by
        have : (1 / η) / h ≤ P3 / h := div_le_div_of_nonneg_right hinvηP hh0.le
        linarith
      linarith [hq1, hq2, hq3, hq4]
    have hSb0 : (0 : ℝ) ≤ S / (B * h) := div_nonneg hS0 hBh.le
    have hcomb : M * (S / (B * h))
        ≤ MB * (4 * (P1 / h) + 10 * (P2 / sx) + 5 * (1 / sx) + 6 * (1 / h)
          + 2 * (P3 / h)) :=
      mul_le_mul hMB (hSb.trans hpoly) hSb0 hMB0
    have hval : MB * (4 * (P1 / h) + 10 * (P2 / sx) + 5 * (1 / sx) + 6 * (1 / h)
          + 2 * (P3 / h))
        = 4 * (MB * P1 / h) + 10 * (MB * P2 / sx) + 5 * (MB / sx) + 6 * (MB / h)
          + 2 * (MB * P3 / h) := by ring
    have := mul_le_mul_of_nonneg_left hcomb (by positivity : (0:ℝ) ≤ 5 * Real.pi)
    rw [hval] at this
    linarith [this]
  linarith [hgroup1, hcof]

end

end RHTower.Sieve

namespace RHTower.Sieve

open Filter Topology

noncomputable section

set_option maxHeartbeats 1000000 in
/-- **The normalised ladder slope is below its majorant.** -/
theorem eventually_slope_quotient_le {A delta Ctot β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hγβ : γ * β < 1) (hCtot : 0 ≤ Ctot) :
    ∀ᶠ x : ℝ in atTop,
      ladderAffineSlope (ladderSteps β γ x) (budgetB β x) ((siftStart (γ * β) x : ℕ) : ℝ)
          (ladderEta β γ x) (budgetRho A delta Ctot β γ x)
        / (((budgetB β x : ℕ) : ℝ) * cardLength β x
          * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2)
      ≤ slopeMajorant A delta Ctot β γ x := by
  have hab : (0 : ℝ) < γ * β := mul_pos hγ0 hβ0
  have hzero := tendsto_ladderEta (β := β) (γ := γ) hβ0 hγβ
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), eventually_le_siftStart hab 2,
    Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1) hzero,
    one_le_ladderSteps hβ0 hγ0 hγ1 hγβ, eventually_siftStart_lt_cardLength hβ0 hγ0 hγ1,
    (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
    (tendsto_ladderMass hβ0 hγ0 hγ1 hγβ).eventually_ge_atTop (1 : ℝ),
    eventually_budgetRho_nonneg (A := A) (delta := delta) (Ctot := Ctot) (γ := γ) hβ0 hCtot,
    eventually_budgetRho_le (A := A) (delta := delta) (Ctot := Ctot) (γ := γ) hβ0 hβ1 hγ0 hCtot,
    eventually_inv_eta_le_steps hβ0 hγ0 hγ1 hγβ,
    eventually_cofactor_ratio_le (β := β) (γ := γ) hβ0 hβ1 hγ0 hγβ,
    eventually_steps_eta_sq_le hβ0 hγ0 hγ1 hγβ,
    eventually_ladderSteps_poly hβ0 hγ0 hγ1 hγβ]
    with x hx1 hQ2 hη1 hL1 h2Q hh1 hW hρ0 hρR hinvη hM hLη hLpoly
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hη : 0 < ladderEta β γ x := ladderEta_pos hx1
  have hQ2R : (2 : ℝ) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) := by exact_mod_cast hQ2
  have hQ1 : (1 : ℝ) < ((siftStart (γ * β) x : ℕ) : ℝ) := by linarith
  have hQh : ((siftStart (γ * β) x : ℕ) : ℝ) ≤ cardLength β x := by linarith
  have hle := ladderPow_le (β := β) (γ := γ) (x := x) (by linarith) hQh hη
  have hL1R : (1 : ℝ) ≤ ((ladderSteps β γ x : ℕ) : ℝ) := by exact_mod_cast hL1
  have hBsx : Real.sqrt x ≤ ((budgetB β x : ℕ) : ℝ) := sqrt_le_budgetB (β := β) x hh1
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hsx1 : (1 : ℝ) ≤ Real.sqrt x := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hB1 : (1 : ℝ) ≤ ((budgetB β x : ℕ) : ℝ) := by linarith
  have hB0 : (0 : ℝ) < ((budgetB β x : ℕ) : ℝ) := by linarith
  have hh0 : (0 : ℝ) < cardLength β x := by linarith
  have hW2 : (1 : ℝ) ≤ (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 := by
    nlinarith [hW]
  have hden : (0 : ℝ) < ((budgetB β x : ℕ) : ℝ) * cardLength β x
      * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 :=
    mul_pos (mul_pos hB0 hh0) (by linarith)
  have hslope := ladderAffineSlope_le (B₀ := budgetB β x)
    (Q := ((siftStart (γ * β) x : ℕ) : ℝ)) (η := ladderEta β γ x) (hR := cardLength β x)
    (ρ := budgetRho A delta Ctot β γ x) hQ1 hη hη1 (L := ladderSteps β γ x) hle
  have hM0 : (0 : ℝ) ≤ Real.log ((⌊((budgetB β x : ℕ) : ℝ) * (1 + ladderEta β γ x)⌋₊ : ℕ) : ℝ)
      / Real.log ((siftStart (γ * β) x : ℕ) : ℝ) := by
    refine div_nonneg (Real.log_nonneg ?_) (Real.log_nonneg (by linarith))
    have h1 : (1 : ℕ) ≤ ⌊((budgetB β x : ℕ) : ℝ) * (1 + ladderEta β γ x)⌋₊ :=
      Nat.one_le_floor_iff _ |>.2 (by nlinarith [hB1, hη.le])
    exact_mod_cast h1
  have harith := slope_quotient_arith
    (L := ((ladderSteps β γ x : ℕ) : ℝ)) (B := ((budgetB β x : ℕ) : ℝ))
    (Q := ((siftStart (γ * β) x : ℕ) : ℝ)) (η := ladderEta β γ x)
    (ρ := budgetRho A delta Ctot β γ x) (R := budgetRhoBound A delta Ctot β γ x)
    (h := cardLength β x)
    (W := mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x))
    (M := Real.log ((⌊((budgetB β x : ℕ) : ℝ) * (1 + ladderEta β γ x)⌋₊ : ℕ) : ℝ)
      / Real.log ((siftStart (γ * β) x : ℕ) : ℝ))
    (sx := Real.sqrt x) (MB := (Real.log x) ^ (1 - γ * β))
    (P1 := (Real.log x) ^ (γ * β - 5 / 4)) (P2 := (Real.log x) ^ (2 * β + 5 / 4 - γ * β))
    (P3 := (Real.log x) ^ (β + 5 / 4 - γ * β))
    hQ1 hη hL1R hB1 hh1 hW2 hρ0 hρR hinvη hsx hBsx hM0 hM
    (Real.rpow_nonneg hlogx.le _) hLη hLpoly
    (le_of_eq (inv_ladderEta_eq (β := β) (γ := γ) hx1)) rfl
  refine (div_le_div_of_nonneg_right hslope hden.le).trans (harith.trans (le_of_eq ?_))
  have e1 : (Real.log x) ^ (1 - γ * β) * (Real.log x) ^ (γ * β - 1) = 1 := by
    rw [← Real.rpow_add hlogx]
    norm_num
  have e2 : (Real.log x) ^ (1 - γ * β) * (Real.log x) ^ (2 * β + 1 - γ * β)
      = (Real.log x) ^ (2 * β + 2 - 2 * (γ * β)) := by
    rw [← Real.rpow_add hlogx]
    congr 1
    ring
  have e3 : (Real.log x) ^ (1 - γ * β) * (Real.log x) ^ (β + 1 - γ * β)
      = (Real.log x) ^ (β + 2 - 2 * (γ * β)) := by
    rw [← Real.rpow_add hlogx]
    congr 1
    ring
  rw [slopeMajorant, e1, e2, e3]

end

end RHTower.Sieve

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- **The normalised ladder slope vanishes.** -/
theorem tendsto_slope_quotient {A delta Ctot β γ : ℝ} (hβ0 : 9 / 10 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hγβ0 : 9 / 10 < γ * β) (hγβ1 : γ * β < 1) (hCtot : 0 ≤ Ctot)
    (hdelta : 0 < delta) :
    Tendsto (fun x : ℝ =>
        ladderAffineSlope (ladderSteps β γ x) (budgetB β x) ((siftStart (γ * β) x : ℕ) : ℝ)
            (ladderEta β γ x) (budgetRho A delta Ctot β γ x)
          / (((budgetB β x : ℕ) : ℝ) * cardLength β x
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2))
      atTop (𝓝 0) := by
  have hβ0' : (0 : ℝ) < β := by linarith
  have hab : (0 : ℝ) < γ * β := by linarith
  refine squeeze_zero' ?_ (eventually_slope_quotient_le hβ0' hβ1 hγ0 hγ1 hγβ1 hCtot)
    (tendsto_slopeMajorant hβ0 hβ1 hγ0 hγ1 hγβ0 hγβ1 hCtot hdelta)
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), eventually_le_siftStart hab 2,
    (tendsto_cardLength hβ0').eventually_ge_atTop (1 : ℝ)] with x hx1 hQ2 hh1
  have hη : 0 < ladderEta β γ x := ladderEta_pos hx1
  have hQ2R : (2 : ℝ) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) := by exact_mod_cast hQ2
  have hnum : (0 : ℝ) ≤ ladderAffineSlope (ladderSteps β γ x) (budgetB β x)
      ((siftStart (γ * β) x : ℕ) : ℝ) (ladderEta β γ x) (budgetRho A delta Ctot β γ x) :=
    ladderAffineSlope_nonneg (by linarith) hη.le
  have hBsx : Real.sqrt x ≤ ((budgetB β x : ℕ) : ℝ) := sqrt_le_budgetB (β := β) x hh1
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hB0 : (0 : ℝ) < ((budgetB β x : ℕ) : ℝ) := by linarith
  have hh0 : (0 : ℝ) < cardLength β x := by linarith
  exact div_nonneg hnum (by positivity)

end

end RHTower.Sieve
