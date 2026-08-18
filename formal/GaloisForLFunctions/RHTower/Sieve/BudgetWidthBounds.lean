import GaloisForLFunctions.RHTower.Sieve.WidthEnvelopeBounds
import GaloisForLFunctions.RHTower.Sieve.BudgetSubstitution

/-!
# The width and the height cost at the chosen parameters

At the top of the annulus the frequency is `2π B₀ ≍ √x`, so the Route-T height envelope is at most
`16 + log x`, and both the width surrogate and the height cost become elementary functions of
`log x`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The Route-T height envelope at the top of the annulus. -/
def budgetZ (x : ℝ) : ℝ := 18 + Real.log x

/-- The reciprocal width surrogate at the top of the annulus. -/
def budgetWinv (A x : ℝ) : ℝ :=
  10 * routeTZeroFreeDeltaEnvelopeConstant A * (budgetZ x) ^ ((9 : ℝ) / 10)
    * (1 + Real.log (budgetZ x)) ^ 2

theorem one_le_budgetZ {x : ℝ} (hx : 1 ≤ x) : 1 ≤ budgetZ x := by
  have := Real.log_nonneg hx
  rw [budgetZ]
  linarith

theorem budgetWinv_pos {A x : ℝ} (hx : 1 ≤ x) : 0 < budgetWinv A x := by
  have hZ := one_le_budgetZ hx
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have h1 : (0 : ℝ) < (budgetZ x) ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos (by linarith) _
  have h2 : (0 : ℝ) ≤ Real.log (budgetZ x) := Real.log_nonneg hZ
  rw [budgetWinv]
  positivity

/-- **The height envelope at the top of the annulus.** -/
theorem eventually_envelope_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop,
      (1 : ℝ) ≤ |2 * Real.pi * budgetT β x|
        ∧ routeTLogHeightEnvelope (4 * (3 * |2 * Real.pi * budgetT β x| / 2 + 1))
            ≤ budgetZ x := by
  filter_upwards [cardLength_le_sqrt hβ0 hβ1, Filter.eventually_ge_atTop (Real.exp 4),
    (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ)] with x hhs hxe hh1
  have hx1 : (1 : ℝ) < x := by
    have h4 : (1 : ℝ) < Real.exp 4 := by
      have := Real.add_one_le_exp (4 : ℝ)
      linarith
    linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : (4 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 4) hxe
    rwa [Real.log_exp] at this
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hT : ((budgetB β x : ℕ) : ℝ) ≤ 2 * Real.sqrt x := by
    rw [budgetB]
    refine le_trans (Nat.floor_le (by positivity)) ?_
    linarith
  have hT1 : (1 : ℝ) ≤ ((budgetB β x : ℕ) : ℝ) := by
    rw [budgetB]
    have : 1 ≤ ⌊Real.sqrt x + cardLength β x⌋₊ :=
      Nat.le_floor (by push_cast; linarith [hsx.le])
    exact_mod_cast this
  have hTdef : budgetT β x = ((budgetB β x : ℕ) : ℝ) := rfl
  have habs : |2 * Real.pi * budgetT β x| = 2 * Real.pi * budgetT β x := by
    rw [abs_of_nonneg (by rw [hTdef]; positivity)]
  refine ⟨?_, ?_⟩
  · rw [habs, hTdef]
    nlinarith [hT1, hpi3]
  · have hge1 : (1 : ℝ) ≤ |2 * Real.pi * budgetT β x| := by
      rw [habs, hTdef]
      nlinarith [hT1, hpi3]
    refine le_trans (routeTLogHeightEnvelope_le hge1) ?_
    rw [habs, hTdef]
    have hlogT : Real.log ((budgetB β x : ℕ) : ℝ) ≤ Real.log 2 + Real.log x / 2 := by
      have hstep : Real.log ((budgetB β x : ℕ) : ℝ) ≤ Real.log (2 * Real.sqrt x) :=
        Real.log_le_log (by linarith) hT
      have hval : Real.log (2 * Real.sqrt x) = Real.log 2 + Real.log x / 2 := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hsx), Real.log_sqrt hx0.le]
      linarith [hstep, hval]
    have hlogprod : Real.log (2 * Real.pi * ((budgetB β x : ℕ) : ℝ))
        = Real.log (2 * Real.pi) + Real.log ((budgetB β x : ℕ) : ℝ) :=
      Real.log_mul (by positivity) (by linarith)
    have hlog2pi : Real.log (2 * Real.pi) ≤ 3 := by
      have h8 : 2 * Real.pi ≤ 8 := by nlinarith [Real.pi_le_four]
      have hstep : Real.log (2 * Real.pi) ≤ Real.log 8 := Real.log_le_log (by positivity) h8
      have hl8 : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        push_cast
        ring
      have hl2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
        linarith
      linarith
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      linarith
    rw [budgetZ]
    linarith [hlogprod, hlog2pi, hlogT, hl2]

/-- **The height cost at the chosen parameters.** -/
theorem eventually_budgetHmaj_le {A β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop,
      budgetHmaj A β x ≤ 1 + (1 + Real.log x) * budgetWinv A x := by
  have hpolylog : Tendsto (fun x : ℝ => 2 * Real.pi * annulusStart β x) atTop atTop := by
    have h : Tendsto (fun x : ℝ => annulusStart β x) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0:ℝ) < (13:ℝ))).comp Real.tendsto_log_atTop
    exact Filter.Tendsto.const_mul_atTop (by positivity) h
  filter_upwards [eventually_envelope_le hβ0 hβ1, cardLength_le_sqrt hβ0 hβ1,
    (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
    hpolylog.eventually_ge_atTop (1 : ℝ),
    Filter.eventually_ge_atTop (Real.exp 6)] with x henv hhs hh1 hw₀ hxe
  have hx1 : (1 : ℝ) < x := by
    have h4 : (1 : ℝ) < Real.exp 6 := by
      have := Real.add_one_le_exp (6 : ℝ)
      linarith
    linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : (6 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 6) hxe
    rwa [Real.log_exp] at this
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hZ1 : (1 : ℝ) ≤ budgetZ x := one_le_budgetZ hx1.le
  have hinv := inv_routeTWidthPolylogLower_le (A := A) (τ := 2 * Real.pi * budgetT β x)
    henv.1 henv.2 hZ1
  have hplw := routeTWidthPolylogLower_pos A (2 * Real.pi * budgetT β x)
  have hfirst : 1 / (2 * Real.pi * annulusStart β x) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hT : ((budgetB β x : ℕ) : ℝ) ≤ 2 * Real.sqrt x := by
    rw [budgetB]
    refine le_trans (Nat.floor_le (by positivity)) ?_
    linarith
  have hT1 : (1 : ℝ) ≤ ((budgetB β x : ℕ) : ℝ) := by
    rw [budgetB]
    have : 1 ≤ ⌊Real.sqrt x + cardLength β x⌋₊ :=
      Nat.le_floor (by push_cast; linarith [hsx.le])
    exact_mod_cast this
  have hTdef : budgetT β x = ((budgetB β x : ℕ) : ℝ) := rfl
  have hlognum : Real.log (3 * (2 * Real.pi * budgetT β x) / 2) ≤ 1 + Real.log x := by
    have hval : 3 * (2 * Real.pi * budgetT β x) / 2 = 3 * Real.pi * ((budgetB β x : ℕ) : ℝ) := by
      rw [hTdef]; ring
    rw [hval]
    have hle : 3 * Real.pi * ((budgetB β x : ℕ) : ℝ) ≤ 24 * Real.sqrt x := by
      nlinarith [Real.pi_le_four, hT, hsx.le, hT1]
    have hstep : Real.log (3 * Real.pi * ((budgetB β x : ℕ) : ℝ)) ≤ Real.log (24 * Real.sqrt x) :=
      Real.log_le_log (by positivity) hle
    have hval2 : Real.log (24 * Real.sqrt x) = Real.log 24 + Real.log x / 2 := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hsx), Real.log_sqrt hx0.le]
    have hl24 : Real.log 24 ≤ 4 := by
      have hstep2 : Real.log 24 ≤ Real.log 32 := Real.log_le_log (by norm_num) (by norm_num)
      have hl32 : Real.log 32 = 5 * Real.log 2 := by
        rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
        push_cast
        ring
      have hl2 : Real.log 2 ≤ 0.7 := by
        have := Real.log_two_lt_d9
        linarith
      linarith
    linarith [hstep, hval2, hl24, hlogx]
  have hlognum0 : (0 : ℝ) ≤ Real.log (3 * (2 * Real.pi * budgetT β x) / 2) := by
    refine Real.log_nonneg ?_
    rw [hTdef]
    nlinarith [hT1, hpi3]
  have hdiv : Real.log (3 * (2 * Real.pi * budgetT β x) / 2)
        / routeTWidthPolylogLower A (2 * Real.pi * budgetT β x)
      ≤ (1 + Real.log x) * budgetWinv A x := by
    have hstep : Real.log (3 * (2 * Real.pi * budgetT β x) / 2)
        * (1 / routeTWidthPolylogLower A (2 * Real.pi * budgetT β x))
        ≤ (1 + Real.log x) * budgetWinv A x := by
      refine mul_le_mul hlognum ?_ (by positivity) (by linarith)
      rw [budgetWinv, budgetZ] at *
      exact hinv
    rw [div_eq_mul_one_div]
    exact hstep
  rw [budgetHmaj]
  linarith [hfirst, hdiv]

/-- **The width surrogate at the chosen parameters, bounded below.** -/
theorem eventually_budgetMu_ge {A delta β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop,
      min delta (1 / budgetWinv A x) / 2 ≤ budgetMu A delta β x := by
  filter_upwards [eventually_envelope_le hβ0 hβ1, Filter.eventually_ge_atTop (1 : ℝ)]
    with x henv hx1
  have hZ1 : (1 : ℝ) ≤ budgetZ x := one_le_budgetZ hx1
  have hge := routeTWidthPolylogLower_ge (A := A) (τ := 2 * Real.pi * budgetT β x)
    henv.1 henv.2 hZ1
  rw [budgetMu]
  have hmin : min delta (1 / budgetWinv A x)
      ≤ min delta (routeTWidthPolylogLower A (2 * Real.pi * budgetT β x)) := by
    refine le_min (min_le_left _ _) (le_trans (min_le_right _ _) ?_)
    rw [budgetWinv, budgetZ] at *
    exact hge
  linarith

end

end RHTower.Sieve
