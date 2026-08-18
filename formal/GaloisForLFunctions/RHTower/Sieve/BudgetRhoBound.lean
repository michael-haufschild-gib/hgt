import GaloisForLFunctions.RHTower.Sieve.BudgetWidthBounds
import GaloisForLFunctions.RHTower.Sieve.PolylogLimits

/-!
# The annulus constant at the chosen parameters, bounded

The relative scaled majorant is increasing in the height cost and decreasing in the width, so the
bounds of the previous file transfer to it, and the annulus constant becomes an elementary function
of `log x`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The relative scaled majorant is monotone in the height cost and antitone in the width. -/
theorem relScaledMajorant_mono {Ctot D Lx Hmaj Hmaj' μ μ' q t₀ xmin : ℝ}
    (hCtot : 0 ≤ Ctot) (hq0 : 0 ≤ q) (hH0 : 0 ≤ Hmaj) (hH : Hmaj ≤ Hmaj') (hμ : μ' ≤ μ)
    (ht₀ : 0 < t₀) :
    relScaledMajorant Ctot D Lx Hmaj μ q t₀ xmin
      ≤ relScaledMajorant Ctot D Lx Hmaj' μ' q t₀ xmin := by
  have hexp : Real.exp (-(μ * q)) ≤ Real.exp (-(μ' * q)) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith [hμ, hq0]
  have hin0 : (0 : ℝ) ≤ Real.exp (-(μ * q)) + 1 / t₀ ^ 2 := by positivity
  have hprod : Hmaj * (Real.exp (-(μ * q)) + 1 / t₀ ^ 2)
      ≤ Hmaj' * (Real.exp (-(μ' * q)) + 1 / t₀ ^ 2) :=
    mul_le_mul hH (by linarith) hin0 (by linarith)
  rw [relScaledMajorant, relScaledMajorant]
  have hmain : Ctot * D ^ 2 * (Lx ^ 2 / t₀ + Hmaj * (Real.exp (-(μ * q)) + 1 / t₀ ^ 2))
        / (2 * Real.pi)
      ≤ Ctot * D ^ 2 * (Lx ^ 2 / t₀ + Hmaj' * (Real.exp (-(μ' * q)) + 1 / t₀ ^ 2))
        / (2 * Real.pi) := by
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- The annulus constant at the chosen parameters, in elementary terms. -/
def budgetRhoBound (A delta Ctot β γ x : ℝ) : ℝ :=
  (4 / Real.log 2)
    * ((1 + ladderEta β γ x)
        * relScaledMajorant Ctot (ladderWidth β x) ((Real.log x) ^ β)
            (1 + (1 + Real.log x) * budgetWinv A x)
            (min delta (1 / budgetWinv A x) / 2)
            (Real.log ((siftStart (γ * β) x : ℕ) : ℝ)) (2 * Real.pi * annulusStart β x)
            ((siftStart (γ * β) x : ℕ) : ℝ)
      + 7 * Real.exp 9 / ((siftStart (γ * β) x : ℕ) : ℝ))

/-- **The annulus constant is bounded by its elementary form.** -/
theorem eventually_budgetRho_le {A delta Ctot β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hCtot : 0 ≤ Ctot) :
    ∀ᶠ x : ℝ in atTop,
      budgetRho A delta Ctot β γ x ≤ budgetRhoBound A delta Ctot β γ x := by
  have hab : (0 : ℝ) < γ * β := mul_pos hγ0 hβ0
  have hpolylog : Tendsto (fun x : ℝ => 2 * Real.pi * annulusStart β x) atTop atTop := by
    have h : Tendsto (fun x : ℝ => annulusStart β x) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0:ℝ) < (13:ℝ))).comp Real.tendsto_log_atTop
    exact Filter.Tendsto.const_mul_atTop (by positivity) h
  filter_upwards [eventually_budgetHmaj_le (A := A) hβ0 hβ1,
    eventually_budgetMu_ge (A := A) (delta := delta) hβ0 hβ1,
    eventually_le_siftStart hab 1, Filter.eventually_gt_atTop (1 : ℝ),
    hpolylog.eventually_gt_atTop (0 : ℝ),
    eventually_envelope_le hβ0 hβ1] with x hH hμ hQ1 hx1 hw₀ henv
  have hQ : (1 : ℝ) ≤ ((siftStart (γ * β) x : ℕ) : ℝ) := by exact_mod_cast hQ1
  have hq0 : (0 : ℝ) ≤ Real.log ((siftStart (γ * β) x : ℕ) : ℝ) := Real.log_nonneg hQ
  have habs : |2 * Real.pi * budgetT β x| = 2 * Real.pi * budgetT β x := by
    rw [abs_of_nonneg (by rw [budgetT]; positivity)]
  have h1ge : (1 : ℝ) ≤ 2 * Real.pi * budgetT β x := by
    rw [← habs]
    exact henv.1
  have hH0 : (0 : ℝ) ≤ budgetHmaj A β x := by
    have hlognn : (0 : ℝ) ≤ Real.log (3 * (2 * Real.pi * budgetT β x) / 2) :=
      Real.log_nonneg (by linarith)
    have h1 : (0 : ℝ) < 1 / (2 * Real.pi * annulusStart β x) := by positivity
    have h2 : (0 : ℝ) ≤ Real.log (3 * (2 * Real.pi * budgetT β x) / 2)
        / routeTWidthPolylogLower A (2 * Real.pi * budgetT β x) :=
      div_nonneg hlognn (routeTWidthPolylogLower_pos _ _).le
    rw [budgetHmaj]
    linarith
  rw [budgetRho, ladderRho, budgetRhoBound]
  have hmono := relScaledMajorant_mono (Ctot := Ctot) (D := ladderWidth β x)
    (Lx := (Real.log x) ^ β) (q := Real.log ((siftStart (γ * β) x : ℕ) : ℝ))
    (t₀ := 2 * Real.pi * annulusStart β x) (xmin := ((siftStart (γ * β) x : ℕ) : ℝ))
    hCtot hq0 hH0 hH hμ hw₀
  have hη0 : (0 : ℝ) < 1 + ladderEta β γ x := by
    have := ladderEta_pos (β := β) (γ := γ) hx1
    linarith
  have hlog2 : (0 : ℝ) < 4 / Real.log 2 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 2)
    positivity
  have hstep := mul_le_mul_of_nonneg_left hmono hη0.le
  exact mul_le_mul_of_nonneg_left (by linarith [hstep]) hlog2.le

end

end RHTower.Sieve
