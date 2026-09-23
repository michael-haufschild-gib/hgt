import GaloisForLFunctions.RHTower.Sieve.MoebiusHeadGate
import GaloisForLFunctions.RHTower.Sieve.MoebiusHeadBudget

/-!
# The Route E gate at the optimal cutoff

Putting `Sieve/MoebiusHeadGate` and `Sieve/MoebiusHeadBudget` together: the averaged short-interval
mean square for `μ` at window `h(x)` follows from **one** relative smallness statement,

```text
   ( ∫_{|w| ≤ T₀(x)} ‖∑_{n ≤ M} μ(n)n^{-2πiw}‖² dw ) / M²  →  0 ,
      M = ⌊√x + h⌋ ,   T₀ = (M/h)·ω(x) ,   ω → ∞ arbitrarily slowly.
```

Nothing else about `μ` enters, and no condition on the slope of the mean square survives.
-/

namespace RHTower.Sieve

open MeasureTheory Filter

noncomputable section

/-- The logarithmic window width is at most `h/√x`. -/
theorem fibreWidth_le_div_sqrt {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    fibreWidth x h ≤ h / Real.sqrt x := by
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
  have ht0 : (0 : ℝ) ≤ h / Real.sqrt x := by positivity
  have hkey : Real.log (1 + h / Real.sqrt x) ≤ (1 + h / Real.sqrt x) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  rw [fibreWidth]
  linarith

/-- The Gallagher cutoff at the optimal choice. -/
def headG (x h : ℝ) : ℝ := ((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ) / h

/-- The height at which the single head bound is required. -/
def headT₀ (x h ω : ℝ) : ℝ := headG x h * ω

/-- **The Route E gate from one relative head bound.** -/
theorem averagedMeanSquare_moebius_of_headSmall {hh ω B : ℝ → ℝ}
    (hgrow : Tendsto hh atTop atTop)
    (hdata : ∀ᶠ x : ℝ in atTop,
      4 ≤ x ∧ 1 ≤ hh x ∧ hh x ≤ Real.sqrt x ∧ 1 ≤ ω x ∧ 0 ≤ B x
        ∧ (∫ w in Set.Icc (-(headT₀ x (hh x) (ω x))) (headT₀ x (hh x) (ω x)),
            ‖logPoly (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
              (fibreIndex x (hh x)) w‖ ^ (2 : ℕ)) ≤ B x)
    (hωgrow : Tendsto ω atTop atTop)
    (hrel : Tendsto (fun x : ℝ => B x / ((⌊Real.sqrt x + hh x⌋₊ : ℕ) : ℝ) ^ (2 : ℕ)) atTop (nhds 0)) :
    AveragedMeanSquare (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) hh := by
  have hfacts : ∀ᶠ x : ℝ in atTop,
      4 ≤ x ∧ 1 ≤ hh x ∧ hh x ≤ Real.sqrt x ∧ 1 ≤ ω x ∧ 0 ≤ B x
        ∧ (0 : ℝ) < ((⌊Real.sqrt x + hh x⌋₊ : ℕ) : ℝ)
        ∧ Real.sqrt x ≤ ((⌊Real.sqrt x + hh x⌋₊ : ℕ) : ℝ)
        ∧ ((⌊Real.sqrt x + hh x⌋₊ : ℕ) : ℝ) ≤ 2 * Real.sqrt x := by
    filter_upwards [hdata] with x hx
    obtain ⟨hx4, hh1, hhx, hω1, hB0, -⟩ := hx
    have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hlow : Real.sqrt x ≤ ((⌊Real.sqrt x + hh x⌋₊ : ℕ) : ℝ) := by
      have := Nat.sub_one_lt_floor (Real.sqrt x + hh x)
      have hfl : Real.sqrt x + hh x - 1 ≤ ((⌊Real.sqrt x + hh x⌋₊ : ℕ) : ℝ) := by linarith
      linarith
    have hhigh : ((⌊Real.sqrt x + hh x⌋₊ : ℕ) : ℝ) ≤ 2 * Real.sqrt x := by
      have := Nat.floor_le (by positivity : (0 : ℝ) ≤ Real.sqrt x + hh x)
      linarith
    exact ⟨hx4, hh1, hhx, hω1, hB0, by linarith, hlow, hhigh⟩
  refine averagedMeanSquare_moebius_of_headBound (G := fun x => headG x (hh x))
    (T₀ := fun x => headT₀ x (hh x) (ω x)) (B := B) hgrow ?_ ?_ ?_
  · filter_upwards [hdata] with x hx using hx.2.2.1
  · filter_upwards [hdata, hfacts] with x hx hf
    obtain ⟨-, hh1, hhx, hω1, hB0, hhead⟩ := hx
    obtain ⟨-, -, -, -, -, hM0, hlow, -⟩ := hf
    have hh0 : (0 : ℝ) < hh x := lt_of_lt_of_le zero_lt_one hh1
    have hG1 : 1 ≤ headG x (hh x) := by
      rw [headG, le_div_iff₀ hh0, one_mul]
      linarith
    refine ⟨hG1, ?_, hB0, hhead⟩
    rw [headT₀]
    nlinarith [hG1, hω1]
  · refine squeeze_zero' (g := fun x : ℝ => 90 / hh x + 60 / ω x
      + 9 * (B x / ((⌊Real.sqrt x + hh x⌋₊ : ℕ) : ℝ) ^ (2 : ℕ))) ?_ ?_ ?_
    · filter_upwards [hdata, hfacts] with x hx hf
      obtain ⟨hx4, hh1, hhx, hω1, hB0, -⟩ := hx
      obtain ⟨-, -, -, -, -, hM0, hlow, hhigh⟩ := hf
      have hh0 : (0 : ℝ) < hh x := lt_of_lt_of_le zero_lt_one hh1
      have hδ : 0 ≤ fibreWidth x (hh x) := fibreWidth_nonneg hx4 hh0.le
      have hslope : (0 : ℝ) ≤ moebiusHeadSlope x (hh x) (headT₀ x (hh x) (ω x)) := by
        have hT0 : (0 : ℝ) < headT₀ x (hh x) (ω x) := by
          rw [headT₀, headG]
          have : (0 : ℝ) < ((⌊Real.sqrt x + hh x⌋₊ : ℕ) : ℝ) / hh x := by positivity
          nlinarith [hω1]
        rw [moebiusHeadSlope]
        have := Real.pi_pos
        have := (Real.exp_pos 1).le
        positivity
      have hG0 : (0 : ℝ) < headG x (hh x) := by rw [headG]; positivity
      positivity
    · filter_upwards [hdata, hfacts] with x hx hf
      obtain ⟨hx4, hh1, hhx, hω1, hB0, -⟩ := hx
      obtain ⟨-, -, -, -, -, hM0, hlow, hhigh⟩ := hf
      have hh0 : (0 : ℝ) < hh x := lt_of_lt_of_le zero_lt_one hh1
      have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
      have hδle : fibreWidth x (hh x)
          ≤ 2 * hh x / ((⌊Real.sqrt x + hh x⌋₊ : ℕ) : ℝ) := by
        refine le_trans (fibreWidth_le_div_sqrt (by linarith) hh0.le) ?_
        rw [div_le_div_iff₀ hs0 hM0]
        nlinarith [hhigh, hh0.le]
      have hδ0 : 0 ≤ fibreWidth x (hh x) := fibreWidth_nonneg hx4 hh0.le
      have hkey := headBudget_le (M := ((⌊Real.sqrt x + hh x⌋₊ : ℕ) : ℝ))
        (δ := fibreWidth x (hh x)) (h := hh x) (ω := ω x) (B := B x) hM0 hh1 hω1 hδ0 hδle hB0
      refine le_trans (le_of_eq ?_) hkey
      rw [moebiusHeadSlope, headT₀, headG]
    · have h1 : Tendsto (fun x : ℝ => (90 : ℝ) / hh x) atTop (nhds 0) :=
        Tendsto.div_atTop tendsto_const_nhds hgrow
      have h2 : Tendsto (fun x : ℝ => (60 : ℝ) / ω x) atTop (nhds 0) :=
        Tendsto.div_atTop tendsto_const_nhds hωgrow
      have h3 : Tendsto (fun x : ℝ =>
          9 * (B x / ((⌊Real.sqrt x + hh x⌋₊ : ℕ) : ℝ) ^ (2 : ℕ))) atTop (nhds 0) := by
        have := hrel.const_mul (9 : ℝ)
        simpa using this
      have := (h1.add h2).add h3
      simpa using this

end

end RHTower.Sieve
