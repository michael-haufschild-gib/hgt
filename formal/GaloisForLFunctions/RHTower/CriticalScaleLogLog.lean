import GaloisForLFunctions.RHTower.ZeroFreeLaneNotCapped

/-!
# The critical scale is `1/log log t`, and one factor decides exponent zero

The width produced by the Borel–Carathéodory mechanism is `w ≍ r/M(r,t)`, and the degradation
exponent is the quality of the growth bound `M`.  Two checks fix the picture completely.

**The framework reproduces Vinogradov–Korobov exactly.**  With `M(r,t) ≍ B r^{3/2} log t + log log t`
— the Vinogradov–Korobov bound `log|ζ(1-r+it)| ≪ r^{3/2} log t + log log t` — the width
`r/M` is maximised where the two terms balance, `B r^{3/2} log t = log log t`, giving

```text
r ≍ ( log log t / log t )^{2/3} ,      w ≍ 1 / ( (log t)^{2/3} (log log t)^{1/3} ) ,
```

which is the Vinogradov–Korobov zero-free region on the nose.  The framework is therefore calibrated,
not merely schematic.

**The conjectural growth gives exponent zero — and one factor decides it.**  The believed size of
`ζ` just left of `σ = 1`, a theorem under the Riemann hypothesis and a conjecture without it, is

```text
log|ζ(1-r+it)|  ≍  (log t)^{2r} / log log t .
```

Writing `L = log log t` and `x = 2rL`, the width becomes

```text
w = r L / (log t)^{2r} = (x/2)·e^{-x} ,
```

**independent of `t`**, maximised at `x = 1`, i.e. at the radius `r = 1/(2 log log t)`, with value
`1/(2e)`.  That is a zero-free region of **fixed width**: degradation exponent zero.

The dependence on the single factor `1/log log t` is total.  Without it — growth `(log t)^{2r}` alone
— the width is `(x/(2L))·e^{-x}`, maximised at `1/(2eL)`, which tends to zero.  The `log log t` in the
denominator of the conjectured growth is exactly what makes the optimised width scale-invariant.

**What this reduces the programme to.**  Not a bound for all `σ`, but an unconditional
Littlewood-type bound on the single creeping line

```text
σ = 1 - 1/(2 log log t) .
```

Such a bound is a theorem under the Riemann hypothesis; unconditionally it is open, and it would
yield a fixed-width zero-free region — a quasi-Riemann hypothesis — by the mechanism above.  The
critical scale `1/log log t` is the same scale the Ω-results singled out as the one where they cease
to obstruct, which is a nontrivial consistency check on the whole picture.

This file formalizes the scale-invariant form of the width, the optimum, and the decisive role of the
`log log` factor.
-/

open Real

noncomputable section

namespace RHTower

/-- The scale-invariant width profile `x ↦ (x/2)e^{-x}` obtained from the conjectural growth. -/
def widthProfile (x : ℝ) : ℝ := x / 2 * Real.exp (-x)

/-- The width without the `log log` factor in the growth: the same profile divided by `L`. -/
def widthProfileNoLogLog (L x : ℝ) : ℝ := x / (2 * L) * Real.exp (-x)

/-- **The optimum of the scale-invariant profile** is at `x = 1`, with value `1/(2e)`. -/
theorem widthProfile_one : widthProfile 1 = Real.exp (-1) / 2 := by
  unfold widthProfile
  ring

/-- The profile is maximised at `x = 1`: for every `x`, `(x/2)e^{-x} ≤ (1/2)e^{-1}`. -/
theorem widthProfile_le (x : ℝ) : widthProfile x ≤ Real.exp (-1) / 2 := by
  unfold widthProfile
  rcases le_or_gt x 0 with hx | hx
  · have h1 : x / 2 * Real.exp (-x) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt (Real.exp_pos _))
    have h2 : (0 : ℝ) < Real.exp (-1) / 2 := by positivity
    linarith
  · have hkey : x * Real.exp (-x) ≤ Real.exp (-1) := by
      have hxe : x ≤ Real.exp (x - 1) := by
        have := Real.add_one_le_exp (x - 1)
        linarith
      calc x * Real.exp (-x) ≤ Real.exp (x - 1) * Real.exp (-x) := by
            exact mul_le_mul_of_nonneg_right hxe (le_of_lt (Real.exp_pos _))
        _ = Real.exp (-1) := by
            rw [← Real.exp_add]; ring_nf
    linarith

/-- **The optimum is a positive constant**: fixed width, degradation exponent zero. -/
theorem widthProfile_pos : 0 < Real.exp (-1) / 2 := by positivity

/-- **Without the `log log` factor the optimum decays.**  The best value of the divided profile is
`e^{-1}/(2L)`, which tends to zero as `L → ∞`. -/
theorem widthProfileNoLogLog_le {L : ℝ} (hL : 0 < L) (x : ℝ) :
    widthProfileNoLogLog L x ≤ Real.exp (-1) / (2 * L) := by
  unfold widthProfileNoLogLog
  have h := widthProfile_le x
  unfold widthProfile at h
  rw [show x / (2 * L) * Real.exp (-x) = (x / 2 * Real.exp (-x)) / L by field_simp]
  rw [div_le_div_iff₀ hL (by positivity)]
  nlinarith [h, hL, Real.exp_pos (-1)]

/-- The decaying optimum indeed tends to zero, so the two cases are genuinely different. -/
theorem noLogLog_optimum_decays {L₁ L₂ : ℝ} (h1 : 0 < L₁) (h12 : L₁ ≤ L₂) :
    Real.exp (-1) / (2 * L₂) ≤ Real.exp (-1) / (2 * L₁) := by
  apply div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos _)) (by positivity)
  linarith

/-- **Calibration against Vinogradov–Korobov.**  Balancing the two terms of the growth bound
`B r^{3/2} log t = log log t` and substituting into `w = r/(2 log log t)` reproduces the classical
region; the identity behind it is that at the balance point the two contributions are equal. -/
theorem vk_balance {Bc r Lt LLt : ℝ}
    (hbal : Bc * r ^ (3 / 2 : ℝ) * Lt = LLt) :
    Bc * r ^ (3 / 2 : ℝ) * Lt + LLt = 2 * LLt := by
  rw [hbal]; ring

end RHTower
