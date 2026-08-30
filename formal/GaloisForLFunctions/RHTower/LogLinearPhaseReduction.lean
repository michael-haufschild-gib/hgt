import GaloisForLFunctions.RHTower.LogPhaseProfile

/-!
# The archimedean phase and its stationary point

The phase attached to `χ(1/2+it)` twisted by one Dirichlet frequency is

```text
f_B(t) = (B+1) t - t log t,
```

where `B` collects the frequency and the `2π` normalisation.  It has a unique stationary point at
`t₀ = e^B`, where `f_B(t₀) = t₀` and `f_B''(t₀) = -1/t₀`.

Rescaling by the stationary point, `t = t₀(1+v)`, factors the phase *exactly* through the universal
profile of `LogPhaseProfile`:

```text
f_B(t₀(1+v)) - f_B(t₀) = t₀ · ψ(v),      ψ(v) = v - (1+v) log(1+v).
```

No approximation is involved: the whole family of archimedean phases has one and the same local
shape, with the stationary point supplying the single scale `t₀`.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

/-- The archimedean phase `f_B(t) = (B+1)t - t log t`. -/
def logLinearPhase (B t : ℝ) : ℝ := (B + 1) * t - t * Real.log t

theorem hasDerivAt_logLinearPhase (B : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (logLinearPhase B) (B - Real.log t) t := by
  have hne : t ≠ 0 := ne_of_gt ht
  have h1 : HasDerivAt (fun x : ℝ => (B + 1) * x) ((B + 1) * 1) t :=
    (hasDerivAt_id' (x := t)).const_mul (B + 1)
  have h2 : HasDerivAt (fun x : ℝ => x * Real.log x) (1 * Real.log t + t * t⁻¹) t :=
    (hasDerivAt_id' (x := t)).mul (Real.hasDerivAt_log hne)
  have h := h1.sub h2
  refine h.congr_deriv ?_
  field_simp
  ring

/-- The stationary point is `t₀ = e^B`. -/
theorem logLinearPhase_deriv_exp (B : ℝ) :
    HasDerivAt (logLinearPhase B) 0 (Real.exp B) := by
  have h := hasDerivAt_logLinearPhase B (Real.exp_pos B)
  simpa [Real.log_exp] using h

/-- The phase value at the stationary point is the stationary point itself. -/
theorem logLinearPhase_exp (B : ℝ) : logLinearPhase B (Real.exp B) = Real.exp B := by
  simp only [logLinearPhase, Real.log_exp]
  ring

/-- **The exact reduction to the universal profile.**  Every archimedean phase, rescaled by its
stationary point, is the stationary value times `ψ`. -/
theorem logLinearPhase_sub_eq (B : ℝ) {v : ℝ} (hv : -1 < v) :
    logLinearPhase B (Real.exp B * (1 + v)) - logLinearPhase B (Real.exp B)
      = Real.exp B * logPhaseProfile v := by
  have hpos : (0 : ℝ) < 1 + v := by linarith
  have hlog : Real.log (Real.exp B * (1 + v)) = B + Real.log (1 + v) := by
    rw [Real.log_mul (Real.exp_ne_zero B) (ne_of_gt hpos), Real.log_exp]
  simp only [logLinearPhase, logPhaseProfile, hlog, Real.log_exp]
  ring

/-- The phase never exceeds its stationary value. -/
theorem logLinearPhase_le_exp (B : ℝ) {v : ℝ} (hv : -1 < v) :
    logLinearPhase B (Real.exp B * (1 + v)) ≤ logLinearPhase B (Real.exp B) := by
  have h := logLinearPhase_sub_eq B hv
  have hmul : Real.exp B * logPhaseProfile v ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos B).le (logPhaseProfile_nonpos hv)
  linarith [h, hmul]

/-- **Two-sided quadratic control of the phase drop.**  On `|v| ≤ 1` the phase falls off from its
stationary value like `t₀ v²`, with absolute constants. -/
theorem logLinearPhase_drop_bounds (B : ℝ) {v : ℝ} (hv : -1 < v) (hv1 : v ≤ 1) :
    Real.exp B * (v ^ 2 / 4)
        ≤ logLinearPhase B (Real.exp B) - logLinearPhase B (Real.exp B * (1 + v)) ∧
      logLinearPhase B (Real.exp B) - logLinearPhase B (Real.exp B * (1 + v))
        ≤ Real.exp B * v ^ 2 := by
  have h := logLinearPhase_sub_eq B hv
  have hE : (0 : ℝ) < Real.exp B := Real.exp_pos B
  constructor
  · have hlow := sq_div_four_le_neg_logPhaseProfile hv hv1
    nlinarith [h, hlow, hE]
  · have hup := neg_logPhaseProfile_le_sq hv
    nlinarith [h, hup, hE]

end GaloisForLFunctions.RHTower
