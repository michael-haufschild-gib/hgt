import GaloisForLFunctions.BiScaleUncertainty.HyperbolicShiftCommutatorAndParityIntertwining
import GaloisForLFunctions.BiScaleUncertainty.KreinKantorovichMeasureTransportAndPrimePolarPairing

/-!
# Pillar XVI: Hyperbolic Multiplier Increment Calculus & Leakage-Proof Odd-Sector Coercivity

This module develops **Pillar XVI** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**
(`GaloisForLFunctions.BiScaleUncertainty`), resolving **Trap 7 (Hyperbolic Multiplier Leakage,
`OddMultiplierLeakageFamily.lean`)** for the odd-sector routes `OWU`, `HF`, and `CHMD`.

## Mathematical Motivation

In `OddMultiplierLeakageFamily.lean`, it was shown that source blindness `h_f(log 2) = 0` for an
odd 6-packet translation train does **not** imply multiplier blindness
`h_{sinh(α ·) f}(log 2) = 0`: long-range translations can cancel `h_f(log 2)` at a single point
while `sinh(α u)` weights the distant packets exponentially, making `h_{sinh(α ·) f}(log 2)`
arbitrarily large relative to `h_f(0)`.

Why did that leakage occur? Because prior transfer attempts treated `h_{S_α f}(t)` as if it had to
vanish at `t`, instead of coupling the **signed value** `h_{S_α f}(t)` to the collar increments of
`S_α f` and `C_α f` via Pillar XIV (`SignedKreinCollarAndPrimeDeficitTransfer.lean`) and Pillar VI
(`HyperbolicShiftCommutatorAndParityIntertwining.lean`).

This module establishes the **Leakage-Proof Hyperbolic Multiplier Increment Calculus**:
1. **Exact Hyperbolic Multiplier Defect Decomposition (`coshMultiplier_defect_add_sinh_half_sq_eq`):**
   $$\bigl(h_{C_\alpha f}(0) - h_{C_\alpha f}(x)\bigr) + 2\sinh(\alpha x / 2)^2 h_f(0)
     = \cosh(\alpha x)\bigl(h_f(0) - h_f(x)\bigr) + \bigl(h_{S_\alpha f}(0) - h_{S_\alpha f}(x)\bigr).$$
   Since both terms on the right-hand side are pointwise nonnegative for every `x ∈ ℝ`, this single
   identity simultaneously bounds `h_{S_α f}(0) - h_{S_α f}(x)` and `cosh(α x)(h_f(0) - h_f(x))` by
   the `C_α f` increment plus `2 sinh(α x / 2)² h_f(0)`.
2. **Signed Collar Leverage on `sinhMultiplier` & `coshMultiplier` (No Multiplier Blindness Needed):**
   Applying Pillar XIV to `S_α f` and `C_α f` shows that for **arbitrary signed** `h_{S_α f}(t) ∈ ℝ`,
   $$W_0\bigl(h_{S_\alpha f}(0) - h_{S_\alpha f}(y)\bigr) + w\bigl(h_{S_\alpha f}(0) - h_{S_\alpha f}(t + y)\bigr)
     + w\,h_{S_\alpha f}(t) \;\ge\; \left(w - \frac{w^2}{2 W_0}\right) h_{S_\alpha f}(0).$$
3. **Zero-Grid Coincidence Lift (`coshMultiplier_signed_collar_ge_of_source_zero`):**
   Whenever the original source is blind at `t` (`h_f(t) = 0`), zero-grid coincidence gives
   `h_{C_α f}(t) = h_{S_α f}(t)`, so the leaked multiplier value `w h_{S_α f}(t)` combines with the
   `C_α f` collar defect to bound **both** the base energy `h_f(0)` and the full multiplier energy
   `h_{S_α f}(0)`:
   $$W_0\bigl(h_{C_\alpha f}(0) - h_{C_\alpha f}(y)\bigr) + w\bigl(h_{C_\alpha f}(0) - h_{C_\alpha f}(t + y)\bigr)
     + w\,h_{S_\alpha f}(t) \;\ge\; \left(w - \frac{w^2}{2 W_0}\right)\bigl(h_f(0) + h_{S_\alpha f}(0)\bigr).$$
-/

namespace GaloisForLFunctions.BiScaleUncertainty

open MeasureTheory Set Filter
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open scoped RealInnerProductSpace BigOperators

noncomputable section

/-! ## §1. Exact Two-Positive-Term Hyperbolic Multiplier Defect Decomposition -/

/-- **Exact Hyperbolic Multiplier Defect Decomposition:**
For any continuous compactly supported `f : ℝ → ℝ` and any `α, x ∈ ℝ`,
$$\bigl(h_{C_\alpha f}(0) - h_{C_\alpha f}(x)\bigr) + 2\sinh(\alpha x / 2)^2 h_f(0)
  = \cosh(\alpha x)\bigl(h_f(0) - h_f(x)\bigr) + \bigl(h_{S_\alpha f}(0) - h_{S_\alpha f}(x)\bigr).$$
Both terms on the right-hand side are nonnegative for all `x ∈ ℝ`. -/
theorem coshMultiplier_defect_add_sinh_half_sq_eq {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (α x : ℝ) :
    (autocorr (coshMultiplier α f) 0 - autocorr (coshMultiplier α f) x) +
        2 * Real.sinh (α * x / 2) ^ 2 * autocorr f 0 =
      Real.cosh (α * x) * (autocorr f 0 - autocorr f x) +
        (autocorr (sinhMultiplier α f) 0 - autocorr (sinhMultiplier α f) x) := by
  have h0 := autocorr_coshMultiplier_zero_eq hf hfc α
  have hx := autocorr_coshMultiplier_sub_sinhMultiplier hf hfc α x
  have hcosh := cosh_sub_one_eq_two_mul_sinh_half_sq α x
  linear_combination h0 - hx - autocorr f 0 * hcosh

/-- **Domination of the `sinhMultiplier` Increment by the `coshMultiplier` Increment:**
For every `α, x ∈ ℝ`,
$$0 \;\le\; h_{S_\alpha f}(0) - h_{S_\alpha f}(x)
  \;\le\; \bigl(h_{C_\alpha f}(0) - h_{C_\alpha f}(x)\bigr) + 2\sinh(\alpha x / 2)^2 h_f(0).$$ -/
theorem sinhMultiplier_defect_le_coshMultiplier_defect {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (α x : ℝ) :
    autocorr (sinhMultiplier α f) 0 - autocorr (sinhMultiplier α f) x ≤
      (autocorr (coshMultiplier α f) 0 - autocorr (coshMultiplier α f) x) +
        2 * Real.sinh (α * x / 2) ^ 2 * autocorr f 0 := by
  have hdecomp := coshMultiplier_defect_add_sinh_half_sq_eq hf hfc α x
  have hsource_nn : 0 ≤ Real.cosh (α * x) * (autocorr f 0 - autocorr f x) :=
    mul_nonneg (le_of_lt (Real.cosh_pos _)) (autocorr_sub_nonneg hfc hf x)
  linarith

/-- **Domination of the `cosh`-Weighted Source Increment by the `coshMultiplier` Increment:**
For every `α, x ∈ ℝ`,
$$\cosh(\alpha x)\bigl(h_f(0) - h_f(x)\bigr)
  \;\le\; \bigl(h_{C_\alpha f}(0) - h_{C_\alpha f}(x)\bigr) + 2\sinh(\alpha x / 2)^2 h_f(0).$$ -/
theorem cosh_mul_source_defect_le_coshMultiplier_defect {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (α x : ℝ) :
    Real.cosh (α * x) * (autocorr f 0 - autocorr f x) ≤
      (autocorr (coshMultiplier α f) 0 - autocorr (coshMultiplier α f) x) +
        2 * Real.sinh (α * x / 2) ^ 2 * autocorr f 0 := by
  have hdecomp := coshMultiplier_defect_add_sinh_half_sq_eq hf hfc α x
  have hsinh_nn :
      0 ≤ autocorr (sinhMultiplier α f) 0 - autocorr (sinhMultiplier α f) x :=
    autocorr_sub_nonneg (hasCompactSupport_sinhMultiplier α hfc)
      (continuous_sinhMultiplier α hf) x
  linarith

/-! ## §2. Leakage-Proof Signed Collar Leverage for `sinhMultiplier` and `coshMultiplier` -/

/-- **Signed Origin-Collar Leverage for `sinhMultiplier α f` (No Multiplier Blindness Needed):**
For any continuous compactly supported `f`, any `α, t, y ∈ ℝ`, any origin weight `W₀ > 0`, and any
collar weight `w ≥ 0`,
$$\left(w - \frac{w^2}{2 W_0}\right) h_{S_\alpha f}(0)
  \;\le\; W_0\bigl(h_{S_\alpha f}(0) - h_{S_\alpha f}(y)\bigr)
    + w\bigl(h_{S_\alpha f}(0) - h_{S_\alpha f}(t + y)\bigr) + w\,h_{S_\alpha f}(t).$$ -/
theorem sinhMultiplier_signed_collar_origin_leverage_add {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (α : ℝ)
    {W₀ w : ℝ} (hW₀ : 0 < W₀) (hw : 0 ≤ w) (t y : ℝ) :
    (w - w ^ 2 / (2 * W₀)) * autocorr (sinhMultiplier α f) 0 ≤
      W₀ * (autocorr (sinhMultiplier α f) 0 - autocorr (sinhMultiplier α f) y) +
        w * (autocorr (sinhMultiplier α f) 0 - autocorr (sinhMultiplier α f) (t + y)) +
        w * autocorr (sinhMultiplier α f) t :=
  autocorr_signed_collar_origin_leverage_add
    (hasCompactSupport_sinhMultiplier α hfc) (continuous_sinhMultiplier α hf) hW₀ hw t y

/-- **Signed Origin-Collar Leverage for `coshMultiplier α f`:**
For any continuous compactly supported `f`, any `α, t, y ∈ ℝ`, any origin weight `W₀ > 0`, and any
collar weight `w ≥ 0`,
$$\left(w - \frac{w^2}{2 W_0}\right)\bigl(h_f(0) + h_{S_\alpha f}(0)\bigr)
  \;\le\; W_0\bigl(h_{C_\alpha f}(0) - h_{C_\alpha f}(y)\bigr)
    + w\bigl(h_{C_\alpha f}(0) - h_{C_\alpha f}(t + y)\bigr) + w\,h_{C_\alpha f}(t).$$ -/
theorem coshMultiplier_signed_collar_origin_leverage_add {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (α : ℝ)
    {W₀ w : ℝ} (hW₀ : 0 < W₀) (hw : 0 ≤ w) (t y : ℝ) :
    (w - w ^ 2 / (2 * W₀)) * (autocorr f 0 + autocorr (sinhMultiplier α f) 0) ≤
      W₀ * (autocorr (coshMultiplier α f) 0 - autocorr (coshMultiplier α f) y) +
        w * (autocorr (coshMultiplier α f) 0 - autocorr (coshMultiplier α f) (t + y)) +
        w * autocorr (coshMultiplier α f) t := by
  have hbase := autocorr_signed_collar_origin_leverage_add
    (hasCompactSupport_coshMultiplier α hfc) (continuous_coshMultiplier α hf) hW₀ hw t y
  rw [← autocorr_coshMultiplier_zero_eq hf hfc α]
  exact hbase

/-- **Zero-Grid Coincidence Lift (Resolving Trap 7 at Source Zero Nodes `h_f(t) = 0`):**
Whenever `autocorr f t = 0` (as in `OddMultiplierLeakageFamily.lean`), zero-grid coincidence gives
`h_{C_α f}(t) = h_{S_α f}(t)`. Substituting this into `coshMultiplier_signed_collar_origin_leverage_add`
shows that the leaked multiplier correlation `w h_{S_α f}(t)` plus the `C_α f` collar defect is
bounded below by **both** the base energy `h_f(0)` and the full multiplier energy `h_{S_α f}(0)`:
$$\left(w - \frac{w^2}{2 W_0}\right)\bigl(h_f(0) + h_{S_\alpha f}(0)\bigr)
  \;\le\; W_0\bigl(h_{C_\alpha f}(0) - h_{C_\alpha f}(y)\bigr)
    + w\bigl(h_{C_\alpha f}(0) - h_{C_\alpha f}(t + y)\bigr) + w\,h_{S_\alpha f}(t).$$ -/
theorem coshMultiplier_signed_collar_ge_of_source_zero {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (α : ℝ)
    {W₀ w t : ℝ} (hW₀ : 0 < W₀) (hw : 0 ≤ w) (hz : autocorr f t = 0) (y : ℝ) :
    (w - w ^ 2 / (2 * W₀)) * (autocorr f 0 + autocorr (sinhMultiplier α f) 0) ≤
      W₀ * (autocorr (coshMultiplier α f) 0 - autocorr (coshMultiplier α f) y) +
        w * (autocorr (coshMultiplier α f) 0 - autocorr (coshMultiplier α f) (t + y)) +
        w * autocorr (sinhMultiplier α f) t := by
  have hbase := coshMultiplier_signed_collar_origin_leverage_add hf hfc α hW₀ hw t y
  have hcoinc := autocorr_coshMultiplier_eq_sinhMultiplier_of_zero hf hfc α hz
  rw [hcoinc] at hbase
  exact hbase

/-- **Joint Base-Plus-Multiplier Collar Coercivity Under Source Blindness `h_f(t) = 0`:**
Expanding the `C_α f` collar increments via `coshMultiplier_defect_add_sinh_half_sq_eq` shows that
when `h_f(t) = 0`, the leaked multiplier value `w h_{S_α f}(t)` plus the `cosh`-weighted base
collar increments and `S_α f` collar increments controls `(w - w² / (2 W₀))(h_f(0) + h_{S_α f}(0))`
**plus** the nonnegative hyperbolic shift bonus
`2 (W₀ sinh(α y / 2)² + w sinh(α(t + y) / 2)²) h_f(0) ≥ 0`. -/
theorem joint_base_sinhMultiplier_collar_ge_of_source_zero {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (α : ℝ)
    {W₀ w t : ℝ} (hW₀ : 0 < W₀) (hw : 0 ≤ w) (hz : autocorr f t = 0) (y : ℝ) :
    (w - w ^ 2 / (2 * W₀)) * (autocorr f 0 + autocorr (sinhMultiplier α f) 0) +
        2 * (W₀ * Real.sinh (α * y / 2) ^ 2 + w * Real.sinh (α * (t + y) / 2) ^ 2) *
          autocorr f 0 ≤
      W₀ * (Real.cosh (α * y) * (autocorr f 0 - autocorr f y) +
          (autocorr (sinhMultiplier α f) 0 - autocorr (sinhMultiplier α f) y)) +
        w * (Real.cosh (α * (t + y)) * (autocorr f 0 - autocorr f (t + y)) +
          (autocorr (sinhMultiplier α f) 0 - autocorr (sinhMultiplier α f) (t + y))) +
        w * autocorr (sinhMultiplier α f) t := by
  have hbase := coshMultiplier_signed_collar_ge_of_source_zero hf hfc α hW₀ hw hz y
  have hd_y := coshMultiplier_defect_add_sinh_half_sq_eq hf hfc α y
  have hd_ty := coshMultiplier_defect_add_sinh_half_sq_eq hf hfc α (t + y)
  linear_combination hbase + W₀ * hd_y + w * hd_ty

end

end GaloisForLFunctions.BiScaleUncertainty
