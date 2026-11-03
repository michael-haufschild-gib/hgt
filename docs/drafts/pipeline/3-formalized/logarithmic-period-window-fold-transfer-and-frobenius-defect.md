# Logarithmic Period Unitary Equivalence, Window Frobenius Defect, and `sym_n` / Stick-Schur Transfer

- **ID:** logarithmic-period-window-fold-transfer-and-frobenius-defect
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [obstacles-summary.md](../../../reports/review-0211/obstacles-summary.md) (§2.4, §2.5.1, §2.6.2)
- **Statement:** (1) The logarithmic period transform `(U_LP f)(u) = (2 cosh u)^(-3) e^(u/4) f(e^u)` is a norm- and inner-product-preserving unitary bijection between `H_LP = L²((0, ∞), w_LP da)` and `L²(ℝ, du)` intertwining `I_s` with `windowMultiplier u (2s) * F(-u)` (`windowMultiplier u (2s) = e^(-(2s - 1/2) u)`) and transforming the folded co-isometry defect of every `+1` `I_s`-fixed period `ψ` into `-∫_0^∞ (e^(δu) + e^(-δu))(e^(δu) - e^(-δu))² ‖F(u) F(-u)‖ du` (`δ = 2 Re s - 1/2`); (2) for every continuous window test `H` supported on `[-A, 0]` (`A ≥ 0`), its canonical `+1` `I_s`-invariant Mayer period lift `ψ_{H,s}` satisfies `lewisCoIsometryDefect s ψ_{H,s} = -∫_{-A}^0 (‖windowMultiplier x (2s)‖ + ‖windowMultiplier (-x) (2s)‖)(‖windowMultiplier x (2s)‖ - ‖windowMultiplier (-x) (2s)‖)² H(x)² dx`, while `foldSym A (log n) H` and `foldEnergy A (log n) H` (`n ≥ 2`, `log n ≤ A`) equal the multiplicative-Haar `db/b` symmetric and antisymmetric `b ↦ n b` dilation integrals of the canonical period profile `(W_s ψ_{H,s})(b) = (b + b⁻¹)^(-3) b^(Re s) ψ_{H,s}(b)` on `[1, e^A / n]`; and (3) `-lewisCoIsometryDefect s ψ_{H,s}` satisfies two-sided quantitative transfer bounds against `(foldSym, foldEnergy)` — lower-bounded at every active stage `A ≥ log n` by `¼ (n^δ + n^(-δ))(n^δ - n^(-δ))² (foldSym A (log n) H - foldEnergy A (log n) H)` (sharpening to `½ (...) foldSym` on fold-symmetric tests) and upper-bounded for `A ≥ 2 log 2` by `frobeniusDefectFactor s A * (½ foldEnergy A (log 2) H + foldSym A (log 2) H)` — together with an integrated coupled `T₂`-stick Schur lower bound across `[-A, -log 2]` via `g₁₂ * foldEnergy A (log 2) H`.

## Goal
Build the exact Hilbert-space and quadratic-form bridge between the folded Mayer co-isometry defect kernel `-(b + b⁻¹)^(-6) b^(2 Re s - 1)(b^δ + b^(-δ))(b^δ - b^(-δ))²` on `(1, ∞)` (`LewisPeriodReflectionPositivity.lean`), the CWS window Frobenius multiplier (`TheFrobeniusAtInfinityOfAWindow.lean`) and symmetric fold masses `foldSym` (`TheFirstPrimeFold.lean`, §2.5.1), the nonlocal `T₂`-stick Schur squares (`VariableHubSchurAndFoldedMarkovObstruction.lean`), and the §2.4 conformal/Frobenius rate `δ = 2 Re s - 1/2`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.MayerWindowFoldTransfer`, `lake --old env lean` green, `#print axioms` `[propext, Classical.choice, Quot.sound]`

## Complete Paper Proof `[PROVED HERE]`

### 1. Logarithmic Unitary Isomorphism `U_LP : H_LP ≃ L²(ℝ)` and Window Frobenius Intertwining

Define for `f : ℝ → ℂ` and `u ∈ ℝ`:
```text
(U_LP f)(u) := (2 cosh u)^(-3) e^(u/4) f(e^u),
(U_LP⁻¹ F)(a) := (a + a⁻¹)^3 a^(-1/4) F(log a)   (a > 0).
```
Since `2 cosh u = e^u + e^(-u) > 0`, for `a > 0` (`u = log a`, `e^u = a`, `e^(-u) = a⁻¹`), `(U_LP⁻¹(U_LP f))(a) = f(a)` and `(U_LP(U_LP⁻¹ F))(u) = F(u)`.
By the exponential change of variables `a = e^u` (`da = e^u du`) from `ℝ` onto `(0, ∞)`:
```text
lewisCriticalNormSq f = ∫_0^∞ ‖f(a)‖² (a + a⁻¹)^(-6) a^(-1/2) da
  = ∫_ℝ ‖f(e^u)‖² (2 cosh u)^(-6) e^(-u/2) e^u du
  = ∫_ℝ ‖(2 cosh u)^(-3) e^(u/4) f(e^u)‖² du = ∫_ℝ ‖(U_LP f)(u)‖² du,
```
and likewise `lewisCriticalInner f g = ∫_ℝ (U_LP f)(u) conj((U_LP g)(u)) du`.

For `I_s f(a) = a^(-2s) f(a⁻¹)` and `u ∈ ℝ`, since `cosh(-u) = cosh u` and `(e^u : ℂ)^(-2s) = exp(-2s u)`:
```text
(U_LP(I_s f))(u) = exp(-((2s - 1/2) * u)) (U_LP f)(-u) = windowMultiplier u (2s) * (U_LP f)(-u).
```
For any `+1` `I_s`-fixed period `ψ` satisfying the integrability hypotheses of `lewisCoIsometryDefect_eq_neg_integral`, set `F = U_LP ψ` and `δ = 2 Re s - 1/2`. Then `F(-u) = windowMultiplier (-u) (2s) * F(u)`, so `‖F(u) F(-u)‖ = e^(δu) ‖F(u)‖² = (2 cosh u)^(-6) e^((2 Re s) u) ‖ψ(e^u)‖²`. Substituting `b = e^u` (`db = e^u du`) on `(1, ∞)` (`u ∈ (0, ∞)`) into `lewisCoIsometryDefect_eq_neg_integral` yields:
```text
lewisCoIsometryDefect s ψ
  = -∫_0^∞ (e^(δu) + e^(-δu)) (e^(δu) - e^(-δu))² ‖F(u) F(-u)‖ du.
```

### 2. Canonical `I_s`-Invariant Mayer Period Lift of Window Tests and Multiplicative-Haar Fold Dictionary

Let `H : ℝ → ℝ` be continuous with `supp(H) ⊆ [-A, 0]` (`A ≥ 0`, so `H(0) = 0`). Define `F_{H,s} : ℝ → ℂ` by
```text
F_{H,s}(u) :=
  if u > 0 then e^(-((Re s - 1/4) u)) H(-u)
  else if u < 0 then exp(-((2s - 1/2) u)) e^((Re s - 1/4) u) H(u)
  else 0,
```
and set `ψ_{H,s}(a) := (U_LP⁻¹ F_{H,s})(a)` on `(0, ∞)`.
1. **`I_s`-invariance:** `windowMultiplier u (2s) * F_{H,s}(-u) = F_{H,s}(u)` holds for all `u ∈ ℝ`, so `lewisModularInversion s ψ_{H,s} a = ψ_{H,s} a` for all `a > 0`.
2. **Compact support on `[e^(-A), e^A]` and exact defect formula:** `F_{H,s}` is continuous on `ℝ` and vanishes outside `[-A, A]`. For `u > 0`, `‖F_{H,s}(u) F_{H,s}(-u)‖ = H(-u)²`. Substituting `x = -u ∈ [-A, 0]` gives:
   ```text
   lewisCoIsometryDefect s ψ_{H,s}
     = -∫_{-A}^0 (‖windowMultiplier x (2s)‖ + ‖windowMultiplier (-x) (2s)‖) *
         (‖windowMultiplier x (2s)‖ - ‖windowMultiplier (-x) (2s)‖)² * H(x)² dx.
   ```
3. **Multiplicative-Haar Period Dictionary for `foldSym` and `foldEnergy`:**
   For `b > 1`, `(W_s ψ)(b) := (b + b⁻¹)^(-3) b^(Re s) ψ(b)` satisfies `(W_s ψ_{H,s})(b) = H(-log b)`. For any `n ≥ 2` with `log n ≤ A`, substituting `u = -log b - log n` (`b ∈ [1, e^A / n]`, `du = db / b`) yields:
   ```text
   foldSym A (log n) H
     = (1/2) ∫_{b ∈ Icc 1 (e^A / n)} ((W_s ψ_{H,s})(n b) + (W_s ψ_{H,s})(b)).re² / b db,
   foldEnergy A (log n) H
     = ∫_{b ∈ Icc 1 (e^A / n)} ((W_s ψ_{H,s})(n b) - (W_s ψ_{H,s})(b)).re² / b db.
   ```

### 3. Two-Sided Quantitative Transfer Bounds and `T₂`-Stick Schur Elimination

Let `D_s(u) := frobeniusDefectFactor s u = (e^(δu) + e^(-δu))(e^(δu) - e^(-δu))² ≥ 0`, which is nondecreasing on `[0, ∞)`.
1. **Universal `n`-th Fold Lower Bound (`A ≥ log n`, `n ≥ 2`):**
   On `[-A, -log n]`, `D_s(-x) ≥ D_s(log n) = (n^δ + n^(-δ))(n^δ - n^(-δ))²`, while `8 H(x)² - (H(x) + H(x + log n))² + 2 (H(x) - H(x + log n))² = (3 H(x) - H(x + log n))² ≥ 0` integrates to `∫_{-A}^{-log n} H(x)² dx ≥ (foldSym A (log n) H - foldEnergy A (log n) H) / 4`, yielding `-lewisCoIsometryDefect s ψ_{H,s} ≥ (D_s(log n) / 4) * (foldSym A (log n) H - foldEnergy A (log n) H)` (sharpening to `(D_s(log n) / 2) * foldSym A (log n) H` on fold-symmetric tests).
2. **Universal First-Prime Capacity Upper Bound (`A ≥ 2 log 2`):**
   When `A ≥ 2 log 2`, `inWindowCount A (log 2) x ≥ 1` across `[-A, 0]`, so `∫_{-A}^0 H(x)² dx ≤ ∫ inWindowCount A (log 2) x * H(x)² dx = foldEnergy A (log 2) H / 2 + foldSym A (log 2) H`, yielding `-lewisCoIsometryDefect s ψ_{H,s} ≤ D_s(A) * (foldEnergy A (log 2) H / 2 + foldSym A (log 2) H)`.
3. **Integrated Coupled `T₂`-Stick Schur Lower Bound Across `[-A, -log 2]`:**
   Integrating `WindowJumpCounts.twoVertexStick_ge_schur` pointwise at `(u₁, u₂) = (H(x + log 2), H(x))` across `x ∈ [-A, -log 2]` couples inner-origin potentials `(p₁, w₁)` with outer-edge potentials `(p₂, w₂)` (allowing `p₂(x) + w₂(x) < 0`) via `g₁₂ * foldEnergy A (log 2) H`.

## Lean Formalization
- `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.MayerWindowFoldTransfer`:
  - `logPeriodTransform`, `logPeriodInverse`, `windowLogLift`, `windowPeriodLift`, `periodWindowProfile`, `frobeniusDefectFactor`
  - `logPeriodInverse_comp_transform`, `logPeriodTransform_comp_inverse`, `lewisCriticalNormSq_eq_l2NormSq_logPeriodTransform`, `lewisCriticalInner_eq_l2Inner_logPeriodTransform`, `integrable_logPeriodTransform_normSq_iff`
  - `logPeriodTransform_modularInversion`, `lewisCoIsometryDefect_eq_neg_log_integral`, `frobeniusDefectFactor_eq_windowMultiplier`, `frobeniusDefectFactor_mono_nonneg`
  - `lewisModularInversion_windowPeriodLift`, `periodWindowProfile_windowPeriodLift`, `windowPeriodLift_coIsometryDefect_eq`
  - `foldSym_eq_haar_periodWindowProfile`, `foldEnergy_eq_haar_periodWindowProfile`
  - `windowPeriodLift_neg_defect_ge_foldSym_sub_foldEnergy`, `windowPeriodLift_neg_defect_ge_half_foldSym_of_symmetric`, `windowPeriodLift_neg_defect_le_firstPrime_fold`, `integral_firstPrime_stick_ge_schur`

## Log
- 2026-11-02 — complete dependency-closed paper proof recorded in `2-fully-proven/`
- 2026-11-02 — unconditionally formalized in Lean 4 and moved to `3-formalized/`
