# Logarithmic Period Unitary Equivalence, Window Frobenius Defect, and `sym_n` / Stick-Schur Transfer

- **ID:** logarithmic-period-window-fold-transfer-and-frobenius-defect
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** [obstacles-summary.md](../../../reports/review-0211/obstacles-summary.md) (§2.4, §2.5.1, §2.6.2)
- **Statement:** (1) The logarithmic period transform `(U_LP f)(u) = (2 cosh u)^(-3) e^(u/4) f(e^u)` is a norm-preserving unitary map from `H_LP = L²((0, ∞), w_LP da)` onto `L²(ℝ, du)` intertwining `I_s` with `windowMultiplier u (2s) * F(-u)` (`windowMultiplier u (2s) = e^(-(2s - 1/2) u)`) and transforming the folded co-isometry defect of every `+1` `I_s`-fixed period `ψ` into `-∫_0^∞ (e^(δu) + e^(-δu))(e^(δu) - e^(-δu))² |F(u) F(-u)| du` (`δ = 2 Re s - 1/2`); (2) for every continuous window test `H` supported on `[-A, 0]` (`A > 0`), its canonical `+1` `I_s`-invariant Mayer period lift `ψ_{H,s}` satisfies `lewisCoIsometryDefect s ψ_{H,s} = -∫_{-A}^0 (‖windowMultiplier x (2s)‖ + ‖windowMultiplier (-x) (2s)‖)(‖windowMultiplier x (2s)‖ - ‖windowMultiplier (-x) (2s)‖)² H(x)² dx`, while `foldSym A (log n) H` and `foldEnergy A (log n) H` (`n ≥ 2`, `log n ≤ A`) equal the multiplicative-Haar `da/a` symmetric and antisymmetric `b ↦ n b` dilation integrals of the canonical period profile `(W_s ψ_{H,s})(b) = (b + b⁻¹)^(-3) b^(Re s) ψ_{H,s}(b)` on `[1, e^A / n]`; and (3) `lewisCoIsometryDefect s ψ_{H,s}` satisfies two-sided quantitative transfer bounds against `(foldSym, foldEnergy)` — lower-bounded at every active stage `A ≥ log n` by `¼ (n^δ + n^(-δ))(n^δ - n^(-δ))² (foldSym A (log n) H - foldEnergy A (log n) H)` (sharpening to `½ (...) foldSym` on fold-symmetric tests, with first-prime coefficient equal to the `windowMultiplier (log 2) (2s)` Frobenius gap) and upper-bounded for `A ≥ 2 log 2` by `(e^(δA) + e^(-δA))(e^(δA) - e^(-δA))² (½ foldEnergy A (log 2) H + foldSym A (log 2) H)` — together with an integrated 3-square `twoVertexStick_sq_eq` Schur elimination across the disjoint first-prime fold `log 2 ≤ A < 2 log 2`.

## Goal
Build the exact Hilbert-space and quadratic-form bridge between the folded Mayer co-isometry defect kernel `-(b + b⁻¹)^(-6) b^(2 Re s - 1)(b^δ + b^(-δ))(b^δ - b^(-δ))²` on `(1, ∞)` (`LewisPeriodReflectionPositivity.lean`), the CWS window Frobenius multiplier (`TheFrobeniusAtInfinityOfAWindow.lean`) and symmetric fold masses `foldSym` (`TheFirstPrimeFold.lean`, §2.5.1), the nonlocal `T₂`-stick Schur squares (`VariableHubSchurAndFoldedMarkovObstruction.lean`), and the §2.4 conformal/Frobenius rate `δ = 2 Re s - 1/2`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean module `MayerWindowFoldTransfer.lean`, `lake --old env lean` green, `#print axioms` PASS

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
(U_LP(I_s f))(u) = (2 cosh u)^(-3) e^(u/4) exp(-2s u) (2 cosh u)^3 e^(u/4) (U_LP f)(-u)
  = exp(-((2s - 1/2) * u)) (U_LP f)(-u) = windowMultiplier u (2s) * (U_LP f)(-u).
```
For any `+1` `I_s`-fixed period `ψ` satisfying the integrability hypotheses of `lewisCoIsometryDefect_eq_neg_integral`, set `F = U_LP ψ` and `δ = 2 Re s - 1/2`. Then `F(-u) = exp((2s - 1/2) u) F(u)`, so `‖F(-u)‖ = e^(δu) ‖F(u)‖` and `‖F(u) F(-u)‖ = e^(δu) ‖F(u)‖² = (2 cosh u)^(-6) e^((2 Re s) u) ‖ψ(e^u)‖²`. Substituting `b = e^u` (`db = e^u du`) on `(1, ∞)` (`u ∈ (0, ∞)`) into `lewisCoIsometryDefect_eq_neg_integral` yields:
```text
lewisCoIsometryDefect s ψ
  = -∫_0^∞ (e^(δu) + e^(-δu)) (e^(δu) - e^(-δu))² ‖F(u) F(-u)‖ du
  = -8 ∫_0^∞ cosh(δu) sinh²(δu) ‖F(u) F(-u)‖ du.
```

### 2. Canonical `I_s`-Invariant Mayer Period Lift of Window Tests and Multiplicative-Haar Fold Dictionary

Let `H : ℝ → ℝ` be continuous with `supp(H) ⊆ [-A, 0]` (`A > 0`, so `H(0) = 0`). Define `F_{H,s} : ℝ → ℂ` by
```text
F_{H,s}(u) :=
  if u > 0 then e^(-δu / 2) H(-u)
  else if u < 0 then exp((2s - 1/2)(-u) - δ(-u)/2) H(u)
  else 0,
```
and set `ψ_{H,s}(a) := (U_LP⁻¹ F_{H,s})(a) = (a + a⁻¹)^3 a^(-1/4) F_{H,s}(log a)` on `(0, ∞)`.
1. **`I_s`-invariance:** At `a = 1` (`u = 0`), `F_{H,s}(0) = 0` gives `ψ_{H,s}(1) = 0 = (I_s ψ_{H,s})(1)`. For `a > 0` with `u = log a ≠ 0`, `windowMultiplier u (2s) * F_{H,s}(-u) = F_{H,s}(u)` holds by direct sign split (`u > 0` vs `u < 0`), so `lewisModularInversion s ψ_{H,s} a = ψ_{H,s} a` for all `a > 0`.
2. **Compact support on `[e^(-A), e^A]` and exact norm/defect formulas:** `F_{H,s}` is continuous on `ℝ` (`H(0) = 0` matches both branches at `u = 0`) and vanishes outside `[-A, A]`. For `u > 0`, `‖F_{H,s}(u)‖² = e^(-δu) H(-u)²`, `‖F_{H,s}(-u)‖² = e^(δu) H(-u)²`, and `‖F_{H,s}(u) F_{H,s}(-u)‖ = H(-u)²`. Substituting `x = -u ∈ [-A, 0]` gives:
   ```text
   lewisCriticalNormSq ψ_{H,s} = ∫_{-A}^0 (e^(δx) + e^(-δx)) H(x)² dx,
   lewisCoIsometryDefect s ψ_{H,s}
     = -∫_{-A}^0 (‖windowMultiplier x (2s)‖ + ‖windowMultiplier (-x) (2s)‖) *
         (‖windowMultiplier x (2s)‖ - ‖windowMultiplier (-x) (2s)‖)² * H(x)² dx.
   ```
3. **Multiplicative-Haar Period Dictionary for `foldSym` and `foldEnergy`:**
   For `b > 1` (`u = log b > 0`), the canonical normalized period profile
   `(W_s ψ)(b) := (b + b⁻¹)^(-3) b^(Re s) ψ(b)` satisfies `(W_s ψ_{H,s})(b) = H(-log b)`.
   For any `n ∈ ℕ` (`n ≥ 2`) with `log n ≤ A`, substituting `x = -log(n b) = -log b - log n` (`b ∈ [1, e^A / n]`, `x ∈ [-A, -log n]`, `x + log n = -log b`, `dx = db / b`) yields:
   ```text
   foldSym A (log n) H
     = (1/2) ∫_{b ∈ Icc 1 (e^A / n)} ((W_s ψ_{H,s})(n b) + (W_s ψ_{H,s})(b)).re² / b db,
   foldEnergy A (log n) H
     = ∫_{b ∈ Icc 1 (e^A / n)} ((W_s ψ_{H,s})(n b) - (W_s ψ_{H,s})(b)).re² / b db.
   ```

### 3. Two-Sided Quantitative Transfer Bounds and `T₂`-Stick Schur Elimination

Let `D_δ(u) := (e^(δu) + e^(-δu))(e^(δu) - e^(-δu))² = 8 cosh(δu) sinh²(δu) ≥ 0` on `[0, ∞)`.
For `0 ≤ u₁ ≤ u₂`, `|δ u₁| ≤ |δ u₂|` implies `cosh(δ u₁) ≤ cosh(δ u₂)` and `sinh²(δ u₁) = sinh²(|δ u₁|) ≤ sinh²(|δ u₂|) = sinh²(δ u₂)`, so `D_δ` is nondecreasing on `[0, ∞)`.
1. **Universal `n`-th Fold Lower Bound (`A ≥ log n`, `n ≥ 2`):**
   For `x ∈ [-A, -log n]`, `-x ≥ log n ≥ 0`, so `D_δ(-x) ≥ D_δ(log n) = (n^δ + n^(-δ))(n^δ - n^(-δ))²`.
   For all real `a, b`, the sum-of-squares identity `8 a² - (a + b)² + 2 (a - b)² = (3 a - b)² ≥ 0` gives `a² ≥ (1/8)(a + b)² - (1/4)(a - b)²` with exact remainder `(1/8)(3a - b)²`.
   Setting `a = H(x)`, `b = H(x + log n)` and integrating over `[-A, -log n]` gives
   ```text
   ∫_{-A}^{-log n} H(x)² dx ≥ (1/4) foldSym A (log n) H - (1/4) foldEnergy A (log n) H,
   ```
   and hence
   ```text
   -lewisCoIsometryDefect s ψ_{H,s}
     ≥ ((n^δ + n^(-δ))(n^δ - n^(-δ))² / 4) * (foldSym A (log n) H - foldEnergy A (log n) H).
   ```
   When `H(x + log n) = H(x)` on `[-A, -log n]` (`foldEnergy = 0`), `foldSym A (log n) H = 2 ∫_{-A}^{-log n} H(x)² dx`, sharpening the constant from `1/4` to `1/2`:
   `-lewisCoIsometryDefect s ψ_{H,s} ≥ ((n^δ + n^(-δ))(n^δ - n^(-δ))² / 2) * foldSym A (log n) H`.
   At the first prime `n = 2`, `(2^δ + 2^(-δ))(2^δ - 2^(-δ))²` equals `(‖windowMultiplier (log 2) (2s)‖ + ‖windowMultiplier (-log 2) (2s)‖)(‖windowMultiplier (log 2) (2s)‖ - ‖windowMultiplier (-log 2) (2s)‖)²`.
2. **Universal `T₂` Capacity Upper Bound (`A ≥ 2 log 2`):**
   When `A ≥ 2 log 2`, every `x ∈ [-A, 0]` satisfies either `x ≤ -log 2` (`x ∈ [-A, -log 2]`) or `x > -log 2 ≥ log 2 - A` (`x ∈ [log 2 - A, 0]`), so `inWindowCount A (log 2) x ≥ 1` on `[-A, 0]`. Since `D_δ(-x) ≤ D_δ(A)` on `[-A, 0]` and `∫ inWindowCount A (log 2) x * H(x)² dx = foldEnergy A (log 2) H / 2 + foldSym A (log 2) H`,
   ```text
   0 ≤ -lewisCoIsometryDefect s ψ_{H,s}
     ≤ D_δ(A) * ∫_{-A}^0 H(x)² dx
     ≤ (e^(δA) + e^(-δA))(e^(δA) - e^(-δA))² * (foldEnergy A (log 2) H / 2 + foldSym A (log 2) H).
   ```
   Consequently, any nonlocal capacity or Schur upper bound `foldSym A (log 2) H ≤ B` transfers directly to `-lewisCoIsometryDefect s ψ_{H,s} ≤ D_δ(A) (foldEnergy A (log 2) H / 2 + B)`.
3. **Integrated `T₂`-Stick 3-Square Schur Elimination on Disjoint First-Prime Windows (`log 2 ≤ A < 2 log 2`):**
   For `x ∈ [-A, -log 2]` (`x₁ = x + log 2 ∈ [log 2 - A, 0]` near the self-dual point `0` where `D_δ(0) = 0`, `x₂ = x ∈ [-A, -log 2]` in the outer cusp sector), applying `WindowJumpCounts.twoVertexStick_ge_schur` pointwise to `(u₁, u₂) = (H(x + log 2), H(x))` with potentials `p₁(x), p₂(x)`, hub weights `w₁(x), w₂(x)`, and `T₂` fold bridge `g₁₂ * (H(x + log 2) - H(x))²` (whose integral over `[-A, -log 2]` is `g₁₂ * foldEnergy A (log 2) H`) yields the exact nonlocal Schur lower bound absorbing outer negativity `p₂(x) + w₂(x) < 0` whenever `stickDiag1 > 0` and `stickDet > 0`.

## Log
- 2026-11-02 — complete dependency-closed paper proof recorded in `2-fully-proven/`.
