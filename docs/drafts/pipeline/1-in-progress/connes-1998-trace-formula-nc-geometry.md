# Connes 1998 — Trace formula in noncommutative geometry and the zeros of the Riemann zeta function

- **ID:** connes-9811068
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — formalization programme
- **Source:** arXiv:math/9811068 (Selecta Math. NS 5 (1999) 29–106). Local LaTeX copy fetched from
  `https://arxiv.org/e-print/math/9811068` (single file `zeta.tex`, 5468 lines).
- **Statement:** Formalize unconditionally in Lean 4 every lemma / theorem / provable proposition of
  the paper that mathlib or the HGT corpus does not already own.

## Goal
Own, as closed Lean theorems with no hypotheses beyond the literal mathematical data, the
self-contained mathematical content of Connes' adele-class trace formula paper. The deep global
statements (Thm III.1, Thm VII.4, Thm VIII.5) sit on a large adelic-analysis stack; the programme
builds that stack bottom-up, and every intermediate brick is itself a closed theorem.

## Paper statement inventory

Labels below are `§sec (eq)` or `App X Lemma n`. Status column is maintained here — this card is the
compaction-surviving ledger.

### Tier A — elementary / self-contained
| Tag | Statement | Lean module | Status |
|---|---|---|---|
| A1 | §III(17), App I(2): `ρ(u)=(1+u²)^{δ/2}` submultiplicative up to `2^{δ/2}` | `ConnesSobolevWeight` | DONE |
| A2 | App I(4)(5): weighted translation norm `‖V(v)‖ ≤ (c ρ(v))^{1/2}`; `V(f)` defined | `ConnesSobolevWeight` | DONE |
| A3 | App I(29): `∫ (log|x|)^{2k}(1+log²|x|)^{-δ/2} d*x < ∞ ↔ 2k − δ < −1` | `ConnesSobolevWeight` | DONE |
| A4 | §VII(8): S-unit lattice sup bound `Sup_S y_v ≥ (1/2n)∑|y_v|` on `∑ y_v = 0` | `ConnesSUnitSupBound` | DONE |
| A5 | §VII(43): `|a⁺ − b⁺| ≤ |a − b|` | `ConnesSUnitSupBound` | DONE |
| A6 | §VIII(39)(43): semiclassical area `∫_{D'_+} ω = (2E/2π)logΛ − (E/2π)(log(E/2π) − 1)` | `ConnesSemiclassicalArea` | DONE |
| A7 | App II Lemma 2: `A + B = 0`, i.e. `(1−1/q)² ∑ (−n log q) q^{-n} = −q^{-1} log q` | `ConnesNonArchPrincipalValue` | DONE |
| A8 | App IIb: unique Haar on modulated group; `N=ℝ*₊ ⟹ dλ/λ`; `N=μ^ℤ ⟹ α=log μ`; (9)–(12) | `ConnesModulatedHaar` | DONE |
| A9 | App I(34): `W(λ)^t η_{t,a} = ∑_b C(a,b) λ^{it}(log λ)^b η_{t,a−b}` | `ConnesJordanTriangular` | DONE |
| A10 | §V(28): `g(λ) = h((λ+1)^{-1})|λ+1|^{-1}` is `C_c^∞` on `K` when `h ∈ C_c^∞(K^*)` | `ConnesSymbolChart` | DONE |
| A11 | §III(19): `E U(a) = |a|^{1/2} V(a) E` | `ConnesPeriodizationEquivariance` | DONE |
| A12 | App I(37)(38): `E(f)(x) = E(f̂)(1/x)` for `f ∈ 𝒮(A)₀` from Poisson summation | `ConnesPeriodizationEquivariance` | DONE |
| A13 | App II(44): `(1/2π)∫₀^{2π} dθ/|1−e^{iθ}z|² = 1/(1−|z|²)` (`|z|<1`), `1/(|z|²−1)` (`|z|>1`) | `ConnesComplexFiberIntegral` | DONE |
| A14 | App II(53): `−4∫₀^{π/2} log sin u du = 2π log 2` | `ConnesComplexFiberIntegral` | DONE |
| A15 | App II(49)(51): `j(ε) = 4∫_{log ε}^{log 2} arccos(e^x/2) dx = 2π log(1/ε) + o(1)` | `ConnesComplexLogAreaAsymptotics` | TODO |
| A16 | App II(35): `lim(∫_{|x|≥ε} f d*x + log ε f(0)) = lim(∫ f\|x\|^ε d*x − f(0)/ε)` | `ConnesArchPrincipalValue` | PARTIAL — both indicator computations `A_ε(1_box)=0`, `B_ε(1_box)=0` proved; the limit form needs DCT (moved to B9) |
| A17 | App II(32): `⟨−log|u|, e^{−πu²}⟩ = ½log π + γ/2 + log 2` | `ConnesArchPrincipalValue` | TODO |
| A18 | App II(41): `⟨−log|z|_ℂ, e^{−2π|z|²}⟩ = log 2π + γ` | `ConnesComplexFiberIntegral` | TODO |
| A19 | §V(35): `P(f_a) = P(f) − log|a| f(0)` for the log-regularized principal value | `ConnesArchPrincipalValue` | DONE |
| A20 | §VIII(30): pairs of projections; `sin Θ = |P₁−P₂|`; `Θ` commutes with `P_i`; ℤ/2∗ℤ/2 irreps ≤ 2-dim | `ConnesProjectionPair` | DONE |
| A21 | App I(15)–(20): `⟨1_R,Δ'_s⟩=1`, homogeneity `⟨f^a,Δ'_s⟩=|a|^{-s}⟨f,Δ'_s⟩`, `Δ'_s=(1−q^{-s})Δ_s` | `ConnesLocalHomogeneousDistribution` | DONE |
| A22 | App III: graph δ-section, `∫δ(y−f(x))ξ(y)dy = ξ(f(x))`; transversality ⟺ `1−P` invertible | `ConnesGraphDelta` | TODO |
| A23 | §IV(19)–(21): 1-D flow trace `∫ h(t)/|1−e^t| dt`; multiplicative form `∫ h(u)/|1−u| d*u` | `ConnesGraphDelta` | TODO |
| A24 | §V(7): `(φ∘L)^ = |det L|^{-1} φ̂∘(L^{-1})^t` | `ConnesLinearFourier` | DONE |
| A25 | §V(10)(11): convolution of the two line measures gives the constant `|1−λ|^{-1}` | `ConnesLinearFourier` | DONE |
| A26 | §VIII Lemma 3 model: `Lim ⟨V(f)η_z,η_z⟩ = ∫_{|u|=1} P_z(u) f̂(u) du`; asymptotic orthogonality | `ConnesResonanceModel` | TODO |
| A27 | App I(27)(28): `φ·α = 0` for `α ∈ 𝒟'`, `φ` smooth with finite-order zeros ⟹ `α ∈ span{δ^{(k)}_{x_i}}` | `ConnesDivisionDistribution` | TODO |

### Tier B — heavy analytic layers
| Tag | Statement | Blocking input |
|---|---|---|
| B1 | §V Thm 3 (local trace formula) | symbol calculus + `F(−log|u|) = ρ^{-1}/|a|` on a general local field |
| B2 | §VII Lemma 1 | `L²(X_S)` completion + Fubini on the `O_S^*` orbit |
| B3 | §VII Thm 4 | B1 + B2 + Lemma VII.2 |
| B4 | §VII Lemma 2 | Besov-type `‖ε_Λ η‖_{(1,α,v)} = O(Λ^{-N})` |
| B5 | App I Lemmas 1–5 | Tate/Iwasawa homogeneous distributions on `A` |
| B6 | App I / Thm III.1 | B5 + growth of `L(χ₀,½+it)` |
| B7 | App II Thm 6 | Weil's explicit formula (cited [W3], not proved in the paper) |
| B8 | §VIII Lemma 1, Cor 2, Thm 5, Lemma 3 | B3 + B6 + Weil positivity criterion |
| B9 | App II (35) in limit form | dominated convergence for `∫_{|x|≥ε} h d*x → ∫ h d*x` and `∫ h\|x\|^ε d*x → ∫ h d*x` on `h = f − f(0)1_box`; the reduction to `h(0)=0` is exactly the two indicator computations already proved |

Note: App II Theorem 1 (Weil's explicit formula) is *quoted*, not proved, in this paper; it is not in
the "provable propositions of this paper" scope except through the corpus's own explicit-formula
layer (`XiGuinandWeilExplicitFormula`, `xi_explicitFormula_logDeriv`).

## Corpus assets found before building (do not rebuild)
- `RHTower/FieldOneFiniteStage*` (≈65 modules): `A_S = ℝ × ∏_{v∈S} ℚ_v`, self-dual Haar, S-units,
  Bruhat–Schwartz carrier, orbit summability/periodization (Connes–Marcolli Lemma 2.29 = §VII Lemma 1a
  for `k=ℚ`), idele-class module, fundamental domain, multiplicative-from-additive Haar.
- `RHTower/Slepian*`, `Prolate*`, `CCMRadialProlate*`: the Landau–Pollak–Slepian layer of §VIII.
- `RHTower/XiGuinandWeilExplicitFormula`, `XiExplicitFormulaLogDeriv`: explicit formulas.
- `HTGeometry/PoissonBoundaryPositivity`, `Bottcher/PoissonBoundary`: Poisson kernel.
- `RHTower/ArchimedeanMellinFourier`: Poisson summation (even/dilated).
- `RHTower/CCMRationalAdelicBruhatSchwartzSpace`: Bruhat–Schwartz on `𝔸_ℚ`.

## Log
- 2026-08-21 — created; paper read in full; statement inventory frozen; corpus audit done.
- 2026-08-21 — A1-A3 landed (`ConnesSobolevWeight`); A4, A5 landed (`ConnesSUnitSupBound`);
  A6 landed (`ConnesSemiclassicalArea`); A7 landed (`ConnesNonArchPrincipalValue`);
  A13, A14 landed (`ConnesComplexFiberIntegral`).
- 2026-08-21 — A9 (`ConnesJordanTriangular`), A10 (`ConnesSymbolChart`), A24/A25
  (`ConnesLinearFourier`), A11/A12 (`ConnesPeriodizationEquivariance`) landed.
- 2026-08-21 — A8 (`ConnesModulatedHaar`), A20 (`ConnesProjectionPair`),
  A21 (`ConnesLocalHomogeneousDistribution`), A19 + A16-indicators
  (`ConnesArchPrincipalValue`) landed.  A16's limit form split off as B9.
