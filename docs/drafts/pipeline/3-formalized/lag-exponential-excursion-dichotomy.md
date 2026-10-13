# Lag excursions: exponential rarity is rigid, subexponential rarity is blind

- **ID:** lag-exponential-excursion-dichotomy
- **Stage:** 3-formalized (both halves)
- **Source:** JAS goal loop row 201

## Statement
Setting: positive weights `c_i` with `Σ c_i < ∞`, locally finite exponents `w_i` with `Re w_i ≤ B`, and `Φ(t) = Re Σ c_i e^{t w_i}`.

1. **[L] Rigidity.** If `Φ ≤ M` on `[0,∞) ∖ E` with `∫_E e^{κu} du < ∞` for some `κ > 0`, then all `Re w_i ≤ 0`.
2. **[P] Sharpness.** Let `f > 0` be decreasing with `∫^∞ f(t) dt/t < ∞`. Then there is an off-line configuration with `|{Φ > 0} ∩ [k,k+1]| ≤ e^{−f(k)k}` for all large `k`.

## Proof of 1 (Lean)
- Put `φ = Φ` off `E` and `φ = M` on `E`. Then `Lφ = Λ − ∫_E(Φ−M)e^{−su}`.
- The correction is holomorphic on `Re s > B − κ`, with a uniform bound `(|M| + Σc)∫_E e^{κu}` for real `s > B − κ`.
- `false_of_realPole` therefore excludes the maximal real exponent `p > max(B − κ, 0)`.
- The twist `1 + cos(t Im w_j)` keeps `Φ ≤ M` off the same `E`, so `Re w_i ≤ max(B − κ, 0)`.
- Iterate `⌈B/κ⌉` times.

## Proof of 2 (paper)
- Blocks `b`: points `δ_b + i d ω_b` for `0 < |d| < K_b`, with Fejér weights. Block lag `(c_b e^{δ_b t}/2)(F_b − 1)`.
- `Φ > 0` forces `t` into the windows `{|sin(ω_b t/2)| < ε_b}` with `ε_b = (2^{b+1}/K_b)^{1/2}` and `t < τ_b = log(2^{b+1}K_b c_b/c_{b+1})/g_b`.
- Summability fixes `c_{b+1} = c_b K_b 2^{−b}/K_{b+1}`, so `τ_b ≈ L_{b+1}/g_b` with `L_b = log K_b`.
- Density `≤ e^{−f(t)t}` on `[τ_{b−1}, τ_b)` needs `g_b ≳ 2f(τ_b)L_{b+1}/L_b`.
- With `L_{b+1} = 2L_b`, `Σ g_b < ∞` reduces to `Σ_b f(c2^b) < ∞`, i.e. `∫ f/t < ∞`.
- Local finiteness: block `b` lives at heights `≥ ω_b = b + 1`.

## Open
- The window `f → 0`, `∫ f/t = ∞` (e.g. density `e^{−t/log t}`): blind or rigid?
- `ζ` corollary: DONE (row 202, MUST-1389). `RHTower.riemannHypothesis_iff_integrableOn_exp_lagExcursion` in `RHTower/WeilLagFunctionExponentialExceptionCriterion`, by a direct `ζ` bootstrap through the strip-form positive-part criterion.

## Lean
- Module `RHTower/WeilLagExponentialExceptionRigidity`.
- Theorems: `re_nonpos_of_lag_le_except`, `re_nonpos_of_integrableOn_exp_excursion`, `re_le_of_lag_le_except`, and the generic `hasDerivAt_laplace_of_integrable`.
- MUST-1386. Standard axioms.

## Addendum (row 203): finite measure and attained tops [L]
- `exists_re_gt_of_lag_le_finiteMeasure`: if the excursions off which `Φ ≤ M` holds have finite measure, then no exponent attains a positive `sup Re w`.
- So finite measure is rigid for attained tops and blind for non-attained ones (MUST-1382).
- **Conjecture (Paley–Wiener law).** Excursion density `e^{−f(t)t}` (`f` decreasing) is rigid iff `∫^∞ f(t) dt/t = ∞`.
  - The blind side is the paper construction above.
  - The rigid side would need a quasianalytic (Carleman / Levinson–Sjöberg type) continuation of the exceptional correction across `Re s = sup Re w` at a non-attained top.

## Sharpness in Lean (row 205)
- `RHTower.SubexpExcursion.exists_configuration_excursion_le` in `RHTower/WeilLagSubexponentialExcursionBlind`.
- Statement: for every decreasing `f` with `Σ f(2^b) < ∞` there is an off-line configuration with excursion density `≤ e^{−f(k)k}`. Standard axioms.
- The Fejér family is optimal: it can reach exactly `Σ f(2^b) < ∞`.

## Addendum — ζ with finite-measure excursions (MUST-1392)

- **Theorem [L].** For every real `a`: `Φ ≤ M e^{aL}` on `[0,∞)` minus a measurable finite-measure set, together with an attained top `β₀`, gives `β₀ ≤ ½ + a`.
- **Capstones [L].**
  - RH ⟺ ZAL ∧ ∃M, `|{L ≥ 0 : Φ(L) > M}| < ∞`. EventualHadamardPositivity may replace ZAL.
  - RH ⟺ ZAL ∧ JAS level-one interval positivity off a finite-measure set of log-scales.
- **Proof.** The ζ configuration has complex weights `1/(ρ(1−ρ))` with Re > 0, and multiplicities (non-injective exponents) are allowed. `MaxRealPositive` holds because every weight has positive real part. Twist `1 + cos(γ₀L)` at the attaining zero, then apply the sharp Landau round at κ = 0.
- Module `RHTower/WeilLagFunctionFiniteMeasureExcursion`.
