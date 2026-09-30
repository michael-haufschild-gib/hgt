# Dyadic rigidity: no Weil-positive system deviates from Λ only at the powers of 2

- **ID:** L159 / weil-cone-dyadic-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** hf-positive-hodge-attack/krein-producer-loops.md (L159)
- **Statement:** Let `lam` be full-cone Weil-positive with `lam(m) = Λ(m)` for every `m ≥ 2` that is not a power `2^k` (`k ≥ 1`). Then `lam = Λ`. The values at `2^k` are unrestricted: any sign, any size within the Weil box, no summability.

## Goal
L158 left one single prime-power line open: `p = 2`. Its ratio-3 decay budget needs
`K(log 2)/K(0) ≲ 0.24`, and the generic shift law gives only `0.388`.

## Gates
- [x] 0 → 1
- [x] 1 → 2 (paper proof below)
- [x] 2 → 3: `RHTower.eq_vonMangoldt_of_weilPositiveFull_of_powers_two`, in `formal/GaloisForLFunctions/RHTower/WeilFullConeDyadicRigidity.lean`.
  - `lake build` is green (22 s).
  - Axioms: `[propext, Classical.choice, Quot.sound]`.
  - Lint reports nothing for the module, which is wired into `RHTower.lean` after `WeilFullConeLacunaryRigidity`.
  - The collision sweep (25 names, ilean plus source) is clean. The generic helpers are private.
- [ ] 3 → 4 (not pursued)

## Paper proof
1. **Sharp lead-term product.** Let `φ₁(s) = e^{−πe^{2s}}(4π²e^{9s/2} − 6πe^{5s/2})`, the leading term of Riemann's `Φ`.
   - With the half-step `d = ½log 2` and all real `s`: `φ₁(|s+d|)φ₁(|s−d|) ≤ (7/50)φ₁(|s|)²`.
   - Substituting `V = e^{2d} ∈ [1,2]` reduces this to `e^{7d}e^{−πV}(8π−3V)(2πV−3) ≤ (7/50)(4π−3V)²`.
   - That inequality is proved on four pieces, `[1, 1.25]`, `[1.25, 1.5]`, `[1.5, 1.75]` and `[1.75, 2]`. It uses monotone envelopes, Taylor lower bounds `e^{π/4} ≥ 2.0937`, `e^{π/2} ≥ 4.45` and `e^{3π/4} ≥ 10.43`, and the substitution `e^{7d} = V³√V`.
   - The case `s < 0` reduces to `s ≥ 0` by symmetry, with the region `|s| < d` treated separately.
2. **Autocorrelation.** Write `K(log 2) = ∫Φ(s+d)Φ(s−d)ds`, apply the sandwich `φ₁ ≤ Φ ≤ (101/100)φ₁` pointwise, then step 1, then `φ₁² ≤ Φ²`. This gives `K(log 2) ≤ (101/100)²(7/50)K(0) ≈ 0.1429·K(0)`.
3. **Higher dyadic steps.** For `k ≥ 2`, the L156 shift law and `R(k+2) ≤ (19/50)8^{−k}` give `K(k log 2) ≤ (101/100)²(19/50)(1/64)^{k−1}K(0)`.
4. **Weight `3 + log n`.** The ratio `(3+log n_i)/(3+log n_j)` is at most `1 + |log n_i − log n_j|/3`. With this weight:
   - `(1 + k log2/3)K(k log2) ≤ 0.177·18^{−(k−1)}K(0)`;
   - `Σ_{k≥1} ≤ 0.1875`;
   - the cross family `Σ_i K(log n_i + log n_j)` is at most `0.0105` times `K(0)`.
5. **Pair test at atom `j`.** Use `Φχ_L − sgn(v_j)Φχ_L(·−log 2^{j+1})`.
   - Positivity with `L → ∞` gives `2|v_j|K(0) ≤ M(3+log n_j)·1.521·K(0)`, with `M = sup|v_i|/(3+log n_i) < ∞` by the Weil box bound.
   - Hence `M ≤ 0.7605M`, so `M = 0`.

## What is new
Every single prime-power line `{p^k : k ≥ 1}` is now rigid in the full Weil cone (L158 and L159).

The constant `7/50` at one dyadic step is a pointwise gap of Riemann's leading theta term. It comes from the double-exponential decay `e^{−πe^{2s}}`, which makes the shifted product small uniformly in `s`.

The rigid sets proved in Lean are the 3-lacunary sets (L158) and the dyadic line (L159). General 2-lacunary sets should follow from the same bounds once `D ↦ (1+D/3)K(D)` is shown monotone on `[log 2, ∞)`; that is not formalized. The open classes are the log-dense ones.

## Log
- 2026-09-30 — L159: sharpened kernel bound, weight change `1 + log n → 3 + log n`, Lean module in one cycle.
