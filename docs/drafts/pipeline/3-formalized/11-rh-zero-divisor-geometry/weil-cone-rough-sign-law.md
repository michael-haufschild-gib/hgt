# The rough sign law of the Weil cone (notch-small decorations only remove rough mass)

- **ID:** weil-cone-rough-sign-law
- **Stage:** 3-formalized (MC loop cycle 178)
- **Type:** THEOREM (Lean)
- **Source:** cycle 177 (MUST-599) boundary; HF krein-producer-loops L200/L201/L206 (evaporation profiles)
- **Statement:** For every full-cone Weil-positive `lam` whose deviation `d = lam − Λ` is notch-small, and every `y ≥ 2`, `liminf_k Σ_{n≤k, n y-rough} d(n)/n ≤ 0`. In particular, for every `κ > 0` the Cramér-restored profile `Λ + κ(1_ℙ − 1/log n)` is not Weil-positive.

## Goal
- MUST-599 needed fibre sums that converge and are summable on composites. Its method sees more: with `ε = 0`, the notch main functional is exactly the `P`-rough harmonic sum of `d`. So the method yields a **sign law** on every deviation class it can control. The class it controls is exactly "notch-small":
  - `Σ_{n≤x}|d|/n = o(log x)`;
  - `Σ_{n≤x}|d|/√n = o(√x)`;
  - `Σ_{n>x}|d|n^{−3/2} = o(x^{−1/2})`.
- Notch-small is strictly larger than `o(Λ)`. It contains every null sequence, hence HF's Cramér density `κ/log n` on composites, which MUST-599 cannot reach.

## Gates
- [x] 0 → 1: well-posed; the kill attempt and audit are below.
- [x] 1 → 2: complete paper proof, below.
- [x] 2 → 3: formalized. Lean theorems:
  - `RHTower.WeilAbscissa.roughSum_nonpos_of_weilPositiveFull`;
  - `RHTower.WeilAbscissa.nonpos_of_roughSum_ge` (deviation form);
  - `RHTower.WeilAbscissa.not_weilPositiveFull_cramerProfile`;
  - class API `RHTower.PrimeSmallDeviation.NotchSmall`, with `IsLittleOVonMangoldt.notchSmall`, `notchSmall_of_tendsto_zero`, `NotchSmall.add` and `NotchSmall.mono`.

  `lake build --old` is green, `lake env lean` gives a clean final audit, and only the standard axioms are used.

## Approach and proof
1. **Rough main functional.** The notch weight `q = notchWeight P 0 n₀` (`ε = 0`) has main weight `mW(n) = 1_{vecOf P n = 0} n^{−½}`. So `Σ v(n) mW(n) = Σ_{rough} d(n)/n`.
2. **Ramp lower bound without an upper bound on `S`.** For `M ≥ T`, the Abel form is `β₀ R(M) + S(M)(β₀ log(u/M) + β₁)`. Here `u ≥ 4K₀M` gives `log(u/M) ≥ log 4`, and `β₁ ≥ −(log 2) β₀` (`notchProfileLogMass_ge`: the profile lives on `[½, 5/2]`). So the coefficient of `S(M)` is `≥ 0`, and `S(M) ≥ c` suffices. Only a lower bound on `S(k)` for `k < T` is needed, which is a finite set.
3. **Scale inequality.** The MUST-599 bookkeeping goes through verbatim with `NotchSmall` in place of `o(Λ)`. The four fields are exactly the harmonic, square-root, tail and summability inputs used there. The result is `κ log(L − 1) ≤ C_η + η K log(L − 1)`, which contradicts `Y > 0`.
4. **Cramér corollary** (`y = 2`, so rough means odd):
   - The odd rough sum of `d = κ(1_ℙ − 1/log n)` is `κ(Σ_{odd p≤k} 1/p − Σ_{odd 3≤n≤k} 1/(n log n))`.
   - Mertens (`mertens_lower_add_one`) gives the first sum `≥ log log(k+1) − 3/2`.
   - The pairing `2·Σ_odd g ≤ Σ g` for the decreasing `g(n) = 1/(n log n)`, with the telescoping bound `g(n) ≤ log log n − log log(n−1)`, gives the second sum `≤ ½ log log k + 1`.
   - So the sum is `≥ κ` for `k ≥ e^{e^7}`, and the sign law gives `κ ≤ 0`.
   - `d = κ1_ℙ − κ/log n` is notch-small: `κ1_ℙ = o(Λ)`, and `κ/log n → 0`.

## Kill attempt and audit
- **FALSE?** No; the proof is complete and formal.
- **CIRCULAR?** No.
- **REDISCOVERED?**
  - The corpus exclusions (MUST-584/586/588/591/599) are all two-sided or summability-based.
  - None excludes a pinned, sign-indefinite, non-summable deviation carrying a composite Cramér density.
  - HF's trace heuristic (L201) predicts that a continuous producer must have a prime deficit `+1/(4π)`. The rough sign law is a rigorous one-sided version for notch-small decorations: rough excess is impossible.
- **INSIGNIFICANT?** Moderate significance.
  - It proves rigorously the sign half of HF's L200 principle ("a decoration of `Λ` must remove zero-mass"), for notch-small decorations.
  - It kills the prime-excess half of the Cramér-profile family.
  - It does **not** reach HF's actual pinned profile (`κ < 0` here, i.e. prime deficit). There the rough sums tend to `−∞` and the notch pairing is consistent.
- **Verdict:** SURVIVES → [L].

## No-go closure (for the method)
- **Exact limit:** the notch cannot exclude any deviation whose rough sums have `liminf ≤ 0`. Prime-deficit profiles (HF's L201, `κ = −1/(4π)` in this card's convention) are invisible to every notch or Bohr-lift test. Their exclusion needs local (GUE-scale) information near the zeros, as in L201's `log|ζ|` argument, which is RH-conditional and heuristic.
- **Strongest positive survivor:** the rough sign law itself, formal.
- **New insight:**
  - Notch/Bohr-lift tests weight all rough integers equally, and prime reciprocals dominate the rough harmonic mass.
  - So these tests certify only "no rough excess".
  - Window pinning then forces rough deficits to be balanced by non-rough excess.
  - Any complete exclusion of evaporation must use a test that separates primes from rough composites, i.e. a `Λ`- or `μ`-weighted test. This is HF's L214 MC/mollifier terminus.

## Log
- 2026-10-01 — cycle 178: conjecture, proof and formalization (modules `WeilRoughFibreSignLaw`, extended `PrimeSmallDeviationArithmetic`, `ZetaNotchRampMainTerm`, `WeilLittleOVonMangoldtRigidity`).
