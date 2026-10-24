# The Möbius energy transfers at every superlinear horizon

- **ID:** BVI-SUPERLINEAR-TRANSFER-2026-10-24
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) → Lean
- **Source:** BVI README §7.7 (rates in the cofinal Möbius laws uniform in the band ratio `B`);
  §6.1 Q3 (where the actual Möbius row beats generic bounds); generic mean-square transfer needs
  windows of length `N^{2±o(1)}` (§3.4, flat Selberg row).
- **Statement:** for every `ε > 0` there are `B₀, N₀` with
  `|E_N(M)/M − κ| ≤ ε` for all `N ≥ N₀` and all `M ≥ B₀ N`, where
  `E_N(M) = Σ_{k ≤ M} s_{N,μ}(k)²` and `κ = cofinalMobiusSlope`. Equivalently `E_N(M)/M → κ`
  whenever `M/N → ∞`.

## Paper proof
Write `B = ⌊M/N⌋`.

**Small ratio, `B ≤ J = ⌊N^{1/16}⌋`.** The corpus identity (`sieveL2PrefixEnergy_moebiusReal_eq_quotient_pairs`)
at `M' = (B+1)N` gives `E_N(M') = 1 + Σ_{q,r ≤ B} [Pref(a,b,M'/l) − Pref(a,b,max(q,r)N/l)]`,
`l = [q,r]`, `a = r/(q,r)`, `b = q/(q,r)`, with `Pref(a,b,X) = μ(a)μ(b)·#{n ≤ X : n sqfree, (n,ab)=1}`.
The coprime-squarefree count is `D(ab)X + O(τ(ab)√X)` (`μ²[(·,m)=1] = Σ_{d²e∣·} μ(d)μ(e)`), so
`|E_N((B+1)N) − 1 − N P(B)| ≪ B⁵√N log N` (crude `τ(n) ≤ n`, error `√X log X` per count).
Monotonicity of `E_N` in `M` sandwiches `E_N(M)/M` between `P(B−1)/(B+1)` and `P(B)/B` up to
`≪ J^{-3}`, and `P(B)/B → κ`.

**Large ratio, `B > J`, so `N ≤ B¹⁶`.** `E_N(M) = Σ_{d,e ≤ N} μ(d)μ(e)⌊M/[d,e]⌋`, so
`E_N(M)/M = C(N) − R`, `R = M⁻¹ Σ μ(d)μ(e){M/[d,e]}`. Gcd coordinates `d = gb`, `e = ga`:
`R = M⁻¹ Σ_g μ(g)² Σ_{(a,g)=1} μ(a) Σ_{b ≤ N/g, (b,ag)=1} μ(b){M/(gab)}`. For fixed `(g,a)` put
`t = ⌊M/(ga)⌋ ≥ B`. On the pieces `⌊t/b⌋ = n`, `1 ≤ n ≤ √t`, the weight `{M/(gab)}` is
monotone in `b`, so Abel summation and the coprime Mertens bound
`|Σ_{b ≤ s, (b,f)=1} μ(b)| ≪ Π(f) s/(1+log s)⁴` (from the arbitrary-log-rate PNT through the Rankin
kernel) give `≪ Π(f) t/(1+log t)³`; `b ≤ √t` costs `√t`; `b > t` is `t·(m_f(X) − m_f(t))`.
Summing with `Σ μ²Π/g ≤ (1+log N)E` and `1 + log N ≤ 16(1 + log B)`:
`|R| ≪ 1/(1+log B) + (1+log B)²/√B`. Finally `C(N) → κ` (`tendsto_moebiusPeriodMeanSquare`).

Numerics (exploratory): `N = 4000`: `E_N(M)/M = 0.4405 ± 0.0002` for `M/N` from `512` to `32000`,
including `M ≈ N²`.

## Gates
- [x] 0 → 1  well-posed, attack
- [x] 1 → 2  paper proof closed
- [x] 2 → 3  Lean, audit (`propext`, `Classical.choice`, `Quot.sound` only)

## Lean
- `BezoutValuationIncidence/CoprimeMertensSawtoothCancellation.lean`:
  `exists_abs_coprimeMoebiusHarmonicSum_le_four`, `exists_abs_coprimeMoebiusSum_le`,
  `abs_sum_Ioc_mul_le_of_antitone`, `exists_abs_sum_coprime_moebius_fract_le`.
- `BezoutValuationIncidence/TheMoebiusPrefixEnergyAtLargeBandRatio.lean`:
  `sieveL2PrefixEnergy_eq_sum_lcm`, `sum_moebius_fract_lcm_eq`,
  `abs_sieveL2PrefixEnergy_div_sub_le_of_le_pow`.
- `BezoutValuationIncidence/TheMoebiusEnergyTransfersAtEverySuperlinearHorizon.lean`:
  `abs_coprimeSquarefreeCount_sub_le`, `abs_sieveL2PrefixEnergy_band_sub_le`,
  `abs_sieveL2PrefixEnergy_div_sub_le_of_band`, `exists_abs_sieveL2PrefixEnergy_div_sub_le`,
  `tendsto_sieveL2PrefixEnergy_div`.
- `TheCofinalMobiusSlopeIsThePeriodVariance.lean` now exports `coprimeSquarefreeCount_eq_sum`.

## Log
- 2026-10-24 — created in 1-in-progress
- 2026-10-24 — formalized, wired into the BVI umbrella
