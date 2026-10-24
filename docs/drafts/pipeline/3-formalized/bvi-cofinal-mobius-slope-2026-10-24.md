# The cofinal Möbius profile is asymptotically linear

- **ID:** BVI-COFINAL-SLOPE-2026-10-24
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** BVI README §7.7 (concavity of the cofinal profile, uniformity in the band ratio);
  THIM README §7.3 (sign of the band averages A(B), concavity)
- **Statement:** `P(B)/B → κ = ρ Σ_{j≥1} S(j) log(1+1/j)`, where `ρ = 6/π²`,
  `S(X) = Σ_{a,b≤X, (a,b)=1} μ(a)μ(b)/(σ(a)σ(b))`; equivalently the band slopes
  `γ_t = P(t) − P(t−1)` converge to `κ`, and `Σ_{b≥1} A(b)/(b(b+1)) = −κ`.

## Goal
`P(B) = lim_N Q_N((B+1)N)/N` (`cofinalMobiusQuadraticProfile`) is known for each fixed `B`, with
`P(1..4)` and the band averages `A(1..4) < 0` computed; its shape is open. The theorem gives its
large-band law and turns the Buchstab band calculus into a convergent sum rule.

## Paper proof
1. `γ_t = P(t) − P(t−1) = Σ_{q,r≤t} D(q,r)/[q,r]`, `D = moebiusDilationPairDensity (r/g) (q/g)`.
2. For `g = (q,r)`, `a = r/g`, `b = q/g`: `D/[q,r] = ρ w(a) w(b)/g`, `w = μ/σ`
   (`∏_{p|ab} p/(p+1) = ab/(σ(a)σ(b))` on coprime squarefree `a, b`). Hence
   `γ_t = ρ Σ_{g≤t} S(⌊t/g⌋)/g`.
3. `S(X) = Σ_{δ≤X} μ(δ) w(δ)² T_δ(⌊X/δ⌋)²`, `T_δ(Y) = Σ_{a≤Y,(a,δ)=1} w(a)` (coprimality sieve;
   `w(δa) = w(δ)w(a)` for coprime, `0` otherwise).
4. Rate: `|T_δ(Y)| ≤ C g(δ)/log² Y` with `Σ g(δ)²/δ² < ∞`, from `Σ_{n≤z} μ(n)/n = O(log^{-4} z)`
   (`RHTower.Sieve.exists_abs_deningerHarmonicPartial_le_const_div_log_pow`) and a nonnegative
   convolution `w·1_{(·,δ)=1} = (μ/id) * β_δ`. Hence `S(X) = O(1/log² X)`.
5. Split `Σ_{g≤t} S(⌊t/g⌋)/g` at `g = t/T`: the head tends to `Σ_{j<T} S(j) log(1+1/j)`, the
   tail is `O(1/log T)` uniformly. So `γ_t → κ`; Cesàro gives `P(B)/B → κ`; the THIM identity
   `P(B) = −(B+1) Σ_{b≤B} A(b)/(b(b+1))` gives the sum rule.

Exploratory numerics (not proof): `κ/ρ ≈ 0.7250`, `κ ≈ 0.4407`; this equals the limit of the
period mean `Σ_{d,e≤N} μ(d)μ(e)/[d,e]` (≈ 0.44074 at `N = 10^5`). `A(10) = ρ/9 > 0` is the first
positive band average; about 57% of `B ≤ 2000` have `A(B) ≥ 0`.

## Gates
- [x] 0 → 1  well-posed, source-pure, attack idea
- [x] 1 → 2  paper proof closed (constants: Rankin mass `K = (25/4) exp(3 Σ n^{-7/4})`)
- [x] 2 → 3  Lean: `tendsto_cofinalBandSlope`, `tendsto_cofinalMobiusQuadraticProfile_div`,
  `tendsto_sum_bandAverageStep` (`TheCofinalMobiusProfileIsAsymptoticallyLinear.lean`);
  decay input `exists_abs_coprimePairMoebiusSigmaSum_le` (`CoprimeMoebiusSigmaSumsDecay.lean`).
  Standard axioms only; wired into the BVI umbrella.
- [ ] next: identify `κ` with `lim_N Var_N(μ)` (cofinal slope = period variance)

## Log
- 2026-10-24 — created in 1-in-progress
- 2026-10-24 — formalized; moved to 3-formalized
