# The critical degree of the one-prime semilocal Jacobi matrix — numerical study

- **Date:** 2026-09-03
- **Parent cards:** `3-formalized/new_scientific_knowledge/route-j-semilocal-prolate-first-euler-critical-boundary.md`
  (survivor targets 1–2), `…-second-…`, `…-third-euler-critical-boundary.md`;
  corpus definitions `SemilocalProlateCriticalPotential.routeJProlateSourceCriticalResidual`,
  `SoninSemilocalFinitePrimeMeasure`, `SemilocalProlateFirstEulerCriticalJet`.
- **Machine:** RunPod, 16 cores, numpy in 80-bit extended precision.
- **Status of the numbers:** direct high-accuracy numerics with validation against the exact
  archimedean radii (drift below `3·10⁻¹³` at degree 1300) and grid-refinement stability
  (`10⁻¹⁴`); not interval-certified.

## 1. The question

Connes–Consani–Moscovici (arXiv:2403.01247) attach to the set of places `S = {p, ∞}` the
probability measure

```
dν_p(s) ∝ |Γ(1/4 + is/2)|² · |1 − p^{−1/2} e^{i s log p}|^{−2} ds ,     q := 1/p ,
```

whose orthonormal polynomials satisfy `s p_n = A_{n+1} p_{n+1} + A_n p_{n−1}` (symmetric
measure, no diagonal). At `q = 0` the radii are `A_n = r_n = √((n+½)(n+1))`. The corpus's Route J
cards study the four-radius critical residual

```
R_k(q) = A_{2k}A_{2k+1} − A_{2k+1}² − A_{2k+2}² + A_{2k+2}A_{2k+3}
```

through its Taylor jets in `q`: the first jet `[q] R_k ~ 4√(2/π) √(2(2k+2))` becomes order one
at `n ≍ p²`, the third jet `[q³] R_k ~ −160√(2/π)(2k+1)^{5/2}` at `n ≍ p^{6/5}`, and the
first-Euler card leaves open (survivor target 2) *whether all fixed Euler orders share the scale
`n ≍ p²` and whether they resum there*. This computation evaluates the exact `R_k(q)` at finite
`q` and locates the degree at which the deformation is actually order one.

## 2. Method

Discretized Stieltjes procedure on a grid of step `0.02` over `|s| ≤ 2.2 n_max + 60`, run on the
normalized functions `p_n √w` so that all quantities stay `O(1)`; the weight is exponentiated in
80-bit extended precision (in double precision it underflows beyond `|s| ≈ 450`, which caps the
radii at `n ≈ 235` — this failure was observed and is the reason for the extended precision).
`R_k(q)` uses the corpus's index convention (`A_n = a[n+1]`, `R_k(0) → 1`). Validation
(`python3 routej_scale.py check`): archimedean radii equal `√((n−½)n)` in the code's indexing to
`10⁻¹³` up to `n = 1300`; grid refinement changes nothing beyond `10⁻¹⁴`; `R_k(0)` increases
monotonically to `1`.

Outputs: the relative deviation `D_k(q) = (R_k(q) − R_k(0)) / R_k(0)` for 21 primes
`2 ≤ p ≤ 1009` up to degree `n = 1400` (`routej_scale.json`), and a scaling-collapse run in the
variable `x = n/p = 2kq` for `101 ≤ p ≤ 2003` up to `n = 4600` (`routej_collapse.json`).

## 3. Results

### 3.1 The first jet is confirmed, then immediately overtaken

At `p = 1009` the finite-difference slope `(R_k(q) − R_k(0))/q` is 10.98 at `k = 5` and 18.9 at
`k = 20` against the corpus's first-jet law `4√(2/π)√(2(2k+2))` = 15.6 and 29.3 (asymptotic in
`k`; the agreement improves with `k` while the linear regime lasts). Already at `k = 100`,
`q = 10⁻³`, the slope is `−21.7` against `+64`: the response is no longer linear in `q` although
`q√k ≈ 0.01`. The corpus's third-jet constant explains this: `128 (2k+1)^{5/2} q³ ≈ 1` at
`k ≈ 285` for `p = 1009`, and the measured deviation is `−0.31` at `k = 300`.

### 3.2 Order-one deviation occurs at degree `n ≈ p`

First degree `n = 2k` at which `|D_k(q)|` exceeds a threshold (`routej_scale.json`, `n_max = 1400`):

| p | q | n(|D| ≥ 0.1) | n(|D| ≥ 0.5) | n(|D| ≥ 1) | n(|D|≥1) / p | π p²/64 (first jet) | p^{6/5} (third jet) |
|---|---|---|---|---|---|---|---|
| 101 | 0.0099 | 20 | 34 | 54 | 0.53 | 501 | 254 |
| 151 | 0.0066 | 32 | 58 | 144 | 0.95 | 1119 | 412 |
| 211 | 0.0047 | 48 | 88 | 206 | 0.98 | 2185 | 615 |
| 307 | 0.0033 | 74 | 146 | 308 | 1.00 | 4626 | 965 |
| 401 | 0.0025 | 102 | 224 | 412 | 1.03 | 7893 | 1330 |
| 503 | 0.0020 | 132 | 474 | 528 | 1.05 | 12420 | 1745 |
| 701 | 0.0014 | 194 | 674 | 766 | 1.09 | 24122 | 2599 |
| 1009 | 0.0010 | 298 | 996 | 1172 | 1.16 | 49975 | 4024 |

For small primes (`p ≤ 23`) the deviation is already of order `1`–`10` at `k = 1` and grows to
`10³`–`10⁴` by `k = 600`: the asymptotic jets say nothing at `q ≥ 0.05`.

**Reading.** Over this range of primes the exact deformation becomes order one at degree
`n ≈ p` (ratio `n/p` drifting slowly upward, 0.98 → 1.16), far below the first-jet scale `p²`.
Section 3.3 explains the drift: the deviation is `q^{1/2}Φ(qn)`, so the order-one degree grows
like `p` times a slowly growing power, `n ~ p^{6/5}` asymptotically. The answer to survivor
target 2 is therefore negative in a specific way: the fixed Euler orders do not share a scale,
the first jet's `p²` is not the scale of anything, and the full response resums into a
universal profile of the single variable `qn`.

### 3.3 Scaling collapse: `D_k(q) = q^{1/2} Φ(qn) + O(q)` with a universal profile `Φ`

`routej_collapse.json` (`101 ≤ p ≤ 2003`, `n ≤ 4600`; validity `n ≤ 3500` because the
extended-precision weight underflows beyond `|s| ≈ 7200`, which is why the `p = 2003`, `x = 2`
entry is discarded). The quantity `√p · D` at fixed `x = n/p` is the same for every prime:

| x | Φ(x) = √p·D, mean over p ≥ 307 | spread |
|---|---|---|
| 0.1 | 0.567 | 0.018 |
| 0.3 | −3.386 | 0.066 |
| 0.5 | −9.256 | 0.060 |
| 0.6 | −9.953 | 0.033 |
| 0.8 | −1.868 | 0.104 |
| 1.0 | 17.465 | 0.295 |
| 1.2 | 33.918 | 0.100 |
| 1.3 | 34.949 | 0.097 |
| 1.5 | 15.784 | 0.472 |
| 1.6 | −3.415 | 0.793 |
| 1.8 | −47.392 | 0.406 |
| 2.0 | −72.273 | 0.075 |

Zeros of `Φ` (identical for `p = 1009` and `p = 1511` to three decimals): `x = 0.159, 0.823,
1.586, 2.369`, with spacings `0.664, 0.763, 0.783` approaching `π/4 ≈ 0.785`. Extrema:
`Φ ≈ +0.66` at `x ≈ 0.068`, `−10.0` at `0.579`, `+35.4` at `1.269`, `−72.5` at `2.024`; the
envelope grows roughly like `x^{5/2}` between the extrema listed. The full profile is in
`phi_profile.csv`.

**How the Lean-proved jets sit inside `Φ`.** In the variable `x = qn`, the fixed Euler orders
scale as `q^j n^{(2j−1)/2} = q^{1/2} x^{(2j−1)/2}` for odd `j` and as `q^j n^{j−1/2} =
q · x^{j−1/2} · …` for even `j` (the second-Euler card's `[q²]R_k ~ −(32/π)·2k` gives `q²n =
q·x`). So the odd orders are the Taylor coefficients of the leading profile,
`Φ(x) = c₁ x^{1/2} + c₃ x^{5/2} + c₅ x^{9/2} + …` with `c₁ = 4√(2/π)·√2 = 4.51` and
`c₃ = −160√(2/π) = −127.7` from the corpus's first- and third-Euler cards, and the even orders
are the `O(q^{1/2})` corrections to the collapse — which is why the collapse converges more
slowly at small `x`. The first zero of `Φ` is where the first and third jets balance:
`x² ≈ c₁/|c₃| = 0.035`, `x ≈ 0.19` against the measured `0.159` (higher orders shift it). The
coefficients grow fast (`c₁ = 4.5`, `c₃ = −128`, `c₅ ~ 10⁴` from the fits), so the jet series is
asymptotic; `Φ` is its resummation and is oscillatory with growing amplitude.

**Sinusoidal form of the profile (`phi_fit.json`, `fit_profile.py`).** On `0.35 ≤ x ≤ 2.3` the
profile is fitted to within 0.4–0.7 % of its root-mean-square by a single modulated sinusoid,

```
Φ(x) ≈ −26.1 · x^{1.45} · sin(4.06 x − 0.19)        (p = 1511: A = −26.06, α = 1.436, ω = 4.084, φ = −0.216, rms 0.15 on rms(Φ) = 35.7)
```

(`p = 1009`: A = −26.09, α = 1.466, ω = 4.049, φ = −0.157, rms 0.26). Fixing `ω = 4` costs a
factor 4 in the residual, so the frequency is slightly above 4, or the phase drifts slowly. The
envelope exponent is `1.45 ± 0.05`, i.e. `x^{3/2}` within the fit's resolution, so the large-`x`
behaviour is `Φ ~ −26 x^{3/2} sin(4x + …)`, not the `x^{5/2}` suggested by the third jet alone.
With an `x^{3/2}` envelope, `|D| = 1` at `26 x^{3/2} = √p`, i.e. at degree

```
n* ≈ p^{4/3} / 8.8      (p = 1009: 1147 predicted, 1172 measured; p = 503: 453 vs 528; p = 307: 236 vs 308),
```

up to the position of the nearest extremum of the sinusoid. The frequency `4` in `x = n/p` is
an unexplained number: it is the analytic question this computation leaves for the Route J
programme.

### 3.4 Two primes do not superpose: the cross term dominates (`routej_twoprime.json`)

For `S = {p₁, p₂, ∞}` the deviation `D₁₂` is compared with `D₁ + D₂` (each relative to the
archimedean residual). It is not additive at any degree; the cross term `D₁₂ − D₁ − D₂` is of
the same size as `D₁₂` itself and much larger than either single-prime deviation:

| S | n | D₁ | D₂ | D₁₂ | D₁₂ − D₁ − D₂ |
|---|---|---|---|---|---|
| {503, 1009} | 100 | −0.034 | +0.018 | −1.63 | −1.61 |
| {503, 1009} | 400 | −0.098 | −0.204 | −9.42 | −9.12 |
| {307, 401} | 200 | −0.525 | −0.464 | −2.80 | −1.81 |
| {101, 211} | 100 | +1.80 | −0.61 | −4.07 | −5.25 |
| {101, 1009} | 100 | +1.80 | +0.018 | +1.58 | −0.24 |

The pair `{101, 1009}` (ratio 10) interacts weakly, the pairs with ratio near 2 or below
interact strongly. The natural explanation: the product of the two Euler factors contains the
beat term `2(p₁p₂)^{−1/2} cos(s · log(p₂/p₁))`, a slow modulation of the measure at the small
frequency `log(p₂/p₁)`, whereas each single Euler factor only carries the fast frequencies
`m log p`. Slow modulations shift recurrence coefficients at first order without the
suppression that makes the one-prime response `O(√q)`. See Section 3.5 for the test of this
mechanism.

### 3.5 The cross-prime term is the linear response to the beat frequency (`routej_crossterm.json`)

Replace the two Euler factors by the archimedean weight times the single slow mode
`1 + 2ε cos(δ s)` with `ε = (p₁p₂)^{−1/2}` and `δ = log(p₂/p₁)`, and compare its residual
deviation with the measured cross term `D₁₂ − D₁ − D₂` at every degree up to 800:

| S | ratio | ε | δ | correlation | rms ratio |
|---|---|---|---|---|---|
| {307, 401} | 1.31 | 2.85·10⁻³ | 0.267 | 0.9999 | 1.000 |
| {211, 421} | 2.00 | 3.36·10⁻³ | 0.691 | 1.0000 | 1.000 |
| {503, 1009} | 2.01 | 1.40·10⁻³ | 0.696 | 1.0000 | 1.000 |
| {1009, 2017} | 2.00 | 7.0·10⁻⁴ | 0.693 | 1.0000 | 1.000 |
| {101, 211} | 2.09 | 6.85·10⁻³ | 0.737 | 1.0000 | 1.000 |
| {997, 1009} | 1.01 | 1.0·10⁻³ | 0.012 | (both ≈ 10⁻³, no cross term in range) | — |

So the cross-prime part of the two-prime deformation is, to all displayed digits, the **linear
response of the archimedean Jacobi matrix to the beat mode** `2(p₁p₂)^{−1/2} cos(s log(p₂/p₁))`
of the product of the two Euler factors: `D₁₂ − D₁ − D₂ = ε · H(n, δ) + …` with `H` the
first-order response to a cosine modulation of the archimedean measure, an oscillating function
of `nδ` whose amplitude grows like `n^{3/2}` in the computed range (`H/ε` reaches `10⁴` by
`n = 800`). For primes of comparable size this term exceeds the one-prime term `√q Φ(qn)` by a
factor of order `p`: the one-prime response carries the suppression that makes it `O(√q)`, the
beat mode does not. When the ratio tends to 1 the beat frequency tends to 0 and the cross term
disappears in the computed range, as a constant multiplier must.

**Consequence for the Route J programme (survivor target 3).** The one-prime boundary layer is
not the building block of the finite-`S` semilocal Jacobi matrix: for any two primes of
comparable size the pairwise beat term dominates, and the finite-`S` problem has to be
organized around the beat frequencies `log(p_i/p_j)` — i.e. around the Euler product assembled
first, as the corpus's moment-defect card already required. The analytic object to compute is
the first-order response `H(n, δ)` of the archimedean (Meixner–Pollaczek) Jacobi matrix to the
multiplier `1 + 2ε cos(δ s)`, whose matrix elements `∫ p_i p_j e^{iδ s} dμ_∞` are classical and
whose residual combination is the cross-prime analogue of the corpus's first-Euler jet.

## 4. Files

| file | content |
|---|---|
| `routej_scale.py` | Stieltjes solver, residual, sweep (`check` and `run` modes) |
| `routej_scale.json`, `routej.log` | 21 primes, `n ≤ 1400`: thresholds, slopes, samples of `D`, radii samples |
| `routej_collapse.py`, `routej_collapse.json`, `collapse.log` | `D_k` at every `k` for `101 ≤ p ≤ 2003`, crossings in `x = n/p`, `D` at fixed `x` |
| `phi_profile.csv` | the universal profile `Φ(x) = √p·D` on `0 < x ≤ 3.5` for `p = 1009, 1511, 2003` |
| `fit_profile.py`, `phi_fit.json` | sinusoidal fit of `Φ` |
| `routej_twoprime.py`, `routej_twoprime.json`, `twoprime.log` | two-prime measures `S = {p₁, p₂, ∞}`, additivity test |
| `routej_crossterm.py`, `routej_crossterm.json`, `crossterm.log` | same-ratio pairs and the synthetic beat-frequency multiplier (mechanism test) |

## 5. How to interpret and reuse

- The corpus's Lean-proved jets (first and third Euler orders) are confirmed numerically in
  their regime of validity and are seen to be overtaken: the natural variable of the finite-`q`
  problem is `x = n/p`. Any analytic treatment of the semilocal Jacobi matrix at large degree
  should be organized around `qn`, not around the fixed-order jets.
- `D` changes sign repeatedly as `n` grows past `p` and its amplitude grows; the residual is a
  sensitive probe (relative change `ε` in a radius produces `D ≈ ε n²`), so small radius changes
  appear as large `D`.
- The Stieltjes procedure needs the weight represented without underflow on the whole support of
  the degree-`n` orthonormal functions (`|s| ≲ 2n`); double precision fails silently beyond
  `n ≈ 235` by saturating the radii. Check the archimedean drift before trusting any run.

### 3.6 The whole one-prime deviation is the first-order response to `cos(s log p)` (`routej_firstorder.json`)

`routej_firstorder.py` computes, alongside the Stieltjes recursion, the diagonal cosine moments
`m_d[n] = Σ_s q_n(s)² cos(d·s·log p)` of the archimedean orthonormal functions for the harmonics
`d = 1..4`, and forms the first-order radii `a_n(1 + Σ_d ε_d (m_d[n] − m_d[n−1]))` with the
Euler-factor amplitudes `ε_d = r^d/(1 − r²)`, `r = p^{−1/2}` (the mode `d` of
`|1 − r e^{i s log p}|^{−2} = (1 − r²)^{−1} Σ_d r^{|d|} e^{i d s log p}`).  The residual deviation
built from these first-order radii is compared with the exact one (`D_exact`, from the exact
one-prime Stieltjes run) over the full degree range `n ≤ 2.6 p`:

| `p` | `nmax` | corr(`D_exact`, first order, `d = 1` only) | rms ratio first/exact |
|---|---|---|---|
| 211 | 588 | 0.9999959 | 1.0042 |
| 503 | 1347 | 0.9999991 | 1.0018 |
| 1009 | 2663 | 0.9999997 | 1.0009 |
| 1511 | 3968 | 0.9999998 | 0.9973 |

The single mode `d = 1` at first order in `ε₁ = p^{−1/2}/(1 − 1/p)` reproduces the exact
deviation to 0.1–0.4 %, and the discrepancy shrinks with `p`.  Higher harmonics and higher orders
are `O(q)` corrections, as the scaling law of §3.3 requires.  Hence the universal profile `Φ` is a
first-order object: `Φ(x) = lim √p · [first-order residual response to cos(s log p) at n = xp]`.

### 3.7 Derivation of `Φ` from the Meixner–Pollaczek structure (`phi_derivation_check.py`)

The archimedean orthonormal polynomials are Meixner–Pollaczek polynomials (`λ = 1/4`, `φ = π/2`,
`x = s/2`).  Their generating function `Σ_n P_n(x) w^n = (1 − iw)^{−λ+ix}(1 + iw)^{−λ−ix}` tilts
the Gamma weight by `e^{2x(arctan w + arctan z)}`, and the tilted Fourier integral is the corpus's
characteristic function `(cosh)^{−1/2}` at the complex rapidity `t − i(arctan w + arctan z)`.
Since `cosh(t − iα) = [cosh t (1 − wz) − i sinh t (w + z)] / √((1 + w²)(1 + z²))`, the prefactors
cancel and one obtains the **generating function of all boost matrix elements**

    Σ_{m,n} c_m c_n M_{mn}(t) w^m z^n = (cosh t)^{−1/2} (1 − wz − i tanh t (w + z))^{−1/2},
    M_{mn}(t) = ∫ p_m p_n e^{its} dμ,   c_n = √((2n)!)/(2^n n!),

whose `m = 0` row is the corpus's Lean closed form `semilocalArchimedeanJacobiFourier_eq_closedForm`
(`i^n c_n (cosh t)^{−1/2} tanh^n t`).  Extracting `[w^n z^n]` gives the **diagonal cosine moments**

    m_n(t) = M_{nn}(t) = (cosh t)^{−1/2} ₂F₁(−n, n + 1/2; 1; tanh² t) = (cosh t)^{−1/2} P_n^{(0,−1/2)}(1 − 2 tanh² t).

`phi_derivation_check.py` (log `phi_derivation_check.log`) verifies both against grid values: the
diagonal to 8 digits for `n ≤ 8` at `t = 0.7`, all entries `m, n ≤ 8` of the generating function
to `1.3·10⁻⁹` (the naive variant in `mp_genfun_check.py`, with the wrong real shift `cosh(t − α)`,
is kept as a negative control: it matches only the first row).

**Double scaling.**  At `t = log p`, `sech t = 2p/(p² + 1)`, so the Jacobi argument is
`−1 + 8/p² + O(p⁻⁴)`.  With `P_n^{(0,−1/2)}(−y) = (−1)^n P_n^{(−1/2,0)}(y)` and `y = cos θ`,
`θ = 4/p + O(p⁻³)`, the Mehler–Heine limit `P_n^{(−1/2,0)}(cos(z/n)) ~ n^{−1/2} π^{−1/2} cos z`
at `z = nθ = 4n/p` gives

    m_n(log p) = (−1)^n √(2/(π p n)) cos(4n/p) (1 + O(1/n) + O(1/p)).

**This is the origin of the frequency `4` in `x = n/p`:** it is the Mehler–Heine angle
`θ = 2 sech(log p) = 4/p` of the Jacobi polynomial `P_n^{(−1/2,0)}` at the boost rapidity `log p`.

**Residual response.**  By the Lean theorem `hasDerivAt_cosineModeJacobiRadius`
(`SemilocalCosineModeFirstOrderResponse.lean`) the first-order radius response is
`u_n = ε r_n (m_{n+1} − m_n)`, and by `hasDerivAt_cosineModeCriticalResidual` the residual jet is
`residualJetOf`.  Writing `u_j = (−1)^{j+1} W(j)` with the smooth envelope `W(j) = r_j (|m_{j+1}| + |m_j|)`,
the residual jet expands as `J = 0·rW + 4 rW′ + 0·r′W + 6 r′W′ + 6 rW″ + …`: the alternating
leading term cancels exactly (the residual is a second difference), and the surviving term is
`J ≈ 4 r W′ ≈ 8n (M + n M′)` with `M(n) = √(2/(πpn)) cos(4n/p)`.  Since
`M + nM′ = √(2/(πp)) n^{−1/2} [cos(4x)/2 − 4x sin(4x)]`, `ε = p^{−1/2}(1 + O(1/p))`, and
`R_k(0) → 1`,

    Φ(x) = 4 √(2/π) [ √x cos(4x) − 8 x^{3/2} sin(4x) ].

**Checks against the data (`phi_derivation_check.log`).**  Over `0.3 ≤ x ≤ 2.3` the rms deviation
between the measured profile and the derived one is 1.1 % (`p = 1009`) and 0.8 % (`p = 1511`) of
the rms of `Φ`; at the extrema the measured/derived values are `−9.92/−9.84` (`x = 0.6`),
`35.36/35.39` (`x = 1.269`), `−72.51/−72.47` (`x = 2.024`).  The zeros of `Φ` are the roots of
`tan(4x) = 1/(8x)`: `0.163, 0.823, 1.593, 2.366` versus measured `0.159, 0.823, 1.586, 2.369`.  The
Taylor expansion `Φ = 4√(2/π)[x^{1/2} − 40 x^{5/2} + 96 x^{9/2} − …]` has coefficients
`c₁ = 4√(2/π) = 3.1915`, `c₃ = −160√(2/π) = −127.66`, `c₅ = 384√(2/π) = 306.4`: the first two are
exactly the Lean-proved first and third Euler jets (`tendsto_criticalResidualJet_div_sqrt_boundary`,
`SemilocalProlateThirdEulerCriticalJet`); the third is a prediction for the fifth Euler jet.  (The
measured slopes `(R_k(q) − R_k(0))/q` at `k = 5, 10` are `10.98, 14.54` against `4√(2/π)√(2k) =
10.09, 14.27`; a `√2` in an earlier transcription of `c₁` was wrong.)  The order-one threshold follows
from the envelope: `32√(2/π) x^{3/2} = √p` gives `n* = p^{4/3}/8.66`, the empirical
`p^{4/3}/8.8` of §3.3.

**Interpretation.**  The one-prime Euler deformation of the semilocal Jacobi matrix is, at the
scale `n ≍ p`, the first-order response of the SU(1,1) discrete-series (Bargmann index `1/4`)
matrix elements of the boost by rapidity `log p`; the universal profile is a Mehler–Heine limit of
Jacobi polynomials.  No intrinsic prime-scale boundary layer exists: the "order-one deformation at
`n ≈ p`" is the point where the Bessel-regime oscillation `cos(4n/p)` of the boost elements has
amplitude `√p` relative to the residual.

## 4b. Additional files (first-order test and derivation)

- `routej_firstorder.py`, `routej_firstorder.json`, `firstorder.log` — §3.6.
- `mp_genfun_check.py` — grid boost matrix elements and a Cauchy-integral extractor of the generating
  function coefficients; its own `F` has the wrong shift and serves as the negative control.
- `phi_derivation_check.py`, `phi_derivation_check.log` — §3.7: closed-form diagonal moments,
  corrected generating function, derived `Φ` versus the collapse profile.

### 3.8 Lean status of the derivation (2026-09-03)

Steps (i)–(iii) of §3.7 are Lean theorems: the generating function
(`SemilocalJacobiMeixnerPollaczekGeneratingFunction`), the complex-rapidity characteristic function
and the two-variable boost generating function (`SemilocalGammaComplexRapidityCharacteristic`,
`SemilocalBoostGeneratingFunctionClosedForm`), and the diagonal closed form
`m_n(δ) = (cosh δ)^{−1/2} Σ_l C(n,l) Ring.choose(−(n+½), l) tanh^{2l} δ`
(`SemilocalBoostDiagonalClosedForm.cosineDiagonalMoment_eq`).  Only the Mehler–Heine limit of the
finite sum at `δ = log p`, `n = xp` (and the elementary residual-jet expansion) remains for `Φ`.

### 3.9 `Φ` is a Lean theorem (2026-09-03)

`RHTower.RouteJProfile.ScalingData.tendsto_residual_profile` (module `RouteJScalingProfile`) proves
the scaling limit of §3.3/§3.7 exactly: for `p_j → ∞`, `2k_j/p_j → X > 0`, the first-order residual
response `residualJetOf (cosineModeDeterminantJet (log p_j)) k_j` converges to
`4√(2/π)[√X cos 4X − 8X^{3/2} sin 4X]`, and `J/R(0)` has the same limit.  The route is the Pfaff
transformation to the `σ`-form (no cancellation), two contiguous relations that turn the residual
into first differences of smooth sequences, Tannery's theorem for the Mehler–Heine limits, and the
Wallis limit.  Pre-certification script: `mehler_heine_precert.py` (+ `contiguous_check.py`).

### 3.10 The beat-mode (fixed-`δ`) law is a Lean theorem (2026-09-03)

`RHTower.RouteJBeatMode.tendsto_beatMode_profile` (module `RouteJBeatModeProfile`): for fixed
`δ > 0`, `σ = sech δ`, `τ = tanh δ`, `φ = arccos σ`,

    J_k(δ) / k^{3/2}  −  32 √(2/π) σ^{3/2} τ^{5/2} sin((4k + 9/2) φ − π/4)  →  0.

Route: `∫p_n² cos(δs)dμ = (cosh δ)^{-1/2} P_{2n}(sech δ)` (Legendre), the residual as an exact
combination of `P_{4k}, …, P_{4k+8}`, Laplace–Heine with the explicit constant
`|P_N(cos φ) − 2C_N(2 sin φ)^{-1/2}cos((N+½)φ − π/4)| ≤ 400/(N sin φ)` (proved from the convolution
`P_N(cos φ) = Σ C_k C_{N−k} cos((N−2k)φ)` by Abel summation and Abel's limit theorem), Wallis, and the
identity `−cos(χ−4φ) + 2cos(χ−2φ) − 2cos(χ+2φ) + cos(χ+4φ) = 8 sin 2φ sin²φ sin χ`.
Pre-certification: `beat_mode_precert.py` (`beat_mode_precert.log`): Legendre identification to
`10⁻³⁰`, convolution identity, `N·(P_N − asymptotic)` bounded, exact Legendre form of `J_k` to `10⁻²⁹`,
`J_k / beat law → 1` (`1.0005` at `k = 3200`).  At `δ = log(p₂/p₁)` this is the two-prime cross term of
§3.5.  Next (MUST-170): the uniform two-term law joining this to `Φ`.
