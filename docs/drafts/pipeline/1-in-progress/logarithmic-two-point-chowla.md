# Logarithmic two-point Chowla

- **ID:** A21 (review-1111 §2.1, classical inputs)
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / FORMALIZATION PROGRAMME
- **Statement:** for every integer `h ≥ 1`, `(1/log x) Σ_{n ≤ x} λ(n)λ(n+h)/n → 0`.

## Proof architecture

Route: entropy decrement and prime-shift self-similarity (Tao), then a circle method whose major
arcs are the Matomäki–Radziwiłł theorem for `λχ` at a fixed modulus and whose minor arcs are
Vinogradov's equidistribution of `pβ`.

### §0 Limit functionals

`A_x(f) = (1/log x) Σ_{1≤n≤x} f(n)/n`. For an ultrafilter `U ≤ atTop` on `ℝ` and bounded `f`,
`L(f) = lim_U A_x(f)`. A bounded `A_x(g) → 0` iff `L(g) = 0` for every such `U`.

- (L1) `L` is linear, positive, `L(1) = 1`, `|L(f)| ≤ ‖f‖_∞`.
- (L2) `L(f(·+1)) = L(f)`: `|A_x(f(·+1)) − A_x(f)| ≤ 3‖f‖/log x`.
- (L3) `L(f(d·)) = L(d·1_{d|·} f)`: `Σ_{n≤x} f(dn)/n = d Σ_{m≤dx, d|m} f(m)/m`, and the range
  `x < m ≤ dx` costs `‖f‖(1 + log d)`.
- (L4) `L(1_{n ≡ r mod Q}) = 1/Q`.

`c(d) = L(λ(n)λ(n+d))`. By (L3) and `λ(pn)λ(pn+ph) = λ(n)λ(n+h)`:
`c(h) = L(p·1_{p|n} λ(n)λ(n+ph))` for every prime `p`.

### §1 Finite laws and entropy

A random variable is `g : ℕ → α` with `α` finite; its law is `a ↦ L(1_{g=a})`. Entropy,
conditional entropy and conditional mutual information are those of the finite laws. Stationarity:
`g ∘ (·+1)` has the law of `g` (L2). Needed facts: chain rule; conditioning reduces entropy;
invariance under bijections of the value set; `0 ≤ H ≤ log |α|`; the event inequality
`μ(A) log(1/ν(A)) ≤ D(μ‖ν) + log 2`.

### §2 Entropy decrement

`𝐏_k` = primes in `(2^k, 2^{k+1}]`, `H_k = 2^{k+1}(h+2)` (so `H_{k+1} = 2H_k`),
`X_k(n) = (λ(n+i))_{i<H_k}`, `R_k(n) = (n mod p)_{p ∈ 𝐏_j, k₀ ≤ j < k}`,
`Y_k(n) = (n mod p)_{p ∈ 𝐏_k}`, `φ(k) = H(X_k | R_k)/H_k ∈ [0, log 2]`.

`H(X_{k+1}|R_{k+1}) ≤ 2 H(X_k|R_{k+1})`: `X_{k+1} = (X_k, X_k∘(·+H_k))`, conditional
subadditivity, and the shift by `H_k` permutes the values of `R_{k+1}` (stationarity of the pair).
`R_{k+1} = (R_k, Y_k)`, so `H(X_k|R_{k+1}) = H(X_k|R_k) − I_k`, `I_k = I(X_k ; Y_k | R_k)`. Hence
`I_k/H_k ≤ φ(k) − φ(k+1)` and `Σ_k I_k/H_k ≤ log 2`. If `log(K'/K) > (log 2)/δ`, some
`k ∈ [K, K')` has `I_k ≤ δ H_k / k`.

### §3 Hoeffding at one scale

`N = 2^{k+2}`, `W_p(x, y) = (1/N) Σ_{j<N} (p·1[y + j ≡ 0 mod p] − 1) x_j x_{j+ph}` (positions
`< N + 2^{k+1}h = H_k`), `Z = |𝐏_k|^{-1} Σ_p W_p(x, y_p)`. `|W_p| ≤ 5/2` (at most `N/p + 1`
multiples of `p` among `N` consecutive integers, `p ≤ N/2`) and `Σ_{y mod p} W_p(x, y) = 0`. For
`y` uniform on `Π_p ℤ/p` and every `x`: `P(|Z| ≥ ε) ≤ 2 exp(−2|𝐏_k| ε²/25)`.

### §4 Event inequality at a good scale

`μ` = law of `(X_k, R_k, Y_k)`; `ν` = law of `(X_k, R_k)` times the uniform law of `Y_k`. By (L4)
and CRT `(R_k, Y_k)` is uniform, so `D(μ‖ν) = I_k`. With `A = {|Z| ≥ ε}`:
`μ(A) ≤ (I_k + log 2)/(2|𝐏_k|ε²/25 − log 2)`.

`L(Z(X_k, Y_k)) = c(h) − |𝐏_k|^{-1} Σ_{p∈𝐏_k} c(ph)` by (L2), (L3). So
`|c(h) − avg_{p∈𝐏_k} c(ph)| ≤ ε + (5/2) μ(A)`. With `|𝐏_k| ≥ c₀ 2^k/k` and
`δ = c₀ε³/(25(h+2))`: for every `K ≥ K₀(ε, h)` there is `k ∈ [K, e^{C(h)/ε³} K]` with
`|c(h) − avg_{p∈𝐏_k} c(ph)| ≤ 4ε`.

### §5 Circle method

`S_{M,n}(α) = Σ_{m<M} λ(n+m) e(mα)`, `F_M(α) = L(|S_{M,n}(α)|²)/M ≥ 0`, `∫₀¹ F_M = 1`,
`K_k(β) = avg_{p∈𝐏_k} e(pβ)`. By (L2) and `Σ_{m<M} a_m a_{m+d} = ∫|S|² e(dα) + O(d)`:
`|avg_{p∈𝐏_k} c(ph)| ≤ ∫₀¹ F_M(α) |K_k(hα)| dα + 2^{k+1}h/M`.

**(PRIME)** For every `η > 0` there are `Q₀, W, k₁` such that for `k ≥ k₁` and every `β`:
`|K_k(β)| ≤ η` unless `|β − a/q| ≤ W/2^k` for some `q ≤ Q₀`.

Then `hα` is within `W/2^k` of `a/q` iff `α` is within `W/(h2^k)` of a rational `b/s`, `s | hq`.
Arc mass: for `T = ⌊1/(2w)⌋`, `|D_T(θ)| ≥ 2T/π` on `|θ| ≤ 1/(2T)` and Parseval give
`∫_{|θ|≤w} |S(θ₀+θ)|² ≤ (π²/(4T²)) Σ_t |Σ_{t≤m<t+T} c_m e(mθ₀)|²`, hence with (L2)
`∫_{|α−b/s|≤w} F_M ≤ (π²/4)(V_{b/s}(T) + 2T/M)`,
`V_{b/s}(T) = L(|T^{-1} Σ_{u<T} λ(n+u) e(ub/s)|²)`. Letting `M → ∞`:
`|avg_{p∈𝐏_k} c(ph)| ≤ η + (π²/4) Σ_{s ≤ hQ₀} Σ_{b<s} V_{b/s}(⌊2^{k−1}/W⌋)`.

**(MR)** For every fixed `b/s`: `limsup_x A_x(|T^{-1}Σ_{u<T} λ(n+u)e(ub/s)|²) → 0` as `T → ∞`.

§4 and §5 at a good `k` give `|c(h)| ≤ 6ε + 2η`.

Lean form of §2–§4: weights `w_k = (|𝐏_k| − C)₊/H_k` replace `1/k`; `Σ_k w_k = ∞` follows from
`Σ_p 1/p = ∞`, so no prime counting is needed. A good scale has `|𝐏_k| > C = 25 log 2/ε³` and
`I_k ≤ (ε³/25)|𝐏_k|`, hence `μ(A) ≤ 2ε` and `|c(h) − avg c(ph)| ≤ 6ε`.

### §6 (PRIME)

Dirichlet with denominator bound `2^k/k^{12}` gives `|β − a/q| ≤ k^{12}/(q2^k)`, `q ≤ 2^k/k^{12}`.
(Lean form of §5 uses arcs of width `1/(4T)` and the discrete circle `ℤ/R`, `R = M + 2^{k+1}h + T`.)

- `q > k^{12}`: Vaughan's identity, `|Σ_{n≤N} Λ(n)e(nβ)| ≪ (N q^{-1/2} + N^{4/5} + (Nq)^{1/2})(log N)^4`.
- `Q₀ < q ≤ k^{12}`: `e(pa/q) = φ(q)^{-1} Σ_χ χ̄(a) τ(χ) χ̄(p)`, `|τ(χ)| ≤ √q` (Parseval over `a`),
  `τ(χ₀) = μ(q)`. The principal term is `≤ 1/φ(q)`; every other character has
  `ψ(x, χ) ≪ x (log x)^{-A}` uniformly in `q ≤ (log x)^{12}` (Siegel–Walfisz: the uniform region
  `1 − c/log²(q(|t|+3))` away from real zeros of real characters, Siegel's `β ≤ 1 − c(ε)q^{-ε}`
  for those, the uniform local zero count, and the window bound of A59 with `h = x`). Partial
  summation against `e(tθ)/log t` costs `1 + 2π|θ|2^{k+1} ≤ 3πk^{12}`.
- `q ≤ Q₀`, `W/2^k < |β − a/q|`: the same expansion; the principal term is
  `φ(q)^{-1} avg_p e(pθ) ≪ 1/(W φ(q))`, the others are `o(1)` (fixed modulus).

### §7 (MR)

`e(ub/s)` splits into residue classes mod `s`; a class `r` with `g = (r,s)` reduces by
`λ(gm) = λ(g)λ(m)` and (L3) to a coprime class mod `s/g`, which is a combination of `λχ`,
`χ mod s/g`. `λχ = Σ_{d²|·} χ(d)² μχ(·/d²)`: the terms `d ≤ D` are windows of length `T/d²`,
the rest cost `1/D` by (L4). So (MR) follows from: for every fixed Dirichlet character `χ`,
`limsup_X X^{-1} Σ_{X<n≤2X} |T^{-1}Σ_{n<m≤n+T} μ(m)χ(m)|² → 0` as `T → ∞` — Matomäki–Radziwiłł
for `μχ`. Its non-generic input is a Vinogradov–Korobov-type zero-free region for `L(s, χ)`
(twisted Weyl sums through the finite Fourier expansion of `χ`).

## Inputs and status

| Input | Content | Corpus | Status |
|---|---|---|---|
| §0–§4 | limit functionals, entropy, decrement, Hoeffding, event inequality | — | **Lean** (`exists_scale_corr_close`) |
| §5 | circle method, arc mass | — | **Lean** (`abs_avg_corr_le`) |
| §6 minor arcs | Vaughan bound for general `β` | Vaughan at prime roots of unity (`BezoutValuationIncidence.TheCentredPrimeRowIsMinorArcBelowTheDiagonal`), Type II (`Sieve.VaughanTypeIIEstimate`) | open |
| §6 intermediate arcs | Siegel–Walfisz for `q ≤ (log x)^{12}`: **Lean** for primitive `χ` in short windows (`ShortIntervalPrimesInProgressions.siegelWalfisz_window`); partial summation to `Σ_p χ(p)e(pθ)` and the character expansion of `e(pa/q)` open | Siegel `RHTower.siegel_zero_free`; uniform region `RHTower.uniform_zero_free_region` (width `c/log²(q(|γ|+3))`); uniform local count `RHTower.localCountChi_uniform'`; window bound `ShortIntervalPrimesInProgressions.norm_psiChi_window_le` (its constant is `2‖γ'‖ + 8D`, uniform but stated existentially) | open |
| §7 | MR for `μχ`, fixed `χ` | MR for `μ`: fibre form all `h → ∞` (`Sieve.MoebiusAveragedMeanSquareAllLengths`), integer start `ℓ ≥ log N` (`TwinPrime.eventually_dyadicMeanSquare_moebius_le_integerWindowRate`); VK for `ζ` (`Sieve.VinogradovKorobovZeroFree`) | open |

## Lean

Folder `formal/GaloisForLFunctions/LogarithmicChowla/`, umbrella `LogarithmicChowla.lean`.

| Module | Content | Status |
|---|---|---|
| `LogarithmicAverages` | `A_x(f)`; shift `3B`, dilation `dB`, `A_x(1) → 1` | compiled |
| `LimitFunctional` | `L_U`, (L1)–(L4), laws of finite-valued sequences | compiled |
| `FiniteEntropy` | entropy, pushforward, submodularity, data processing, event inequality | compiled |
| `ResidueHoeffding` | Hoeffding on a finite product | compiled |
| `EntropyDecrement` | `H(X_{2H}|R) ≤ 2H(X_H|R)`, refinement by CRT, `Σ I_k/H_k ≤ log 2`, good scales | compiled |
| `ShiftDeviation` | `W_p`, `|W_p| ≤ 5/2`, mean zero, concentration of `Z` | compiled |
| `PrimeShiftReduction` | `L(Z) = c(h) − avg c(ph)`, event bound, `exists_scale_corr_close` | compiled |
| `DiscreteFourier` | `e(x)`, orthogonality over `ℤ/R`, twisted Parseval, `|D_T(θ)| ≥ T/2` on `|θ| ≤ 1/(4T)` | compiled |
| `ArcMass` | box identity, arc mass `≤ 4V(θ,T)(M+1)/M + 8T/M` | compiled |
| `CircleMethod` | `|avg c(ph) − R⁻¹Σ F(r) Re K(hr/R)| ≤ 2^{k+1}h/M` | compiled |
| `CircleBound` | minor/major split, covering by arcs, `M → ∞`: `abs_avg_corr_le` | compiled |

## Log
- 2026-11-11 — created; paper architecture §0–§7.
