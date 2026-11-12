# Matomäki–Radziwiłł for `λχ`

**Goal.** For a Dirichlet character `χ` (fixed modulus `q`) and `f = λχ`: for every `ε > 0` there is
`h₀` such that for `h ≥ h₀` and all large `X`,

`(1/X) Σ_{X<n≤2X} |Σ_{n<m≤n+h} f(m)|² ≤ ε h²`.

Consumer: A21 (`logarithmic-two-point-chowla.md` §7): `V(b/s, T) → 0` as `T → ∞`.

Folder: `formal/GaloisForLFunctions/MatomakiRadziwill/` (top level, umbrella `MatomakiRadziwill.lean`).

## Architecture

| Phase | Content | Status |
|---|---|---|
| V | Vinogradov–Korobov zero-free region for `L(s,χ)` | **Lean** (`LFunction_ne_zero_vinogradovKorobov`) |
| RT | Route T for `χ`: `Σ_{p∈B} χ(p)p^{-it}` small for high blocks `B`, `\|t\| ≤ X` | **Lean** (`exists_twistedChebyshev_le`, `exists_primeBlock_le`) |
| D | low frequencies: `sup_{\|t\|≤T₀} \|Σ_{n≤x} λχ(n)n^{-it}\| = o(x)` | open |
| L | the ladder: Ramaré, mean value, large values, Halász–Montgomery, rough class | open |
| P | Parseval: additive short windows from the Dirichlet-polynomial mean square | open |
| A | assembly for `λχ`; transfer to `V(b/s,T)` | open |

### V. Zero-free region for `L(s,χ)`

`L(s,χ) = q^{-s} Σ_{a=1}^{q} χ(a) ζ(s, a/q)`; blocks `Σ_{Y<n≤2Y, n≡a} n^{-s} = q^{-s} Σ_m (m+α)^{-s}`,
`α = a/q`.

1. **Shifted Vinogradov.** The corpus estimate (`Sieve.norm_sum_logPhase_le_vinogradov`) passes
   through the shift average `Q² |Σ n^{it}| ≤ Σ_x |R(t,x,Q)| + 8Q⁴`
   (`Sieve.sq_mul_norm_sum_logPhase_le`) with `R(t,x,Q)` evaluated at the *real* point `x`. For
   `(m+α)^{it}` the same shift gives `R(t, m+α, Q)`; everything downstream is unchanged. Result:
   `|Σ_{A<m≤A+L} (m+α)^{it}| ≤ C L N^{-δ_R/4} + 200 N^{1/2}` on `[N, 2N]`.
2. **Growth.** `|L(σ+iτ,χ)| ≤ C_q log τ` for `σ ≥ 1 − θ(log τ)` (as `Sieve.norm_riemannZeta_le_vinogradovKorobov`):
   truncation of the `L`-series, blocks by 1. (middle) and the derivative test (large).
3. **Zero-free.** `3 + 4cos + cos 2` for `L(σ,χ₀)³ L(σ+iτ,χ)⁴ L(σ+2iτ,χ²)` with the growth bound
   (Landau's lemma, as `Sieve.riemannZeta_ne_zero_vinogradovKorobov`):
   `L(β+iγ, χ) ≠ 0` for `β > 1 − c (log γ)^{-2/3}(log log γ)^{-5/3}`, `γ ≥ γ₀(q)`.

### RT. Route T for `χ`

Statement (Lean, `χ ≠ 1`, any `θ > 2/3`, `A ≥ 0`, all large `X`, `|τ| ≤ X`):
`‖Σ_{n≤N} χ(n)Λ(n)n^{-iτ}‖ ≤ N/(log X)^A` for `N ≤ X`, `log N ≥ (log X)^θ`;
`‖Σ_{P<p≤Q} χ(p)p^{-1-iτ}‖ ≤ (log X)^{-A}` for `P ≤ Q ≤ min(2P, X)`, `log P ≥ (log X)^θ`.

1. Reflection `L(s, χ⁻¹) = conj L(conj s, χ)` (identity theorem from `Re s > 1`) puts the
   Vinogradov–Korobov region at both signs of the height.
2. Strip: crude growth `‖L(s)‖ ≤ 2q(1 + ‖s‖/Re s)` on the disc of radius `11/10` about `9/8 + iγ`,
   `‖L(9/8 + iγ)‖ ≥ 1/9`, Landau's lemma, the zero count at the centre (`Re L'/L ≤ −ζ'/ζ(9/8)`), retained
   zeros at distance `≥ ε/2`: `‖L'/L(σ+iγ)‖ ≤ C log Y/ε(Y+1)` for `|γ| ≤ Y`, `σ ≥ 1 − ε(Y+1)/2`; low heights
   by compactness (no zero on `[1, 9/8] × [−T₀, T₀]`, so none on a thickening).
3. Truncated Perron at `x = N + ½`, `σ₀ = 1 + 1/log x`, `T = (log X)^{A+6}`; Cauchy on
   `[1 − ε(2X+1)/2, σ₀] × [−T, T]`. Error `≤ 720N(log X)²/T + BTx^{σ₁} + Bx/T`, `B ≤ 4(C/κ₀)(log X)²`.
4. `ε(t) ≥ κ₀(log t)^{-β}` for any `β > 2/3` (from `log log t ≤ (log t)^δ/δ`), so
   `x^{-ε/2} ≤ exp(−κ(log X)^{θ−β})`, which beats every power of `log X`.
5. Abel against `1/(n log n)`: the bracket telescopes to `1/(P log P)`; prime powers cost `9/√P`.

### L. Ladder (paper proof, fixed `h`, `X → ∞`)

The A21 consumer needs fixed window length `h` while `X → ∞` (then `h → ∞`). The corpus μ-MR
(`Sieve.MoebiusMeanSquare`) works at `h = exp((log x)^{0.99})` with one large scale and cannot
reach fixed `h`; the full ladder is needed.

Notation: `f` completely multiplicative, `|f| ≤ 1`; `D(a;t) = Σ_n a_n n^{-1-it}`; `T = KX/h ≤ X`;
`α = 1/4 − η`, `η = 1/100`.

* **(MVT)** `∫_{-T}^{T} |D(a;t)|² ≤ C₁ Σ (T + n)|a_n|²/n²` (corpus
  `Sieve.integral_Icc_normSq_logPoly_le_general`, `δ = 1/T`).
* **(dMVT)** for 1-spaced `𝒯 ⊂ [−T, T]`: `Σ_{t∈𝒯} |D(a;t)|² ≤ C(T + N)(1 + log N) Σ|a_n|²/n²`
  (Sobolev–Gallagher: `|F(t)|² ≤ ∫_{t±1/2} |F|² + |F F'|`, then MVT for `F` and `F'`).
* **(HM)** for 1-spaced `𝒯 ⊂ [−T, T]`: `Σ_{t∈𝒯} |Σ_{n≤N} a_n n^{-it}|² ≤ C(N + |𝒯| T^{1/2} log T) Σ|a_n|²`
  (corpus `halaszMontgomery_logPoly_finset`, to be checked).

**Scales.** `𝒥_j = [P_j, Q_j]`, `j = 1..J`, and the RT scale `𝒥_* = [P_*, Q_*]`,
`P_* = exp((log X)^{0.8})`, `Q_* = exp((log X)^{0.85})`. `Q₁ = h^{1/2}`, `P₁ = (log h)^{200}`,
`log Q_j = K_j log P_j`, `log P_{j+1} = 2(log Q_j)²`, `K_j = j² K₁`, `H_j = (log Q_j)³` (`j ≥ 2`),
`H₁ = P₁^{1/10}`, `H_* = log X`; `J` = last `j` with `Q_j ≤ P_*`. Then `log P_J ≥ (log X)^{0.39}`.
`S` = `n ∈ (X, 4X]` with a prime factor in every `𝒥_j` and in `𝒥_*`.

1. **Rough class.** `#{n ≤ 4X : no prime in [P, Q]} ≤ C X log P/log Q` (upper sieve); with (MVT),
   `∫_{-T}^{T} |D(f 1_{∉S})|² ≤ C Σ_j log P_j/log Q_j + C (log X)^{-0.05} ≤ C/K₁ + o(1)`.
2. **Ramaré at a scale `[P, Q]`, width `H ≤ P`.** For `n ∈ S`: `f(n) = Σ_{p|n, p∈[P,Q]} f(p) f(n/p)/ω(n)`,
   `ω = ω_{[P,Q]}`. With `Q_v(t) = Σ_{p∈[P,Q], e^{v/H} ≤ p < e^{(v+1)/H}} f(p)p^{-1-it}` and
   `R_v(t) = Σ_{Xe^{-v/H} < m ≤ 4Xe^{-v/H}, m ∈ S^{(j)}} f(m)/(ω(m)+1) m^{-1-it}` (`S^{(j)}`: a prime in
   every other scale — stable under `p ∈ [P,Q]`),
   `∫_{-T}^{T} |D(f1_S) − Σ_v Q_v R_v|² ≤ C(1/H + 1/P)`: the difference lives on `p² | n` (density
   `≤ 1/P`) and on the boundary ranges `n ∈ (X, Xe^{1/H}] ∪ (4Xe^{-1/H}, 4Xe^{1/H}]` with coefficients
   `≤ 1` (every `p | n` contributes `≤ 1/ω(n)`).
3. **Sets.** `𝒯₁ = {t : |Q_{1,v}(t)| ≤ e^{-αv/H₁} ∀v}`, `𝒯_j = {t ∉ 𝒯₁∪…∪𝒯_{j−1} : |Q_{j,v}(t)| ≤ e^{-αv/H_j} ∀v}`,
   `𝒰 = [−T, T] \ ∪_j 𝒯_j`. On each set Cauchy–Schwarz: `|Σ_v Q_v R_v|² ≤ |I| Σ_v |Q_v R_v|²`.
4. **Scale 1.** `∫|R_v|² ≤ 3C₁(T e^{v/H}/X + 4)`, so
   `∫_{𝒯₁} ≤ 3C₁|I₁|(e|I₁| K h^{-3/4+η} + 4P₁^{-2α}(H₁/(2α) + 1)) → 0` as `h → ∞`.
5. **Scale `j ≥ 2` (moment trick).** `t ∈ 𝒯_j` ⇒ some `u ∈ I_{j−1}` has `|Q_{j−1,u}(t)| > e^{-αu/H_{j−1}}`;
   with `ℓ = ⌈(v/H_j)/(u/H_{j−1})⌉`: `∫_{𝒯_j}|R_{j,v}|² ≤ Σ_u e^{2ℓαu/H_{j−1}} ∫ |Q_{j−1,u}^ℓ R_{j,v}|²`.
   The product has length `≥ X ≥ T`, so (MVT) gives `≤ 2C₁ Σ |c_n|²/n ≤ 6C₁ Σ_{p⃗,q⃗} 1/lcm(Πp⃗, Πq⃗)`
   (the `m`-sum over multiples of `Πq⃗/gcd`), and `gcd ≤ Σ_{d|gcd} d` gives
   `Σ_{p⃗,q⃗} 1/lcm ≤ (ℓ+1)(ℓ²σ_u)^ℓ`, `σ_u = Σ_{p∈I_u} 1/p ≤ 3/H_{j−1}`. Since `ℓu/H_{j−1} ≤ v/H_j + log Q_{j−1} + 1`,
   the total is `≤ C|I_j|²|I_{j−1}| Q_{j−1}^{1/2}(ℓ+1)(3ℓ²/H_{j−1})^ℓ`; `ℓ ≥ log P_j/log Q_j−1 = 2 log Q_{j−1}`
   and `3eℓ² ≤ H_{j−1}` give `≤ Q_{j−1}^{-3/2} polylog(Q_{j−1})`, summable, `→ 0` as `h → ∞`.
6. **Exceptional set.** `t ∈ 𝒰` ⇒ some `u ∈ I_J` has `|Q_{J,u}(t)| > y^{-α}`, `y = e^{u/H_J}`.
   *Large values:* with `k = ⌈log T/log y⌉`, (dMVT) for `Q^k` (`|c_n| ≤ k!`, `Σ|c_n|²/n² ≤ k!(σ/y)^k`) gives
   at most `C T^{2α} y^{2α} k log y (kσ)^k ≤ C T^{2α} Q_J^{2α} log X` 1-spaced such `t` (`H_J ≥ 3k`).
   Cover `𝒰` by unit intervals; `|𝒦| ≤ 2|I_J| C T^{2α} Q_J^{2α} log X`.
   *RT scale:* `D_S ≈ Σ_{v∈I_*} Q_{*,v} R_{*,v}` (step 2), `|Q_{*,v}(t)| ≤ (log X)^{-A'}` for all `|t| ≤ X`
   (`exists_primeBlock_le`, `f(p) = −χ(p)`), and (HM) on the shifted grids `𝒦 + s`:
   `∫_𝒰 |R_{*,v}|² ≤ 3C(1 + |𝒦| T^{1/2} log T · Q_*/X) ≤ 6C` since `T^{1/2+2α} Q_J^{2α} Q_* ≤ X^{1−η}`.
   So `∫_𝒰 |D_S|² ≤ 6C |I_*|² (log X)^{-2A'} + C/H_* → 0` (`A' = 3`).
7. **Total.** For nonprincipal `χ`: `∫_{-T}^{T} |D(λχ 1_{(X,4X]}; t)|² ≤ ε(h) + o_X(1)`, `ε(h) → 0`. No
   separate low-frequency step: RT holds at every `|t| ≤ X`.

**Principal characters.** `λχ₀(n) = Σ_{d | (n, r)} μ(d)λ(d)λ(n/d)`: windows of `λ` of length `h/d`.
For `λ` the RT scale needs `Σ_{P<p≤P'} p^{-1-it} = (main ≤ 2/(|t| log P)) + O((log X)^{-A})` (ζ Route T,
corpus `Sieve.VonMangoldtTwist*`), valid for `|t| ≥ T₀ = H_*(log X)^{2}`, and step **D** below
`|t| ≤ T₀`: `sup_{|t| ≤ T₀} |Σ_{X<n≤4X} λ(n)n^{-1-it}| = o(T₀^{-1/2})` (PNT for `λ` with log-power
saving at polylogarithmic heights).

### P. Parseval

Multiplicative windows `g(x) = Σ_{x<n≤(1+δ)x} b_n`, `δ = h/X`: Mellin–Plancherel
`∫_0^∞ |g(x)|² x^{-3} dx = (1/2π)∫ |B(1+it)|² |((1+δ)^{1+it} − 1)/(1+it)|² dt`, so
`X^{-1}∫_X^{2X} |g(x)/(δX)|² ≤ C ∫ |B(1+it)|² min(1, (δt)^{-2}) dt`; the tail `|t| ≥ K/δ` costs
`6/(hK) + 24/K²` by (MVT). Additive windows: on blocks `[X_i, X_i(1+η')]` the additive window
`(x, x+h]` differs from `(x, x(1+h/X_i)]` by `≤ 2η'h + 1` terms.

## Lean

| Module | Content | Status |
|---|---|---|
| `ShiftedVinogradov` | `R(t,y,Q)` at real `y`; shift average for `(n+α)^{it}`; Vinogradov on dyadic blocks | compiled |
| `ShiftedPhaseBlocks` | `k`-th derivative test from the start point `N+α`; weighted blocks; saving at the classical scale | compiled |
| `HurwitzGrowth` | middle/large Hurwitz blocks; `‖Σ_{k≤K}(k+α)^{-σ-iτ}‖ ≤ C log τ`, `K ≤ 2τ²` | compiled |
| `LFunctionGrowth` | residues of `[1,qT]`; `‖L(σ+iτ,χ)‖ ≤ (q³+56q+qC) log τ` | compiled |
| `LFunctionThreeFourOne` | 3-4-1 for `−L'/L`; pole via `−ζ'/ζ`; `1/(1+1/δ) ≤ ‖L(1+δ+iy,ψ)‖ ≤ 1+1/δ` | compiled |
| `LFunctionDLVP` | `4/(1+δ−β) ≤ 3/δ + 3A + (80/R)(log Φ + log(1+1/δ))` | compiled |
| `LFunctionZeroFree` | disc growth for every `ψ` mod `q`; zero-free region, width `ε(γ)` | compiled |
| `LFunctionConj` | `L(s, χ⁻¹) = conj L(conj s, χ)`; `L'/L` reflection; VK region at `\|γ\| ≥ γ₀` | compiled |
| `LFunctionLogDerivStrip` | `‖L'/L(σ+iγ, χ)‖ ≤ C log Y/ε(Y+1)`, `\|γ\| ≤ Y`, `σ ≥ 1 − ε(Y+1)/2` | compiled |
| `TwistedChebyshevContour` | Perron + rectangle: master inequality for `Σ χ(n)Λ(n)n^{-iτ}` | compiled |
| `TwistedChebyshevBound` | `‖Σ_{n≤N} χ(n)Λ(n)n^{-iτ}‖ ≤ N/(log X)^A`, `log N ≥ (log X)^θ` | compiled |
| `PrimeBlockRouteT` | `‖Σ_{P<p≤2P} χ(p)p^{-1-iτ}‖ ≤ (log X)^{-A}` | compiled |
| `LadderMeanValue` | moment computation `∫\|Q^ℓ C\|²` for arbitrary bounded prime coefficients | compiled |
| `RamareDecomposition` | `ω_Pr`; `Σ_{p∣n} 1/(ω(n/p)+1) ≤ 1`, `= 1` if `ω(n) ≥ 1` and `p² ∤ n` | compiled |
| `RamareBlocks` | blocks `⌊H log p⌋`, cofactor ranges; interior `n` see every factorisation | compiled |
| `RamareBlockError` | error coefficients `≤ 2/n`, vanish off boundary and squareful `n` | compiled |
| `RamareBlockMVT` | step 2: `∫\|Σ_{n∈S} f(n)/n n^{2πiw} − Σ_p Σ_m a(p)c(m)(pm)^{2πiw}\|² ≤ (5πW/2+20eX)(4/X²)(10X/H+16X/P)` | compiled |

Corpus inputs for the ladder: MVT over index families `Sieve.integral_normSq_sum_unitLogPhase_le`;
coincidence count `Sieve.sum_card_coincidences_le`; set-integral Halász–Montgomery
`Sieve.setIntegral_normSq_logPoly_le_HM_window_recip` (mass `2N + C√W log W·|E| + 48πN log(2+4πW)`).

## Log
- 2026-11-12 — created; architecture after surveying the corpus μ-ladder (`Sieve.MoebiusHeadWindowAllLengths`, Route T via ζ).
