# Walls ledger — status quo

Three wall families block every route: **Σ** the critical sign, **Π** square-root precision, **Γ**
selection of ζ. All three are readings of one integer, `κ(K_ζ) = #` zeros right of the critical line,
on one hyperplane, the pole-orthogonal hyperplane `v₁^⊥` (= boost hyperplane = Markov hyperplane =
harmonic hyperplane). The archimedean place glues by that hyperplane and supplies the single global
square; no assembly of local poles at two or more primes does.

Status: **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, with its exact
form a theorem), **Open**, **No-go** (the mechanism is refuted), **Classified** (answered by a
classification theorem). Strength: **RH**, **≥qRH** (implies a zero-free half-plane), **sub**.
`[L]` Lean statement read; `[K]` frontier-map label for individually checked Lean; `[S]` Lean source
unfinished or outside its umbrella; `[map]` frontier-map status.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Complete Weil positivity on an RH-complete schedule | Sharpened | RH | Universal regime: tilted spline, all vectors, `c ≤ (log N)^{α<α*}`, `α* = min(1/500, 1/(60C_cut))`, `C_cut` ineffective [L]. RH regime: full space at `2(log N)^{α>¼}`, `v₁^⊥` at `α>½` [L]; every C^∞ profile on `v₁^⊥` at every `2(log N)^{α>0}` [L]; sinc profile at `≍ L(log L)²`, `L = log log N` [L]. |
| Σ1a Defect-only confinement | No-go | — | Subexponential defect-only capture fails (`Q < 2^k` witnesses) [L]. |
| Σ1b Edge and Haar payment | Partially solved | sub | Joint top-band shell–pole cancellation [L]; full prime window cancels the `√Y` head pole on fixed packets [L]; growing Euler head alone unbounded [L]; growing packets and the joint non-arithmetic Gamma graph + signed diagonal + roots + poles payment open. |
| Σ1c Confinement | Sharpened | sub (universal regime); RH (RH-complete) | Reverse defect gap: squared distance `> ‖y‖²/16` from `conductorSubspace Q` ⇒ `poleDefect ≥ (log Q/C_cut − 1)‖y‖²`; exponential cutoff `log R ≤ C(K+1)/η³` [L]. Nonpositive units have defect `≤ C c¹⁶` [L], so confinement stays below `√N` only for `c ≤ (log N)^{<1/16}`; the power-log proof runs at cutoff `exp(C c⁴⁶)`. |
| Σ1d Floor–completeness tradeoff | Sharpened | — | Ground energy `E₁(c) ≍ τ(c)` (profile Fourier tail). Tilted spline: floor `c⁻⁷` [L], universal regime to `α*`. C^∞ profiles: RH on `v₁^⊥` at every power of `log N` [L]. Sinc: RH-complete exactly where `τ(c) log N ≈ 1` [L]. |
| Σ1e Conductor averages at RH-complete overlap | Solved | — | `θ < ½`, `c²/log N → 0`: summed residual `= o(Σ E_m²)`, nonpositive-conductor fraction `→ 0`, nonpositive span dimension `o(N^θ)` [L]. |
| Σ1f Low-conductor block / ground state | Solved in the universal regime | — | Fixed `c` with gap `E₁ + g/2` on `v₁^⊥` [L]; diagonal schedules [L]; all vectors to `(log N)^{α*}` [L]. Beyond: Σ13. |
| Σ1g Exceptional conductors | Open | sub | The `o(N^θ)` nonpositive conductors of Σ1e are not excluded individually beyond `(log N)^A`; complete-Weil face of exceptional moduli (Π9). |
| Σ1h Square-root conductor barrier | Open | sub | Frames and residual averages need `m² ≤ N` [L]; above, confinement `exp(C c¹⁶)` exceeds `√N` for `α > 1/16`. |
| Σ2 Extension / carrier | Solved | — | Escape, mixing, height decay ⇒ `κ ∈ {0, ∞}`; Haar successor + continuous dilation ⇒ `κ = ∞`; finite-index Haar kernels split uniquely `k = p + ψ∘slope + Q`; punctured dilation limits exactly the reals `≤ 0` (sharp) [L]. |
| Σ3 Markov criticality / odd sector | Open | RH | RH ⇔ `R ≤ ½` on odd vectors ⇔ no odd eigenvector above `½` [L]. |
| Σ4 Rank uniformity (theta, heat Hankel, Jensen) | Partially solved | RH | Rank 7 strict, rank 8 PSD; fixed Jensen degree eventually hyperbolic [L]. |
| Σ5 Finite index / heat count | Sharpened | ≥qRH (for `K_ζ`); RH (for `K_ζ⊠K_ζ`) | `κ < ∞` ⇒ Lindelöf + half-plane [L]; heat count `≤ C₀R log R`, `R = 2πe^{(2/3+ε)/t}` [L]; `κ(K_ζ⊠K_ζ) ∈ {0, ∞}`, `0` iff RH [L]. |
| Σ6 Realization | Open | RH | Lossless realization needs infinitely many resonances; normal real-zero approximant family forces RH (Vitali) [L]. |
| Σ7 Explicit image / resolvent orientation | Partially solved | RH in strip | Depth identity `σ > 1`; theta–prime expression at `s = 4` [L]; strip version is the PBM convergence problem. |
| Σ8 Collision quantum | Sharpened | RH | `O ∈ 2ℕ`; RH ⇔ `O < 2` per window; `κ ≤ sup O` [L]. Integer theta Wiener–Hopf index = `O` on every window; RH ⇔ rounded readings vanish ∀T, `n ≥ 6`; index `0` on `T ≤ 3` [L]. |
| Σ9 Local signatures (finite) | Solved | — | Pole–successor `κ = κ₀ + 1` at every place of every field; every full finite-sieve partition has one positive direction; separable `Σκ₀ ≤ κ ≤ Σκ₀ + 1`; tower signature `Σκ₀ + 1 ≤ κ ≤ Σκ₀ + 2` [L]. |
| Σ10 Gluing at a place | Solved | — | `κ(K(|a|) + |a|_v^{−s/2}ψ(b)) = κ_v(K) + 1` at every place; Weil's correlation glued at `∞` or any prime has `κ_ζ + 1`; stable gluing `0 < s < 1`; readings add with zero-blind translation reading `= 1`; on `ℓ = 0` Weil dilation form + shell squares [L]. |
| Σ11 Product-formula gluing of the global pole | Classified | — | Sum of `|S|` local poles: `|S|` squares; tensor product: `2^{|S|−1}`; renormalized infinite product: `∞`, global-pole weight `2^{−|S|} → 0`; the extremal weight is the archimedean pole on `S`-units and the only archimedean weight [L]. The one square is supplied by the archimedean place. |
| Σ12 Running counterterm | Sharpened | RH | Local form = renormalized hyperbolic pair + shell squares [L]; no fixed counterterm makes the prime kernel Pontryagin [L]; the infinite assembly needs `log N − γ`. |
| Σ13 Residual-versus-floor barrier | Sharpened | sub | Norm-quasimode positivity requires `K Q⁵ rate / floor² ≤ 1/36` [L]; residual `K m⁴(c⁵/log N + c³/√log N)` against floor `c⁻⁷` stops fixed packets at `(log N)^{1/19}` [L]. At RH-complete overlap the floor is `≲ 1/log N`. |
| Σ14 Detection edge | Sharpened | RH | A regime with unconditional positivity cannot exclude an off-line zero beyond what is excluded unconditionally; RH is positivity across the edge between the universal and the RH regime. Edge location: tilted spline in `[α*, ¼]`; C^∞ profiles below every power of `log N`; sinc at `τ(c) log N ≈ 1` [L for the bracketing theorems]. |
| Σ15 Tensor amplification | No-go | — | `K_ζ^n` PD ⇔ RH for every `n ≥ 1`; `κ_ζ² ≤ κ(K_ζ⊠K_ζ)`; diagonal frequencies `ρ + ρ'`; arithmetic side = square of the prime side; no finite nonzero Künneth index [L]. |
| Σ16 Heat homotopy of the glued state | Sharpened | RH | `κ(φ_c^{(t)}) = N(t)/2 + 1 < ∞`, continuous source, lower semicontinuous, antitone, drop `Σ⌊m/2⌋` per collision, `1` for `t ≥ 1/8`; RH ⇔ constant index; `κ(φ_c) ≤ liminf_{t→0⁺}`; `0 ≤ Λ < 1/8` [L]. |

## Π — square-root precision

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1 Global law | Solved (as equivalence) | RH | `ψ(x) − x ≤ C√x log²x` ⇔ RH ⇔ `κ = 0` [L]. |
| Π2 Deciding input | Open | RH | No unconditional source input at square-root precision. |
| Π3 Producer cost | Partially solved | sub / RH | Ceilings `2 log 2`, `1 + 1/((P+1)(P+2))`, `31/30`, `exp(−0.87n)`; growing-alphabet parity-selective producers reach `ψ ≤ (1+ε)x + C_ε log²x` [L]. Open: ε-uniform error; dual precision = convergence rate of `Σ μ(b) log b/b`. |
| Π4 Gamma reach | Partially solved | sub | Gamma pays Euler heads to `(log A)²`; every Haar piece except the first-prime coarse layer has uniform finite index [L]. |
| Π5 Dispersion / parity | Open | RH | Liouville twin count `2ψ(⌊√n⌋) − ψ(n)`; joint Möbius-moment / Mertens / sawtooth payment. |
| Π6 Depth visibility | Sharpened | — | Aperture positivity forces companions of comparable depth [L]; a cluster of `≍ log t` zeros hides a depth-`δ` zero from heat at `κ ≍ δ²` [L]; a window depth-mass bound on all windows is a zero-free strip [L]. |
| Π7 Amplifier rank | No-go (finite support); abstract law solved | — | No extra exponent at fixed total support; fixed-loss moment bounds kill frequencies above `B`, growing losses `e^{2kλ}` keep radius `Be^λ` [L]. |
| Π8 Census | Partially solved | sub | `≥ 0.6725` simple critical, `≥ 4/5 − ε` critical ordinates [L]; 70% or simple near-line core [K]; right-half squared-depth moment `o(V)`, deep zeros `o(V)`, deep windows `o(T)` [L]; a per-window off-line bound ⇒ critical fraction `→ 1` [L]. |
| Π9 Exceptional moduli | Partially solved | sub | Uniform zero-free region and Siegel for `q ≤ (log x)^A`; every inverse-log rate at one conductor-uniform horizon [L]; beyond open. |
| Π10 Logarithmic-saving barrier | Sharpened | sub | Individual estimates save every power of `log` for `q ≤ (log x)^A` [L]; in the complete Weil matrix the binding losses are the overlap powers (`c⁵/log N`, `c³/√log N`), not the arithmetic rate. |
| Π11 Quasi-RH rung | Solved (as equivalence) | ≥qRH | Zero width `≤ σ` ⇔ sign-free section shortfall at rate `e^{2βr}`, `β > σ` [L]. |
| Π12 Local count layer | Sharpened | sub | Pointwise tangent-disc count forces bounded critical multiplicity, holds for density-one heights [L]; `λ_t log t → 0` ⇔ zeros tend to the line; a strip gives Littlewood windows [L]. |
| Π13 Gap-dependent detection scale | Sharpened | sub | Integer collision readings are accurate to `< 1/8` uniformly for `n ≥ 6`, but a collision is read only from stage `max 6 ⌈√log(8B(T)²)/δ⌉`, `δ` the collision gap; Rouché stabilization depends on `min|ξ|` off zero discs; first stabilized prefix unbounded in height; boundary ingress mandatory; no single-scale contour sees all splits [L]. |

## Γ — selection

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Trivial gauge point | Open | RH | `Θ ≥ ½`, Haar-a.e. `½`; RH ⇔ trivial point typical [L]. |
| Γ2 Twin resolution (finite) | Solved | — | Pole-index window: ζ `0`, Liouville `1` [L]; glued test index `∞` for every nonempty finite flip, `κ_ζ + 1` for `Λ` [L]; atomic Hodge index separates ζ from a sign gauge iff its margin is below `2 log 2`: Liouville, `S_N² = o(log N)`, flips `p < 11` [L]. |
| Γ3 Twin-blindness of soft structure | No-go (complete) | — | Krein index invariant under unitary twists; pointwise-closed weight classes contain every unitary twist [L]. |
| Γ4 Hecke invariance / Frobenius at infinity | Open | RH | RH ⇔ collided form Hecke-invariant ⇔ `W = D` [L]; collided side computed exactly from theta data [L]; missing: an arithmetic correspondence acting as conjugation on the divisor. |
| Γ5 Source identification | Partially solved | RH | Integer counting + full-cone positivity ⇒ `λ = Λ` and RH [L]. |
| Γ6 Boundary sign / coherence | Solved | — | Pole boundary sign separates ζ from size-equivalent twins. |
| Γ7 Affine carrier with Weil dilation | Solved | — | Finite-index carriers with Weil dilation and visible successor exist via gluing at a place (`κ_ζ + 1` at `∞` and every prime); integer/Haar successors force `κ = ∞` [L]. |
| Γ8 Poisson rigidity | Sharpened | RH | Positive tent-self-dual measures with gap are Dirac combs; zero-side positivity = RH [S]. |
| Γ9 Archimedean continuity vs height decay | Solved (no-go) | — | Continuous dilation reading against denominator-decaying finite-adelic reading ⇒ `κ = ∞` [L]. |
| Γ10 Function-field indistinguishability | Sharpened | — | Conformality and the local index wall are identical over `𝔽_q(X)` (wall at `∞`) [L]; the distinguishing datum is density of the extremal-weight exponents: dense for two primes, a lattice for one prime and for `𝔽_q[T]` [L]. |
| Γ11 Pole-blindness of the glued state | Solved (no-go) | — | Simple pole absorbed at any strength; double pole costs a square; the glue absorbs exactly the pair at its own exponent [L]. Selection must come from Gamma and prime data. |
| Γ12 Maximal-margin twins | Open | sub | Flips of primes `≥ 11` and gauges with `S_N/H_N → 1` keep margin `2 log 2` and are invisible to the atomic Hodge index [L]; finite ones are separated by the glued test index [L]; infinite ones open. |
| Γ13 Source-uniform extinction | No-go | — | A source family defined at every nonreal strip point has optical flux `−16(Re s−½)Im s·M₊M₋` and cannot force extinction (fails at `3/4 + i`) [L]; zero selection enters only through the coefficient `Λ(s)` of `E*(·, s/2)`. |

## Bridges

| Bridge | Anchor |
|---|---|
| `κ(K_ζ)` = right zeros = Hodge defect `κ^{(½)}(K_ζ)` = one-sided count defect | HKT, RIT, ACS, ACP [L] |
| `κ(φ_c) = κ_ζ + 1` at every place = multiplicative reading `κ_ζ` + additive reading `1` | AKG [L] |
| Boost hyperplane = `v₁^⊥` = Markov hyperplane = harmonic hyperplane; `v₁` = complete-Weil ground state | RIT, SMAP, SSHA, CACT [L] |
| `κ(φ_c^{(t)}) − 1` = Hodge defect of `K_t` = `N(t)/2` = future collision pairs; `κ_ζ ≤ sup O` | AKG, RIT [L] |
| Collision charge = winding of a theta-prefix Zhukovsky loop = Fredholm index of its Wiener–Hopf operator | CDG [L] |
| `κ < ∞` ⇔ bounded heat counts ⇔ finite off-line support ⇒ Lindelöf; `κ(K_ζ⊠K_ζ) < ∞` ⇒ RH | HKT, RIT [L] |
| Global pole = extremal weight of the product of local poles = archimedean pole on `S`-units | RIT [L] |
| `W = D` ⇔ RH; Hecke defect = symmetric second difference of `D` | AP, CDG [L] |
| Running counterterm `cR` (local) ↔ `log N − γ` (horizon) ↔ pole-index window | AKG, HKT [L] |
| Ground energy `E₁(c) ≍` Fourier tail `τ(c)`; RH threshold of the sinc profile at `τ(c) log N ≈ 1` | RAPT, TM [L] |
| Section shortfall rate = zero width = Birman–Schwinger / lag / deficit / band / damping rates | SPTL, ACCE, SSIC [L] |

## Status counts

| Family | Solved | Partially solved | Sharpened | Open | No-go | Classified |
|---|---|---|---|---|---|---|
| Σ | 5 (Σ1e, Σ1f, Σ2, Σ9, Σ10) | 3 (Σ1b, Σ4, Σ7) | 9 (Σ1, Σ1c, Σ1d, Σ5, Σ8, Σ12, Σ13, Σ14, Σ16) | 4 (Σ1g, Σ1h, Σ3, Σ6) | 2 (Σ1a, Σ15) | 1 (Σ11) |
| Π | 2 (Π1, Π11) | 4 (Π3, Π4, Π8, Π9) | 4 (Π6, Π10, Π12, Π13) | 2 (Π2, Π5) | 1 (Π7) | — |
| Γ | 5 (Γ2, Γ6, Γ7, Γ9, Γ11) | 1 (Γ5) | 2 (Γ8, Γ10) | 3 (Γ1, Γ4, Γ12) | 2 (Γ3, Γ13) | — |
