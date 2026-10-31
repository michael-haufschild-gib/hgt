# Walls ledger — status quo

Three wall families block every route: **Σ** the critical sign, **Π** square-root precision, **Γ**
selection of ζ at the trivial gauge point. The only channel between primes, and between the additive
and multiplicative readings, is the archimedean place; it glues by one hyperplane (the boost
hyperplane, orthogonal to the pole conductor).

Ledger status: **Solved** (the face is a theorem), **Partially solved**, **Open**, **No-go** (the
mechanism is refuted), **Sharpened** (open, with its exact form a theorem), **New** (wall face exposed
by the current results, outside the 3010 wall set). Strength: **RH**, **≥qRH** (implies a zero-free half-plane), **sub**.
`[L]` Lean anchor read; `[S]` source-level result in the frontier map.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Complete Weil positivity on an RH-complete schedule | Sharpened | RH | All vectors positive for `c ≤ (log log N)^{<1/16}` [L]; fixed packets `(log N)^{<1/19}` [L]; RH ⇔ positivity at `2(log N)^{α>¼}` [L]. The sign problem sits in the confinement of negative vectors (Σ1c), not in conductor averages (Σ1e) or the low block (Σ1f). |
| Σ1a Defect-only confinement | No-go | — | Subexponential defect-only capture fails (`Q < 2^k` witnesses) [L]. |
| Σ1b Edge payment (top band, Euler head) | Partially solved | sub | Joint top-band shell–pole cancellation [L]; growing Euler head alone unbounded [L]; full prime window cancels the `√Y` head pole on fixed packets [L]; growing packets open. |
| Σ1c Confinement / logarithmic reserve | Sharpened | RH at `α > ¼` | `W ≥ ac⁻⁷(D_N − C log(2c)‖x‖²)` with absolute constants for `c ≤ (log log N)^{<1/16}` [L]. The exponent `1/16` is the exponential conductor cutoff `exp(O(c¹⁶))`; polynomial confinement would reach `(log N)^α`. Zero detectors have long Möbius transforms [L], so under ¬RH the reserve fails at RH-complete overlap. |
| Σ1d Floor–completeness tradeoff | Open | sub | Smoother profiles lower the RH-complete overlap but shrink the floor at that overlap (inference; no theorem). |
| Σ1e Conductor averages at RH-complete overlap | Solved [S] | — | Level of distribution `θ < ½` for the complete residual; conductor-average energy `→ ∞`; nonpositive fraction `→ 0`; `κ(W|V_{N^θ}) = o(N^θ)` [S]. |
| Σ1f Low-conductor block / ground state | Solved at fixed `c`; diagonal schedules [L] | — | Low spectrum localized on conductors with `E_m(c) < T`; unique lowest eigenvalue `→ E_1(c)` on the pole vector `v_1` [L]. |
| Σ1g Exceptional conductors | New | sub | The `o(M)` nonpositive conductors of Σ1e are not excluded individually beyond `(log N)^A`; the complete-Weil face of exceptional moduli (Π9). |
| Σ1h Square-root conductor barrier | New | sub | Riesz frames and residual averages hold for `m² ≤ N` only [S]; conductors `N^{½} < m ≤ N` (where detectors live) carry no frame or average control. |
| Σ2 Extension / carrier | Solved | — | Hecke-supported or escaping ⇒ `κ ∈ {0, ∞}`; Haar successor with continuous dilation ⇒ `κ = ∞`; the archimedean successor gives `κ = κ_ζ + 1` [L]. |
| Σ3 Markov criticality / odd sector | Open | RH | RH ⇔ `R ≤ ½` on odd vectors ⇔ no odd eigenvector above `½` [L]. |
| Σ4 Rank uniformity (theta, heat Hankel, Jensen) | Partially solved | RH | Rank 7 strict, rank 8 PSD; fixed Jensen degree eventually hyperbolic. |
| Σ5 Finite index / heat count | Sharpened | ≥qRH | `κ < ∞` ⇒ Lindelöf + half-plane [L]; heat count `≤ C₀R log R`, `R = 2πe^{(2/3+ε)/t}` [L]; size-only floor `½` [L]; `c d²/log X ≤ Λ_X ≤ (2/3+ε)/log X` [L]. |
| Σ6 Realization | Open | RH | Lossless realization needs infinitely many resonances; a normal real-zero approximant family forces RH (Vitali) [L]. |
| Σ7 Explicit image / resolvent orientation | Partially solved | RH in strip | Depth identity `σ > 1`, theta–prime expression at `s = 4` [L]; strip version is the PBM convergence problem. |
| Σ8 Collision quantum | Sharpened | RH | `O ∈ 2ℕ`; RH ⇔ `O < 2` per window [L]; `κ ≤ sup O` [L]; prime current summable ⇔ `O = 0` [L]; theta-prefix readings round to `O`. |
| Σ9 Local signatures (finite) | Solved | — | Single prime; every full finite-sieve partition has one positive direction [L]; per place `κ = κ₀ + 1`; separable `Σκ₀ ≤ κ ≤ Σκ₀ + 1` [L]. |
| Σ10 Archimedean gluing | Solved | — | `κ(Φ_{K,c}) = κ^{(½)}(K) + 1` for every Hermitian `K`; sub-boost or periodic data glue at full index; prime towers glue at `κ + 1` [L]. |
| Σ11 Product-formula gluing of the global pole | New | sub | Pole–successor states at `k` distinct places have `κ = k` (separated boosts) [L]; a one-square global state is not an assembly of local states at `≥ 2` places; boosts multiply to `1` only on principal units. Open: a coupled assembly with one square. |
| Σ12 Running counterterm | Sharpened | RH | Local form = renormalized hyperbolic pair `2Re(X̄Y) − cR|X|²` + shell squares, positive off the pole by identity [L]; no fixed counterterm makes the prime kernel Pontryagin [L]; the infinite assembly needs the horizon counterterm `log N − γ`. |

## Π — square-root precision

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1 Global law | Solved (as equivalence) | RH | One-sided `ψ(x) − x ≤ C√x log²x` ⇔ RH ⇔ `κ = 0` [L]. |
| Π2 Deciding input | Open | RH | No unconditional source input at square-root precision. |
| Π3 Producer cost | Partially solved | sub / RH | Ceilings: single prime `2 log 2`, finite alphabet `1 + 1/((P+1)(P+2))`, parity-blind `31/30`, univariate sup norm `exp(−0.87n)` [L]; parity-selective growing alphabets reach slope `1 + ε`, `ψ ≤ (1+ε)x + C_ε log²x` [L]. Open: ε-uniform error; the dual certificate's precision is the convergence rate of `Σ μ(b) log b/b`. |
| Π4 Gamma reach | Partially solved | sub | Gamma pays Euler heads to `(log A)²`; every Haar piece except the first-prime coarse layer has uniform finite index [L]. |
| Π5 Dispersion / parity | Open | RH | Liouville twin count `2ψ(⌊√n⌋) − ψ(n)`; joint Möbius-moment / Mertens / sawtooth payment. |
| Π6 Depth visibility | Sharpened | — | Positivity at aperture `a` forces companions of comparable depth [L]; a cluster of `≍ log t` zeros hides a depth-`δ` zero from heat at `κ ≍ δ²` [L]. |
| Π7 Amplifier rank | No-go (finite support); abstract law solved | — | No extra exponent at fixed total support; bounded index over all tensor degrees ⇔ positivity [L]. |
| Π8 Census | Partially solved | sub | `≥ 4/5 − ε` of ordinates critical [L]; 70% or a simple off-line core within `A/log T` [L]; a uniform off-line count per window ⇒ critical fraction `→ 1` [L]. |
| Π9 Exceptional moduli | Partially solved | sub | Uniform zero-free region and Siegel for `q ≤ (log x)^A` [L]; every inverse-log rate at one conductor-uniform horizon [L]; beyond open (Σ1g is its complete-Weil face). |
| Π10 Logarithmic-saving barrier | Sharpened | sub | Individual source estimates save powers of `log`; conductor averages save enough at RH-complete overlap [S]. The barrier is individual, not average. |
| Π11 Quasi-RH rung | Solved (as equivalence) | ≥qRH | Zero width `≤ σ` ⇔ sign-free section shortfall at rate `e^{2βr}`, `β > σ` [L]. |
| Π12 Local count layer | New | sub | Pointwise tangent-disc count forces bounded critical multiplicity; not implied by counting nor by RH (critical-cluster falsifier); holds for density-one heights for ζ [L]. |

## Γ — selection at the trivial gauge point

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Trivial gauge point | Open | RH | `Θ ≥ ½`, Haar-a.e. `½`; RH ⇔ trivial point typical [L]. |
| Γ2 Twin resolution (finite) | Solved | — | Pole-index window: ζ index 0, Liouville 1 [L]; one profile separates ζ from every cofinite flip at fixed `c`; odd tests at `r > 27/50` separate ζ from the Liouville twin [map]. |
| Γ3 Twin-blindness of soft structure | No-go (complete) | — | Krein index invariant under unitary twists [L]. |
| Γ4 Hecke invariance | Open | RH | RH ⇔ collided form Hecke-invariant ⇔ `W = D` [L]. |
| Γ5 Source identification | Partially solved | RH | Integer counting + full-cone positivity ⇒ `λ = Λ` and RH [L]. |
| Γ6 Boundary sign / coherence | Solved | — | Pole boundary sign separates ζ from size-equivalent twins. |
| Γ7 Affine carrier with Weil dilation | Solved | — | Finite-index carriers with Weil dilation and visible successor exist exactly via the archimedean successor: `κ(φ_c) = κ_ζ + 1` [L]; integer/Haar successors force `κ = ∞` [L]. |
| Γ8 Poisson rigidity | Sharpened | RH | Positive tent-self-dual measures with gap are Dirac combs; zero-side positivity = RH. |
| Γ9 Archimedean continuity vs height decay | Solved (no-go) | — | Continuous dilation reading against denominator-decaying finite-adelic reading ⇒ `κ = ∞` [L]. |
| Γ10 Function-field indistinguishability | Solved (no-go) | — | `−|·|_∞` on `𝔽_q[T]` and `−|·|` on `ℚ` both have one negative square [L]; conformality cannot see what separates ℤ from `𝔽_q[T]`. |
| Γ11 Pole-blindness of the glued state | New | — | `κ(K_ζ + t·polePair` glued`) = κ_ζ + 1` for every `t` [L]: on the boost hyperplane the pole is invisible, so selection must come from Gamma and prime data. |

## Bridges

| Bridge | Anchor |
|---|---|
| `κ(K_ζ)` = right zeros = Hodge defect = one-sided count defect | HKT, ACS, ACP [L] |
| `κ(φ_c) = κ_ζ + 1`; boost hyperplane = `v_1^⊥`; `v_1` = complete-Weil ground state | AKG, RAPT, CACT [L] |
| `κ < ∞` ⇔ bounded heat counts ⇔ finite off-line support ⇒ Lindelöf | HKT [L] |
| `O < 2` ⇔ `κ ≤ 1` ⇔ cofinal source work `≤ 2` ⇔ RH; collision mass `= 2(κ + E)` | RHTower, HKT, AID [L] |
| `W = D` (Weil = collided) ⇔ RH; `D ≥ 0` unconditionally | AP [L] |
| Running counterterm `cR` (local) ↔ `log N − γ` (horizon) ↔ pole-index window | AKG, HKT [L] |
| Zeros read atomic vectors through Möbius horizons; conductor modes see only depth-`N` boundaries | RAPT [L] |
| Section shortfall rate = zero width = Birman–Schwinger / lag / deficit / band / damping rates | SPTL, ACCE, SSIC [L] |

## Status counts

| Family | Solved | Partially solved | Sharpened | Open | No-go | New |
|---|---|---|---|---|---|---|
| Σ | 5 (Σ1e, Σ1f, Σ2, Σ9, Σ10) | 3 (Σ1b, Σ4, Σ7) | 5 (Σ1, Σ1c, Σ5, Σ8, Σ12) | 3 (Σ1d, Σ3, Σ6) | 1 (Σ1a) | 3 (Σ1g, Σ1h, Σ11) |
| Π | 2 (Π1, Π11) | 4 (Π3, Π4, Π8, Π9) | 2 (Π6, Π10) | 2 (Π2, Π5) | 1 (Π7) | 1 (Π12) |
| Γ | 5 (Γ2, Γ6, Γ7, Γ9, Γ10) | 1 (Γ5) | 1 (Γ8) | 2 (Γ1, Γ4) | 1 (Γ3) | 1 (Γ11) |
