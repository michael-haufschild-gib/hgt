# Walls ledger — status quo

Three wall families block every route: **Σ** the critical sign, **Π** square-root precision, **Γ**
selection of ζ at the trivial gauge point. The only channel between primes, and between the additive
and multiplicative readings, is the archimedean place (rank one).

Ledger status: **Solved** (the face is a theorem), **Partially solved**, **Open**, **No-go** (the
mechanism is refuted), **Sharpened** (the wall is open and its exact form is a theorem), **New** (wall
not in the 3010 ledger). Strength: **RH**, **≥qRH** (implies a zero-free half-plane), **sub**.
`[L]` = Lean anchor read.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Growing-overlap complete positivity | Sharpened | RH | Fixed `c`, all vectors: log reserve [L], horizon ineffective in `c`. Explicit polynomial reserve [L]. Fixed packets positive at `(log log N)^A`, `(log N)^{<1/48}` [L], `(log N)^{<1/19}` (SSH). Conductor residual uniform for `m ≤ (log N)^A` [L]. RH ⇔ positivity at `c = (log N)^{α>¼}`. |
| Σ1a Defect-only confinement | No-go | — | Subexponential defect-only capture fails (`Q < 2^k` witnesses). |
| Σ1b Edge payment (top band, Euler head) | Partially solved | sub | Joint top-band shell–pole cancellation [L]; growing Euler head alone has unbounded index [L]; full prime window cancels the `√Y` head pole on fixed packets [L]. Open: growing packets. |
| Σ1c Reach ledger | New | sub/RH | Residual `c^a/(log N)^b` vs floor `c⁻¹⁴` gives reach `α < b/(a+14)` (inference; reproduces `1/19`). RH needs horizon exponent `K < 4` in `N ≥ exp(c^K)` **and** `b > (a+14)/4`; which of the two carries the RH content is open. |
| Σ1d Floor–completeness tradeoff | New | sub | Smoother profiles lower the RH-complete overlap (spline `(log N)^{¼}`, smooth `(log N)^ε`, Gevrey-2 `(log log N)^{>2}`, Steklov `L(log L)²`) but shrink the floor at that overlap faster (inference; no theorem). |
| Σ2 Extension / carrier | Solved as no-go classes | — | Hecke-supported or escaping ⇒ `κ ∈ {0, ∞}` [L]; Hecke-supported finite-index Weil extension ⇒ RH [L]; Haar successor ⇒ `κ = ∞` [L]. Remaining: Γ7. |
| Σ3 Markov criticality (positive supersolution) | Open | RH | Odd sector: RH ⇔ `R ≤ ½` on odd vectors ⇔ no odd eigenvector above `½` [L]. |
| Σ4 Rank uniformity (theta, heat Hankel, Jensen) | Partially solved | RH | Rank 7 strict, rank 8 PSD; fixed Jensen degree eventually hyperbolic; all ranks open. |
| Σ5 Finite index / heat count | Sharpened | ≥qRH | `κ < ∞` ⇒ Lindelöf + zero-free half-plane [L]. Heat count `≤ C₀R log R`, `R = 2πe^{(2/3+ε)/t}` [L]; size-only floor `½` [L]; `a < 1` ⇒ `X^{o(1)}` deep counts [L]. |
| Σ6 Realization | Open | RH | Lossless realization needs infinitely many resonances; Vitali: a real-zero approximant family that stays normal forces RH, so a failing one must blow up [L]. |
| Σ7 Explicit image / resolvent orientation | Partially solved | RH in strip | Depth identity for `σ > 1`, theta–prime expression at `s = 4` [L]; in `½ < σ ≤ 1` the prime side is the PBM convergence problem. |
| Σ8 Collision quantum | Sharpened | RH | `O ∈ 2ℕ`; RH ⇔ `O < 2` on every window [L]; prime current summable ⇔ `O = 0` [L]; theta-prefix readings round to `O`; source work `≤ 2` cofinally ⇒ RH [L]. |
| Σ9 Local-to-global signature (finite) | Solved | — | Single prime; every full finite-sieve partition has exactly one positive direction [L]; per place `κ = κ₀ + 1` [L]; separable assembly `Σκ₀ ≤ κ ≤ Σκ₀ + 1` [L]. |
| Σ10 Running counterterm | New | RH | Each local pole–successor form is a renormalized hyperbolic pair `2Re(X̄Y) − cR|X|²` plus shell squares, positive off the pole by identity [L]; no fixed counterterm makes the full prime kernel Pontryagin [L]; the infinite assembly needs a counterterm running with the horizon (`log N − γ`). |

## Π — square-root precision

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1 Global law | Solved (as equivalence) | RH | One-sided `ψ(x) − x ≤ C√x log²x` ⇔ RH ⇔ `κ = 0` [L]. |
| Π2 Deciding input | Open | RH | No unconditional source input at square-root precision. |
| Π3 Producer cost | Sharpened | sub | Landau factorial `(2 log 2 − ε)mn`; Adams `2^{qr}`; Chebyshev `ψ ≥ 0.89x`; Hecke auxiliaries critical-only and `K`-monomial vanishing `< K` [L]. |
| Π4 Gamma reach | Partially solved | sub | Gamma pays Euler heads to `(log A)²`; every Haar piece except the first-prime coarse layer has uniform finite index [L]. |
| Π5 Dispersion / parity | Open | RH | Liouville twin count `2ψ(⌊√n⌋) − ψ(n)`; joint Möbius-moment / Mertens / sawtooth payment. |
| Π6 Depth visibility | Sharpened | — | Positivity at aperture `a` forces companions of comparable depth [L]; a cluster of `≍ log t` zeros hides a depth-`δ` zero from heat at `κ ≍ δ²` [L]. |
| Π7 Amplifier rank | No-go (finite support); abstract law solved | — | No extra exponent at fixed total support; bounded index over all tensor degrees ⇔ positivity (`TensorPolarizationAmplification`) [L]. |
| Π8 Census | Partially solved | sub | `≥ 4/5 − ε` of ordinates critical [L]; simple-critical `≥ 0.6725`; 70% or a simple off-line core within `A/log T` [L]; 100% open. |
| Π9 Exceptional zeros | Partially solved | sub | Uniform zero-free region and Siegel for `q ≤ (log x)^A` [L]; beyond open. |
| Π10 Logarithmic-saving barrier | New | sub | Every unconditional source estimate in the corpus saves powers of `log`: sawtooth `(1 + log t)^{−3}` [L], complete residual `1/log N`, `1/√log N` [L], Dirichlet `exp(−κ(log x)^{1/10})`. Σ1c converts these exponents into overlap reach. |
| Π11 Quasi-RH rung | New | ≥qRH | Zero width `≤ σ` ⇔ sign-free section shortfall at rate `e^{2βr}`, `β > σ` [L]; every exponent gain on the count side is a quasi-RH statement. |

## Γ — selection at the trivial gauge point

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Trivial gauge point | Open | RH | `Θ ≥ ½`, Haar-a.e. `½`; RH ⇔ trivial point typical. |
| Γ2 Twin resolution (finite) | Solved | — | Pole-index window: ζ index 0, Liouville 1 [L]; one profile separates ζ from every cofinite flip at fixed `c`; odd tests at `r > 27/50` separate ζ from the Liouville twin. |
| Γ3 Twin-blindness of soft structure | No-go (complete) | — | The Krein index is invariant under unitary twists [L]; pointwise-closed classes twin-blind. |
| Γ4 Hecke invariance | Open | RH | RH ⇔ collided form Hecke-invariant ⇔ `W = D` [L]; two-scale depth rigidity [L]. |
| Γ5 Source identification | Partially solved | RH | Integer counting + full-cone positivity ⇒ `λ = Λ` and RH [L]; count precision alone does not select. |
| Γ6 Boundary sign / coherence | Solved | — | Pole boundary sign separates ζ from size-equivalent twins. |
| Γ7 Affine extension | Partially solved | sub | Blind extension index-minimal; regular extension index 0 ⇔ RH; separable or Hecke-supported carriers with continuous Weil dilation have `κ = ∞` [L]. Open: nonseparable, non-Hecke-supported states with continuous dilation. |
| Γ8 Poisson rigidity | Sharpened | RH | Positive tent-self-dual measures with gap are Dirac combs; zero-side positivity = RH. |
| Γ9 Archimedean continuity vs height decay | New | — | A dilation reading continuous at `1` and a finite-adelic reading decaying with the denominator cannot coexist at finite index [L]. |
| Γ10 Function-field indistinguishability | New | — | `−|·|_∞` on `𝔽_q[T]` and `−|·|` on `ℚ` both have exactly one negative square [L]; conformality cannot see what separates ℤ from `𝔽_q[T]` (the quantized factor of one place). |

## Bridges between the families

| Bridge | Anchor |
|---|---|
| `κ(K_ζ)` = right zeros = Hodge defect = one-sided count defect | HKT, ACS, ACP [L] |
| `κ < ∞` ⇔ bounded heat counts ⇔ finite off-line support ⇒ Lindelöf | HKT [L] |
| `O < 2` ⇔ `κ ≤ 1` ⇔ cofinal source work `≤ 2` ⇔ RH | RHTower, HKT, AID [L] |
| `W = D` (Weil = collided) ⇔ RH; `D ≥ 0` unconditionally | AP [L] |
| Running counterterm: local shell counterterm `cR` ↔ horizon counterterm `log N − γ` ↔ pole-index window of width `2 log 2` | AKG, HKT [L] |
| Section shortfall rate = zero width = Birman–Schwinger rate = lag/deficit/band/damping rates | SPTL, ACCE, SSIC [L] |

## Status counts

| Family | Solved | Partially solved | Sharpened | Open | No-go | New |
|---|---|---|---|---|---|---|
| Σ | 2 | 3 | 3 | 2 | 1 | 3 |
| Π | 1 | 3 | 2 | 2 | 1 | 2 |
| Γ | 2 | 2 | 1 | 2 | 1 | 2 |
