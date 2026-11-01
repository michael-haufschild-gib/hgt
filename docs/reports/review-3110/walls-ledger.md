# Walls ledger — status quo

Three wall families block every route: **Σ** the critical sign, **Π** square-root precision, **Γ**
selection of ζ. All three are readings of one even integer, `κ(K_ζ) = #` zeros right of the critical
line, on one hyperplane, the pole-orthogonal hyperplane `v₁^⊥` (= boost hyperplane = Markov
hyperplane = harmonic hyperplane). The archimedean place glues by that hyperplane and supplies the
single global square; no assembly of local poles at two or more primes does. The zeros are carried
by the inter-tower coupling: two primes suffice for the test lattice, finitely many primes suffice
on every window, and separable data are blind.

Status: **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, with its exact
form a theorem), **Open**, **No-go** (the mechanism is refuted), **Classified** (answered by a
classification theorem). Strength: **RH**, **≥qRH** (implies a zero-free half-plane and Lindelöf),
**LH** (implies Lindelöf, no half-plane known), **sub**. `[L]` Lean statement read; `[K]` frontier-map
label for individually checked Lean; `[S]` Lean source unfinished or outside its umbrella; `[D]`
derived from `[L]` statements, not formalized; `[map]` frontier-map status.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Complete Weil positivity on an RH-complete schedule | Sharpened | RH | Universal regime: tilted spline, all vectors, `1 ≤ c ≤ (log N)^{α}`, `α < 1/144` explicit [L]. RH regime: tilted full space at `2(log N)^{α>¼}`, `v₁^⊥` at `α>½`; C^∞ nonnegative profiles (unitBump explicit) on `v₁^⊥` at every `2(log N)^{α>0}`; sinc at `≍ L(log L)²`; every admissible C² profile at `2(log N)^{β>¼}` [L]. No transfer between the universal-regime profile and the C^∞ receivers. |
| Σ1a Defect-only confinement | No-go | — | Subexponential defect-only capture fails (`Q < 2^k` witnesses) [L]. |
| Σ1b Edge and Haar payment | Partially solved | sub | Joint top-band shell–pole cancellation; full prime window cancels the `√Y` head pole on fixed packets; growing Euler head alone unbounded [L]. Prime heads and the literal prime residual bounded relative to adjunction energy with polylogarithmic conductor cost, uniformly in packet size [S]. Open: Gamma/polar side at growing packets; joint non-arithmetic Gamma graph + signed diagonal + roots + poles. |
| Σ1c Confinement | Sharpened | sub (universal regime); RH (RH-complete) | Explicit: `log R ≤ C_quad(K+1)/η²`; reverse gap `poleDefect ≥ (log Q/(256C_quad) − 1)‖y‖²` outside squared tolerance `1/16`; supported-above-`Q` packets likewise; truncation measured by the logarithmic class moment [L]. Nonpositive units have defect `≤ Cc¹⁶`; the power-log proof runs at cutoff `log R' ≤ C_R c¹⁶ + log Q₁` [L]; confinement below `√N` holds only for `α < 1/16`. |
| Σ1d Floor–completeness tradeoff | Sharpened | — | `E₁(c) ≍ τ(c)`. Tilted spline: floor `c⁻⁷`, universal regime to `1/144`. C^∞ profiles: RH on `v₁^⊥` at every power of `log N`. Sinc: RH-complete exactly where `τ(c) log N ≈ 1` [L]. |
| Σ1e Conductor averages at RH-complete overlap | Solved | — | `θ < ½`, `c²/log N → 0`: summed residual `= o(Σ E_m²)`, nonpositive-conductor fraction `→ 0`, nonpositive span dimension `o(N^θ)` [L]. |
| Σ1f Low-conductor block / ground state | Solved in the universal regime | — | Fixed `c` with gap `E₁ + g/2` on `v₁^⊥`; diagonal schedules; Hodge index on fixed and slowly growing packets at `(log N)^{<1/19}`; all vectors to `(log N)^{1/144}` [L]. Beyond: Σ13. |
| Σ1g Exceptional conductors | Partially solved | sub | Single Ramanujan modes `(log N)^A ≤ m ≤ N^θ`, `θ < ½`, `α < ¼`, `A > 8α`, every C² profile: energy `≥ ((1−2θ)/4) log m`, no exceptional single conductor [L]. Packet pole defect `≥ (log N − 3 log Q − 1) L_Q` [L]. Spans: the `o(N^θ)` nonpositive dimension of Σ1e is not excluded; low conductors `m < (log N)^A` open (Π9). |
| Σ1h Square-root conductor barrier | Open | sub | Frames and residual averages need `m² ≤ N` [L]; above, confinement `exp(Cc¹⁶)` exceeds `√N` for `α > 1/16`. |
| Σ2 Extension / carrier | Classified | — | Escape, mixing, height decay ⇒ `κ ∈ {0, ∞}`; for every additive `H ≤ ℚ`, a finite-index carrier with translation reading `1_H` and continuous dilation at `1` exists iff `H ∈ {{0}, ℚ}`, both with PD carriers; finite-index Haar kernels split uniquely `k = p + ψ∘slope + Q`; punctured limits exactly the reals `≤ 0` [L]. |
| Σ3 Markov criticality / odd sector | Open | RH | RH ⇔ `R ≤ ½` on odd vectors ⇔ no odd eigenvector above `½` [L]. |
| Σ4 Rank uniformity (theta, heat Hankel, Jensen) | Partially solved | RH | Rank 7 strict, rank 8 PSD; fixed Jensen degree eventually hyperbolic [L]. |
| Σ5 Finite index / heat count | Sharpened | ≥qRH (for `K_ζ`); RH (for `K_ζ⊠K_ζ`) | `κ < ∞` ⇔ bounded `N(t)` ⇔ bounded cumulative collision charge ⇒ Lindelöf + half-plane [L]; heat count `≤ C₀R log R`, `R = 2πe^{(2/3+ε)/t}` [L]; `κ(K_ζ⊠K_ζ) ∈ {0, ∞}` [L]; `κ_ζ` even, `κ(φ_c) ≠ 2` [S]. |
| Σ6 Realization | Open | RH | Lossless realization needs infinitely many resonances; normal real-zero approximant family forces RH (Vitali) [L]. |
| Σ7 Explicit image / resolvent orientation | Partially solved | RH in strip | Depth identity `σ > 1`; theta–prime expression at `s = 4` [L]; strip version is the PBM convergence problem. |
| Σ8 Collision quantum | Sharpened | RH | `O ∈ 2ℕ`; RH ⇔ `O < 2` per window; `κ ≤ sup O` [L]. Integer theta Wiener–Hopf index = `O` on every window; root-free stopping certificate sound and eventually complete; RH ⇔ the stopping-prefix index vanishes eventually in scale at every integer height; index `0` on `T ≤ 3` [L]. `n_off ≤ ΔO ≤ 2·max H·n_off`, `ΔO ≪ log²T`; bounded `ΔO` ⇒ density one; fibre multiplicity `H(γ) ≤ C(1 + log|γ|/L) − Re Π_{F_L} + 4E_γ(L)` [L]. |
| Σ9 Local signatures (finite) | Solved | — | Pole–successor `κ = κ₀ + 1` at every place; every full finite-sieve partition has one positive direction; separable `Σκ₀ ≤ κ ≤ Σκ₀ + 1`; tower signature `Σκ₀ + 1 ≤ κ ≤ Σκ₀ + 2` [L]; on `ℤ`, `κ₀(k) = κ(Δ²k)`, decaying second difference gives `{0, ∞}`, with one pole pair `{0, 1, ∞}` [S]. |
| Σ10 Gluing at a place | Solved | — | `κ(K(|a|) + |a|_v^{−s/2}ψ(b)) = κ_v(K) + 1` at every place; Weil's correlation glued at `∞` or any prime has `κ_ζ + 1`; stable gluing `0 < s < 1`; readings add with zero-blind translation reading `= 1`; on `ℓ = 0` Weil dilation form + shell squares [L]. |
| Σ11 Product-formula gluing of the global pole | Classified | — | Sum of `|S|` local poles: `|S|` squares; tensor product: `2^{|S|−1}`; renormalized infinite product: `∞`; the extremal weight is the archimedean pole on `S`-units and the only archimedean weight [L]. |
| Σ12 Running counterterm | Sharpened | RH | Local form = renormalized hyperbolic pair + shell squares; no fixed counterterm makes the prime kernel Pontryagin; the infinite assembly needs `log N − γ` [L]. Local counterterms `C + Dδ₀ − A|n|` on separable towers make `Λ` and a prime-flip twin both glued index `1` [S]. |
| Σ13 Residual-versus-floor barrier | Sharpened | sub | Norm-quasimode positivity requires `K Q⁵ rate / floor² ≤ 1/36`; residual `K m⁴(c⁵/log N + c³/√log N)` against floor `c⁻⁷` stops fixed packets at `(log N)^{1/19}` [L]. Prime residual relative to adjunction energy costs only `(1+log Q)²` [S]; the overlap/Gamma/pole `c`-power rates are the binding terms. |
| Σ14 Detection edge | Sharpened | RH | Edge `e_φ(N)` defined; RH ⇔ `e_φ ≡ ∞` (all or eventually all `N`), every admissible profile; edge dichotomy: `∞` everywhere or `≤ 2(log N)^β` infinitely often for every `β > ¼`; tilted edge `≥ (log N)^{α}`, `α < 1/144`, and `→ ∞` unconditionally; hyperplane edge `≤ 2(log N)^β` i.o. for `β > ½` (tilted) and every `β > 0` (smooth) [L]. Threshold-curve form `PositiveAt φ c N ⇔ N < h(atom_{c/N})`; over a curve edge `≤ 2g`, edge `∞` iff unitary [S]. Unconditional positivity cannot cross the edge. |
| Σ15 Tensor amplification | No-go | — | `K_ζ^n` PD ⇔ RH for every `n ≥ 1`; `κ_ζ² ≤ κ(K_ζ⊠K_ζ)`; no finite nonzero Künneth index [L]. |
| Σ16 Heat homotopy of the glued state | Sharpened | RH | `κ(φ_c^{(t)}) = N(t)/2 + 1 < ∞`, lower semicontinuous, antitone, drop `Σ⌊m/2⌋` per collision, `1` for `t ≥ 1/8`; RH ⇔ constant index; `0 ≤ Λ < 1/8` [L]. |
| Σ17 Prime-pole coherence cost | Sharpened | sub | `B_Q(a)² ≤ S_Q L_Q(a)` with optimal `S_Q = Σ_{p≤Q} log p/p = log Q + O(1)`, extremizer `a_p = √(p−1)/p`; the cost survives on every finite-horizon pole hyperplane [S]. In prime-incidence coordinates (`1_{p|n} − 1/p`) generator, jumps and tails are nonnegative counts; the coherent prime residual is `≥ ½ log P · (pole mass)² − C(1+log Q)·mass`, beyond the scalar row's reach [L]. Payment must come from the pole term, its running counterterm and Mertens' constant. |
| Σ18 Separable assemblies | Classified (no-go) | — | Separable `S`-truncated assemblies: glued index `∞` or `r_S + 1`, `r_S + 2`, zero-independent [S]. Every separable assembly annihilates coprime cross-differences; no separable net converges pointwise to `ratCorr`; untruncated axial assemblies of `ratCorr` overcount (`κ₀ ≥ κ_ζ − 1` per non-blind prime) and diverge on the finite non-RH stratum; fixed-`S` global truncated correlations `∈ {1, ∞}` [L]. |
| Σ20 Inter-tower coupling | Sharpened | RH | Coupled `S`-tower assembly (`|S| ≥ 2`) = axial + inter-tower coupling, coupling zero on axes and equal to `K(uv) − K(u) − K(v) + K(1)` off them; coupled assemblies carry `κ_ζ + 1` exactly; window explicit formula with primes `≤ e^{2L+8}` exact on log-height `≤ L`, supremum `κ_ζ + 1`; zero coupling of a continuous profile ⇒ affine, `κ ≤ 2`; `ratCorr` has nonzero coupling [L]. RH ⇔ bounded coupling on `⟨2,3⟩ × ⟨5,7⟩` [D: Hyers–Ulam + density + bounded-kernel theorem]. |
| Σ19 Deformation to a positive model | No-go (as a free input) | — | Crossing-free Hermitian path `A → I` exists iff `A` is PD; negative index constant along nondegenerate connected families, rises by at most the nullity at a crossing; an integer within `½` of a continuous real reading is constant [L]. An index computed by deformation equals the sign; noncrossing must be proved from the source. |

## Π — square-root precision

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1 Global law | Solved (as equivalence) | RH | `ψ(x) − x ≤ C√x log²x` ⇔ RH ⇔ `κ = 0` [L]. |
| Π2 Deciding input | Open | RH | No unconditional source input at square-root precision. |
| Π3 Producer cost | Partially solved | sub / RH | Ceilings `2 log 2`, `1 + 1/((P+1)(P+2))`, `31/30`, `exp(−0.87n)`; growing-alphabet producers reach `ψ ≤ (1+ε)x + C_ε log²x` [L]. Open: ε-uniform error. |
| Π4 Gamma reach | Partially solved | sub | Gamma pays Euler heads to `(log A)²`; every Haar piece except the first-prime coarse layer has uniform finite index [L]. |
| Π5 Dispersion / parity | Open | RH | Liouville twin count `2ψ(⌊√n⌋) − ψ(n)`; joint Möbius-moment / Mertens / sawtooth payment. |
| Π6 Depth visibility | Sharpened | — | Aperture positivity forces companions of comparable depth; a cluster of `≍ log t` zeros hides a depth-`δ` zero from heat at `κ ≍ δ²`; a window depth-mass bound on all windows is a zero-free strip [L]. |
| Π7 Amplifier rank | No-go (finite support); abstract law solved | — | No extra exponent at fixed total support; growing losses `e^{2kλ}` keep radius `Be^λ` [L]. |
| Π8 Census | Partially solved | sub / LH | `≥ 0.6725` simple critical, `≥ 4/5 − ε` critical ordinates [L]; right-half squared-depth moment `o(V)`, deep zeros `o(V)` [L]; bounded collision increments ⇒ density one; `ΔO = o(log T)` ⇒ off-line sparsity ⇒ Lindelöf (composition of [L] results). |
| Π9 Exceptional moduli | Partially solved | sub | Uniform zero-free region and Siegel for `q ≤ (log x)^A`; every inverse-log rate at one conductor-uniform horizon [L]; beyond open. |
| Π10 Logarithmic-saving barrier | Sharpened | sub | Individual estimates save every power of `log` for `q ≤ (log x)^A` [L]; in the complete Weil matrix the binding losses are the overlap powers, not the arithmetic rate. |
| Π11 Quasi-RH rung / quadratic RR | Solved (as equivalences) | ≥qRH; RH | Zero width `≤ σ` ⇔ sign-free section shortfall at rate `e^{2βr}` [L]; renormalized Hodge index ⇔ a nonnegative Serre-dual `h⁰` with quadratic RR lower bound and cofinal degree-zero subquadratic growth [L]. Construction open. |
| Π12 Local count layer | Sharpened | sub | Pointwise tangent-disc count forces bounded critical multiplicity, holds for density-one heights; `λ_t log t → 0` ⇔ zeros tend to the line [L]. Fibre multiplicity `H(γ) ≪ log|γ|/log log|γ| + E_γ(¼ log log|γ|)` with no prime cancellation [L]; `E_γ = o(log|γ|)` would give multiplicity `o(log|γ|)`. |
| Π13 Gap-dependent detection scale | Sharpened | sub | Readings accurate to `< 1/8` for `n ≥ 6`; source-intrinsic stopping certificate sound and eventually complete with no simplicity assumption [L]; the admissible stage `thetaWindowScale T` depends on divisor separation and strip margins; first stabilized prefix unbounded in height; boundary ingress mandatory [L]. |
| Π14 Window uniformity | Sharpened | RH | Finitely many primes are exact on every window: primes `≤ e^{2L+8}` reproduce `ratCorr` on log-height `≤ L`, and the window supremum is `κ_ζ + 1` [L]. A two-prime test lattice carries the full `κ` [L]. The Π problem is uniformity over windows: square-root control of the coupled prime windows at every height. |

## Γ — selection

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Trivial gauge point | Open | RH | `Θ ≥ ½`, Haar-a.e. `½`; RH ⇔ trivial point typical [L]. |
| Γ2 Twin resolution | Solved for all prime-set flips | — | Pole-index window: ζ `0`, Liouville `1`; glued test index `∞` for every nonempty finite flip; edge of every single prime flip eventually bounded while the tilted edge of ζ `→ ∞` [L]. Atomic Hodge index alone separates iff greatest gap `< 2 log 2`; the fixed ordinary and two-adic margin tests together select exactly the trivial prime pattern, without density assumptions (RIT `primeSetFlip_two_margins_iff_trivial`) [L]. |
| Γ3 Twin-blindness of soft structure | No-go (complete) | — | Krein index invariant under unitary twists; pointwise-closed weight classes contain every unitary twist [L]. |
| Γ4 Hecke invariance / Frobenius at infinity | Open | RH | RH ⇔ collided form Hecke-invariant ⇔ `W = D` [L]; collided side exact from theta data [L]; RH ⇔ dyadic Hecke defects subexponential, a bound at one large dyadic scale suffices [L]. Missing: an arithmetic correspondence acting as conjugation on the divisor. |
| Γ5 Source identification | Partially solved | RH | Integer counting + full-cone positivity ⇒ `λ = Λ` and RH [L]. |
| Γ6 Boundary sign / coherence | Solved | — | Pole boundary sign separates ζ from size-equivalent twins. |
| Γ7 Affine carrier with Weil dilation | Solved | — | Finite-index carriers with Weil dilation and visible successor exist via gluing at a place; subgroup successors with continuous dilation force `κ = ∞` except the PD endpoints [L]. |
| Γ8 Poisson rigidity | Sharpened | RH | Positive tent-self-dual measures with gap are Dirac combs; zero-side positivity = RH [S]. |
| Γ9 Archimedean continuity vs height decay | Solved (no-go) | — | Continuous dilation reading against denominator-decaying finite-adelic reading ⇒ `κ = ∞` [L]. |
| Γ10 Function-field indistinguishability | Sharpened | — | Conformality and the local index wall are identical over `𝔽_q(X)` [L]; ℤ differs by density of the extremal-weight exponents and by an unbounded edge (curve edge `≤ 2g`, ℤ edge `→ ∞`) [L/S]. |
| Γ11 Pole-blindness of the glued state | Solved (no-go) | — | Simple pole absorbed; double pole costs a square; the glue absorbs exactly its own pair [L]. |
| Γ12 Maximal-margin twins | Partially solved | sub | Prime-set class closed: every actual gap is bounded by every finite-cutoff gap (ACP `primeSetGreatestGap_le_every_cutoff`); the fixed ordinary and two-adic tests select the trivial pattern among all prime-set flips [L]. Remaining: general gauges with `S_N/H_N → 1`. |
| Γ13 Source-uniform extinction | No-go | — | Optical flux `−16(Re s−½)Im s·M₊M₋` cannot force extinction (fails at `3/4 + i`) [L]. |
| Γ14 Local counterterm selection | No-go | — | For every finite `S`, diagonal counterterms give `Λ` and a prime-flip twin glued index `1` while one global index is `∞` [S]. Selection cannot be produced by local renormalization. |

## Bridges

| Bridge | Anchor |
|---|---|
| `κ(K_ζ)` = right zeros = Hodge defect = one-sided count defect = band poles of `Λ(s)/Λ(s+1)` | HKT, RIT, ACS, ACP [L] |
| `κ(φ_c) = κ_ζ + 1` at every place = multiplicative reading `κ_ζ` + additive reading `1`; odd or `∞` | AKG [L]; STruncated [S] |
| Boost hyperplane = `v₁^⊥` = Markov hyperplane = harmonic hyperplane | RIT, SMAP, SSHA, CACT [L] |
| Edge `e_φ(N)` ↔ threshold `h(w)` of the width-`w` atom: `W_{φ,c,N}` PSD ⇔ `N < h(atom_{c/N})`; `sup_N d_f(N)` = right zeros seen by `f` | EHT [L/S] |
| `κ(φ_c^{(t)}) − 1` = Hodge defect of `K_t` = `N(t)/2` = future collision pairs | AKG, RIT [L] |
| Collision charge = theta-prefix Zhukovsky winding = Wiener–Hopf Fredholm index at the stopping prefix | CDG [L] |
| `κ < ∞` ⇔ bounded `N(t)` ⇔ `sup_T O(T) < ∞` ⇒ Lindelöf + half-plane; `κ(K_ζ⊠K_ζ) < ∞` ⇒ RH | HKT, AOG, RIT [L] |
| `ΔO` bounded ⇒ density one; `ΔO = o(log T)` ⇒ off-line sparse ⇔ Lindelöf | CDG, RHTower [L] |
| Fibre multiplicity ≤ prime polynomial + Hecke defect at every scale `1 ≤ L ≤ 4 log|γ|`; `ΔO ≤ 2·max H·n_off` | CDG [L] |
| `κ_ζ + 1` = glued index of the coupled two-prime assembly = supremum of finite-prime window Grams; zero information = inter-tower coupling | AKG [L] |
| Prime mode `×√(p−1)/p` = centered divisibility indicator; dilation jump = incidence event | CSAR [L] |
| Global pole = extremal weight of the product of local poles = archimedean pole on `S`-units | RIT [L] |
| `W = D` ⇔ RH; Hecke defect = symmetric second difference of `D`; dyadic amplification | AP, CDG, RBG [L] |
| Renormalized Hodge index ⇔ quadratic RR (Serre-dual `h⁰`) on the scaling surface | RIT [L] |
| Ground energy `E₁(c) ≍` Fourier tail `τ(c)`; sinc RH threshold at `τ(c) log N ≈ 1` | RAPT, TM [L] |
| Section shortfall rate = zero width = Birman–Schwinger / lag / deficit / band / damping rates | SPTL, ACCE, SSIC [L] |

## Status counts

| Family | Solved | Partially solved | Sharpened | Open | No-go | Classified |
|---|---|---|---|---|---|---|
| Σ | 4 (Σ1e, Σ1f, Σ9, Σ10) | 4 (Σ1b, Σ1g, Σ4, Σ7) | 11 (Σ1, Σ1c, Σ1d, Σ5, Σ8, Σ12, Σ13, Σ14, Σ16, Σ17, Σ20) | 3 (Σ1h, Σ3, Σ6) | 3 (Σ1a, Σ15, Σ19) | 3 (Σ2, Σ11, Σ18) |
| Π | 2 (Π1, Π11) | 4 (Π3, Π4, Π8, Π9) | 5 (Π6, Π10, Π12, Π13, Π14) | 2 (Π2, Π5) | 1 (Π7) | — |
| Γ | 5 (Γ2, Γ6, Γ7, Γ9, Γ11) | 2 (Γ5, Γ12) | 2 (Γ8, Γ10) | 2 (Γ1, Γ4) | 3 (Γ3, Γ13, Γ14) | — |
