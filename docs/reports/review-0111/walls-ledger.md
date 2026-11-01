# Walls ledger — status quo

Three wall families block every route: **Σ** the critical sign, **Π** square-root precision, **Γ**
selection of ζ. All three read one even integer, `κ = κ(K_ζ) = #` distinct zeros right of the
critical line, on one hyperplane, the pole-orthogonal hyperplane `v₁^⊥` (= boost = Markov =
harmonic hyperplane). Their present shape:

- **Σ** is the sign of the complete Weil form on `v₁^⊥` along the overlap flow `c ↦ W_{c,N}`.
  Positivity holds for `c ≤ (log N)^{1/19}`, where the universal method meets its residual ceiling.
  Confinement fails above `(log N)^{1/16}` because the shells are paid apart from the pole. From
  `(log N)^{¼}` on, positivity is RH. A finite edge is a zero mode of a PSD form.
- **Π** is the precision of two prime statistics. The one-point statistic is the smoothed prime
  error in multiplicative windows; it equals Weil's kernel and the inter-tower coupling. The
  conjugate-diagonal statistic is the Hecke defect, a non-holomorphic depth functional. Counts and
  the linear explicit formula cannot bound it.
- **Γ** is closed for every prime-set flip. What remains is Frobenius at infinity, the identity of
  the reflection pairing `ρ ↔ 1 − ρ` with the conjugation pairing `ρ ↔ ρ̄`, which is RH. Every
  selector in the corpus is a margin or index statement on a partial form, never a positivity
  producer for the complete form.

Status: **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, with its exact
form a theorem), **Open**, **No-go** (the mechanism is refuted), **Classified** (answered by a
classification theorem). Strength: **RH**, **≥qRH** (implies a zero-free half-plane and Lindelöf),
**LH** (implies Lindelöf), **sub**. Evidence: `[L]` Lean source read (statement or module docstring); `[M]` frontier
map or killed-routes entry, Lean not re-read; `[D]` derived here from `[L]`, not formalized.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Complete Weil positivity on an RH-complete schedule | Sharpened | RH | Universal regime: tilted spline, all vectors, `1 ≤ c ≤ (log N)^α`, every `α < 1/19`, floor `κ/(2c⁷)`, reserve `(b/c²³)D_N` [L]. RH regime: tilted full space `α > ¼`, `v₁^⊥` `α > ½`; unitBump (every `C^∞` nonnegative profile) on `v₁^⊥` at every `α > 0`; every `C²` profile at `β > ¼`; sinc at `≍ L(log L)²` [L/M]. Every `C²` profile without real Fourier zeros is positive at every fixed overlap [L]. No transfer between the universal-regime profile and the `C^∞` receivers. |
| Σ1a Defect-only confinement | No-go | — | Subexponential defect-only capture fails (`Q < 2^k` witnesses) [M]. |
| Σ1b Edge and Haar payment | Partially solved | sub | Prime–pole cancellation on fixed packets and on growing packets up to `exp(√log Y/23040000)` with remainder `exp(−√log Y/7680000)` [M]; growing Euler head alone unbounded [M]. Open: joint non-arithmetic Gamma graph + signed diagonal + roots + poles. |
| Σ1c Confinement | Sharpened | sub (universal); RH (RH-complete) | Explicit quadratic confinement and reverse gap [M]. Nonpositive unit vectors have `D_N ≤ (C/a)c¹⁶` for `N ≥ Hc⁸` and lie within `η` of a conductor sector with `log P ≍ c¹⁶/η` [L]. The exponent `16` is intrinsic to paying the shells apart from the pole [L]. Below `√N` only for `α < 1/16`. |
| Σ1d Floor–completeness tradeoff | Sharpened | — | `E₁(c) ≍ τ(c)`; tilted floor `c⁻⁷`; `C^∞` profiles RH on `v₁^⊥` at every power of `log N`; sinc RH-complete where `τ(c) log N ≈ 1`; Denjoy–Carleman classes `> 1` decide at `(log log N)^α`, `α > 1`; compact Gevrey `≤ 1` impossible [L/M]. |
| Σ1e Conductor averages at RH-complete overlap | Solved | — | `θ < ½`, `c²/log N → 0`: summed residual `o(Σ E_m²)`, nonpositive fraction `→ 0`, nonpositive dimension `o(N^θ)` [M]. |
| Σ1f Low-conductor block / ground state | Solved in the universal regime | — | All vectors to `(log N)^{1/19}` [L]; fixed `c` gap `E₁ + g/2` on `v₁^⊥` [M]. Beyond: Σ13. |
| Σ1g Exceptional conductors | Partially solved | sub | Single modes `(log N)^A ≤ m ≤ N^θ` coercive, exceptional set empty, every `C²` profile [L]. Spans of low conductors `m < (log N)^A` open. |
| Σ1h Square-root conductor barrier | Open | sub | Frames and residual averages need `m² ≤ N` [M]; above, Elliott–Halberstam-type input. |
| Σ2 Extension / carrier | Classified | — | Escape, mixing, height decay ⇒ `κ ∈ {0, ∞}`; finite-index carriers with translation reading `1_H` and continuous dilation exist iff `H ∈ {{0}, ℚ}`; finite-index Haar kernels split `p + ψ∘slope + Q` [M]. |
| Σ3 Markov criticality / odd sector | Open | RH | RH ⇔ `R ≤ ½` on odd vectors [M]. |
| Σ4 Rank and degree uniformity | Partially solved | RH | Rank 7 strict, rank 8 PSD [M]; fixed Jensen degree eventually hyperbolic [M]; PF₃₇ at the centre [L]; RH ⇒ simple roots in reversed Xi Jensen sections [L]. |
| Σ5 Finite index / heat count | Sharpened | ≥qRH (`K_ζ`); RH (`K_ζ⊠K_ζ`) | `κ < ∞` ⇔ bounded `N(t)` ⇔ bounded `O(T)` ⇒ Lindelöf + half-plane [L/M]; no softening at any resolution [L]. |
| Σ6 Realization | Open | RH | Lossless realization needs infinitely many resonances; normal real-zero approximants force RH (Vitali) [M]. |
| Σ7 Explicit image / resolvent orientation | Partially solved | RH in strip | Depth identity `σ > 1`; theta–prime expression at `s = 4` [M]. |
| Σ8 Collision quantum | Sharpened | RH | `O ∈ 2ℕ`; RH ⇔ `O < 2` per window; Fredholm index = charge; stopping certificate sound and eventually complete [M]; every horizon defect `≤ sup O`, all `O ≤ 1` ⇒ RH [L]. |
| Σ9 Local signatures | Solved | — | Pole–successor `κ = κ₀ + 1` at every place; finite sieve partitions have one positive direction [M/L]. |
| Σ10 Gluing at a place | Solved | — | `κ(φ_c) = κ + 1` at `∞` and every prime [L]; readings add; dilation form + shell squares on `ℓ = 0` [M]. |
| Σ11 Product-formula gluing of the global pole | Classified | — | Sum of local poles: `|S|` squares; tensor: `2^{|S|−1}`; renormalized infinite product: `∞`; extremal weight = archimedean pole on `S`-units [M]. |
| Σ12 Running counterterm | Sharpened | RH | At strict separation `log N − γ` cancels the prime diagonal exactly through `Λ ∗ 1 = log`, leaving `R(M) → 0` and `δ_N ∈ [0, log 2]` [L]; no fixed counterterm makes the prime kernel Pontryagin [M]. |
| Σ13 Residual-versus-floor barrier | Sharpened (binding) | sub | The universal regime ends at `1/19`: residual `c⁵/log N` per low mode against floor² `c⁻¹⁴` [L]. A signed low-band estimate is required to pass it. |
| Σ14 Detection edge | Sharpened | RH | RH ⇔ no edge; ¬RH ⇒ edge `≤ 2(log N)^β` i.o. (`β > ¼`); a finite first edge is PSD with a zero mode; no edge ⇔ bounded coupling [L]. Under ¬RH the tilted edge lies in `[(log N)^{1/19}, 2(log N)^{¼+}]` i.o. [D]. Aperture visibility law for an isolated pair: `S_δ(a) > L` [L]. Atomic edge dictionary open. Unconditional positivity cannot cross the edge. |
| Σ15 Tensor amplification | No-go | — | `K_ζ^n` PD ⇔ RH; `n₋(G⊗G) = 2n₊n₋` at every horizon [L/M]. |
| Σ16 Heat homotopy of the glued state | Sharpened | RH | `κ(φ_c^{(t)}) = N(t)/2 + 1`, antitone, `1` for `t ≥ 1/8`; RH ⇔ constant index [M]. |
| Σ17 Prime–pole coherence | Solved (as identity) | — | `B_Q² ≤ S_Q L_Q`, `S_Q = log Q + O(1)` sharp [M]; the prime form is jump squares minus an exact Mertens diagonal, the pole enters only through Mertens' constant and the counterterm, which cancel [L]; literal residual scale `(log Q)²` sharp [M]. |
| Σ18 Separable assemblies | Classified (no-go) | — | Separable assemblies annihilate the coupling, are zero-blind when truncated, overcount and diverge when untruncated [M]. |
| Σ19 Deformation to a positive model | No-go (as a free input) | — | Crossing-free path `A → I` ⇔ `A` PD [L]; axial→coupled homotopy has coupling form `t·L_aL_bK`: full index for `t > 0`, zero at `t = 0` [L]. |
| Σ20 Inter-tower coupling | Solved (as equivalence) | RH | Coupling ≤ 4·kernel, kernel deviation ≤ coupling/2 on dense lattices; RH ⇔ bounded coupling on `⟨p,q⟩×⟨r,s⟩` or on one `⟨p⟩×⟨q⟩`; rate = width; cone ⇒ RH or unattained width; finite stratum ⇒ RH [L]. Open: cone attainment (sub). |
| Σ21 Shell degree / joint shell–pole payment | Sharpened | sub (below `(log N)^{¼}`); RH (RH-complete) | At every overlap the complete form is `J_N + ½A_N +` bounded diagonal `− Σ d_n F² +` center/far/pole/near terms; `d_n` is the only overlap-growing non-square term [L]. Separate payment sharp at `c²/ε` [L]; joint top-band coefficient `O_φ(G(c + log N))` [L]. All-vector joint payment open. |
| Σ22 Zero modes of the overlap flow | Sharpened | RH | Positivity at small `c` [L] and edge = crossing [L] give: RH ⇔ `W_{c,N}` has no zero mode on `v₁^⊥` for any `c`, `N` [D]. Kernel rigidity available: successor + dyadic incidence energy has kernel the constant packet [M]. Link between a zero mode and the incidence kernel open. |

## Π — square-root precision

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1 Global law | Solved (as equivalence) | RH | `ψ(x) − x ≤ C√x log²x` ⇔ RH ⇔ `κ = 0` [M]. |
| Π2 Deciding input | Open | RH | No unconditional source input at square-root precision. |
| Π3 Producer cost | Partially solved | sub / RH | Ceilings `2 log 2`, `1 + 1/((P+1)(P+2))`, `31/30`, `exp(−0.87n)`; growing-alphabet producers reach `ψ ≤ (1+ε)x + C_ε log²x` [M]. Open: `ε`-uniform error. |
| Π4 Gamma reach | Partially solved | sub | Gamma pays Euler heads to `(log A)²`; every Haar piece except the first-prime coarse layer has uniform finite index [M]. |
| Π5 Dispersion / parity | Open | RH | Liouville twin count `2ψ(⌊√n⌋) − ψ(n)`; joint Möbius-moment / Mertens / sawtooth payment [M]. |
| Π6 Depth visibility | Sharpened | — | Isolated pair at depth `δ`, height `ξ`, RVM background: visible at aperture `a` iff `sinh(2δa)/(2δ) − a > (1/2π)log(ξ/2π)`; archimedean domination is blind at every depth [L]; clusters hide depth from heat [M]; an all-window depth-mass bound is a zero-free strip [M]. |
| Π7 Amplifier rank | No-go (finite support) | — | Growing losses `e^{2kλ}` keep radius `Be^λ` [M]. |
| Π8 Census | Partially solved | sub / LH | `≥ 0.6725` simple critical [M]; right-half squared-depth moment `o(V)` [M]; bounded `ΔO` ⇒ density one [M]. |
| Π9 Exceptional moduli | Partially solved | sub | Uniform zero-free region and Siegel for `q ≤ (log x)^A`; every inverse-log rate at one conductor-uniform horizon [M]. |
| Π10 Logarithmic-saving barrier | Sharpened | sub | Individual estimates save every power of `log` for `q ≤ (log x)^A` [M]; in the complete Weil matrix the binding losses are overlap powers (Σ13, Σ1c). |
| Π11 Quasi-RH rung / quadratic RR | Solved (as equivalences) | ≥qRH; RH | Zero width `≤ σ` ⇔ section shortfall at rate `e^{2βr}`; renormalized Hodge index ⇔ Serre-dual `h⁰` with quadratic RR [M]. Construction open. |
| Π12 Local count layer | Sharpened | sub | Local count ⇒ bounded critical multiplicity, true for density-one heights; `H(γ) ≪ log|γ|/log log|γ| + E_γ(¼ log log|γ|)` [L]. |
| Π13 Gap-dependent detection scale | Sharpened | sub | Stopping certificate sound, eventually complete; admissible stage depends on divisor separation; first stabilized prefix unbounded in height [M]. |
| Π14 Window precision (kernel = coupling) | Sharpened (equivalence) | RH | Primes `≤ e^{2L+8}` are exact on log-height `≤ L` [M]. Weil's kernel is the smoothed prime error in fixed-length multiplicative windows [D]; the coupling equals the kernel up to absolute constants [L]. Square-root control of these windows at every height is RH. |
| Π15 Conjugate diagonal (Hecke defect) | Sharpened | sub → RH | `E_γ(L) = Σ_ρ w_ρ(2cosh(2δ_ρL) − 2)` is non-holomorphic in `ρ`. At log scale the prime polynomial carries `O(1/log T)` of it; counts + linear explicit formula cannot bound it; fixed-`c` bound ⇔ corridor (≥qRH); one constant at all dyadic scales ⇔ RH; doubly-log scale ⇒ multiplicity `o(log|γ|)` (sub) [L]. No arithmetic access identified. |
| Π16 Frequency localization of cancellation | Sharpened | ≥qRH (3/4 strip); RH | Every positive-power band of the Chebyshev cyclotomic remainder retains the full infimal exponent `2Θ` [L]; band bound `O(N^{r+ε})` ⇔ `2Θ ≤ r` [M]. Localization alone saves nothing. |

## Γ — selection

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Trivial gauge point | Open | RH | `Θ ≥ ½`, Haar-a.e. `½`; RH ⇔ trivial point typical [M]. |
| Γ2 Twin resolution | Solved for all prime-set flips | — | Ordinary or two-adic atomic Hodge margin separates every nontrivial prime pattern, no density assumption [L]; diagonal coupling recovers any flip set; ζ and a `p`-flip never both have finite coupling index [L]; single-flip edges bounded [L]; Wirsing asymptotics, residue-class and zero-density twins [L]. |
| Γ3 Twin-blindness of soft structure | No-go (complete) | — | Krein index invariant under unitary twists; pointwise-closed classes contain every unitary twist [M]. |
| Γ4 Hecke invariance / Frobenius at infinity | Open | RH | `σ(ρ) = 1 − ρ̄` fixes exactly the line; trivial on ζ's zeros ⇔ RH; `κ = #` moved right zeros; RH ⇔ every Hecke translation is a similitude of the collided form [L]; RH ⇔ one constant for the dyadic Hecke defects [L]. Missing: an arithmetic correspondence acting as conjugation on the divisor. |
| Γ5 Source identification | Partially solved | RH | Integer counting + full-cone positivity ⇒ `λ = Λ` and RH [M]. |
| Γ6 Boundary sign / coherence | Solved | — | Pole boundary sign separates ζ from size-equivalent twins [M]. |
| Γ7 Affine carrier with Weil dilation | Solved | — | Finite-index carriers with Weil dilation and visible successor exist via gluing at a place [M]. |
| Γ8 Poisson rigidity | Sharpened | RH | Positive tent-self-dual measures with gap are Dirac combs; zero-side positivity = RH [M]. |
| Γ9 Archimedean continuity vs height decay | Solved (no-go) | — | Continuous dilation reading against decaying finite-adelic reading ⇒ `κ = ∞` [M]. |
| Γ10 Function-field indistinguishability | Sharpened | — | Local index walls identical over `𝔽_q(X)` [M]. ℤ differs by an unbounded edge (curve edge `≤ 2g`) [L] and by incommensurable towers: curve towers sample the antidiagonal exactly, two-prime log-lattices only densely [L]. |
| Γ11 Pole-blindness of the glued state | Solved (no-go) | — | Simple pole absorbed, double pole costs a square [M]. |
| Γ12 Maximal-margin twins / general gauges | Partially solved | sub | Prime-set class closed [L]; entrywise-nonnegative gauges of the coupled archimedean+prime kernel exist only on the archimedean characters `n^{iτ}` [L]; nonnegative twisted Selberg source forces `ω(p) = 1` for sign gauges [L]. Open: unimodular gauges with `S_N/H_N → 1`. |
| Γ13 Source-uniform extinction | No-go | — | Optical flux cannot force extinction (fails at `3/4 + i`) [M]. |
| Γ14 Local counterterm selection | No-go | — | Diagonal counterterms give `Λ` and a prime-flip twin glued index `1` on every finite assembly [M]. |
| Γ15 Functional-equation twins without Euler product | Open | sub | Davenport–Heilbronn-type combinations: no Lean statement in the corpus. |
| Γ16 Selection–sign gap | Sharpened | RH | Every selector (atomic pole index, two-adic probe, Metzler gauge, twisted Selberg source, coupling diagonal, finite-flip edge) is a margin, sign or index statement on a partial form [L]; none yields complete-form positivity for ζ. Transfer of a selective sign to the complete form at growing overlap is open. |

## Bridges

| Bridge | Anchor |
|---|---|
| `κ(K_ζ)` = right zeros = Hodge defect = band poles of `Λ(s)/Λ(s+1)` = zeros moved by `σ(ρ) = 1 − ρ̄` | HKT, RIT [M]; EHT `FrobeniusAtInfinity` [L] |
| `κ(φ_c) = κ + 1` at every place; odd or `∞` | AKG [L] |
| boost hyperplane = `v₁^⊥` = Markov = harmonic hyperplane | RIT, SMAP, SSHA [M] |
| bounded `K_ζ` ⇔ bounded coupling ⇔ no edge ⇔ RH; coupling rate = zero width | RIT, ACPL [L] |
| complete form on packets = jump squares + affine incidence squares + bounded diagonal − shell degree + boundary terms | ACPL [L] |
| edge `e_φ(N)` ↔ threshold `h(w)`; at a finite edge the form is PSD with a zero mode | EHT [L] |
| `κ(φ_c^{(t)}) − 1 = N(t)/2` = future collision pairs | AKG, RIT [M] |
| collision charge = Fredholm index; every horizon defect `≤ sup O` | CDG [M]; EHT [L] |
| bounded `N(t)` ⇔ bounded `O(T)`; `N(t) ≤ 2O(R(0))` under a moving barrier | CDG [L] |
| `H(γ) ≤` prime polynomial + Hecke defect; prime polynomial self-absorbed at log scale | CDG [L] |
| fixed-scale Hecke bound ⇔ log corridor; dyadic-uniform ⇔ RH | CDG [L] |
| Hecke similitude of the collided form ⇔ Frobenius at infinity ⇔ RH | EHT, PL [L] |
| renormalized Hodge index ⇔ quadratic RR on the scaling surface | RIT [M] |
| ground energy `E₁(c) ≍ τ(c)`; sinc RH threshold at `τ(c) log N ≈ 1` | RAPT, TM, EHT [M/L] |
| curve: bounded tower coupling ⇔ unitary ⇔ Castelnuovo–Severi on the Frobenius span | ACPL [L] |

## Status counts

| Family | Solved | Partially solved | Sharpened | Open | No-go | Classified |
|---|---|---|---|---|---|---|
| Σ (30) | 6 (Σ1e, Σ1f, Σ9, Σ10, Σ17, Σ20) | 4 (Σ1b, Σ1g, Σ4, Σ7) | 11 (Σ1, Σ1c, Σ1d, Σ5, Σ8, Σ12, Σ13, Σ14, Σ16, Σ21, Σ22) | 3 (Σ1h, Σ3, Σ6) | 3 (Σ1a, Σ15, Σ19) | 3 (Σ2, Σ11, Σ18) |
| Π (16) | 2 (Π1, Π11) | 4 (Π3, Π4, Π8, Π9) | 7 (Π6, Π10, Π12, Π13, Π14, Π15, Π16) | 2 (Π2, Π5) | 1 (Π7) | — |
| Γ (16) | 5 (Γ2, Γ6, Γ7, Γ9, Γ11) | 2 (Γ5, Γ12) | 3 (Γ8, Γ10, Γ16) | 3 (Γ1, Γ4, Γ15) | 3 (Γ3, Γ13, Γ14) | — |
