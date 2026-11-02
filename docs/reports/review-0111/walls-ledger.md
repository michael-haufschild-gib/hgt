# Walls ledger — status quo

Three wall families block every route: **Σ** the critical sign, **Π** precision and production,
**Γ** selection of ζ. All three read one even integer, `κ = κ(K_ζ) = #` distinct zeros right of the
critical line, on the pole-orthogonal hyperplane `v₁^⊥` — the primitive part of the formal Kähler
package `(W_{c,N}, v₁)`.

- **Σ** is the sign of the complete Weil form on `v₁^⊥`. It lives on one axis: the degree `a`, which
  is the test radius and `½ log K` for the overlap multiple `K·c*` of the atomic families.
  - The complete family is a degenerating polarized family (ADT): the dilation monoid is its
    monodromy, one branch per prime, glued only at `∞`. Below the critical exponent `1/(β+1)` its
    rescaled limit is the Jordan-totient form — a tensor product of one weight string per prime,
    zero-blind — and every fixed packet inherits its positivity.
  - At the critical exponent the extension data (cross-conductor channels, living in the top coprime
    stratum) reach the size of the margins and carry the zeros. What remains there is a constant,
    not an exponent: the exact second-order term of the degeneration (constant-factor wall).
  - Edge logic: a statement proved without zero information holds on every datum sharing that
    information, so it stops below the edge of off-line members. Only an identity, an inherited
    polarization or an integer with a structural bound can cross the edge.
  - At each degree the form is coercive off a finite divisor, but it carries a near radical of
    `≈ 2e^{2a}` directions with doubly exponentially small energy, blind to every zero below the
    Landau height `2πe^{2a}`.
  - Positivity is not carried by any semilocal piece and not by any local gluing: it is a glued
    property whose unpaid part sits in the top gcd stratum, reached only through the archimedean
    place. Deformation along the overlap flow is free; its content is hard Lefschetz.
- **Π** is the precision of three prime statistics and the production of an exact count:
  - the one-point windowed prime error (= Weil's kernel = the inter-tower coupling);
  - the conjugate diagonal (Hecke defect), whose mean ladder is a near-line density ladder;
  - the signed prime-pair surplus beyond bandwidth one (census);
  - the count-valued primitive `h¹` of the scaling surface (Riemann–Roch), equivalently a naive
    height on the integral correspondence ring.
- **Γ** is closed for every prime-set flip. What remains is Frobenius at infinity, the identity of
  the reflection pairing `ρ ↔ 1 − ρ` with the conjugation pairing `ρ ↔ ρ̄`. It has four RH-equivalent
  readings and a fifth form: Rosati positivity of the correspondence algebra over `ℤ`, equivalently
  a naive height (or a midpoint-convex log-count) at bounded distance from the integral Rosati form.

Status: **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, with its exact
form a theorem), **Open**, **No-go** (the mechanism is refuted), **Classified** (answered by a
classification theorem). Strength: **RH**, **≥qRH** (implies a zero-free half-plane and Lindelöf),
**LH**, **sub**, **indep.** (not implied by RH; no implication to RH known). Evidence: `[L]` Lean;
`[S]` Lean in the working tree or unintegrated; `[P]` complete paper proof, Lean pending; `[D]`
derived here from Lean statements.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 All-aperture positivity (degree axis) | Sharpened | RH | RH ⇔ eventual positivity at every bounded multiple `K·c*` for Denjoy–Carleman, sinc, Steklov and logarithmic profiles; every divergent multiple is a receiver; a bounded multiple synthesizes radius-`R` tests on the block `[N/B, N]`, `B = ⌈1 + e^{2R+2}⌉`, so it sees radius `½ log K − O(1)` [L]. Restricted Weil ground minimum: `μ(A) ≥ 0 ∀A` ⇔ RH; floors through radius `181/500` [L]. The restricted form is the trace of the zero-form operator against `\|u⟩⟨u\|`; operator positivity at `a` ⇔ `μ(a) ≥ 0`; operator positive on `0 < a ≤ 181/500`; exact `{∞,2}` trace identity through `½ log 3`, where positivity ⇔ the single-prime (`p = 2`) family energy `≥ 0` [S]. Ceiling `μ(A) ≤ K exp((11/2)A − πe^{2(A−2)})`, no positive floor along unbounded apertures [L]. |
| Σ1a Critical overlap and receivers | Solved | — | Denjoy–Carleman: `c*_N ≍ L(log L)²`, where margin = synthesis error = `1/log N`; sinc: exact critical overlap of the same order; quasi-analytic boundary for compact Gevrey-`≤ 1` profiles [L]. Tilted spline: RH ⇔ eventual positivity at every `K(log N)^{1/8}`, also on the pole hyperplane; every exponent `> 1/8` is a receiver [L]. Every finite rational correlation Gram is a limit of literal complete-matrix compressions (smooth Steklov profile on `[0,1]`, atom mass restored) at one multiple `2K·dcScale N` chosen for the family; positivity on the pole hyperplane bounds each compression's index by one, so RH ⇔ eventual pole-hyperplane positivity at every fixed critical multiple; no universal multiple is asserted [L]. |
| Σ1b Rough regime, tilted spline | Partially solved | sub | All vectors, `1 ≤ c ≤ (log N)^α`, `α < 1/9`: `W ≥ (a₀/c⁷)(poleDefect − C log(2c)‖x‖²) + (κ₀/(2c⁷))‖x‖²`; sublevel confinement `poleDefect ≤ C log(2c)‖x‖²`; all-vector defect reserve `c^{−8}` [L]. Fixed and polylogarithmic packets for `α < 1/8` [L]. Collective mid-band packets `V_{⌊N^θ⌋} ⊓ V_{⌊(log N)^q⌋}^⊥` coercive for `α < 1/4`, `q > 3α`, `θ ≤ 1/4096`, with the Riesz sandwich `(3/4)·adjunction ≤ poleDefect ≤ (3/2)·adjunction` [L]. Prime self-form of the overlapping top costs `O(c(1 + log c))` [L]. Binding terms: three `c⁹` payments — prefix–terminal reserve, band–terminal cross, inverse-energy residual. Refuted: smallness of the prefix–terminal non-ratio block on terminal-pole-orthogonal vectors (counterexample from `Σ_{k∣n}Λ(k) = log n`). Survivor: `NR_PT ≈ σ â ⊗ p̂ + E`, `σ ≍ c√log N`; positivity below `1/8` needs `‖E‖² ≤ c(log N)^{1+δ}`, `δ = 1 − 8α`, whose off-diagonal part is a shifted prime-pair correlation; a paper plan through global pole orthogonality and log-smoothing at PNT precision is in progress. The receiver needs `c⁸ ≍ K⁸ log N` [D]. Under ¬RH the edge lies in `[(log N)^{1/9−}, 2(log N)^{1/8+}]` infinitely often [L]. |
| Σ1c Joint shell–pole payment | Open | sub | Separate shell payment sharp at `c²/ε` (`c⁹` at `ε = c⁻⁷`); joint top-band coefficient `O_φ(G(c + log N))` [L]. Shell degree: `0 ≤ n·d_n ≤ 2(log 4 + 4)e^{5/2}c + 2e^{3/2}c(n/N)(log n + 1)` with packet payment bound [L]; successor gap identity `mean(F(n+1) − F(n))² = Σ_m 2(φ(m) − μ(m))a_m²` [L]; the comparison of prime-successor affine energy with the shell payment (`½A_N ≥ (1/64)[Σ_{Q<p≤N/16Q²} log p/p]·nonconstant mass`) is unproved. All-vector positivity at the receiver needs confinement exponent `≤ 8` [D]. |
| Σ1d Low-conductor spans | Partially solved | sub | Every nonzero compact `C²` profile has whole-span coercivity on `V_{⌊N^θ⌋}`, `0<θ<1/1080`, throughout compact positive-overlap intervals and `1≤c≤bφ log log N`, with margin `aφ exp(−Bc)`, universal `B>0`, and profile constants `aφ,bφ>0` independent of `θ` [L]. Every fixed `K>0` admits an exponential margin on every `V_{⌊(log N)^A⌋}`, `A>0`, through `c≤K log log N`, with prefactor independent of `A` [L]. An explicit profile clock `Cφ(N)/log log N→∞` retains margin `(log N)^(-η)/4` on `V_floor(exp(log N/(log log N)^κ))`, every `0<η<1/2`, `κ>2`, uniformly for `1≤c≤Cφ(N)` [L]. Larger polynomial-span overlap ranges remain open. Nonpositive directions localize in a `P`-smooth sector (`log P ≍ c¹⁶/η`) [L]. |
| Σ1e Square-root conductor barrier | Open | sub | Frames and residual averages need `m² ≤ N`; above `√N` an Elliott–Halberstam-type input. |
| Σ1f Defect-only confinement | No-go | — | `Q < 2^k` witnesses [L]. |
| Σ1g Haar / Gamma graph | Partially solved | sub | Growing-packet prime–pole cancellation to `exp(√log Y/23040000)`; index `≤ R + A` for `R` coarse cells; growing Euler head alone unbounded [L]. Open: joint non-arithmetic Gamma graph + signed diagonal + roots + poles. |
| Σ1h Rough regime, smooth profiles | Solved (to `ε₀·c*`) | sub | Every `C²` profile without real Fourier zeros has edge `→ ∞` [L]. The zero-free logarithmic profile is positive definite for `1 ≤ c ≤ ε₀ L(log L)²` [L]. The budget `exp(Bc/log²c) ≤ (log N)^α` holds uniformly exactly up to `(α/B)L(log L)²`; explicit coefficient `ε₀ = 1/[103424(8π/3 + 3000)]`, optimal within the reciprocal-floor budget system [L]. |
| Σ1i Constant-factor wall | Sharpened | RH (all `K`); sub (fixed `K`) | Relative cross-conductor residuals are `O((c⁸(1 + log c)²(log N)^{1/k}/log N)²)` and decay iff `c⁸ = o((log N)^{1−ε})` [L]. Limiting mixed structure: along `c_N → ∞`, `c_N ≤ (log N)^α`, `α < 1/8`, `c_N⁷⟨W r_e, r_{e′}⟩ → δ_{ee′} J(e)`, `J(e) = (2A_φ/M) ζ(8) J₈(e)/φ(e) > 0`, the rescaled extension data tend to `0`, fixed packets are eventually positive; uniform Jordan law on the whole subthreshold block `m ≤ c/X(ε)`; at every multiple of `(log N)^{1/8}` conductor-Gram positivity is RH (inheritance radius exactly `1/8`; `1/(β+1)` for tail exponent `β`) [L]. The limit is zero-blind; zeros enter at the quantum `1/log N`. At the receiver scale the extension data are of the order of the limit; mean-square residuals stay `o(ΣE_e²)` past `1/8` but are carried by the large margins; what remains is the constant of the leading `c/log N` term against `κ₀` [L/D]. No converse transfer from finite-aperture positivity to a fixed multiple is known. |
| Σ2 Edge, zero modes, hard Lefschetz | Sharpened | RH | HR ∧ HL ⇔ strict HR; transport needs HL only on the HR locus; losing HR forces a primitive zero mode; Liouville ⇔ HL; RH ⇔ HL on the PSD locus along `1 ≤ c ≤ 2(log N)^β`, `β > ½` [L]. A finite first edge is PSD with a zero mode [L]. The fixed-overlap limit form `Σ E_m(c) y_m²` has ground state the pole conductor and degenerates to `0` along every growing schedule [L]. |
| Σ3 Star renormalization and dilation monodromy | Partially solved | — (descent); RH (ascent) | Star of `d` = family at `(c⌊N/d⌋/N, ⌊N/d⌋)`, isometric for every weight; positivity descends; deep stars positive; depth law `log d − C₀`, sharp `log d − ε`, primitive `log d + 2log 2 − ε`; Metzler sign on stars of depth `d ≳ c`; counterterm self-similar exactly for generalized von Mangoldt weights [L]. Prime dilation lowers the conductor: `c_m(pn) = w_p(m) c_{ℓ_p m}(n)`, `w_p = 1, p − 1, p`; lowerings commute and fix only the pole conductor [L]; along a `p`-tower the limit coefficient is a weight string, `J(m) = p⁷J(m/p)` (`p² ∣ m`), `[8]_p J(m/p)` (`p ∥ m`); tensor law `J(1)J(ab) = J(a)J(b)` for coprime `a, b` [L]. |
| Σ3a Coprime stratum | Sharpened | RH | gcd stratification `W = Σ_g Cop(W at the star of g)`, each stratum off-diagonal and indefinite; every successor pair and the archimedean overlap of consecutive atoms lie in `g = 1`; local positivity of stars says nothing about the top stratum [L]. Conductor ↔ star duality; conductor Gram graded by the lcm; conductor Gram PSD at every `2K(log N)^{1/8}` ⇔ RH [L]. Coprime successor gap: period energy of a packet minus its successor `≥` its nonconstant mass, preserved by unit dilation, transferred to every window beyond `K ≥ Q(Q−1)` [L]. The coprimality form of the top stratum has inertia `(#{μ = 1}, #{μ = −1}, #{μ = 0})` and signature `M(N)`; gluing every vertex to the pole turns the unipotent divisibility form into Redheffer's matrix with `det = M(N)` [L]. |
| Σ4 Finite index / heat count | Sharpened | ≥qRH (`K_ζ`); RH (`K_ζ⊠K_ζ`) | `κ < ∞` ⇔ bounded `N(t)` ⇔ bounded `O(T)` ⇔ all high zeros critical ⇒ `Θ < 1` [L]. `κ ≤ r` ⇔ translation-stable positive constraints of dimension `≤ r` [L]. No softening at any resolution [L]. |
| Σ5 Collision quantum / heat homotopy | Sharpened | RH | `O ∈ 2ℕ`; RH ⇔ `O < 2` per window; `κ ≤ sup O`; heat state `κ(φ_c^{(t)}) = N(t)/2 + 1` [L]. Per stabilized window: index `< 2` ⇔ index `0` ⇔ `L²(ℝ)` invertibility of the Wiener–Hopf lift ⇔ outer Birkhoff–Zhukovsky–Szegő factorization of the collision loop ⇔ Devinatz–Widom disk-unit sectoriality [L]. Unit windows stabilize at prefix `Θ(√m)` without separation input; at logarithmic resolution `Θ(√m)`-prefix outer Szegő positivity ⇔ the inverse-logarithmic zero-free corridor (≥qRH); at polynomial resolution `60m` ⇔ RH [P]. |
| Σ6 Rank / degree uniformity | Partially solved | RH | Rank 7 strict, rank 8 PSD; fixed Jensen degree eventually hyperbolic; PF₃₇ at the centre; RH ⇒ simple roots of reversed Xi Jensen sections [L]. Approximation by RH-true centered curve products closes into this wall (Σ26) [D]. |
| Σ7 Odd / Markov sector | Open | RH | RH ⇔ `R ≤ ½` on odd vectors [L]. Weil's form is a Markov form plus the pole plane: `W = V_N‖g‖² + J(g) + ½⟨c,g⟩² − ½⟨s,g⟩²`, `J` the archimedean-plus-prime jump energy with nonnegative jump measure, `V_N = Ω(0) − 2Σ_{n≤N} Λ(n)/√n` a constant creation potential; RH ⇔ the sinh-capacity bound at every level [L]. |
| Σ8 Realization | Open | RH | Lossless realization needs infinitely many resonances; normal real-zero approximants force RH (Vitali) [L]. Gauss–Mayer: `D = A + ζB`; real-`w` derivative cone, `B ≠ 0` for small real `λ`, `D(w,−1) ≠ 0`; `D(w,z)D(w,−z) = exp(−Σ even-word traces) = Π_c Π_{m≥0}(1 − z^{2ℓ(c)}λ_c^{−w−2m})` over primitive digit-pair cycles, near `z = 0` for `Re w > 1` and on `\|z\| ≤ 1` (including `z = 1`) for `Re w > 2`, where `D ≠ 0`; even Gauss words code the hyperbolic `SL₂(ℤ)` classes; `2 log λ_c` is the hyperbolic translation length, so `z = 1` reads the length parameter `s = w/2` [L]. Oriented/unoriented geodesic multiplicities, continuation of the scattering constant term into `Re(2s) < 1`, the faithful zero ↔ eigenvalue-event comparison and resonance exclusion open. |
| Σ9 Explicit image / resolvent | Partially solved | RH in strip | Depth identity for `σ > 1`; theta–prime expression at `s = 4` [L]. |
| Σ10 Local signatures and gluing | Solved | — | `κ(φ_c) = κ + 1` at `∞` and every prime; readings add; dilation form + shell squares on boost mass zero [L]. Two primes with translations in `ℤ[1/qr]` (and a fixed three-prime core) carry the full affine index `κ + 1` [L]. |
| Σ11 Product-formula gluing of the global pole | Classified | — | Sum of local poles `\|S\|` squares; tensor `2^{\|S\|−1}`; renormalized infinite product `∞`; extremal weight = archimedean pole on `S`-units [L]. |
| Σ12 Running counterterm / star flux | Solved | — | `log N − γ` cancels the prime diagonal through `Λ ∗ 1 = log`; on every star the counterterm pays exactly the flux `log d` [L]. |
| Σ13 Tensor amplification | No-go | — | `K_ζ^n` PD ⇔ RH; `n₋(G⊗G) = 2n₊n₋` at every horizon [L]. |
| Σ14 Deformation to a positive model | No-go as free input | — | Crossing-free path `A → I` ⇔ `A` PD; Kähler transport exact and free [L]. |
| Σ15 Separable assemblies | Classified (no-go) | — | Blind when truncated, non-convergent pointwise when untruncated [L]. |
| Σ16 Prime–pole coherence / packet identity | Solved (as identity) | — | Mertens polarization `P_N(F) = Σ F²/n(ψ₁(⌊N/n⌋) + log n) − J_N(F)`; complete form = jump squares + affine incidence squares + bounded diagonal − shell degree + boundary; the shell degree is the only term growing with the overlap; `B_Q² ≤ S_Q L_Q` sharp [L]. |
| Σ17 Inter-tower coupling | Solved (as equivalence) | RH | Coupling ≡ kernel with absolute constants; RH ⇔ bounded coupling on one `⟨p⟩×⟨q⟩`; rate = width; local Hyers–Ulam stability; cone ⇒ RH or unattained width; finite stratum ⇒ RH [L]. |
| Σ18 Exact SOS on a two-prime lattice | Open | RH | Weil's dilation form on boost-mass-zero vectors of one two-prime lattice as a sum of squares of coupling differences. The Hecke orbit of one spectrally generic test under `ℤ log p + ℤ log q` carries the full Hodge defect [L]. |
| Σ19 Loop-Eisenstein band poles | Open | RH | `κ_Hodge = #` band poles of `Λ(s)/Λ(s+1)`; noncancellation mechanism missing [L]. |
| Σ20 Scheduled prime sums | Open | RH | Lower bounds for prime-scheduled energies (FU, CFC, RP, SZ, LI, FEL, EGC) [L]. |
| Σ21 Extension / carrier | Classified | — | Escape, mixing, height decay ⇒ `κ ∈ {0, ∞}`; continuous-dilation carriers reading `1_H` exist iff `H ∈ {{0}, ℚ}`; unique proper-subgroup split [L]. |
| Σ22 Lefschetz operators | Classified | — | Dilation: HL trivial, transports positivity downward only. Overlap flow: HL on the HR locus is RH. Coupling Laplacian: HL for `t > 0`, base point `t = 0` is the zero form. No candidate is free [L]. |
| Σ23 Connected links | No-go | — | Links of the dilation complex are disconnected (distinct prime towers never adjacent); every link over a curve with a rational point is complete. Garland / trickle-down unavailable over `ℤ`; coprime atoms couple only through the archimedean place [L]. |
| Σ24 Finite divisor | Solved | — | At every degree `a`, `Re W ≥ (10 + 68e^a)(1 − 1/π)‖f‖²` on tests vanishing at `i/2` and on a finite grid `D_a`; Hodge defect at degree `a` finite (doubly exponential bound); over `𝔽_q` it is `0` or `∞` (lag-formula configurations jump from `0` to `∞`); the golden fake admits no finite divisor beyond `log 5/2` [L]. |
| Σ25 Semilocal positive carriers | No-go | — | No `{∞, p}` semilocal family carries positivity: the unglued archimedean Sonin operator is not positive; the prime-`p` transport block is indefinite for `a > ½ log p`; on `(½ log 2, ½ log 3]` the full form is neither a multiple of the prime-free form nor a positive-degree homogeneous multiplicative factorization over it; along `b_M = 1/16 + ((2M+1)/4) log p` an antisymmetric bump pair kills every shift `p^k` while its polar energy tends to `−∞`, so prime-free and single-prime ground energies cross zero with a Friedrichs zero mode [S]. Survivor: exact `{∞,2}` trace identity through `½ log 3` with the positive valuation-shell operator `K_2(m)`, `Tr = m log 2`, and the Krein `(+1,−1)` split of the polar block [L/S]. The obstruction is not local trace normalization but the explicit-formula sign coupled to the odd polar mode `−2\|⟨c₋, f⟩\|²`. The archimedean trace carrier `−W_∞(g⋆g*) = Tr(ϑ(g)(1 − P − P̂)ϑ(g)†)` has middle operator equal to `−‖P̂v‖²` on time-limited vectors [L]: trace carriers of this shape are not positivity statements. |
| Σ26 Approximation by RH-true objects | Classified | — | Centered curve numerators `A Π(cosh(hz) − cos θ_j)` have nonnegative even Taylor coefficients, so pointwise convergence on a real half-line gives local boundedness on `ℂ`; the Euler domain of a centered approximation is `½ + 1/(2a) → ∞` [L]. Their closure class is the Laguerre–Pólya class in `iz`; real-axis convergence to `ξ(½ + x)` is the Stieltjes / Laguerre–Pólya moment property of the Taylor coefficients of `ξ` at `½`, i.e. Σ6 [D]. |

## Π — precision and production

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1 Global law | Solved (as equivalence) | RH | `ψ(x) − x ≤ C√x log²x` ⇔ RH ⇔ `κ = 0`; prime-star nerve reduced Euler characteristic `−M(N)` = determinant of the pole gluing (Redheffer) = signature of the coprimality form; RH ⇔ `O(N^{½+δ})` growth of any of them [L]. The squarefree complex is (target) a wedge of `≈ (2/π²)N` spheres of mixed dimension, so the Mertens bound needs cancellation between dimensions [L/D]. |
| Π2 Deciding input | Open | RH | No unconditional source input at square-root precision. |
| Π3 Producer cost | Partially solved | sub / RH | Multivariate parity-selective producers reach `ψ, θ ≤ (1+ε)x + C_ε log²x`; every individual producer has slope `> 1`; univariate integer-Chebyshev ceiling `exp(−0.87n)` [L]. Open: `ε`-uniform error. |
| Π4 Window precision (kernel = coupling) | Sharpened | RH | Weil's kernel is the smoothed prime error in fixed-length multiplicative windows; coupling ≡ kernel [L/D]. |
| Π5 Conjugate diagonal (Hecke defect) | Sharpened | sub → ≥qRH → RH | Prime polynomial carries `O(1/log T)` of the defect; counts + linear explicit formula cannot bound it [L]. Dyadic means `O_c(log U)` for every `c < 1/2` (also for the unit-window supremum), `K_c ≤ K_*c²` on `c ≤ 1/5`; one-sided mollified Green–Jensen ceiling, pure abscissa quarter-gate; no superharmonic critical-line weight dominates the depth kernel [L]; `O(U^η)` for `c < 2/3` [L]. `O_c(log U)` for all `c < c*` ⇔ near-line density rate `r` for all `r < 2c*`, every `c* ≤ 2/3`; near-line density holds at every rate `r < 1` [L]. Mean `o(log U)` ⇔ 100% critical-scale clustering [L]. Fixed scale ⇔ corridor (≥qRH). One constant over dyadic scales ⇔ RH [L]. |
| Π6 Averages versus all heights | Sharpened | — | Almost all unit windows zero-free at depth `(1 + ε)loglog T/log T` [L]; right-half depth moment `o(V)`; a density envelope admits a singleton count [L]. Under finite off-line support with ¬RH, fixed-`c` unit-window jets tend to `0` while every dyadic reading is unbounded [L]. |
| Π7 Census / pair surplus | Partially solved | sub / LH | Simple critical `≥ 0.67250071` [L]. Cosine certificate on `λ ∈ (0, 2]`: `(R_cos(λ) + δ_λ − ε)N − S_cos ≤ N₀ˢ`, `R_cos(4/3) ≥ 3/4 + 79/1250`, `R_cos(2) ≥ 5/6 + 43/3750` [L]. Open: the signed prime-pair surplus `S_cos` beyond bandwidth one. |
| Π8 Depth visibility | Sharpened | — | Isolated pair visible at aperture `a` iff `S_δ(a) > (1/2π)log(ξ/2π)`; archimedean domination blind at every depth; finite-aperture positivity forces companions of deep isolated zeros [L]. In the multiple `K = e^{2a}` below Nyquist: index `0` iff `(K^δ − K^{−δ})/(2δ) ≤ 2L_γ + log K`; edge `exp(min(x/δ, L))`, `sinh x − x = 2δL`, between `(4δL)^{1/δ}` and `(6δL+1)^{1/δ}` for `δL ≥ 16`; above Nyquist a lattice-difference test has energy exactly `−2` [L]. Clusters are not excluded [D]. |
| Π9 Exceptional moduli | Partially solved | sub | Uniform zero-free region and Siegel for `q ≤ (log x)^A`; every inverse-log rate at one horizon [L]. |
| Π10 Frequency localization | Sharpened | ≥qRH (¾ strip); RH | Every band `K = ⌈N^δ⌉` retains the infimal exponent `2Θ` [L]. |
| Π11a Cone effectivity | No-go (classified) | — | On any polar surface, an ample cone of nonnegative degree satisfies the RR axiom iff it contains the open positive cone and the Hodge index holds; on an orbit, RR ⇔ orientation [L]. |
| Π11b Bidegree counts | No-go | — | Counts built from the base by its own operations are functions of `(x·H, x·V)`; their primitive `h¹` is `½δ` whatever they are; RI ⇔ Hodge index + pole-plane RI [L]. Künneth effectivity on prime-free cycles and off the finite divisor holds, imported from estimates [L]; all-profile Künneth effectivity and Hodge index through radius `181/500` [S]. |
| Π11c Fixed-rank counts | No-go | — | Fixed-rank lattice counts with bounded `h⁰(·, 0)` and degree `≤ α + β\|x·A\|` violate RI on every polar surface [L]. |
| Π11d Definite counts | No-go | — | `ℤ ⊕ yℤ`, `y > e²` (e.g. `y = 8`): positive count, Poisson duality, FE, simple poles, positive Dirichlet series, real zero in `(½, 1)` [L]. The self-dual point `ℤ ⊕ ℤ` has `Λ₁(σ) < 0` on `(0,1)`: the fakes are created by the boost [L]; where on `0 < \|u\| ≤ 1` the first real zero enters `(½, 1)` is open (numerically near `y ≈ 7.01`). |
| Π11e Siegel majorants | No-go as producer | — | `P_u ≥ 0` on every class ⇔ Hodge index; every primitive Gaussian count of the scaling surface converges ⇔ RH; split plane at fixed boost is a rectangular lattice with fakes for `\|u\| > 1` [L]. |
| Π11f Logarithmic duality of the split surface | Open | sub | Isotropic cone count `= Γ(σ)(2π)^{−σ}ζ(σ)²`, double pole `1/(2π)`, no weak FE-pair; boost average of majorants = cone count [L]. The completion must carry the logarithm of the pole-plane RR `h⁰(D) − h⁰(D^∨) = log(D²/2)`. |
| Π11g Boost transform | Solved (identity) | — | `∫Z⁺(s,u)e^{2wu}du = K(s,w)ζ(s+w)ζ(s−w)`; the boost-equivariant part of the split count carries the Euler product [L]. |
| Π11h Count-valued primitive `h¹` | Open (solved at small radius) | RH | Künneth RR `h_K(x) + h_K(−x) = ½x² + h¹_K + ½δ`; RI on the scaling surface ⇔ RH; Hecke correspondences scale primitive `h¹`; over curves primitive `h¹` of a graph = degree of the correspondence (`N₁` for `1 − F`) [L]. Prime-free cycles: `W = Ω(0)‖f‖² + J(f) + pole term`, `J(f) = ½∫∫(f(u) − f(u+x))² du w(x)dx ≥ 0`, `w(x) = e^{x/2}/sinh x` (the Lévy–Khintchine jump count of the Gamma factor); the count alone gives `W ≥ ‖f‖²/20` and `h¹_prim ≥ ‖f‖²/40` at radius `≤ 1/64` [L]. Over `𝔽_q` the Stepanov count gives Künneth effectivity and `h¹_prim ≥ 0` on every Frobenius window of every odd-characteristic hyperelliptic curve [L]. The exterior charge reaches radius `≈ 0.03`; at `½ log 2` it gives `≈ 3.85` against `\|Ω(0)\| ≈ 5.37`. Missing: the count reading on the whole prime-free window (a Poincaré inequality for the Lévy form on an interval, and the pole signs `+2A²` even, `−2A²` odd), the prime comb past the first Hecke graph, and counts on lattices of growing rank. |
| Π12 Subconvexity / heat floor | Partially solved | sub | `μ(½) ≤ 33/200`, `μ(5/6) ≤ 2/53` [L]; every even heated slice coefficient positive at `(133/200)/log\|t\|` [L]; flow threshold `(2/3 + ε)/log X` [L]. |
| Π13 Prefix scale of quantized readings | Solved (paper) | — | Stopping certificate sound and eventually complete [L]. Theta prefixes: strip zero multiplicity `Θ(N² log N)`, zero-free in the strip above height `C(N+2)²`; first artifact-free prefix `≥ c√T` [L]. Separation-free stabilization (Burnol horizontal selection + convex Boutroux–Cartan avoidance on Zhukovsky ellipses): cumulative windows at `N = O(T log²(T+S))`, unit windows at `N = Θ(√m)`, optimal [P]. |
| Π14 Amplifier rank | No-go (finite support) | — | Growing losses `e^{2kλ}` keep radius `Be^λ` [L]. |
| Π15 Critical-scale residual sign | Sharpened | RH (all `K`) | Margin = synthesis error = `1/log N` at `c*`; sharp literal prime residual scale `(log Q)²/log N` [L]; generic relative bounds stop decaying at the receiver scale (Σ1i) [L]. Only signed cancellation decides [D]. |
| Π16 Genus function | Sharpened | indep. | Near radical at level `a`: dimension `≥ (2 − η)e^{2a}`, energy `≤ exp(−η²e^{2a}/(300a))`, blind to all zeros below `2πe^{2a}` [L]. The genus function counts distinct resolved zeros: `g ≥ (2 − η)e^{2L} + 2(N(0,T) − N_d(0,T))` and `g(L, 2ε) ≥ (2 − η)e^{2L} + 2N(0,T) − #S` for every net `S` of the low zeros at scale `exp(−η²e^{2L}/(100L))` [L]. The genus law `g ≤ (2 + η)e^{2a}` at one `η` gives `N − N^s ≤ 2ηT` (almost all zeros simple, rate `1/log T`) and all but `o(T)` zeros isolated at scale `exp(−η²T/(20 log T))` [L]. Over `𝔽_q` the exact radical is infinite beyond the genus aperture [L]. |

## Γ — selection

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Trivial gauge point | Open | RH | `Θ ≥ ½`, Haar-a.e. `½`; RH ⇔ trivial point typical [L]. |
| Γ2 Prime-set flips | Solved | — | Ordinary or two-adic atomic margin separates every nontrivial prime pattern; coupling diagonal recovers flip sets; every finite flip set has an exact resolution threshold; zero-density twins of relative density `κ ∈ (0, 1/4)` separated iff the conductor series exceeds `1/s` [L]. |
| Γ3 Twin-blindness of soft structure | No-go (complete) | — | Krein index invariant under unitary twists; pointwise-closed classes contain every unitary twist [L]. |
| Γ4 Frobenius at infinity | Open | RH | `σ(ρ) = 1 − ρ̄` fixes exactly the line; RH ⇔ `σ` trivial ⇔ every Hecke translation a similitude of the collided form ⇔ one constant for the dyadic Hecke defects ⇔ partner saturation of resonant states [L]. |
| Γ5 Source identification / pre-divisor | Partially solved | RH | Integer counting + full-cone positivity ⇒ `λ = Λ` and RH; pre-divisor sections need zero-independent forcing [L]. |
| Γ6 Boundary sign / coherence | Solved | — | Pole boundary sign separates ζ from size-equivalent twins [L]. |
| Γ7 Affine carrier with Weil dilation | Solved | — | Gluing at a place; subgroup classification [L]. |
| Γ8 Poisson rigidity | Sharpened | RH | Positive tent-self-dual measures with gap are Dirac combs; zero-side positivity = RH [S]. |
| Γ9 Archimedean continuity vs height decay | No-go | — | Continuous dilation against a decaying finite-adelic reading ⇒ `κ = ∞` [L]. |
| Γ10 Function-field indistinguishability | Sharpened | — | Local index walls identical over `𝔽_q(X)`; curve edge `≤ 2g`; Frobenius conformal with factor `q`, Hecke dilations boosts; Künneth effectivity on every Frobenius window ⇔ unitarity, and holds by the Stepanov count; links complete over curves, disconnected over `ℤ`; finite divisor over `ℤ`, none for fakes [L]. |
| Γ11 Pole-blindness of the glue | No-go | — | Simple pole absorbed, double pole costs a square [L]. |
| Γ12 General gauges | Solved | sub | Entrywise-nonnegative gauges only on archimedean characters; twisted Selberg source forces `ω(p) = 1` [L]. Bare zero-density twins at `κ = 0` satisfy the exact conductor-series criterion, without a density-error rate or positive limiting Euler mass [L]. |
| Γ13 Source-uniform extinction | No-go | — | Fails at `3/4 + i` [L]. |
| Γ14 Local counterterm selection | No-go | — | Diagonal counterterms give `Λ` and a flip twin glued index `1` [L]. |
| Γ15 Functional-equation twins without Euler product | Partially solved (no-go also with nonnegative Ramanujan coefficients) | sub | For every `N`, `k`, `B`, a normalized Dirichlet series agreeing with `ζ³` below `N` has a completion with `k` distinct real zeros beyond `max(B, 3)`, the same functional equation and principal parts [L]: degree-three FE data impose no zero-free right half-plane. Degree-one rigidity holds under its analytic hypotheses [L]. Euler-product-constrained twins open. |
| Γ16 Selection–sign gap | Sharpened | RH | Every selector (atomic pole index, two-adic probe, Metzler gauge, twisted Selberg source, coupling diagonal, finite-flip edges, star flux, conductor series) is a margin, index or counterterm identity on a partial form [L]. |
| Γ17 Scattering recentering | Classified (no-go) | — | A rational map real at infinitely many points of the critical parabola is constant; an algebraic relation real infinitely often on the parabola and on `(¼, ∞)` is a horizontal line [L]. |
| Γ18 Divisor-identity selection | Solved (selection) | — | Self-similar star flux iff generalized von Mangoldt; among completely multiplicative twists `Λω` only `ω ≡ 1` [L]. |
| Γ19 Correspondence algebra over `ℤ` | Sharpened | RH | Correspondences = finitely supported measures on scales; Hecke graphs satisfy Lefschetz, adjunction and `T_gT_g′ = e^{s(g)}`; λ-ring with Adams operators = scaling action; the theorem of the square holds on every polar surface (normalized graphs, degree = `½δ`); Rosati positivity ⇔ orbit Hodge index ⇔ every normalized Hecke graph has nonnegative degree; Lefschetz trace of a corrector = primitive energy; eventual Hasse–Weil ⇒ Hasse–Weil [L]. Tate's limit law: Rosati positivity at a cycle ⇔ its integral Rosati form has a naive height ⇔ it has a midpoint-convex function at bounded distance; for ζ, RH ⇔ every cycle has one; in genus one a naive height exists iff Hasse holds, the golden datum has none [L]. All algebraic identities hold on the golden fake; positivity is the orientation. |

## Bridges

| Bridge | Anchor |
|---|---|
| `κ(K_ζ)` = right zeros = Hodge defect = band poles of `Λ(s)/Λ(s+1)` = zeros moved by `σ`; even; RH ⇔ `κ < 2`; the Hecke orbit of one generic test carries all of it | HKT, RIT, EHT `FrobeniusAtInfinity`, AOG `TheIndexExit`, ACS `TheHodgeDefectIsCyclic` [L] |
| `κ(φ_c) = κ + 1` at every place; two primes with bounded translations carry it | AKG [L] |
| boost hyperplane = `v₁^⊥` = Markov = harmonic hyperplane = primitive part | RIT, HWV [L] |
| bounded `K_ζ` ⇔ bounded coupling ⇔ no edge ⇔ RH | RIT, ACPL [L] |
| overlap multiple `K·c*` ↔ synthesis blocks `e^{2R}` ↔ radius `½ log K` ↔ degree `a` | TM `ReceiverRate` [L] |
| tilted spline: rough regime `1/9`, inheritance radius and receiver `1/8`; logarithmic profile: rough regime `ε₀·c*`, receiver `K·c*` | CACT, ADT, SSHA, TM [L] |
| rescaled limit = Jordan-totient form `J_{β+1}(m)/φ(m) = m^β Π_{p∣m} ζ_p(1)/ζ_p(β+1)`; extension data vanish below `1/8` and carry the zeros at it | ADT [L]; reading [D] |
| aperture ceiling ↔ near radical `(2 − η)e^{2a}` blind below `2πe^{2a}` ↔ finite divisor `D_a` ↔ genus function counting distinct resolved zeros | ArithmeticCompensationTheory, RHTower `SharpWeilNearRadicalCount`, ACS [L] |
| isolated pair visible iff `S_δ(a) > (1/2π)log(ξ/2π)`; edge `≈ (cδ log γ)^{1/δ}` in the multiple; companions forced at finite aperture | ACS, RHTower `IsolatedDeepZeroWeilDetection` [L] |
| Weil form = Markov form (archimedean + prime jumps, creation potential `V_N`) + pole plane; on prime-free cycles the jump part is the Lévy–Khintchine count of the Gamma factor | RHTower `WeilMarkovPoleCapacity`, LST [L] |
| RH ⇔ HL on the PSD locus; Liouville = HL; no free Lefschetz operator | HWV [L] |
| `W = Σ_g Cop(W at the star of g)`; successor and archimedean coupling in `g = 1`; links disconnected; nerve `χ̃ = −M(N)`; no semilocal positive carrier | HWV, SP [L/S] |
| RH ⇔ effectivity with RR and ample axioms; cone RR ⇔ Hodge (universal floor law); orbit RR ⇔ orientation | ACS, AOG [L] |
| theta `h⁰` RR on `Spec ℤ` and the pole plane; `Λ(s)` = Mellin of `e^{h⁰} − 1` | AOG `TheThetaH0OfSpecZ` [L] |
| Künneth `h¹` = count part + `½δ`; primitive `h¹` over curves = degree of the correspondence; Stepanov count pays it over `𝔽_q` | LST [L] |
| Rosati positivity ⇔ orbit Hodge index ⇔ naive height on the integral Rosati form ⇔ midpoint-convex log-count | AOG, AET, ACP [L] |
| first rung: finite Hodge defect ⇔ bounded heat counts ⇔ bounded collision charges ⇒ `Θ < 1` | AOG `TheIndexExit` [L] |
| collision charge = Fredholm index = Wiener–Hopf index; index `0` ⇔ outer Szegő factorization ⇔ disk-unit sectoriality; `κ ≤ sup O`; `Θ(√m)`-prefix Szegő positivity: log resolution ⇔ inverse-log corridor, polynomial resolution ⇔ RH | CDG [L/P] |
| Mertens function = determinant of the pole gluing of the divisibility form = nerve Euler characteristic = signature of the coprimality form | ADT, HWV, RHTower [L] |
| ADT carriers: an identity, an inherited polarization or an integer with a structural bound; estimates stop at the edge | ADT, EHT [L/D] |
| Hecke-defect means ↔ near-line density rates (`r < 2c*`, `c* ≤ 2/3`); `o(log U)` ⇔ critical-scale clustering; dyadic-uniform ⇔ RH | CDG [L] |
| partner saturation of resonant states ⇔ `Re ρ = ½` | RHTower `EisensteinResonantPartnerAngle` [L] |
| Mayer determinant `D = A + ζB`; signed product = exp of even-word traces; primitive coding | RIT [L] |
| curve: bounded coupling ⇔ unitary ⇔ Castelnuovo–Severi on the Frobenius span; Künneth effectivity ⇔ unitarity | ACPL, LST [L] |
| centered curve products ↔ Laguerre–Pólya closure ↔ Hankel / Jensen signs | ART [L]; reading [D] |

## Status counts

| Family | Solved | Partially solved | Sharpened | Open | No-go | Classified |
|---|---|---|---|---|---|---|
| Σ (36) | 7 (Σ1a, Σ1h, Σ10, Σ12, Σ16, Σ17, Σ24) | 6 (Σ1b, Σ1d, Σ1g, Σ3, Σ6, Σ9) | 6 (Σ1, Σ1i, Σ2, Σ3a, Σ4, Σ5) | 7 (Σ1c, Σ1e, Σ7, Σ8, Σ18, Σ19, Σ20) | 5 (Σ1f, Σ13, Σ14, Σ23, Σ25) | 5 (Σ11, Σ15, Σ21, Σ22, Σ26) |
| Π (23) | 3 (Π1, Π11g, Π13 paper) | 4 (Π3, Π7, Π9, Π12) | 7 (Π4, Π5, Π6, Π8, Π10, Π15, Π16) | 3 (Π2, Π11f, Π11h) | 6 (Π11a–e, Π14) | — |
| Γ (19) | 5 (Γ2, Γ6, Γ7, Γ12, Γ18) | 2 (Γ5, Γ15) | 4 (Γ8, Γ10, Γ16, Γ19) | 2 (Γ1, Γ4) | 5 (Γ3, Γ9, Γ11, Γ13, Γ14) | 1 (Γ17) |

Strength of the open walls:
- **RH:** Σ1, Σ1i (all `K`), Σ2, Σ3 (ascent), Σ3a, Σ5, Σ6, Σ7, Σ8, Σ18, Σ19, Σ20, Π2, Π4, Π11h,
  Π15, Γ1, Γ4, Γ5, Γ8, Γ16, Γ19.
- **≥qRH:** Σ4 (`K_ζ`), Π5 (fixed scale), Π10 (¾ strip).
- **sub:** Σ1b–Σ1g, Σ1i (fixed `K`), Π3, Π5 (mean `o(log U)`, density rate `≥ 1`), Π7, Π9, Π11f,
  Π11h (fixed degree), Π12, Γ15.
- **indep.:** Π16 (genus law; implies almost all zeros simple).
