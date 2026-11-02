# Walls ledger — status quo

Three wall families block every route: **Σ** the critical sign, **Π** precision and production,
**Γ** selection of ζ. All three read one even integer, `κ = κ(K_ζ) = #` distinct zeros right of the
critical line, on the pole-orthogonal hyperplane `v₁^⊥`.

- **Σ is Weil's sign on window tests.** RH is Weil positivity of `H(y) = e^{y/2}h(y)`, `h ∈ C²[−A, 0]`,
  for every window length `A`. The complete atomic family decomposes along its degeneration:
  - the **bulk** (fixed conductor packets) converges after rescaling to the Jordan form
    `J(m) = J(1)·#ℙ⁷(ℤ/m)` — a point count, positive, zero-blind; a zero enters the bulk only through
    the pole coefficient with a weight of positive real part, so the bulk carries no selection;
  - the **horizon layer** (blocks `x_n = h(log(n/N))/√n`) is, divided by the overlap, `κ_φ Q(H)` past
    the critical curve and `κ_φ Q(H) + (7J(1)/K)∫e^{−8y}H²` at `c⁸/log N → K`: Weil's form of the
    synthesized test plus a prime-free coercive aliasing term.
  The constant-factor wall, the second-order term of the degeneration, the receiver scale and the
  pole-hyperplane sign of the glued state are all this one statement. On a window of length `A` Weil's
  form is a Markov form whose prime jumps are the prime powers `n ≤ e^A`; jumps leaving the window pay
  exactly their creation potential.
- **Π is the precision of four prime statistics and the production of a count:**
  - the one-point windowed prime error (= Weil's kernel = the inter-tower coupling);
  - windowed zero power sums `Σ_{ρ∈W} x^{ρ−½}` on unit height windows (the Ward/Szegő window energy);
  - the conjugate diagonal (Hecke defect), equivalent to a near-line density ladder;
  - the signed prime-pair surplus beyond bandwidth one (census);
  - the count-valued primitive `h¹` of the scaling surface, equivalently a naive height on the integral
    correspondence ring.
- **Γ is closed for every prime-set flip at every density.** What remains is Frobenius at infinity:
  the identity of the reflection pairing `ρ ↔ 1 − ρ` with the conjugation pairing `ρ ↔ ρ̄`. It is read
  by one function, the rank-one intertwining coefficient `Λ(s)/Λ(s + 1)`: its band poles are the
  Hodge defect, it is the Gauss–Mayer boundary observable `2ζ(s)/ζ(s + 1)`, and it is the scattering
  coefficient of `SL₂(ℤ)\ℍ`. Its fifth form is Rosati positivity of the correspondence algebra over
  `ℤ`, equivalently a naive height at bounded distance from the integral Rosati form.

Status: **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, with its exact
form a theorem), **Open**, **No-go** (the mechanism is refuted), **Classified** (answered by a
classification or identification theorem), **Reduced** (the wall is a theorem-level equivalent of
another wall, named in the entry). Strength: **RH**, **≥qRH** (implies a zero-free half-plane and
Lindelöf), **LH**, **sub**, **indep.** (not implied by RH; no implication to RH known). Evidence: `[L]`
Lean; `[S]` Lean in the working tree or not integrated; `[P]` complete paper proof, Lean pending;
`[D]` derived here from Lean statements.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Weil's sign on window tests (degree axis) | Sharpened | RH | RH ⇔ `Q(e^{y/2}h) ≥ 0` for every C² `h` on every `[−A, 0]` (`riemannHypothesis_iff_halfWeight_nonneg`) ⇔ horizon blocks of the tilted spline eventually `≥ −ε` past the critical curve (`riemannHypothesis_iff_horizon_layer`) ⇔ eventual pole-hyperplane positivity of the complete Beurling matrix on the single schedule `c_N = 2L(log L)²`, `L = log log N` (RIT `TheHodgeIndexAtCriticalOverlap`) ⇔ eventual positivity at every fixed `K·c*` (Denjoy–Carleman, sinc, Steklov, logarithmic profiles) [L]. Restricted ground minimum: `μ(A) ≥ 0 ∀A` ⇔ RH; floors through radius `181/500`; zero-form operator positive on `0 < a ≤ 181/500`; exact `{∞,2}` trace identity through `½ log 3`, where positivity ⇔ single-prime family energy `≥ 0` [L]. Ceiling `μ(A) ≤ K exp((11/2)A − πe^{2(A−2)})` [L]. Any `≤ r` prime towers with arbitrary real weights: `μ_w(A) ≤ C_r − c_r e^A` for `A ≥ 4`; a finite prime set `S` crosses zero by aperture `2 log(\|S\| + 2) + 11`; bounded-below weighted energy forces weight `≥ [min(log κ/4, 1/16)/16]·X` in every `(X, κX]` [L]. |
| Σ1a Critical overlap and receivers | Solved | — | Denjoy–Carleman / sinc `c*_N ≍ L(log L)²` with margin = synthesis error = `1/log N`; tilted spline receiver at every `K(log N)^{1/8}` and on the pole hyperplane; every divergent multiple is a receiver [L]. One fixed C^∞ Beurling profile realizes every finite rational correlation Gram as an entrywise limit of complete-matrix compressions at the universal overlap `2·dcScale N`, independent of the family (`exists_ratCorr_completeWeil_gram_limit_at_universal_critical_overlap`); a compact profile exists at every logarithmic Denjoy–Carleman type [L]. |
| Σ1b Rough regime, tilted spline | Partially solved | sub | All vectors, `1 ≤ c ≤ (log N)^α`, `α < 1/9`: `W ≥ (a₀/c⁷)(poleDefect − C log(2c)‖x‖²) + (κ₀/(2c⁷))‖x‖²`, reserve `c^{−8}` [L]. Below `1/8` [L]: fixed and polylogarithmic packets; the whole growing subthreshold block `e ≤ c/X` inherits the Jordan form with loss `ε`; the polynomial-conductor complement `(V_{⌊N^θ⌋})^⊥` is coercive with floor `c_orth log N/c⁷`, so every nonpositive subspace has dimension `≤ ⌊N^θ⌋`; far reserve `(7/8)D_M + κ/(4c⁷)·log N·S − θ log N·P ≤ W` on `v₁^⊥` (prefix/top split, prime cross = Dirichlet convolution with the prime translate, window sums of the translate = pole coefficient + `O(log K')`·prefix, Gamma form paying frequencies above `T`). Mid-band packets coercive for `α < 1/4` [L]; near-collar cost `130/log N·Σ b_m² m/φ(m)` [L]. Open: the band–far cross and the threshold block `e ≍ c` at the `1/8` rate. Refuted: smallness of the prefix–terminal non-ratio block on terminal-pole-orthogonal vectors; survivor `NR_PT ≈ σ â ⊗ p̂ + E`, `σ ≍ c√log N`, `E` off-diagonal a shifted prime-pair correlation. Under ¬RH the edge lies in `[(log N)^α, 2(log N)^β]` infinitely often for every `α < 1/9`, `β > 1/8` [L]. |
| Σ1c Joint shell–pole payment | Open | sub | Separate shell payment sharp at `c²/ε` (`c⁹` at `ε = c⁻⁷`); joint top-band coefficient `O_φ(G(c + log N))`; shell-degree row bound with packet payment; successor gap identity [L]. With terminal support of the weighted near pairing the high-conductor loss is `O(c²)` under an explicit terminal budget: `(1/16)adj + (1/4)log Q − Cc² ≤ W` [S]. The prime-successor comparison with the shell payment is unproved. All-vector positivity at the receiver needs confinement exponent `≤ 8` [D]. |
| Σ1d Low-conductor spans, general profiles | Partially solved | sub | Every nonzero compact C² profile, Fourier zeros allowed [L]: positive, subexponential and exponential conductor floors; logarithmic high-conductor gap; polynomial high-conductor loss `O(c⁴(1 + log c))`; positivity on `V_{⌊N^θ⌋}`, `θ < 1/1080`, with floor `a e^{−Bc}` (universal `B`) for `1 ≤ c ≤ (log log N)^β`, `β < 1/4`; every polylog span for `1 ≤ c ≤ K log log N`; floor `(log N)^{−η}/4` on almost-polynomial spans `exp(log N/L^κ)`, `κ > 2`, up to an explicit clock `g(L)` with `g(L)/L → ∞`, `g ≤ L log L` [S]. Full-space positivity at super-log-log overlap and spans past `N^θ` open. |
| Σ1e Square-root conductor barrier | Open | sub | Frames and residual averages need `m² ≤ N`; above `√N` an Elliott–Halberstam-type input. |
| Σ1f Defect-only confinement | No-go | — | `Q < 2^k` witnesses [L]. |
| Σ1g Haar / Gamma graph | Partially solved | sub | Growing-packet prime–pole cancellation to `exp(√log Y/23040000)`; index `≤ R + A` for `R` coarse cells; growing Euler head alone unbounded [L]. Open: joint non-arithmetic Gamma graph + signed diagonal + roots + poles. |
| Σ1h Rough regime, smooth profiles | Solved (to `ε₀·c*`) | sub | Every C² profile without real Fourier zeros has edge `→ ∞`; the zero-free logarithmic profile is positive definite for `1 ≤ c ≤ ε₀ L(log L)²`, `ε₀ = 1/[103424(8π/3 + 3000)]`, optimal for the reciprocal-floor budget system [L]. |
| Σ1i Second-order term at the critical curve | Classified | — | Horizon formula: `c⁻¹⟨Wx, x⟩` = pole terms + `(∫φ²)⁻¹∫‖φ̂(wτ)‖²(\|D_x(τ)\|²/N)ν(τ)dτ` with the symbol `ν` of Weil's form; below the atom grid Kuzmin–Landau, above it aliasing tails `O(log N/c^p)`. Two-sided: `\|c⁻¹⟨Wx,x⟩ − κ_φQ(H)\| ≤ ε + K(1 + log N)/c^p`. Sharp: `c⁻¹⟨Wx,x⟩ − κQ(H) − (log N/∫φ²)𝒜_N → 0`, `𝒜_N` the window average of the aliasing density `a_φ(s) = Σ_{k≥1}\|φ̂(2πks)\|²`, and `E₁'(s) = −(2/∫φ²)a_φ(s)` (aliasing = dilation derivative of the bulk). For any profile with `s^βE₁(s) → J`: `→ κQ(H) + (βJ/K)∫e^{−(β+1)y}H²` along `c^{β+1}/log N → K`; tilted spline `κQ(H) + (7J(1)/K)∫e^{−8y}H²` [L]. Zero ledger of the bulk: fixed packets see `ρ` only through `m_ρκy₁²/(ρ(1 − ρ))`, `Re > 0`, for every configuration [L]. Critical-multiple calculus: admissible multiples a closed initial segment; one multiple `K_c` gives only `κQ(H) ≥ −K/K_c`; every negative window is negative past `K* = 7J(1)∫e^{−8y}H²/(κ\|Q(H)\|)` [L]. The constant-factor wall is Weil's sign plus a positive prime-free term. |
| Σ1j Full-space second order and horizon localization | Open | sub | Σ1i is a theorem on horizon blocks and on fixed packets. Open: the rescaled limit of the complete form at the critical curve on all vectors (bulk ⊕ horizon ⊕ mixed), and whether every negative direction there is asymptotically a horizon block. An identity of this kind would make the complete-family sign literally Weil's window sign plus explicit positive terms [D]. |
| Σ1k Strength of one fixed critical multiple | Open | sub | Each fixed `K` is sub-RH with an exact per-window threshold [L]. Which zero configurations it excludes is not computed. Isolated off-line pairs are seen only by windows of length `≳ δ⁻¹ log log γ` (visibility law), so their threshold grows with height; dense off-line clusters of depth `δ` are seen by windows of length `O(δ⁻¹)` at every height [D]. |
| Σ2 Edge, zero modes, hard Lefschetz | Sharpened | RH | HR ∧ HL ⇔ strict HR; transport needs HL only on the HR locus; losing HR forces a primitive zero mode; Liouville ⇔ HL; RH ⇔ HL on the PSD locus along `1 ≤ c ≤ 2(log N)^β`, `β > ½` (`riemannHypothesis_iff_liouville_along_the_overlap_flow`) [L]. A finite first edge is PSD with a zero mode [L]. |
| Σ3 Star renormalization and dilation monodromy | Partially solved | — (descent); RH (ascent) | Star of `d` = family at `(c⌊N/d⌋/N, ⌊N/d⌋)`, isometric; positivity descends; deep stars positive; depth law `log d − C₀` [L]. Monodromy in closed form `c_m(gn) = (φ(m)/φ(m/(m,g)))c_{m/(m,g)}(n)`; eventually idempotent, `D_p^v(D_p − 1) = 0` on a `p`-string of length `v = v_p(m)` (eigenvalues `{0, 1}`, against quasi-unipotence in Hodge theory) [L]. Scaling form `E_m(c) = J(m)c⁻⁷R_m(c/m)`: `R_m` depends only on `rad m` (branches), `J(m)` on the weight string; `R_m → 1` uniformly (Jordan end), `0 ≤ R_m(x) ≤ Cx` (pure end) [L]. Jordan coefficient `J(m) = J(1)#ℙ⁷(ℤ/m)`; weight strings are Hensel towers; tensor law is CRT [L]. Complete degeneration (`F_λ = 0`) holds exactly for `λ = Λ` among real twists [L]. |
| Σ3a Coprime stratum | Sharpened | RH | gcd stratification `W = Σ_g Cop(W at the star of g)`; successor pairs and archimedean overlaps of consecutive atoms in `g = 1` [L]. Graded energy = positive cone sum of top-stratum energies of lowered conductors, `⟨W r_e, r_e⟩ = (log N)⁻¹Σ_g θ_g(e)²Top_{c_g,⌊N/g⌋}(R_{e/(e,g)})`; top = Möbius-signed cone sum of graded energies — alternating, so graded positivity does not pass to the top stratum [L]. Conductor Gram PSD at every `2K(log N)^{1/8}` ⇔ RH; coprimality form signature `M(N)`; pole gluing of the divisibility form = Redheffer, `det = M(N)` [L]. |
| Σ4 Finite index / heat count | Sharpened | ≥qRH (`K_ζ`); RH (`K_ζ⊠K_ζ`) | `κ < ∞` ⇔ bounded `N(t)` ⇔ bounded `O(T)` ⇔ all high zeros critical ⇒ `Θ < 1`; `κ ≤ r` ⇔ translation-stable positive constraints of dimension `≤ r`; no softening at any resolution [L]. |
| Σ5 Collision quantum / window index | Reduced (to Π17) | RH | `O ∈ 2ℕ`; RH ⇔ `O < 2` per window; heat state `κ(φ_c^{(t)}) = N(t)/2 + 1` [L]. Per window: index `0` ⇔ Wiener–Hopf invertibility ⇔ outer Birkhoff–Szegő factorization ⇔ disk-unit sectoriality; separation-free stabilization at prefix `Θ(√m)` (unit windows) and `O(m log²(m + S))` (cumulative); 9-way RH equivalence at these prefixes (`riemannHypothesis_door_opener_tfae`) [L]. The exact outer multiplier exists whenever any multiplier does; every analytic certificate is the exact multiplier times a Carathéodory factor; its cepstrum is a positive Bessel transform of the window energy `\|𝒵(t)\|²` with `(−1)^kS_k ≥ 0`; index `0` ⇔ integrability of `e^{−(1/2 − a_n)t}\|𝒵(t)\|²` [L]. The integer is decided by the growth of the window energy. |
| Σ6 Rank / degree uniformity | Partially solved | RH | Rank 7 strict, rank 8 PSD; fixed Jensen degree eventually hyperbolic; PF₃₇ at the centre; RH ⇒ simple roots of reversed Xi Jensen sections [L]. Approximation by RH-true centered curve products closes into this wall (Σ26) [D]. |
| Σ7 Odd / Markov sector | Open | RH | RH ⇔ `R ≤ ½` on odd vectors [L]. `W = V_N‖g‖² + J(g) + ½⟨c,g⟩² − ½⟨s,g⟩²`, `J` archimedean-plus-prime jump energy, `V_N = Ω(0) − 2Σ_{n≤N}Λ(n)/√n`; RH ⇔ the sinh-capacity bound at every level [L]. On a window of length `A` only the prime powers `n ≤ e^A` jump; departing jumps pay exactly `2Λ(n)/√n‖g‖²`, so the Markov form is level-independent past the support (`primeJump_departing_eq`, `weilQuad_halfWeight_eq_markovForm`) [L]. |
| Σ8 Realization | Open | RH | Lossless realization needs infinitely many resonances; normal real-zero approximants force RH (Vitali) [L]. Gauss–Mayer: determinant = Euler product over genuine periodic modular geodesics (primitive pair cycles classify closed geodesics with least period; reversal = matrix inversion; unoriented product with exact fibre cardinalities); constant-input inverse has divisor exactly ζ's (scattering multiplicity); negative signed channel entire, positive channel carries exactly ζ's strip multiplicities; Epstein → Mayer Cauchy transform continued through the source half-plane; Eisenstein lift; scattering core of finite positive weighted energy at every nonreal strip zero; Cauchy multiplier envelope `2^{(1−Re w)/2}`, contraction iff `Re w ≥ 1` [L]. Open: a structure excluding off-line scattering resonances. |
| Σ9 Explicit image / resolvent | Partially solved | RH in strip | Depth identity for `σ > 1`; theta–prime expression at `s = 4` [L]. |
| Σ10 Local signatures and gluing | Solved | — | `κ(φ_c) = κ + 1` at `∞` and every prime; readings add; two primes with translations in `ℤ[1/qr]` carry the full affine index [L]. |
| Σ11 Product-formula gluing of the global pole | Classified | — | Sum of local poles `\|S\|` squares; tensor `2^{\|S\|−1}`; renormalized infinite product `∞`; extremal weight = archimedean pole on `S`-units [L]. |
| Σ12 Running counterterm / star flux | Solved | — | `log N − γ` cancels the prime diagonal through `Λ ∗ 1 = log`; on every star the counterterm pays exactly `log d` [L]. |
| Σ13 Tensor amplification | No-go | — | `K_ζ^n` PD ⇔ RH; `n₋(G⊗G) = 2n₊n₋` at every horizon [L]. |
| Σ14 Deformation to a positive model | No-go as free input | — | Crossing-free path `A → I` ⇔ `A` PD; Kähler transport exact and free [L]. |
| Σ15 Separable assemblies | Classified (no-go) | — | Blind when truncated, non-convergent pointwise when untruncated [L]. |
| Σ16 Prime–pole coherence / packet identity | Solved (as identity) | — | Mertens polarization; complete form = jump squares + affine incidence squares + bounded diagonal − shell degree + boundary; the shell degree is the only term growing with the overlap [L]. |
| Σ17 Inter-tower coupling and the natural cone | Sharpened | RH (dense lattice); sub (cone) | Coupling ≡ kernel; RH ⇔ bounded coupling on one dense `⟨p⟩×⟨q⟩`; finite stratum ⇒ RH [L]. Natural cone `ℕ²`: bounded coupling ⇒ RH or every zero a polynomial height distance below maximal width, `D − \|Re ρ − ½\| ≥ c/(1 + \|Im ρ\|)^A` (`riemannHypothesis_or_polynomial_boundary_repulsion`; two-clock resolvent, eighth-power height pole of a near-boundary zero, Baker separation) [L]. Countermodels: positive atomic nullseries on any two-generator cone; exact spline coefficients `(sinh z/z)⁸`, unit multiplicities, `≤ 12` atoms per unit height, coupling `≤ 20`, unattained positive width [L]. Open: exclusion of unattained width with Riemann–von Mangoldt density or the explicit formula. |
| Σ18 Exact SOS on a two-prime lattice | Open | RH | Weil's dilation form on boost-mass-zero vectors of one two-prime lattice as a sum of squares of coupling differences; the Hecke orbit of one spectrally generic test under `ℤ log p + ℤ log q` carries the full Hodge defect [L]. |
| Σ19 Rank-one intertwining coefficient | Open | RH | `κ_Hodge = #` band poles of `c(s) = Λ(s)/Λ(s + 1)` in `−½ < Re s < 0` (`riemannHypothesis_iff_reflectionPoles_eq_empty`) [L]. The Gauss–Mayer boundary is `2ζ(s)/ζ(s + 1)`; its slope has Dirichlet weights `(1 − 1/n)Λ(n) ≥ 0` and gives the classical zero-free region `Re ρ ≤ 1 − 1/(1000 log γ)` by 3-4-1 positivity [L]. Same function as the `SL₂(ℤ)` scattering coefficient after `s ↦ 2s − 1` [D]. A noncancellation mechanism in the band is missing. |
| Σ20 Scheduled prime sums | Open | RH | Lower bounds for prime-scheduled energies (FU, CFC, RP, SZ, LI, FEL, EGC) [L]. |
| Σ21 Extension / carrier | Classified | — | Escape, mixing, height decay ⇒ `κ ∈ {0, ∞}`; continuous-dilation carriers reading `1_H` exist iff `H ∈ {{0}, ℚ}` [L]. |
| Σ22 Lefschetz operators | Classified | — | Dilation: HL trivial, transports downward only. Overlap flow: HL on the HR locus is RH. Coupling Laplacian: HL for `t > 0`, base point the zero form [L]. |
| Σ23 Connected links | No-go | — | Links of the dilation complex disconnected; Garland / trickle-down unavailable over `ℤ`; coprime atoms couple only through the archimedean place [L]. |
| Σ24 Finite divisor | Solved | — | At every degree `a`, `Re W ≥ (10 + 68e^a)(1 − 1/π)‖f‖²` off `i/2` and a finite grid `D_a`; Hodge defect at degree `a` finite; over `𝔽_q` it is `0` or `∞` [L]. |
| Σ25 Semilocal and trace carriers | No-go | — | No `{∞, p}` semilocal family carries positivity; the archimedean carrier `A = 1 − P − P̂` satisfies `A² + (P − P̂)² = 1`, is NSD on time-limited and on band-limited vectors; any functional with one negative value has no positive operator-trace or Gram-sandwich carrier [L]. Survivor: exact `{∞,2}` trace identity through `½ log 3` with the valuation-shell operator `K_2(m)`, `Tr = m log 2`, and the Krein `(+1, −1)` split of the polar block [L]. |
| Σ26 Approximation by RH-true objects | Classified | — | Centered curve numerators have nonnegative even Taylor coefficients; Euler domain `½ + 1/(2a) → ∞`; the closure class is Laguerre–Pólya in `iz` (Σ6) [L/D]. |

## Π — precision and production

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1 Global law | Solved (as equivalence) | RH | `ψ(x) − x ≤ C√x log²x` ⇔ RH ⇔ `κ = 0`; Redheffer `det R_N = M(N)` = nerve Euler characteristic = coprimality signature, `Ω±(√N)`; RH ⇔ `O_ε(N^{½+ε})` growth [L]. The squarefree complex is a wedge of `≈ (2/π²)N` spheres of mixed dimension, so a Mertens bound needs cancellation between dimensions [L/D]. |
| Π2 Deciding input | Open | RH | No unconditional source input at square-root precision. |
| Π3 Producer cost | Partially solved | sub / RH | Multivariate parity-selective producers reach `ψ, θ ≤ (1+ε)x + C_ε log²x`; every individual producer has slope `> 1`; univariate integer-Chebyshev ceiling `exp(−0.87n)` [L]. Open: `ε`-uniform error. |
| Π4 Window precision (kernel = coupling) | Sharpened | RH | Weil's kernel is the smoothed prime error in fixed-length multiplicative windows; coupling ≡ kernel [L/D]. |
| Π5 Conjugate diagonal (Hecke defect) | Sharpened | sub → ≥qRH → RH | Prime polynomial carries `O(1/log T)` of the defect; counts + linear explicit formula cannot bound it [L]. Dyadic means `O_c(log U)` for every `c < 1/2`; for `c* ≤ 2/3`, `O_c(log U)` ∀`c < c*` ⇔ `#{ρ ∈ [V, 2V] : \|Re ρ − ½\| ≥ a/log V} ≤ A_r V log V e^{−ra}` ∀`r < 2c*`; rate `r < 1` holds [L]. Mean `o(log U)` ⇔ 100% critical-scale clustering; fixed scale ⇔ corridor (≥qRH); one constant over dyadic scales ⇔ RH [L]. |
| Π6 Averages versus all heights | Sharpened | — | Almost all unit windows zero-free at depth `(1 + ε)loglog T/log T`; right-half depth moment `o(V)`; a density envelope admits a singleton count [L]. |
| Π7 Census / pair surplus | Partially solved | sub / LH | Simple critical `≥ 0.67250071` [L]. Cosine certificate on `λ ∈ (0, 2]` [L]. Open: the signed prime-pair surplus beyond bandwidth one. |
| Π8 Depth visibility | Sharpened | — | Isolated pair visible at aperture `a` iff `S_δ(a) > (1/2π)log(ξ/2π)`; edge in the multiple `exp(min(x/δ, L))`, `sinh x − x = 2δL`; above Nyquist a lattice-difference test has energy `−2`; finite-aperture positivity forces companions [L]. Clusters are not excluded [D]. |
| Π9 Exceptional moduli | Partially solved | sub | Uniform zero-free region and Siegel for `q ≤ (log x)^A` [L]. |
| Π10 Frequency localization | Sharpened | ≥qRH (¾ strip); RH | Every band `K = ⌈N^δ⌉` retains the infimal exponent `2Θ` [L]. |
| Π11a–e Cone, bidegree, fixed-rank, definite and Siegel counts | No-go | — | Cone RR ⇔ Hodge index; bidegree counts see no primitive class (`h¹ = ½δ`); fixed-rank counts violate RI; definite counts have fakes (`ℤ ⊕ yℤ`, `y > e²`; `m² + 64n²` with real zero in `(½, 1)`, nonmultiplicative); Siegel majorant ⇔ Hodge index; split plane at fixed boost has fakes for `\|u\| > 1` [L]. |
| Π11f Logarithmic duality of the split surface | Open | sub | Isotropic cone count `Γ(σ)(2π)^{−σ}ζ(σ)²`, double pole `1/(2π)`, no weak FE-pair; boost average of majorants = cone count [L]. The completion must carry the logarithm of the pole-plane RR. |
| Π11g Boost transform | Solved (identity) | — | `∫Z⁺(s,u)e^{2wu}du = K(s,w)ζ(s+w)ζ(s−w)` [L]. |
| Π11h Count-valued primitive `h¹` | Open (solved at small radius) | RH | Künneth RR `h_K(x) + h_K(−x) = ½x² + h¹_K + ½δ`; RI ⇔ RH; Hecke correspondences scale primitive `h¹`; over curves primitive `h¹` of a graph = degree of the correspondence [L]. Prime-free cycles: `W = Ω(0)‖f‖² + J(f) + pole`, `J` the Lévy–Khintchine jump count of the Gamma factor; `h¹_prim ≥ ‖f‖²/40` at radius `≤ 1/64` [L]. Over `𝔽_q` the Stepanov count pays `h¹_prim` on every Frobenius window of odd-characteristic hyperelliptic curves [L]. Missing: the whole prime-free window, the first prime jump (`n = 2` enters windows of length `> log 2`), counts on growing rank. |
| Π12 Subconvexity / heat floor | Partially solved | sub | `μ(½) ≤ 33/200`; even heated slice coefficients positive at `(133/200)/log\|t\|`; flow threshold `(2/3 + ε)/log X` [L]. |
| Π13 Prefix scale of quantized readings | Solved | — | Strip zeros of prefix `N`: `Θ(N² log N)`; zero-free above `C(N + 2)²`; first artifact-free prefix `≥ c√T`; separation-free stabilization at `Θ(√m)` (unit windows) and `O(m log²(m + S))` (cumulative) [L]. |
| Π14 Amplifier rank | No-go (finite support) | — | Growing losses `e^{2kλ}` keep radius `Be^λ` [L]. |
| Π15 Critical-scale residual sign | Classified | — | Margin = synthesis error = `1/log N` at `c*`; sharp literal prime residual `(log Q)²/log N` [L]. At the critical curve the residual is the prime-free aliasing term plus Weil's form (Σ1i) [L]. |
| Π16 Genus function | Sharpened | indep. | Near radical at level `a`: dimension `≥ (2 − η)e^{2a}`, energy `≤ exp(−η²e^{2a}/(300a))`, blind below `2πe^{2a}`; the genus function counts distinct resolved zeros; the genus law `g ≤ (2 + η)e^{2a}` gives almost all zeros simple and isolated [L]. |
| Π17 Window energy (zero power sums) | Sharpened | RH; ≥qRH (log stage) | `𝒵(t) = Σ_{z∈W} m_z e^{t(z − ½)}` over a reflection-closed window; pair sum `= \|𝒵(t)\|²`; pair resolvent = Laplace transform of `\|𝒵\|²`; abscissa = twice the maximal depth (`integrableOn_energy_iff`) [L]. On centered theta windows `𝒵_N(t) = (2πi)⁻¹∮e^{t(z−½)}(−A_N'/A_N)dz`, a source contour integral; the explicit Bessel–Szegő certificate built from `\|𝒵_N(t)\|²` works at the logarithmic stage on all large windows ⇔ inverse-log corridor (`logStage_besselSzego_iff_invLog_corridor`) [L]. Via the explicit formula a unit-window power sum at `x = e^t` is a height-localized prime polynomial of length `≍ x` [D]. Open: subexponential growth on every window at the polynomial stage (RH); on almost all windows at the log stage needs `#{ρ : depth ≥ A/log V} = o(V)`, a log-free near-line density [D]. |

## Γ — selection

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Trivial gauge point | Open | RH | `Θ ≥ ½`, Haar-a.e. `½`; RH ⇔ trivial point typical [L]. |
| Γ2 Prime-set flips | Solved | — | Ordinary or two-adic atomic margin separates every nontrivial prime pattern; every finite flip set has an exact resolution threshold; zero-density twins with prime mass `O((1 + log N)^α)`, `α < 1`, have positive Euler mass; bare zero-density flips have positive divisor means, regularly varying harmonic means, uniform harmonic ratios and the conductor criterion without any density rate [L]. Every prime flip leaves an overlap-independent indefinite residue `F_{ω_S}` (positive on the pole, negative on a trial) while ζ degenerates completely (`F_Λ = 0`) [L]. |
| Γ3 Twin-blindness of soft structure | No-go (complete) | — | Krein index invariant under unitary twists; pointwise-closed classes contain every unitary twist [L]. |
| Γ4 Frobenius at infinity | Open | RH | `σ(ρ) = 1 − ρ̄`; RH ⇔ `σ` trivial ⇔ every Hecke translation a similitude of the collided form ⇔ one constant for the dyadic Hecke defects ⇔ partner saturation of resonant states [L]. Read by the rank-one coefficient `Λ(s)/Λ(s+1)` (Σ19): Mayer boundary, loop-Eisenstein band poles, `SL₂(ℤ)` scattering resonances on `Re s = 1/4` [L/D]. |
| Γ5 Source identification / pre-divisor | Partially solved | RH | Integer counting + full-cone positivity ⇒ `λ = Λ` and RH; pre-divisor sections need zero-independent forcing [L]. |
| Γ6 Boundary sign / coherence | Solved | — | Pole boundary sign separates ζ from size-equivalent twins [L]. |
| Γ7 Affine carrier with Weil dilation | Solved | — | Gluing at a place; subgroup classification [L]. |
| Γ8 Poisson rigidity | Sharpened | RH | Positive tent-self-dual measures with gap are Dirac combs; zero-side positivity = RH [S]. |
| Γ9 Archimedean continuity vs height decay | No-go | — | Continuous dilation against a decaying finite-adelic reading ⇒ `κ = ∞` [L]. |
| Γ10 Function-field indistinguishability | Sharpened | — | Local index walls identical over `𝔽_q(X)`; curve edge `≤ 2g`; Künneth effectivity on every Frobenius window ⇔ unitarity, paid by the Stepanov count; links complete over curves, disconnected over `ℤ`; finite divisor over `ℤ`, none for fakes [L]. |
| Γ11 Pole-blindness of the glue | No-go | — | Simple pole absorbed, double pole costs a square [L]. |
| Γ12 General gauges | Solved | sub | Entrywise-nonnegative gauges only on archimedean characters; twisted Selberg source forces `ω(p) = 1`; harmonic saturation (`normalized harmonic mean → 1`) holds exactly at the Euler gauge [L]. |
| Γ13 Source-uniform extinction | No-go | — | Fails at `3/4 + i` [L]. |
| Γ14 Local counterterm selection | No-go | — | Diagonal counterterms give `Λ` and a flip twin glued index `1` [L]. |
| Γ15 Functional-equation twins | Partially solved | sub | Degree three: any finite prefix of ζ³'s coefficients, its completed FE and principal parts admit arbitrarily many right-hand real zeros [L]. Degree two with positive coefficients, Ramanujan bounds and scalar FE: `m² + 64n²` has a real zero in `(½, 1)`; coefficients nonmultiplicative [L]. Degree-one rigidity under its analytic hypotheses [L]. Euler-product-constrained twins open. |
| Γ16 Selection–sign gap | Sharpened | RH | Every selector (atomic pole index, two-adic probe, Metzler gauge, twisted Selberg source, coupling diagonal, finite-flip edges, star flux, conductor series, harmonic saturation, complete degeneration) is a margin, index, counterterm or structural identity on a partial form; none gives the sign [L]. |
| Γ17 Scattering recentering | Classified (no-go) | — | A rational map real at infinitely many points of the critical parabola is constant; algebraic relations real infinitely often on parabola and `(¼, ∞)` are horizontal lines [L]. |
| Γ18 Divisor-identity selection | Solved (selection) | — | Self-similar star flux iff generalized von Mangoldt; among completely multiplicative twists `Λω` only `ω ≡ 1`; among real twists with summable defect only `Λ` degenerates completely [L]. |
| Γ19 Correspondence algebra over `ℤ` | Sharpened | RH | λ-ring with Adams operators = scaling action; theorem of the square; Rosati positivity ⇔ orbit Hodge index ⇔ every normalized Hecke graph has nonnegative degree; Tate's limit law: Rosati positivity at a cycle ⇔ a naive height (or midpoint-convex log-count) at bounded distance from its integral Rosati form; the golden datum has none [L]. All algebraic identities hold on the golden fake; positivity is the orientation. |

## Bridges

| Bridge | Anchor |
|---|---|
| `κ(K_ζ)` = right zeros = Hodge defect = band poles of `Λ(s)/Λ(s+1)` = zeros moved by `σ`; even; RH ⇔ `κ < 2`; carried by the Hecke orbit of one generic test on one two-prime lattice | HKT, RIT, EHT `FrobeniusAtInfinity`, AOG `TheIndexExit`, ACS `TheHodgeDefectIsCyclic` [L] |
| Complete atomic family = bulk (Jordan count `J(1)#ℙ⁷(ℤ/m)`, zero-blind) + horizon layer (Weil's window form) + couplings; at the critical curve the horizon layer is `κQ(H) + (7J(1)/K)∫e^{−8y}H²` | ADT, AHD [L] |
| Weil's criterion on window tests ⇔ horizon criterion ⇔ single Beurling schedule ⇔ every fixed `K·c*` | AHD `TheHorizonCriterion`, RIT `TheHodgeIndexAtCriticalOverlap`, TM `ReceiverRate` [L] |
| Window Markov form: only prime powers `n ≤ e^A` jump on a window of length `A`; departing jumps pay their creation | AHD `ThePrimesOfAHorizonWindow`, RHTower `WeilMarkovPoleCapacity` [L] |
| `Λ(s)/Λ(s+1)`: loop-Eisenstein band poles = Mayer boundary `2ζ(s)/ζ(s+1)` = `SL₂(ℤ)` scattering coefficient | RIT `TheLoopEisensteinReflectionCarriesTheHodgeDefect`, `GaussMayerBoundaryPositivity` [L]; scattering reading [D] |
| Window index = Wiener–Hopf index = growth of the window energy `\|𝒵(t)\|²`; abscissa = 2·maximal depth; log stage ⇔ corridor; polynomial stage ⇔ RH | CDG `SzegoCollision` [L] |
| Hecke-defect means ↔ near-line density rates (`r < 2c*`, `c* ≤ 2/3`); `o(log U)` ⇔ critical-scale clustering; dyadic-uniform ⇔ RH | CDG [L] |
| `κ(φ_c) = κ + 1` at every place; two primes with bounded translations carry it | AKG [L] |
| boost hyperplane = `v₁^⊥` = Markov = harmonic hyperplane = primitive part | RIT, HWV [L] |
| bounded `K_ζ` ⇔ bounded dense coupling ⇔ no edge ⇔ RH; bounded natural-cone coupling ⇒ RH or polynomial repulsion from maximal width | RIT, ACPL [L] |
| aperture ceiling ↔ near radical `(2 − η)e^{2a}` blind below `2πe^{2a}` ↔ finite divisor `D_a` ↔ genus function | ArithmeticCompensationTheory, RHTower, ACS [L] |
| RH ⇔ HL on the PSD locus; Liouville = HL; no free Lefschetz operator | HWV [L] |
| gcd stratification (graded = positive cone sum of top strata; top = Möbius-signed sum of graded); links disconnected; nerve `χ̃ = −M(N)` | HWV, ADT [L] |
| Mertens function = Redheffer determinant of the pole gluing = nerve Euler characteristic = coprimality signature | ADT, HWV [L] |
| RH ⇔ effectivity with RR and ample axioms; cone RR ⇔ Hodge; orbit RR ⇔ orientation | ACS, AOG [L] |
| Künneth `h¹` = count part + `½δ`; primitive `h¹` over curves = degree of the correspondence; Stepanov pays it over `𝔽_q`; Lévy jump count pays it on prime-free cycles of radius `≤ 1/64` | LST [L] |
| Rosati positivity ⇔ orbit Hodge index ⇔ naive height on the integral Rosati form ⇔ midpoint-convex log-count | AOG, AET, ACP [L] |
| first rung: finite Hodge defect ⇔ bounded heat counts ⇔ bounded collision charges ⇒ `Θ < 1` | AOG `TheIndexExit` [L] |
| partner saturation of resonant states ⇔ `Re ρ = ½` | RHTower `EisensteinResonantPartnerAngle` [L] |
| curve: bounded coupling ⇔ unitary ⇔ Castelnuovo–Severi on the Frobenius span; Künneth effectivity ⇔ unitarity | ACPL, LST [L] |
| centered curve products ↔ Laguerre–Pólya closure ↔ Hankel / Jensen signs | ART [L]; reading [D] |

## Status counts

| Family | Solved | Partially solved | Sharpened | Open | No-go | Classified | Reduced |
|---|---|---|---|---|---|---|---|
| Σ (38) | 6 (Σ1a, Σ1h, Σ10, Σ12, Σ16, Σ24) | 6 (Σ1b, Σ1d, Σ1g, Σ3, Σ6, Σ9) | 5 (Σ1, Σ2, Σ3a, Σ4, Σ17) | 9 (Σ1c, Σ1e, Σ1j, Σ1k, Σ7, Σ8, Σ18, Σ19, Σ20) | 5 (Σ1f, Σ13, Σ14, Σ23, Σ25) | 6 (Σ1i, Σ11, Σ15, Σ21, Σ22, Σ26) | 1 (Σ5 → Π17) |
| Π (24) | 3 (Π1, Π11g, Π13) | 4 (Π3, Π7, Π9, Π12) | 7 (Π4, Π5, Π6, Π8, Π10, Π16, Π17) | 3 (Π2, Π11f, Π11h) | 6 (Π11a–e, Π14) | 1 (Π15) | — |
| Γ (19) | 5 (Γ2, Γ6, Γ7, Γ12, Γ18) | 2 (Γ5, Γ15) | 4 (Γ8, Γ10, Γ16, Γ19) | 2 (Γ1, Γ4) | 5 (Γ3, Γ9, Γ11, Γ13, Γ14) | 1 (Γ17) | — |

Strength of the open walls:
- **RH:** Σ1, Σ2, Σ3 (ascent), Σ3a, Σ6, Σ7, Σ8, Σ17 (dense lattice), Σ18, Σ19, Σ20, Π2, Π4, Π11h,
  Π17 (polynomial stage), Γ1, Γ4, Γ5, Γ8, Γ16, Γ19.
- **≥qRH:** Σ4 (`K_ζ`), Π5 (fixed scale), Π10 (¾ strip), Π17 (log stage on every window).
- **sub:** Σ1b–Σ1e, Σ1g, Σ1j, Σ1k, Σ17 (natural cone), Π3, Π5 (mean `o(log U)`, density rate `≥ 1`), Π7,
  Π9, Π11f, Π11h (fixed degree), Π12, Π17 (almost all windows at log stage), Γ15.
- **indep.:** Π16.
