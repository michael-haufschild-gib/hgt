# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route), `walls-ledger.md` (walls) and
`route-unification-ledger.md` (core problems and route classes). Labels `A*`, `B*`, `S*` refer to
`route-obstacles.md`; wall labels to `walls-ledger.md`. Corpus: `b4bf677c56` with the working tree,
the programme READMEs and the pipeline cards.

Evidence: `[L]` Lean; `[S]` Lean in the working tree or unintegrated; `[P]` complete paper proof,
Lean pending; `[D]` derived here from Lean statements.

## Picture

1. **One even integer on one hyperplane.** Every route reads `κ = #` distinct zeros right of the
   line, on the pole-orthogonal hyperplane `v₁^⊥` [L]. `κ` is even, RH is `κ < 2`, finite `κ` gives
   `Θ < 1` [L]. Glued at any place the index is `κ + 1` [L]. The Hecke orbit of one generic test
   under two primes carries all of `κ` [L].

2. **Edge logic decides which producers can work.** A statement proved without zero information
   holds on every datum sharing that information, so it stops below the edge of the off-line
   members; an integer read at an RH-complete resolution is RH [L/D]. What can cross the edge is a
   statement that holds there by structure: an identity, an inherited polarization, or an integer
   with a structural bound — concretely a count, a trace or a quantized reading (ADT). Every
   finding below is a statement about one of these carriers.

3. **The complete family is a degenerating polarized family (ADT).**
   - The dilation monoid is its monodromy: `c_m(pn) = w_p(m)c_{ℓ_p m}(n)`, one branch per prime,
     commuting lowerings, the pole conductor the unique fixed point, branches meeting only at `∞` [L].
   - After rescaling by `c^β` the family converges, along every schedule below the exponent
     `1/(β+1)` (`1/8` for the tilted spline), to the **Jordan-totient form**
     `J(m) ∝ J_{β+1}(m)/φ(m) = m^β Π_{p∣m} ζ_p(1)/ζ_p(β+1)`: a tensor product of one weight string
     per prime (`[8]_p = #ℙ⁷(𝔽_p)` at the bottom, `p⁷` per deep step), exact uniformly on the
     subthreshold block `m ≤ c/X(ε)` [L/S; product form D]. Fixed packets inherit its positivity [L].
   - The limit is zero-blind; zeros enter at the quantum `1/log N`. The inheritance radius is
     exactly the RH exponent: at every multiple of `(log N)^{1/8}` conductor-Gram positivity is RH
     [L]. There the extension data — the cross-conductor channels, which live in the top coprime
     stratum — are of the size of the margins; what remains is a constant, not an exponent.
   - **The sign of RH is the sign of the second-order term of the degeneration at the critical
     curve** `c⁸ ≍ log N`. This is the constant-factor wall, HL on the positive locus and the top
     stratum, read in one language.

4. **The rough regime and its limits.** Estimates prove positivity inside the inherited regime: all
   vectors to `(log N)^{1/9}` with logarithmic confinement, fixed packets to `(log N)^{1/8}`,
   mid-band packets to `(log N)^{1/4}`, the logarithmic profile to `ε₀·c*` with
   `ε₀ = 1/[103424(8π/3 + 3000)]`, optimal for its budget system [L]. The remaining `c⁹ → c⁸` step
   has a paper plan; the shortcut through terminal-pole orthogonality is refuted, and the surviving
   structure of the prefix–terminal block is rank-one coherent plus a remainder whose off-diagonal
   part is a shifted prime-pair correlation.

5. **One gluing at the pole creates the arithmetic.** The divisibility form on `1..N` is unipotent;
   gluing every vertex to the pole gives Redheffer's matrix with `det = M(N)`, the Euler
   characteristic of the nerve of the star cover; the coprimality form of the top stratum has
   signature `M(N)` [L/S]. RH is half-power growth of this determinant. The glued state carries
   exactly one extra negative square (`κ + 1`) for the same reason [L]. Positivity is never
   semilocal: no `{∞,p}` family carries it, and the archimedean trace carrier's middle operator
   `1 − P − P̂` is negative on time-limited vectors [L/S].

6. **The degree axis has four laws.** Ceiling `μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})`; near radical
   of dimension `≥ (2 − η)e^{2a}` blind below `2πe^{2a}`; its exact size reads the resolved zeros,
   and the genus law forces almost all zeros simple; coercivity off a finite divisor `D_a` [L].
   Each degree is a finite-dimensional problem with `≈ 2e^{2a}` near-null directions decided by
   zeros above `2πe^{2a}`; an isolated pair of depth `δ` at height `γ` is seen only past the
   multiple `≈ (cδ log γ)^{1/δ}` [L].

7. **SC is a face of the complete family.** Every finite rational correlation Gram is a limit of
   literal complete-matrix compressions at a family-dependent fixed multiple; positivity on the
   pole hyperplane bounds each compression's index by one, so RH ⇔ eventual pole-hyperplane
   positivity of the complete matrix at every fixed critical multiple [L]. No universal multiple is
   asserted.

8. **WD is a sectoriality problem on polynomial-size integer data.** Per stabilized window, index
   `0` ⇔ `L²` invertibility of the Wiener–Hopf lift ⇔ outer Szegő factorization ⇔ disk-unit
   sectoriality [L]. Prefixes `≥ c√T` are necessary [L]; unit windows stabilize at the optimal
   prefix `Θ(√m)` with no separation input; at logarithmic resolution `Θ(√m)`-prefix Szegő
   positivity is equivalent to the inverse-logarithmic zero-free corridor, at polynomial resolution
   to RH [P]. The Hecke-defect ladder is closed on `(0, ½)` and an equivalence up to `2/3` [L].

9. **PM has a Selberg-type product.** `D(w,z)D(w,−z) = Π_c Π_{m≥0}(1 − z^{2ℓ(c)}e^{−(w/2+m)L_c})`
   over primitive digit-pair cycles, `L_c` the hyperbolic translation length; absolutely convergent
   for `Re w > 1` near `z = 0` and on the closed unit disc for `Re w > 2` [L]. Geodesic
   multiplicities, the scattering normalization, a faithful zero ↔ event equivalence and a
   resonance-excluding structure are open; the native self-adjoint domain rejects critical zeros as
   well.

10. **Counts.** On prime-free cycles of radius `≤ 1/64` the primitive `h¹` is paid by the
    Lévy–Khintchine jump count of the Gamma factor [L]; the whole prime-free window needs a
    Poincaré inequality for the Lévy form on an interval and the pole signs; past it the count must
    contain the prime comb. Over `𝔽_q` the Stepanov count pays the primitive `h¹` of every
    odd-characteristic hyperelliptic curve [L]. Cones, bidegree counts, fixed rank, definite counts
    and Siegel majorants are excluded; the boost creates the Epstein fakes [L].

11. **Heights.** Weil's correspondence algebra exists over `ℤ` with λ-ring, Rosati involution,
    Lefschetz traces and a free theorem of the square; Rosati positivity ⇔ a naive height (or a
    midpoint-convex log-count) at bounded distance from the integral Rosati form; RH ⇔ every cycle
    has one [L]. The golden fake satisfies every identity and has no naive height [L].

12. **Precision ladders.** One-point: one-sided count ⇔ RH; producers reach the main term [L].
    Conjugate diagonal: Hecke means ↔ near-line density rates; near-line density at every rate
    `r < 1`; clustering ⇔ `o(log U)` [L]. Census: `0.6725`; further gains need the signed pair
    surplus beyond bandwidth one [L].

13. **Selection.** Every prime-set flip is separated; self-similar star flux selects `Λ`;
    functional-equation data of degree three impose no zero-free right half-plane [L]; Frobenius at
    infinity has four RH-equivalent readings and the naive-height form [L].

14. **Approximation by RH-true objects lands in the Laguerre–Pólya class.** The literal
    centered-Euler-product branch is retired; centered curve numerators are bounded by their real
    values, and their limits are Laguerre–Pólya functions, so the route is the rank/degree sign
    problem (Σ6) [L/D].

## 2.1 Obstacles that are just work

| # | Task | Routes served | Why it is work |
|---|---|---|---|
| A1 | Tilted spline `α < 1/9 → 1/8` on all vectors along the paper plan T1–T4 (risk: becomes a prime-pair correlation if the log-smoothing step fails) | HF, SRT, AIP, ACS | proof plan with PNT-level inputs; structure of `NR_PT` identified |
| A2 | Explicit horizons, residual constants, effective growing schedules | HF, SRT, AIP, ACS, RW | constants |
| A3 | Kernel-certified Weil positivity at `½ log 3` and the next prime apertures | RW, EWU, OWU, HF | finite Schur complement of dimension `≈ 2e^{2a}`; numerics proved in the kernel |
| A4 | ADT tools: twisted-weight limits; pure block; growing-block structure with extension data; first-order correction below `1/8` | HF, ACS | explicit asymptotics |
| A5 | Close `[S]`: top self-form, weight strings/tensor/subthreshold laws, Redheffer determinant, semilocal modules, Künneth to `181/500` | HF, RW, MC, ACS | formalization in progress |
| A6 | Prime-successor comparison with the shell payment; combination with the packet identity | HF, AIP, SRT | Mertens law and affine sampling |
| A7 | Quantitative depth law `d₀(c)`; explicit star horizons | HF, ACS | effectivization |
| A8 | Finite-`N` tabulation of the gcd strata | HF | exact identities |
| A9 | Björner wedge decomposition of the squarefree complex | MC, HF | classical topology; combinatorics formalized |
| A10 | Formalize separation-free polynomial-prefix stabilization and the corridor bridge | WD | complete paper proof |
| A11 | Flow threshold `Λ_X` from sub-Weyl profiles | LA, WD | existing machinery |
| A12 | `ΔO = o(log T)` ⇒ density one ⇒ Lindelöf | WD, SRT | composition |
| A13 | Computable stopping prefix | WD | kernel-certified intervals |
| A14 | Count reading of the whole prime-free window (Lévy Poincaré inequality; pole signs) | ACS, HF | target known by estimates |
| A15 | Künneth primitive `h¹` on the finite divisor at small degree | ACS, HF | calibration |
| A16 | Mixed-jet recovery `≥ 3` primes; explicit main-term producer | WL, ACS | algebra; rounding |
| A17 | Census: `S_cos(λ)`, `λ ≤ 1`; odd-stabilizer calibration | census, ACS | classical pair estimates |
| A18 | Voronoi summation; Zwegers' indefinite theta | ACS, HF | classical theorems |
| A19 | `𝔽_q(X)` calibration; ADT limits over `𝔽_q(T)` and of the fakes | SC, ACS, HF | curve theory proved |
| A20 | `𝔽₃` elliptic loop chain | ACS | foundations formalized; assembly remains |
| A21 | Mayer–Selberg identification: geodesic multiplicities, `Z_Selberg(w/2)`, scattering continuation and normalization | PM | known mathematics |
| A22 | Sharp unit-disk boundary of the Mayer logarithm; simple zero at `w = 2`, `z = 1` | PM | mechanism in hand |
| A23 | Lax–Phillips scattering for the modular surface | PM | classical |
| A24 | Theta Hankel rank 8 strict; ranks 9–10 | TH | finite computation |
| A25 | Hausdorff shifts, Jensen horizons, two-grid degrees, Toeplitz minors beyond PF₃₇ | PA, LA, HCF | effectivization |
| A26 | Nine atom-dominated collar moduli | ACT | finite case analysis |
| A27 | Mixed Schur debit; first-prime/coarse/polar costs | AIP, CHMD | fixed-dimensional estimates |
| A28 | Logarithmic two-point Chowla | MC | Tao's theorem |
| A29 | ADT calibration over `𝔽_q(T)`; limits of the fakes | HF, ACS | function-field theory |
| A30 | Cattani–Kaplan–Schmid theory as a formal model | HF, ADT | classical theorems |

## 2.2 Open mathematical obstacles

Strength: **RH**; **≥qRH**; **LH**; **sub**; **indep.**; **method**.

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Positivity at every fixed multiple `K·c*` / pole-hyperplane positivity at every fixed critical multiple | RH; fixed `K` sub | HF, SRT, AIP, ACT, ACS, SC, RW, EWU, OWU, CHMD |
| B2 | Second-order term of the degeneration at the critical curve | RH (all `K`); sub (one `K`) | HF, SRT, AIP, ACS, ADT |
| B3 | Critical-scale identification of the fixed-`K` limit form | sub | HF, SRT, AIP, ACS, SC |
| B4 | Joint shell–pole / Gamma-graph payment on growing packets | sub | HF, SRT, AIP, CHMD |
| B5 | Low-conductor spans; conductors above `√N` | sub | HF, SRT, AIP, SC |
| B6 | Exact SOS for the dilation form on one two-prime lattice | RH | HF, SC, ACS, RIT |
| B7 | Cluster exclusion below the Landau height | sub | RW, SRT |
| B8 | One universal fixed multiple exhausting the full index | method | SRT, HF |
| B9 | HL on the positive locus | RH | HF, TG, SC, WD |
| B10 | Top coprime stratum: sum–product inequality on conductor packets | RH | HF, ACS, ADT |
| B11 | Cross-tower spectral gap through the archimedean channel | method; uniform RH | HF, AIP |
| B12 | Loop-Eisenstein band-pole noncancellation | RH | HF, ACS, SC |
| B13 | Arithmetic index ceiling uniform in resolution | ≥qRH; RH (tensor) | CHMD, SRT, WD, SC |
| B14 | Zero–one law (no finite nonzero index) | sub | SC, HF, ACS |
| B15 | Subcritical heat count | sub | WD, LA, SC-heat |
| B16 | Pointwise heat horizon `< ½` | ≥qRH | WD, LA |
| B17 | Source-defined sectorial multiplier on every `Θ(√m)`-prefix window | ≥qRH (log resolution); RH (polynomial resolution) | WD, TG, SC-heat |
| B18 | `O(T) = o(N(T))` | sub | WD |
| B19 | `ΔO = o(log T)` | LH | WD |
| B44 | Source-faithful realization | RH | RN, PTR, W1C |
| B45 | Odd-sector bound `R ≤ ½` | RH | CHMD, TT |
| B46 | All-rank / all-degree signs (Laguerre–Pólya property) | RH | TH, LA, HCF, PA, GTA; ART |
| B47 | Lower bounds for scheduled prime energies | RH | FU, CFC, RP, SZ, LI, FEL, EGC |
| B49 | The threshold block `m ≍ c` (the `1/9 → 1/8` gap of the whole space) | sub | HF, ADT |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B20 | Hecke defect at doubly-log scale | sub | WD |
| B21 | Log-free near-line density at rate `r ≥ 1` | sub | WD, census |
| B22 | Critical-scale clustering ⇔ dyadic mean `o(log U)` | sub | WD, census |
| B23 | Pointwise `E = O(1)` | ≥qRH | WD |
| B24 | One constant over dyadic scales | RH | WD |
| B25 | Arithmetic input beyond counts + linear explicit formula | method | WD, HEF |
| B26 | Count-valued primitive `h¹` past the prime-free window / naive height on correspondences | RH; fixed degree sub | ACS, HF, ADT, IRK |
| B27 | Genus law (⇒ almost all zeros simple) | indep. | ACS, RW |
| B28 | Logarithmic Serre duality of the split surface (Voronoi) | sub | ACS, HF, ADT |
| B29 | `ε`-uniform producer | sub / RH | WL |
| B30 | Square-root source input; half-power Redheffer determinant | RH | WL, MC, PBM, RB, JAS, CTF |
| B31 | Near-band cyclotomic energy | ≥qRH | MC |
| B32 | Signed prime-pair surplus beyond bandwidth one | sub | census, ACS |
| B33 | First Epstein real zero on the boost line `0 < \|u\| ≤ 1` | sub | ACS |
| B34 | Bounded coupling on one two-prime lattice; glued index `≤ 1` | RH | SC, ACS |
| B35 | Cone coupling ⇒ RH (pure implication); unattained width | sub; ≥qRH | SC, ACS, PM |
| B36 | Finite-sieve Hodge positivity → global inter-tower form | RH | SC |
| B41 | Hermitian structure on the Mayer operator; zero-free region; scattering gap | sub | PM |
| B43 | Escape: two-prime laws, gauge mass, tightness; cofinal energy | sub/≥qRH; RH | PM |

### Γ — selection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B37 | Selection at the trivial gauge point | RH | MC, BAG, XN |
| B38 | Frobenius at infinity as an operator (Rosati positivity / naive height) | RH | HF, ACS, PL, CDG, EHT |
| B39 | Unimodular gauges, FE twins with Euler product, zero-density twins | sub | HF, ACS, AIP, SRT, SC |
| B40 | Faithful ζ-zero ↔ scattering-event equivalence | method | PM |
| B42 | Off-line resonance exclusion (partner saturation) | RH | PM |
| B48 | Pre-divisor forcing | RH | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |

## 2.3 The three questions to answer next

The edge logic admits three carriers: an identity or inherited polarization, a count, and an integer
with a structural bound. The corpus has located each carrier's open point exactly. The three
questions are those points.

**Q1. What is the second-order term of the degenerating Weil family at the critical curve?**

In hand [L/S]: the Jordan-totient limit and its weight strings and tensor law; inheritance exactly
to `1/8`; uniform exactness on the subthreshold block; the relative cross-conductor bound
`O((c⁸(1 + log c)²(log N)^{1/k}/log N)²)`; mean-square residuals `o(ΣE_e²)` past `1/8`;
pole-hyperplane positivity at every fixed multiple ⇔ RH; the extension data live in the top coprime
stratum; the arithmetic of `μ` is one rank-one gluing at the pole.

The question: along `c⁸ = K log N`, compute the limit of the rescaled extension data
`c⁷(⟨W r_e, r_{e′}⟩ − E_e⟨r_e, r_{e′}⟩)` on fixed packets. Which arithmetic kernel is it — is it
Weil's form on the radius-`½ log K` tests synthesized by one block, plus a coercive conductor part?
How do the zeros enter it, and is it polarized by the dilation monodromy (an SL₂-orbit-type
inheritance through the critical curve)?

Why: this is the single place where the complete-family routes, SC's glued index, HL, the top
stratum and the constant-factor wall meet [D]. A closed form turns each fixed `K` into an explicit
positivity problem (certifiable at small `K` with A3), and decides whether degeneration theory
carries a positivity mechanism of its own or only an inventory.

**Q2. Is Weil's primitive form a count past the prime-free window?**

In hand [L]: on prime-free cycles the primitive `h¹` is the Lévy–Khintchine jump count of the Gamma
factor plus `Ω(0)‖f‖²` and a pole term, and the count pays both to radius `1/64`; the Markov form
puts the prime atoms `Λ(n)/√n δ_{log n}` into the same jump measure, against the creation potential
`V_N`; over `𝔽_q` the Stepanov count pays the primitive `h¹`; Tate's limit law makes the target a
naive height on `ℤ[ℚ_{>0}^×]` at bounded distance from the Rosati form.

The question in three steps: (1) the whole prime-free window by a Lévy Poincaré inequality on an
interval and the pole signs (A14); (2) the first Hecke graph: on primitive tests of radius
`½ log 2 < a ≤ ½ log 3` an identity `W = (Lévy jump count) + (count attached to T₂) + (squares)`
(B26 at fixed degree); (3) the decisive negative form: classify counts with a Poisson-type duality
that read the test component, and show none has `h¹ ≥ 0` on the finite divisor at `½ log 3` if that
is the truth.

Why: it is the only carrier that escapes the doubly exponential ceiling, it is Weil's and
Stepanov's producer, it has a working foothold at small radius over `ℤ` and a full proof over
`𝔽_q`, and it supplies the selection (the naive height is Frobenius at infinity) at the same time.

**Q3. Can the integer-theta collision loop be made sectorial by a source-defined multiplier?**

In hand [L/P]: index `0` ⇔ Wiener–Hopf invertibility ⇔ outer Szegő factorization ⇔ disk-unit
sectoriality; unit windows stabilize at prefix `Θ(√m)` with no separation input; at logarithmic
resolution `Θ(√m)`-prefix Szegő positivity ⇔ inverse-logarithmic zero-free corridor, at polynomial
resolution ⇔ RH; arithmetic reality of the loop symbol.

The question: for the `Θ(√m)`-prefix loop `Λ_{T,n,N}` of each window, construct from the theta
source a nonvanishing disk multiplier `F` with `Re(F·Λ) > 0` on the circle — first at logarithmic
resolution on a positive proportion of windows, then on all windows, then at polynomial resolution.

Why: it is the only reduction of RH to an `O(1)`-precision sign condition on finitely many
computable numbers per window, and its prefix scale is settled on paper. It is the integer carrier
with a candidate structural bound.

## 2.4 A wildly different route

**Verdict: we see none that escapes the three walls.**

Why: every RH-equivalent statement the corpus has met reads the one integer `κ`, and the walls are
walls on producers: estimates stop at the edge; soft structure is twin-blind; local and semilocal
pieces and trace carriers of the shape `1 − P − P̂` carry no positivity; deformation is free; tensor
amplification is all-or-nothing; finite realizations fail; approximation by RH-true objects lands
in the Laguerre–Pólya class. A route far from the current ones needs a producer outside these.
The distant directions all fall back onto a known wall:

| Direction | Producer | Wall it falls on |
|---|---|---|
| Centered curve products (Weil/Honda–Tate numerators converging to `ξ`) | approximation + Hurwitz | literal Euler products cannot converge on a fixed half-plane; centered numerators converge iff the Laguerre–Pólya moment property of `ξ` at `½` holds (Σ6); Katz–Sarnak equidistribution gives flexibility, not selection |
| Exact extremal certificates from modular forms (Fourier-interpolation magic functions for the Weil LP) | exact dual certificate | no attained sharp extremizer at finite aperture (near radical, doubly exponential floor); in the limit the extremal measure is the zero divisor, whose crystalline rigidity needs zero-side positivity (Γ8) |
| Effective horocycle equidistribution (Zagier: rate `y^{3/4−ε}` ⇔ RH) by non-spectral dynamics | Margulis functions, mixing | the error term is the Eisenstein constant term at `ρ/2`: square-root precision (Π); the modular surface selects ζ as in PM |
| Iwasawa-type realization (`p`-adic zeros as eigenvalues on Selmer modules) | integral operator realization | no bridge from `p`-adic zeros to complex zeros |
| Discrete Morse theory on the squarefree complex | combinatorial cancellation | the complex is a wedge of `≈ (2/π²)N` spheres of mixed dimension; Morse inequalities forbid fewer critical cells, so a Mertens bound needs cancellation between dimensions (Π1) |
| Böttcher / period rigidity (ARGON-3 B) | algebraic independence | ζ and all positive algebraic dilates are differentially independent over the theta–Gamma field; no finite relation exists to rigidify |

What would make a route genuinely different: a canonical object built from `ℤ` alone whose
structure theorem (not an inequality) forces `κ = 0`, as the Hodge index theorem on `C × C` does over
`𝔽_q`. The corpus has the algebra of that object and, in ADT, the first piece of its geometry (the
limiting polarized structure), but not the object. That is the field of 2.7, not a separate route.

## 2.5 Breakthrough questions below RH and quasi-RH

### 2.5.1 Whole programme — a count pays the first prime
**Question.** Prove Weil positivity on primitive tests of radius `a ≤ ½ log 3` by an identity whose
terms are cardinalities, Lévy jump counts or manifest squares: the archimedean jump count, a count
attached to the graph of `T₂`, and the pole term (Q2, steps 1–2).
- **Below RH.** It is a finite-aperture statement already known by estimates (`181/500`) and a
  certified computation at `½ log 3` (A3).
- **Advance.** The first place over `ℤ` where a prime is paid by a count instead of an estimate: a
  naive height on the first nontrivial correspondences. It either finds the count or isolates the
  exact obstruction that blocks every count at the first prime, and it calibrates B26.

### 2.5.2 Route PM — a zero-free region from the transfer operator
**Question.** With the Mayer–Selberg identification (A21), construct a Hermitian (Lewis–Zagier /
Krein) structure on eigenfunctions of the transfer operator near `Re w = 1`, scattering sector
included, that separates cusp-form events on `Re w = 1` from scattering events, and derive
`ζ(1 + it) ≠ 0` and a zero-free region near `Re s = 1` (B41, Mayer 3–5).
- **Below RH.** A classical-type zero-free region.
- **Advance.** PM's positivity holds for real `w` and on the closed unit disc for `Re w > 2`, where
  the Euler product converges; the native self-adjoint domain cannot separate critical from
  off-line events. A Hermitian structure that does would be the first statement about ζ zeros from
  PM's own operator, with selection supplied by the modular surface, and the template for 2.6.2.

### 2.5.3 Route WD — critical-scale clustering
**Question.** Prove that 100% of the zeros up to `V` lie within `κ/log V` of the line for every
`κ > 0`; equivalently, dyadic means of the unit-window Hecke defect are `o(log U)` at one
`c < 1/2` (B22). Stepping stone: log-free near-line density at rate `r ≥ 1`, which extends the
`O(log U)` gate into `½ ≤ c < 2/3` (B21).
- **Below RH.** It implies neither Lindelöf nor a zero-free region; the pointwise and logarithmic-
  resolution Szegő statements on WD's ladder are at least qRH, so this mean statement is the route's
  sub-qRH breakthrough.
- **Advance.** The `O(log U)` gate is closed on `(0, ½)`, the almost-all corridor is
  `(1 + ε)loglog T/log T`, the density ladder is an equivalence up to `2/3` [L]; clustering is the
  one remaining mean statement. The input must be a mollifier gain tending to zero on near-line
  shells.

### 2.5.4 Route HF — the second-order term at one multiple
**Question.** For one explicit `K₀` with `½ log K₀ − O(1) > ½ log 2`, compute the limit of the
rescaled extension data at `c = K₀(log N)^{1/8}` (or `K₀·c*` for the logarithmic profile) on fixed
packets and identify the fixed-`K₀` limit form as Weil's form at radius `½ log K₀` plus a coercive
conductor part (B2 at one `K`, B3; Q1). With A3 at that radius this gives eventual positivity of the
complete family at one multiple that sees the first prime.
- **Below RH.** A finite-aperture statement.
- **Advance.** Every proved positivity of the family lies in the inherited regime; one multiple at
  the critical curve is the first exact payment where the extension data are of the order of the
  limit, and it tells ADT whether its language decides signs or only describes them.

## 2.6 Breakthrough questions that open the path to RH

### 2.6.1 Whole programme — a naive height on the correspondences of the scaling surface
**Question.** Construct a function `h` on `ℤ[ℚ_{>0}^×]`, nonnegative because it is a cardinality or
a log-count, with `|h(ξ) − τ_x(ξ ⋆ ξ′)| ≤ C_x` for every cycle `x` (B26, B38).
- **Why it opens the path.** Tate's limit law turns such a height into Rosati positivity at `x`;
  Rosati positivity at every cycle is the orbit Hodge index, which is RH [L].
- Over `𝔽_q` the function is the degree of a graph, the order of a kernel or the Stepanov count
  [L]; over `ℤ` the first instance is the Lévy jump count on prime-free cycles [L]. The finite
  divisor and the near radical say where the count has work to do.

### 2.6.2 Route PM — partner saturation from a Krein-definite structure
**Question.** Extend 2.5.2 to the strip `½ < Re w < 1`: make the transfer operator J-self-adjoint
with `J` definite on the resonant sector, so that eigenvalue events occur only at `Re w = ½`
(Mayer 6, B42), with the faithful zero ↔ event equivalence (B40) as the bridge.
- **Why it opens the path.** Partner saturation of resonant states is RH [L]; definiteness forces
  it. The structure must come from the operator: no algebraic map takes the critical parabola to a
  real spectrum [L], and the native domain rejects critical zeros too.

### 2.6.3 Route WD — a sectorial multiplier at polynomial resolution
**Question.** For every unit window, at resolution `S_m = 60m` and prefix `Θ(√m)`, construct from
finitely many theta values a nonvanishing disk multiplier `F` with `Re(F·Λ) > 0` on the circle
(B17).
- **Why it opens the path.** This sectoriality on every window is equivalent to RH [P]. It is an
  `O(1)`-precision sign condition with polynomial-size data and no separation input; at logarithmic
  resolution the same construction is equivalent to the inverse-logarithmic zero-free corridor
  (≥qRH) [P], a natural first target.

### 2.6.4 Route HF — inheritance through the critical curve
**Question.** Prove that the extension data at every multiple of the critical exponent are paid —
the top gcd stratum (successor pairs and archimedean overlaps of consecutive atoms) bounded by the
root defect, the coprime successor gap and the star depth margins — so that the limiting
polarization is inherited through the critical curve (B2, B9, B10).
- **Why it opens the path.** Below `1/8` inheritance is a theorem; at the critical curve it is RH
  [L]. The gcd stratification is exact, deep stars are positive, positivity descends, and the only
  unpaid coupling sits in the top stratum, reached only through the archimedean place [L].
- Its restriction to one two-prime lattice is the SOS identity B6; over a curve it is
  Castelnuovo–Severi on the Frobenius span [L]. The missing tool is a cross-tower gap through the
  archimedean channel (B11) or an SL₂-orbit theorem for the dilation monodromy.

## 2.7 Does closing RH need a new field?

**Assessment: yes, and ADT is its first construction.** The field is an arithmetic Hodge theory of
degenerations of the scaling surface: a degenerating polarized family with the dilation semigroup
as monodromy, whose positivity is carried through the critical curve by a count (a naive height on
correspondences), an inherited polarization, or an integer with a structural bound.

*Why.* Over `𝔽_q` the three proofs of RH rest on objects `ℤ` lacks: intersection numbers that are
counts (Weil), auxiliary sections whose vanishing is counted (Stepanov–Bombieri), tensor powers of
a realization with Euler products (Deligne). Over `ℤ` the algebra exists (correspondences, λ-ring,
theorem of the square) and Tate's limit law names the missing input (a naive height); integer
producers reach the main term, never the square root; tensor amplification is all-or-nothing. The
other producers are excluded by proved laws (edge logic, ceiling, near radical, free deformation,
margin selectors, semilocal and trace no-gos, Laguerre–Pólya closure).

*What ADT has built [L/S].*
- The dictionary to Hodge theory of degenerations: parameter = resolution `(c, N)`; monodromy =
  dilation, valuation lowering; weight filtration = conductor towers; naive limit degenerates;
  rescaled limit = Jordan-totient form; polarized graded pieces `J(m) > 0`; product law = tensor
  law; extension data = cross-conductor channels; nilpotent-orbit theorem = convergence below
  `1/8`; distance to the orbit = relative residual `≍ c^{β+1}/log N`; the SL₂ of the pole blind on
  `v₁^⊥`; the one negative square = the pole gluing (Redheffer, `κ + 1`); function fields = finite
  monodromy, detection by window `2g`.
- The inheritance radius exactly at the RH exponent; the gluing determinant; the traps (zero-blind
  limits, lowerings transport rather than create, trace carriers with `1 − P − P̂` are not
  positivity).

*What remains of the field.*
- Its SL₂-orbit theorem: the second-order term at the critical curve and its polarization (Q1).
- Its count: a section theory whose primitive `h¹` is a cardinality or log-count past the
  prime-free window, on lattices whose rank grows with the class, with a logarithmic Serre duality
  for the split surface (Voronoi as duality of the cone count) (Q2, B26, B28).
- Its gluing theorem: one negative square at the pole and an exact payment of the top stratum
  through the archimedean channel (B10, B11).
- Its integer: the window index with a structural bound (Q3).
- Its calibrations: rescaled limits over `𝔽_q(T)`, the limiting structure of the fakes, twisted
  weights (A4, A19, A29).

*Criteria it must meet.*
1. `h⁰` from arithmetic counts; `h¹ ≥ 0` because it is a dimension, a cardinality (naive height) or
   a log-count (midpoint convexity).
2. An RR identity at every degree by a Poisson-type duality on lattices of growing rank; the split
   duality completed logarithmically.
3. Primitive `h¹` of a test class `= ½W(f, f)`; for graph classes of correctors a height equal to
   the Lefschetz trace up to bounded error.
4. A degeneration theory whose rescaled limit is the Jordan-totient polarization and whose
   second-order term is polarized at the critical curve.
5. Calibrations: over curves `deg(m − nF)`, `N₁`, Stepanov, Künneth effectivity ⇔ unitarity, finite
   monodromy; on prime-free cycles the Lévy jump count of the Gamma factor; its genus function the
   Shannon number plus the resolved-zero defect.
6. It avoids the proved no-gos: cones, bidegree counts, fixed rank, definite counts, Siegel
   majorants at a fixed boost, ordinary Poisson pairs for the isotropic count, semilocal positive
   carriers, trace carriers of the shape `1 − P − P̂`, separable gluing, free deformation.
7. Selection: it fails for the golden fake (no finite divisor, no naive height), prime flips and
   Epstein lattices beyond the self-dual point, and reproduces Weil and Stepanov over `𝔽_q`.
8. Gluing: global, one negative square at the pole, distinct primes coupled through `∞`.
9. Consistency with quantization: the defect it forces to zero is the window index.

*Questions it must answer.*
- What is the second-order term at the critical curve, and which structure polarizes it?
- What set does `τ_x(ξ ⋆ ξ′)` count, up to a bounded error? What are Stepanov's auxiliary sections
  on the scaling surface?
- How do the prime atoms of the jump measure enter a count, and what pays the creation potential
  `−2Σ Λ(n)/√n`?
- What lattice carries the sections of a class of degree `a` (rank `≈ e^{2a}`), with what metric
  (the Gamma factor as Gaussian and as Lévy measure)?
- What is the logarithmic completion of the isotropic count (Voronoi), and does it commute with
  boost averaging?
- Why `ζ` and not an Epstein function: the boost-equivariant part of the split count is `ζ ⊗ ζ`; the
  self-dual point is the only real-zero-free lattice of the boost line among those classified.

*Tools it aims to develop.* Nilpotent-orbit and SL₂-orbit theorems (Schmid, Cattani–Kaplan–Schmid);
Néron–Tate theory on `ℤ[ℚ_{>0}^×]`; Arakelov `h⁰` (van der Geer–Schoof, Bost) on growing-rank
lattices; Zwegers–Vignéras indefinite theta and Voronoi summation; Lévy–Khintchine and Dirichlet
forms on intervals; Slepian / Landau–Widom with resolution corrections; Wiener–Hopf / Szegő
factorization; λ-rings and Adams operations; Stepanov's method; function-field calibration
(curve windows, elliptic adeles over `𝔽₃`).

*Objects, language, mechanisms.*
- Objects: scaling surface; classes `aH + bV + f`; correspondences `ξ`; normalized graphs; Rosati
  involution; naive heights; section lattices `Λ_a`; `h⁰, h¹, h²`; genus function; finite divisor;
  near radical; degenerating family `W_{c,N}`; monodromy; weight strings; Jordan form; extension
  data; pole gluing; window index.
- Mechanism A (count): naive height ⇒ Tate limit `≥ 0` ⇒ Rosati positivity ⇒ orbit Hodge index ⇒ RH.
- Mechanism B (degeneration): polarized second-order term ⇒ inheritance through the critical curve
  ⇒ HL on the positive locus ⇒ RH.
- Mechanism C (integer): source-defined sectorial multiplier ⇒ window index `0` everywhere ⇒ RH.

No corpus result shows that the field closes RH. Its first tests are 2.5.1 and 2.5.4, where the
answer is not obstructed by zeros.
