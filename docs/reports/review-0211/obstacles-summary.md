# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route), `walls-ledger.md` (walls) and
`route-unification-ledger.md` (core problems and route classes). Labels `A*`, `B*`, `S*` refer to
`route-obstacles.md`; wall labels to `walls-ledger.md`. Corpus: `2605d92e2b` with the working tree.

Evidence: `[L]` Lean; `[S]` Lean in the working tree or not integrated; `[P]` complete paper proof,
Lean pending; `[D]` derived here from Lean statements.

## Picture

1. **One even integer on one hyperplane.** Every route reads `κ = #` distinct zeros right of the
   line, on `v₁^⊥` [L]. `κ` is even, RH is `κ < 2`, finite `κ` gives `Θ < 1`; glued at any place the
   index is `κ + 1`; the Hecke orbit of one generic test under two primes carries all of `κ` [L].

2. **Edge logic decides which producers can work.** A statement proved without zero information
   holds on every datum sharing that information and stops below the edge of the off-line members.
   What crosses the edge holds there by structure: an identity, an inherited polarization, or an
   integer with a structural bound [L/D].

3. **The complete family is Weil's window form plus a count.** The complete atomic Weil family
   degenerates along the resolution axis (ADT, AHD) [L]:
   - its **bulk** (fixed conductor packets, and the growing subthreshold block below `1/8`) converges
     after rescaling to the Jordan form `J(m) = J(1)·#ℙ⁷(ℤ/m)` — the point count of projective
     7-space over `ℤ/m`; weight strings are Hensel towers, the tensor law is the Chinese remainder
     theorem, the monodromy is eventually idempotent; a zero enters the bulk only through a pole
     weight of positive real part, so the bulk is positive, zero-blind and selects nothing;
   - its **horizon layer** (blocks `h(log(n/N))/√n`) is, divided by the overlap, Weil's form `κQ(H)` of
     the synthesized window test `H = e^{y/2}h` past the critical curve, and
     `κQ(H) + (7J(1)/K)∫e^{−8y}H²` at `c⁸/log N → K`; the extra term is the dilation derivative of the
     bulk, prime-free and positive.
   So the constant-factor wall, the second-order term of the degeneration, the receiver scale and the
   glued index are one statement: **Weil positivity of window tests of every length** (the horizon
   criterion; the single Beurling schedule `2L(log L)²`; every fixed `K·c*`) [L]. The degeneration is a
   complete dictionary; it does not produce a sign.

4. **The window Markov form.** On a window of length `A` Weil's form is
   `(Ω(0) − 2Σ_{n≤e^A}Λ(n)/√n)‖H‖² + J_arch(H) + Σ_{n≤e^A}Λ(n)n^{−½}‖H − H(·+log n)‖² + pole(H)`:
   only the prime powers `n ≤ e^A` jump; jumps leaving the window pay exactly their creation [L/D].
   Positivity is known through window length `0.724` (radius `181/500`), past the first prime
   `log 2`; the `{∞,2}` trace identity is exact through `log 3` [L].

5. **The rough regime and its join.** All vectors are positive to `(log N)^{1/9}`. Below `1/8` the
   growing subthreshold block, the mid-band (to `1/4`), and the polynomial-conductor complement with
   its far reserve are coercive [L]; what remains of the whole-space `1/8` is the band–far cross and
   the threshold block `e ≍ c`. General compact profiles (Fourier zeros allowed) are positive on
   polynomial spans to `(log log N)^{1/4}` and on almost-polynomial spans past `log log N` [L/S]; the
   logarithmic profile is positive to `ε₀·c*` [L].

6. **One gluing at the pole creates the arithmetic.** Redheffer `det = M(N)` = nerve Euler
   characteristic = coprimality signature; graded energies are positive cone sums of top-stratum
   energies and the inverse is Möbius-signed, so graded positivity never reaches the top stratum [L].
   Positivity is never semilocal or a trace of a positive operator [L].

7. **The window integer is a zero power sum.** Per stabilized window, index `0` ⇔ Wiener–Hopf
   invertibility ⇔ outer Szegő factorization; the canonical multiplier exists whenever any does and is
   determined by the window energy `|Σ_{z∈W} m_z e^{t(z−½)}|²`, whose Laplace abscissa is twice the
   maximal depth. Log stage ⇔ inverse-log corridor; polynomial stage ⇔ RH; the 9-way door opener and
   separation-free `Θ(√m)` stabilization are in Lean [L]. WD is a precision problem on
   windowed zero power sums.

8. **One function carries Frobenius at infinity.** `Λ(s)/Λ(s+1)` has band poles exactly at the Hodge
   defect, is the Gauss–Mayer boundary `2ζ(s)/ζ(s+1)`, and is the scattering coefficient of
   `SL₂(ℤ)\ℍ` [L/D]. PM realizes ζ's divisor faithfully in a channel of a nuclear operator whose
   determinant is the geodesic Euler product; its boundary slope has nonnegative coefficients
   `(1 − 1/n)Λ(n)` and gives the classical zero-free region [L]. Universal contraction fails below
   `Re w = 1`; the scattering-core energy is positive at every zero, on or off the line [L].

9. **Counts and heights.** On prime-free cycles of radius `≤ 1/64` the primitive `h¹` is the Lévy jump
   count of the Gamma factor; over `𝔽_q` the Stepanov count pays it; Rosati positivity ⇔ a naive
   height at bounded distance from the integral Rosati form; cones, bidegree, fixed-rank, definite and
   Siegel counts are excluded [L].

10. **Precision ladders.** One-point: one-sided count ⇔ RH; producers reach the main term.
    Conjugate diagonal: Hecke means ↔ near-line density rates, rate `r < 1` holds, clustering ⇔
    `o(log U)`. Census: `0.6725`; further gains need the signed pair surplus beyond bandwidth one [L].

11. **Selection is closed for flips.** Every prime-set flip is separated at every density (zero density
    without rate included); only `Λ` degenerates completely; harmonic saturation holds only at the
    Euler gauge; degree-three and positive degree-two FE data admit off-line real zeros [L].

12. **The natural cone needs ζ.** Bounded natural-cone coupling gives RH or polynomial repulsion from
    the maximal width; models with exact spline weights, unit multiplicities, `≤ 12` atoms per unit
    height and unattained width exist [L]. ζ's Riemann–von Mangoldt density is outside these models.

## 2.1 Obstacles that are just work

| # | Task | Routes served | Why it is work |
|---|---|---|---|
| A1 | Join at `1/8`: band–far cross and threshold block `e ≍ c`, with the subthreshold block, mid-band and polynomial complement already coercive (risk: becomes B41 if the shifted prime-pair correlation is needed) | HF, SRT, AIP, ACS | three of the pieces are Lean theorems; Schur and PNT-level inputs |
| A2 | Explicit horizons (`1/9` theorem, logarithmic profile, single Beurling schedule, horizon criterion), residual constants | HF, SRT, AIP, ACS, RW, SC | constants |
| A3 | Kernel-certified Weil positivity at `½ log 3` and the next prime apertures | RW, EWU, OWU, HF, AHD | finite Schur complements on the finite divisor |
| A4 | Strength of one fixed critical multiple: which configurations (isolated pairs, clusters) it excludes; effective window length; equality case `K = K*` | HF, SRT, AHD | analysis of an exact limit form against the visibility law |
| A5 | AHD calibrations: second order over `𝔽_q(T)`; horizon blocks of the fakes; pure block `m ≫ c` | HF, ACS | function-field and model computations |
| A6 | Close `[S]`: terminal-support quadratic loss; explicit-clock coercivity; finite clock products; theta ray; Cayley ladder; first-variation transfer; Poisson rigidity | HF, SC, PM, LI, SZ | formalization in progress |
| A7 | Prime-successor comparison with the shell payment; combination with the packet identity | HF, AIP, SRT | Mertens law and affine sampling |
| A8 | Quantitative depth law, star horizons, gcd-strata tabulation | HF, ACS | effectivization |
| A9 | Björner wedge decomposition of the squarefree complex | MC, HF | classical topology |
| A10 | WD polynomial stage as one statement; computable stopping prefix with certified intervals; flow threshold `Λ_X`; `ΔO` ⇒ density one ⇒ Lindelöf | WD, LA, TG | composition of Lean theorems and classical estimates |
| A11 | Count reading of the whole prime-free window (Lévy Poincaré on an interval; pole signs) | ACS, HF, RW | target known by estimates |
| A12 | Künneth primitive `h¹` on the finite divisor at small degree | ACS, HF | calibration |
| A13 | Mixed-jet recovery `≥ 3` primes; explicit main-term producer | WL, ACS | algebra, rounding |
| A14 | Census: `S_cos(λ)`, `λ ≤ 1`; odd stabilizer; `β = 2` | census, ACS | classical pair estimates |
| A15 | Voronoi summation; Zwegers' indefinite theta | ACS, HF | classical theorems |
| A16 | `𝔽_q(X)` calibration; `𝔽₃` elliptic loop chain | SC, ACS, HF | curve theory proved; assembly |
| A17 | Selberg-zeta normalization of the Mayer product; scattering continuation into `Re(2s) < 1`; Lax–Phillips for `PSL₂(ℤ)\ℍ`; Lewis–Zagier separation of cusp-form events | PM | known mathematics |
| A18 | Operator-native nonvanishing on `Re w = 1` (spectral-Eisenstein template) | PM | known template; risk: may reduce to the Euler product |
| A19 | Natural-cone models with Riemann–von Mangoldt density, or the obstruction | SC, ACS | extension of the sparse-spline construction |
| A20 | Theta Hankel rank 8 strict; ranks 9–10 | TH | finite computation |
| A21 | Hausdorff shifts, Jensen horizons, two-grid degrees, Toeplitz minors beyond PF₃₇ | PA, LA, HCF | effectivization |
| A22 | Nine atom-dominated collar moduli | ACT | finite case analysis |
| A23 | Mixed Schur debit; first-prime/coarse/polar costs | AIP, CHMD | fixed-dimensional estimates |
| A24 | Logarithmic two-point Chowla | MC | Tao's theorem |

## 2.2 Open mathematical obstacles

Strength: **RH**; **≥qRH**; **LH**; **sub**; **indep.**; **method**.

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on window tests of every length (≡ every fixed `K·c*` ≡ horizon criterion ≡ single Beurling schedule ≡ glued index `≤ 1`) | RH; fixed length sub | HF, SRT, AIP, ACT, ACS, SC, RW, EWU, OWU, CHMD, MSC, FEL |
| B2 | Full-space second-order identification at the critical curve; horizon localization of negative directions | sub | HF, SRT, AIP, ACS, SC, AHD |
| B3 | Positivity at one fixed critical multiple (contains dense-cluster exclusion at every height) | sub | HF, SRT, AHD |
| B4 | Joint shell–pole / Gamma-graph payment on growing packets | sub | HF, SRT, AIP, CHMD |
| B5 | Conductors above `√N`; general profiles at super-log-log overlap on the full space | sub | HF, SRT, AIP, SC |
| B6 | Exact SOS for the dilation form on one two-prime lattice | RH | HF, SC, ACS, RIT |
| B7 | Cluster exclusion below the Landau height | sub | RW, SRT |
| B8 | HL on the positive locus | RH | HF, TG, SC |
| B9 | Top coprime stratum: sum–product inequality on conductor packets | RH | HF, ACS, ADT |
| B10 | Cross-tower spectral gap through the archimedean channel | method; uniform RH | HF, AIP |
| B12 | Arithmetic index ceiling uniform in resolution | ≥qRH; RH (tensor) | CHMD, SRT, WD, SC |
| B13 | Zero–one law (no finite nonzero index) | sub | SC, HF, ACS |
| B14 | Heat: subcritical count (sub); horizon `< ½` (≥qRH); `O(T) = o(N(T))` (sub); `ΔO = o(log T)` (LH) | sub / ≥qRH / LH | WD, LA, SC-heat |
| B36 | Source-faithful realization | RH | RN, PTR, W1C |
| B37 | Odd-sector bound `R ≤ ½`; window sinh capacity | RH | CHMD, TT, HF |
| B38 | All-rank / all-degree signs (Laguerre–Pólya) | RH | TH, LA, HCF, PA, GTA; ART |
| B39 | Lower bounds for scheduled prime energies | RH | FU, CFC, RP, SZ, LI, FEL, EGC |
| B41 | Shifted prime-pair correlation for the prefix–terminal remainder (only if A1 needs it) | sub | HF, SRT, AIP |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B15 | Subexponential window energy on every unit window | ≥qRH (log stage); RH (polynomial stage) | WD, TG, SC-heat |
| B16 | Log-free near-line density (log-stage certificate on almost all windows) | sub | WD, census |
| B17 | Near-line density at rate `r ≥ 1`; critical-scale clustering (`o(log U)`) | sub | WD, census |
| B18 | Hecke defect pointwise `O(1)` (≥qRH); doubly-log scale (sub); one dyadic constant (RH) | sub / ≥qRH / RH | WD |
| B19 | Arithmetic input beyond counts + linear explicit formula | method | WD, HEF |
| B20 | Count-valued primitive `h¹` past the prime-free window / naive height on correspondences | RH; fixed degree sub | ACS, HF, ADT, AHD, IRK |
| B21 | Genus law (⇒ almost all zeros simple) | indep. | ACS, RW |
| B22 | Logarithmic Serre duality of the split surface | sub | ACS, HF |
| B23 | `ε`-uniform producer | sub / RH | WL |
| B24 | Square-root source input; half-power Redheffer determinant | RH | WL, MC, PBM, RB, JAS, CTF |
| B25 | Near-band cyclotomic energy | ≥qRH | MC |
| B26 | Signed prime-pair surplus beyond bandwidth one | sub | census, ACS |
| B27 | First Epstein real zero on the boost line | sub | ACS |
| B28 | Bounded coupling on one dense two-prime lattice; glued index `≤ 1` | RH | SC, ACS |
| B29 | Natural cone: exclusion of unattained width for ζ (sub); unattained width excluded outright (≥qRH) | sub / ≥qRH | SC, ACS, PM |
| B30 | Finite-sieve Hodge positivity → global | RH | SC |
| B35 | PM energy/charge control excluding off-line poles with the correction `2ζ(w−1)/(w−1)`; escape | sub / ≥qRH; RH (cofinal) | PM |

### Γ — selection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B11 | Band-pole noncancellation of `Λ(s)/Λ(s+1)` | RH | HF, ACS, SC, PM |
| B31 | Selection at the trivial gauge point | RH | MC, BAG, XN |
| B32 | Frobenius at infinity as an operator (Rosati / naive height; Hecke similitude; partner saturation) | RH | HF, ACS, PL, CDG, EHT |
| B33 | Euler-product FE twins; unimodular gauges | sub | HF, ACS, AIP, SRT, SC |
| B34 | A structure placing the scattering resonances of `SL₂(ℤ)\ℍ` on `Re s = 1/4` (RH); a separated scattering-sector gap with a fixed zero-free strip (≥qRH) | RH / ≥qRH | PM, W1C, PW-B survivor |
| B40 | Pre-divisor forcing | RH | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |

## 2.3 The three questions to answer next

The corpus has located the sign (Weil's window form), the production gap (a count equal to it), and
the precision gap (local zero location per window). The three questions are the three points where
an answer changes what every route does next.

**Q1. Is Weil's window form a count at the first prime?**

In hand [L]: the window Markov form — on a window of length `A` only `n ≤ e^A` jump and departing
jumps pay their creation; the Lévy jump count of the Gamma factor pays the primitive `h¹` on prime-free
cycles of radius `≤ 1/64`; positivity by estimates through window length `0.724 > log 2`; the exact
`{∞,2}` trace with the valuation-shell operator through `log 3`; the first-order structure of the
complete family is the point count `#ℙ⁷(ℤ/m)`; Stepanov pays the primitive `h¹` over `𝔽_q`; Tate's limit
law turns a naive height into Rosati positivity.

The question in three steps: (1) the whole prime-free window `A < log 2` as a count (Lévy Poincaré on an
interval, pole signs — A11); (2) windows `log 2 < A ≤ log 3`: an identity
`Q(H) = (Lévy jump count) + (a count attached to the jump n = 2, the graph of T₂) + (squares)`; (3) if no
such identity exists, the classification of counts with a Poisson-type duality that read the test
component, and the exact obstruction at the first prime.

Why: a count is the only carrier that escapes the doubly exponential ceiling and the near radical; it is
Weil's and Stepanov's producer; the first-order structure of the degeneration is a count and everything
left is Weil's window form; and a naive height supplies selection at the same time.

**Q2. What is the full-space second-order limit of the complete family at the critical curve?**

In hand [L]: the bulk limit (point count, positive pole ledger), the horizon formula and the exact
second order on horizon blocks, the subthreshold block, the polynomial complement and far reserve below
`1/8`, the graded/top Möbius pair, the critical-multiple calculus.

The question: along `c⁸ = K log N`, compute the rescaled limit of the complete form on all vectors —
bulk, horizon, the threshold block `e ≍ c` and the band–far cross — and decide whether every negative
direction is asymptotically a horizon block (horizon localization), or whether a mixed term survives.

Why: it is an identity, so it can cross the edge. If the limit is bulk ⊕ horizon ⊕ positive terms, then
the routes of C1, C2 and C4 are literally Weil's window criterion with explicit positive corrections,
the join A1 follows at the critical curve, and all effort moves to producers (Q1, B6, B37). If a mixed
term survives, it is new zero-carrying structure of the family and a candidate producer.

**Q3. Is there a log-free near-line zero density?**

In hand [L]: window-energy abscissa = twice the maximal depth; log-stage certificate ⇔ inverse-log
corridor on every large window; Hecke-defect dyadic means ⇔ near-line density rates, rate `r < 1` proved;
almost all unit windows zero-free beyond `(1 + ε)loglog T/log T`; right-half squared depth moment
`o(V)`; census `0.6725`.

The question: prove `#{ρ : V ≤ γ ≤ 2V, \|β − ½\| ≥ A/log V} ≤ ε(A)V` with `ε(A) → 0`. Its companion
target in the rate scale is near-line density at rate `r ≥ 1` (B17); neither implies the other.

Why: it is the precision statement where WD, the Hecke defect and the census meet. It would certify the
log-stage Bessel–Szegő condition on almost all unit windows and give 100% critical-scale clustering,
hence dyadic Hecke means `o(log U)` [L equivalence]. It is below quasi-RH (no Lindelöf, no zero-free region) and
belongs to the classical mollifier/zero-detector toolbox, where the obstruction is the `log T` density of
zeros itself.

## 2.4 A wildly different route

**Verdict: no route escapes all three walls. One direction escapes Σ and Π by its mechanism and meets
Γ in a new form: arithmetic measure rigidity of resonant states.**

The distant directions examined fall back on known walls:

| Direction | Producer | Wall it falls on |
|---|---|---|
| Centered curve products / function-field limits | approximation + Hurwitz | Laguerre–Pólya closure (Σ6, Σ26) |
| Exact extremal certificates from modular forms | dual certificate | no attained extremizer at finite aperture; crystalline rigidity needs zero-side positivity (Γ8) |
| Effective horocycle equidistribution | mixing rates | Eisenstein constant term at `ρ/2`: square-root precision (Π) |
| Discrete Morse theory on the squarefree complex | combinatorial cancellation | cancellation between dimensions (Π1) |
| Böttcher / period rigidity | algebraic relations | none exist: ζ and its positive algebraic dilates are differentially independent over the theta–Gamma field |
| Big-Witt / λ-ring geometry over `F₁` | Frobenius lifts at all primes | the λ-ring of correspondences exists; positivity is the orientation (Γ19); the scaling-site pullback fails |
| Deformation / heat flow | noncrossing | crossing-free deformation ⇔ positivity (Σ14) |

**The rigidity direction.** Every route in the corpus produces a sign, a precision or a selector. A
classification theorem is a fourth kind of producer: it identifies an object by structure and entropy,
not by an inequality.

- *Objects.* The scattering resonances of `SL₂(ℤ)\ℍ` sit at `s = ρ/2`; RH is the statement that they lie
  on `Re s = 1/4` (the coefficient `Λ(s)/Λ(s+1)`, Σ19). Each has a resonant state (the Eisenstein series
  at `ρ/2`, truncated); the corpus computes its Hecke data exactly — first moment `p^u + p^{ū}`,
  variance `2(1 − p^{2 Re u})` — and the partner angle `cos² = 4 Re ρ(1 − Re ρ)` [L].
- *Mechanism [D, heuristic].* As `Im ρ → ∞` the resonant states have semiclassical limits on the unit
  tangent bundle; for resonances such limits are expected to be conformal rather than invariant under
  the geodesic flow, with a decay rate fixed by `Re ρ`, and the functional equation pairs the rates of
  `ρ` and `1 − ρ̄` symmetrically about the critical value. Hecke operators act on the limits (the arithmetic input that made
  Lindenstrauss's quantum unique ergodicity work). A rigidity theorem — positive entropy from Hecke
  recurrence, then classification of Hecke-recurrent conformal measures — would pin the rate to the
  symmetric value, i.e. `Re ρ = ½`.
- *Why it is far from every route.* It uses no quadratic form, no window positivity, no prime count at
  any precision, and no index. Its tools (entropy, measure classification for diagonal actions,
  microlocal limits of resonant states) appear nowhere in the corpus.
- *Which wall it meets.* Γ4 in a new form: the entropy argument must see the reflection symmetry
  `ρ ↔ 1 − ρ̄` (the fixed line `Re s = 1/4` of `s ↦ ½ − s̄`), which is not a symmetry of the Laplacian.
  Its own walls: resonant states are not `L²`; their Hecke eigenvalues `p^u + p^{−u}` are non-tempered
  (`|p^u| ≠ 1`), which breaks the positive-entropy step of Bourgain–Lindenstrauss as it stands; and a
  semiclassical limit sees only resonances with `Im ρ → ∞`, so a single off-line zero is invisible —
  the route could at best exclude infinitely many off-line zeros approaching a fixed depth profile,
  which is a Lindelöf-type statement, before reaching RH.

The first test is a sub-RH statement: Hecke-recurrent semiclassical limits of truncated resonant states
along any sequence `ρ_n` with `Re ρ_n → β` have conformal exponent determined by `β`, and positive
entropy. Neither is known; both are statements about objects the corpus already has.

## 2.5 Breakthrough questions below RH and quasi-RH

### 2.5.1 Whole programme — a count pays the first prime
**Question.** Prove Weil positivity on window tests of length `A ≤ log 3` by an identity whose terms are
cardinalities, Lévy jump counts or manifest squares: the archimedean jump count, a count attached to the
jump `n = 2` (the graph of `T₂`), and the pole term (Q1, steps 1–2).
- **Below RH.** It is a finite-aperture statement, known by estimates to length `0.724` and reducible to
  a certified computation to `log 3` (A3).
- **Advance.** The first place over `ℤ` where a prime is paid by a count instead of an estimate: the
  second-order (window) structure of the complete family becomes a count, as its first-order structure
  `#ℙ⁷(ℤ/m)` already is. It either finds the count or isolates the exact obstruction at the first prime,
  and it calibrates B20.

### 2.5.2 Route PM — the operator locates a zero
**Question.** From the Gauss–Mayer operator alone — the geodesic Euler product, the Lewis three-term
relation, the real-`w` derivative cone, the reflection of the period function — prove that infinitely many
scattering resonances of `SL₂(ℤ)\ℍ` lie on `Re s = 1/4` (Hardy's theorem in operator form), then a
positive proportion.
- **Below RH.** Hardy's and Selberg's theorems are classical; the question is their operator-native form.
- **Advance.** PM has a faithful divisor in a channel and the classical zero-free region from its boundary
  coefficients, but ζ enters the determinant as a scalar (`D = A + ζB`) and no statement in the corpus
  says the operator itself places a zero on the line. A location statement derived from the operator's
  real structure is the minimal evidence that PM carries critical-line information beyond the Euler
  product, and it is the template for 2.6.2.

### 2.5.3 Route WD — almost every window is certified
**Question.** Certify the log-stage Bessel–Szegő condition on almost all unit windows: equivalently,
almost all unit windows have every zero within `A/log T` of the line, i.e. a log-free near-line density
`#{ρ : depth ≥ A/log V} ≤ ε(A)V` (Q3). Companion target in the rate scale: near-line density at rate
`r ≥ 1` (B17).
- **Below RH.** It is a density statement: it implies neither Lindelöf nor a zero-free region; the
  per-window log-stage statement is ≥qRH and the polynomial-stage one is RH.
- **Advance.** WD's window machinery is complete (prefix scale, canonical multiplier, energy law, door
  opener); its open input is a classical-type density statement. A positive answer is the first
  unconditional certification of window sectoriality on a full-measure set of heights, and it gives
  `o(log U)` Hecke means.

### 2.5.4 Route HF — the whole space up to the critical exponent
**Question.** Prove positivity of the complete tilted-spline family on all vectors along every schedule
`1 ≤ c ≤ (log N)^α`, `α < 1/8`: join the subthreshold block, the mid-band and the polynomial complement
across the threshold block `e ≍ c` and the band–far cross (A1).
- **Below RH.** It lies in the inherited regime; RH sits at the critical exponent `1/8` itself.
- **Advance.** Estimates would reach exactly the RH exponent on the whole space. Under ¬RH the edge of the
  family would then lie in `[(log N)^{1/8−}, 2(log N)^{1/8+}]` infinitely often: a counterexample to RH is
  pinned to the critical curve, where the second order is Weil's window form (Σ1i). It also decides
  whether the prefix–terminal remainder needs the shifted prime-pair correlation (B41).

## 2.6 Breakthrough questions that open the path to RH

### 2.6.1 Whole programme — a count equal to Weil's window form
**Question.** Construct, for every window length `A`, a count `h_A` (a cardinality, a lattice-point count,
or a log-count) on window tests with `h_A(H) = ½Q(H)` up to manifest squares — equivalently a naive height
`h` on `ℤ[ℚ_{>0}^×]`, nonnegative because it counts, with `\|h(ξ) − τ_x(ξ ⋆ ξ′)\| ≤ C_x` for every cycle
(B20, B32).
- **Why it opens the path.** Tate's limit law turns the height into Rosati positivity at each cycle;
  Rosati positivity at every cycle is the orbit Hodge index, which is RH [L]. On the complete family it is
  the horizon criterion; the bulk is already a count.
- Over `𝔽_q` the function is the degree of a graph or the Stepanov count; over `ℤ` the first instance is
  the Lévy jump count on prime-free cycles, and the first-order structure `#ℙ⁷(ℤ/m)` of the degeneration.

### 2.6.2 Route PM — a structure that places resonances
**Question.** Realize the scattering channel of the Mayer operator as a self-adjoint operator in a Krein or
Lax–Phillips space in which the resonances `ρ/2` become eigenvalues of a definite (or dissipative with
known shift) operator — equivalently, a Herglotz representation of the boundary `2ζ(s)/ζ(s+1)` (or of its
slope, whose coefficients `(1 − 1/n)Λ(n)` are nonnegative) with a positive measure on the critical line;
equivalently, local energy decay of the automorphic wave equation at the optimal rate (B34).
- **Why it opens the path.** RH is the placement of the poles of `Λ(s)/Λ(s+1)` (band poles = Hodge defect
  [L]); partner saturation of resonant states is RH [L]. A definite structure forces the placement.
- **Constraints from the corpus.** No algebraic recentering takes the critical parabola to a real
  spectrum; universal Cauchy contraction fails below `Re w = 1`; core energy is positive at every zero; ζ
  enters `D = A + ζB` as a scalar. The structure must come from the relation between `A`, `B` and the
  eigenvalue parameter, not from the determinant alone.

### 2.6.3 Route WD — subexponential window energy from the source
**Question.** For every unit window at the polynomial stage and prefix `Θ(√m)`, prove from the integer-theta
source that the window energy `\|𝒵_N(t)\|²` grows subexponentially in `t` (B15). `𝒵_N(t)` is a contour
integral of `e^{t(z−½)}(−A_N'/A_N)` around the window: the question is a source identity that cancels the
`e^{t}` flux through the right edge against its functional-equation image to all orders.
- **Why it opens the path.** At the polynomial stage this is equivalent to RH [L]. It is a statement about
  polynomial-size integer data per window with no separation input; the canonical multiplier and the
  certificate then follow automatically [L].

### 2.6.4 Route HF — the window Markov capacity
**Question.** For every window length `A`, prove the Poincaré (capacity) inequality of the window Markov
form on pole-orthogonal window tests: the jump energy — the archimedean Lévy jumps plus the prime jumps
`n ≤ e^A` with weights `Λ(n)/√n` — dominates the creation potential `\|Ω(0) − 2Σ_{n≤e^A}Λ(n)/√n\| ≈ 4e^{A/2}`
(B37; the sinh-capacity form of B1).
- **Why it opens the path.** It is RH [L], and by the horizon criterion it is the RH criterion of the whole
  complete family.
  It is a spectral-gap statement for an explicit Markov generator on an interval — a random walk with
  prime-logarithm steps and Gamma-factor Lévy jumps — so the tools are Dirichlet forms, isoperimetry and
  comparison of jump kernels rather than prime-error estimates. Its algebraic shadow on one two-prime
  lattice is the SOS identity B6; over a curve it is Castelnuovo–Severi on the Frobenius span [L].

## 2.7 Does closing RH need a new field?

**Assessment: yes.** The corpus has built every layer of an arithmetic Hodge theory of the scaling surface
except the one that produces positivity. The degeneration layer (ADT/AHD) is complete and its content is exact:
its first-order structure is a point count (`#ℙ⁷(ℤ/m)`), its second-order structure is Weil's window form
plus a positive prime-free term. A theory of degenerations describes where the sign lives; it does not
supply it. The missing field is a **cohomology of windows of `Spec ℤ`**: a theory that attaches to each
window length `A` (scale cutoff `e^A`) a finite object whose `h¹` is Weil's window form and is nonnegative
because it is a dimension or a cardinality.

*Why.* Over `𝔽_q` the three proofs of RH rest on objects `ℤ` lacks: intersection numbers that are counts
(Weil), auxiliary sections whose vanishing is counted (Stepanov–Bombieri), tensor powers of a realization
with Euler products (Deligne). Over `ℤ` the algebra exists (correspondences, λ-ring, theorem of the square,
Lefschetz trace, Riemann–Roch identities), Tate's limit law names the missing input (a naive height),
integer producers reach the main term but never the square root, tensor amplification is all-or-nothing,
and every other producer is excluded by a proved law (edge logic, ceiling, near radical, free deformation,
margin selectors, semilocal and trace no-gos, Laguerre–Pólya closure, the degeneration's zero-blind bulk).

*What exists [L].*
- The window: Weil's window criterion; the window Markov form (finitely many prime jumps, departing jumps
  paying creation); the finite divisor and near radical at every degree; positivity to `0.724`; the exact
  `{∞,2}` trace to `log 3`.
- The degeneration: Jordan point count, Hensel weight strings, CRT tensor law, idempotent monodromy,
  graded/top Möbius pair, exact second order on horizon blocks, complete degeneration selecting ζ.
- The arithmetic: correspondence algebra with λ-ring and Rosati involution; Tate's limit law; Künneth RR;
  the Lévy count on prime-free cycles; Stepanov over `𝔽_q`; count classification.
- The selector's function: `Λ(s)/Λ(s+1)` with its band poles, its Mayer realization and its scattering
  reading.

*Criteria the field must meet.*
1. `h⁰` from arithmetic counts; `h¹ ≥ 0` because it is a dimension, a cardinality (naive height) or a
   log-count (midpoint convexity).
2. First order: reproduce the Jordan polarization `J_{β+1}(m)/φ(m) = #ℙ^β(ℤ/m)` as point counts, with the
   profile exponent `β` as a dimension.
3. Second order: primitive `h¹` of a window test `= ½Q(H)`; the prime jumps `n ≤ e^A` and the archimedean
   Lévy jumps as the two kinds of correspondences acting on the window; the creation potential as a degree.
4. Riemann–Roch at every window by a Poisson-type duality on lattices whose rank grows like `e^{2a}` (the
   near radical), with a logarithmic completion of the split surface.
5. Locality: the window object depends only on the primes `n ≤ e^A` (departing jumps pay their creation).
6. Calibrations: over curves `deg(m − nF)`, `N₁`, Stepanov, window `2g`; on prime-free cycles the Lévy
   count; the genus function as Shannon number plus resolved-zero defect.
7. It avoids the proved no-gos: cones, bidegree counts, fixed rank, definite counts, Siegel majorants at a
   fixed boost, ordinary Poisson pairs for the isotropic count, semilocal and trace carriers, separable
   gluing, free deformation, zero-blind limits.
8. Selection: it fails for the golden fake, prime flips, Epstein lattices beyond the self-dual point and
   the `m² + 64n²` series, and reproduces Weil and Stepanov over `𝔽_q`.
9. Gluing: global, one negative square at the pole, distinct primes coupled through `∞`; graded
   positivity reaching the top stratum by a mechanism that is not the Möbius inversion.
10. Frobenius at infinity: an operator on the window object whose fixed line is `Re s = ½` and whose action
    on `Λ(s)/Λ(s+1)` places its poles.

*Questions it must answer.*
- What object has Weil's window form as its `h¹`? What set does `τ_x(ξ ⋆ ξ′)` count, up to bounded error?
- Is the profile exponent `β` the dimension of an ambient projective space, and is there a scheme over `ℤ`
  whose point counts over `ℤ/m` give the second-order (window) term the way `ℙ⁷` gives the first?
- What pays the creation potential `−2Σ_{n≤e^A}Λ(n)/√n` — what is the degree of the window's canonical
  class?
- What are Stepanov's auxiliary sections on a window?
- What lattice carries the sections of a window of length `A` (rank `≈ 2e^{2a}`), with what metric (the
  Gamma factor as Gaussian and as Lévy measure)?
- Why `ζ` and not an Epstein function or a positive degree-two series: which axiom fails for them?

*Tools it aims to develop.* Dirichlet forms and Poincaré inequalities for arithmetic jump kernels on
intervals; point counting over `ℤ/m` and Hensel towers; λ-rings and Adams operations; Néron–Tate theory on
`ℤ[ℚ_{>0}^×]`; Arakelov `h⁰` on growing-rank lattices; Zwegers–Vignéras indefinite theta and Voronoi
summation; Stepanov's method; Wiener–Hopf / Szegő factorization; Krein-space and Lax–Phillips scattering
for the modular surface; measure rigidity and entropy (for the direction of 2.4).

*Objects, language, mechanisms.*
- Objects: windows `[−A, 0]`; window tests; the window Markov form (jump kernel, creation potential, pole
  plane); scaling surface classes; correspondences and normalized graphs; Rosati involution; naive
  heights; section lattices `Λ_A`; `h⁰, h¹, h²`; genus function; finite divisor; near radical; the
  degenerating family with its bulk count and horizon layer; `Λ(s)/Λ(s+1)`; window energy.
- Mechanism A (count): naive height on window correspondences ⇒ Tate limit `≥ 0` ⇒ Rosati positivity ⇒
  orbit Hodge index ⇒ RH.
- Mechanism B (capacity): Poincaré inequality of the window Markov form at every length ⇒ Weil's window
  criterion ⇒ RH.
- Mechanism C (placement): a definite structure on the scattering channel ⇒ poles of `Λ(s)/Λ(s+1)` on the
  line ⇒ RH.
- The degeneration is the dictionary connecting them; the window integer reduces to precision and is not
  an independent mechanism.

No corpus result shows that the field closes RH. Its first tests are 2.5.1 (a count at the first prime)
and Q2 (the full-space second order), where the answer is not obstructed by zeros.
