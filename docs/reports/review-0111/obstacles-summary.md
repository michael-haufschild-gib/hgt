# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route), `walls-ledger.md` (walls) and
`route-unification-ledger.md` (core problems and route classes). Labels `A*`, `B*`, `S*` refer to
`route-obstacles.md`; wall labels to `walls-ledger.md`. Corpus: `12f15b70bf` and the working tree.

Evidence: `[L]` Lean; `[S]` Lean in the working tree or unintegrated; `[D]` derived here from Lean
statements.

## Picture

1. **One even integer on one hyperplane.** Every route reads `κ = #` distinct zeros right of the
   line, on the pole-orthogonal hyperplane `v₁^⊥` [L]. `κ` is even, RH is `κ < 2`, and finite `κ`
   already gives all high zeros critical and `Θ < 1` [L]. Glued at any place the index is `κ + 1`
   [L]. Kernel, coupling and window prime error are one quantity [L]. The Hecke orbit of one
   generic test under two primes carries all of `κ` [L].

2. **The complete family is a degenerating family.** After rescaling by the conductor-one decay
   `c⁷`, the complete Weil family of the tilted spline converges along every schedule
   `c ≤ (log N)^α`, `α < 1/8`, to a diagonal form in the conductor basis, the **Jordan-totient
   form** `J(m) ∝ J₈(m)/φ(m) = m⁷ Π_{p∣m} ζ_p(1)/ζ_p(8)` [L; product form D]. Its extension data
   (cross-conductor pairings) vanish there and fixed packets inherit its positivity [L]. Prime
   dilations act on the conductors by lowering valuations, and along a `p`-tower the limit
   coefficient is a weight string with steps `p⁷` and `[8]_p = #ℙ⁷(𝔽_p)` [L/S]. At every multiple of
   `(log N)^{1/8}` conductor-Gram positivity is RH [L]: the inheritance radius is exactly the
   receiver. The estimates live inside the inherited regime — all vectors to `(log N)^{1/9}`,
   fixed packets to `(log N)^{1/8}`, mid-band packets to `(log N)^{1/4}`, logarithmic profile to
   `ε₀·c*` [L]. At the critical exponent the extension data are of the order of the limit and
   carry the zeros [D]. So Σ for the complete-family routes has one coordinate left, the multiple
   `K`; a fixed `K` sees radius `½ log K − O(1)` and is a finite-aperture statement (sub); all `K`
   together are RH.

3. **The degree axis has four proved laws** (degree = aperture = `½ log K`).
   - *Ceiling:* `μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})` [L].
   - *Near radical:* `(2 − η)e^{2a}` independent tests with `|W| ≤ exp(−η²e^{2a}/(300a))‖f‖²`,
     blind to every zero below the Landau height `2πe^{2a}` [L].
   - *Genus function:* the near radical gains two dimensions for every multiple or unresolved low
     zero; the genus law `g ≤ (2 + η)e^{2a}` forces all but `o(T)` zeros simple and isolated at
     scale `exp(−η²T/(20 log T))` [L]. The genus of `ℤ` at degree `a` is a statement about the
     multiplicities and separations of the zeros, not a time–frequency count.
   - *Finite divisor:* off the pole and a finite grid `D_a`, `W` is coercive with constant
     `(10 + 68e^a)(1 − 1/π)`; the Hodge defect at degree `a` is finite [L]. Over `𝔽_q` the opposite
     holds: the defect is `0` or `∞`, and fakes admit no finite divisor [L].

   Reading [D]: at each degree the Hodge index of `ℤ` is a finite-dimensional problem with
   `≈ 2e^{2a}` near-null directions whose energy is doubly exponentially small and fixed by zeros
   above `2πe^{2a}`. An estimate that decides the sign must be accurate to `exp(−e^{2a})`.

4. **Visibility.** An isolated pair at height `γ`, depth `δ` is seen at aperture `a` iff
   `S_δ(a) > (1/2π)log(ξ/2π)`; in the multiple `K = e^{2a}` its edge lies between `(4δL)^{1/δ}` and
   `(6δL+1)^{1/δ}`, `L ≍ log γ` [L]. A fixed multiple misses shallow high zeros; finite-aperture
   positivity forces companions of deep isolated zeros [L]; clusters survive [D].

5. **Deformation is free and empty.** The Kähler package transports HR wherever HL holds;
   Liouville = HL; RH ⇔ HL on the PSD locus; none of the three Lefschetz candidates is free [L].

6. **Positivity is glued, never local.**
   - No `{∞,p}` semilocal family carries positivity: the archimedean Sonin operator alone is not
     positive, prime transport blocks are indefinite past `½ log p`, and every single-prime ground
     energy crosses zero [S].
   - The gcd stratification writes `W` as a sign-free sum of coprime parts of stars; every
     successor pair and the whole archimedean overlap of consecutive atoms lie in the top stratum
     `g = 1` [L]. Links of the dilation complex are disconnected, so coprime atoms couple only
     through the archimedean place [L].
   - Stars are lower horizons, positivity descends, deep stars are positive with depth margin
     `log d − C₀`; the coprime successor gap survives unit dilation beyond `K ≥ Q(Q−1)` [L].
   HL is the gluing of the stars across the top stratum through the archimedean channel.

7. **Weil's form is a Markov form plus the pole plane.** `W = V_N‖g‖² + J(g) + ½⟨c,g⟩² − ½⟨s,g⟩²`,
   with `J` the archimedean + prime jump energy (nonnegative jump measure) and
   `V_N = Ω(0) − 2Σ_{n≤N}Λ(n)/√n` a constant creation potential; the pole is the only
   anti-Markovian term; RH ⇔ the sinh-capacity bound at every level [L].

8. **Riemann–Roch: what a section theory must be.**
   - *Cones fail:* universal floor law; RR on an orbit ⇔ orientation [L].
   - *Simple counts fail:* bidegree counts see no primitive class; fixed-rank counts violate RI;
     definite counts have off-line zeros, created by the boost (the self-dual point has none); the
     Siegel majorant `≥ 0` is the Hodge index; the isotropic count is `ζ²` with a double pole [L].
   - *What survives:* Künneth RR `h_K(x) + h_K(−x) = ½x² + h¹_K + ½δ`; boost averaging restores
     `ζ(s+w)ζ(s−w)`; Hecke correspondences are similitudes of the primitive `h¹`; over a curve the
     primitive `h¹` of a graph is the degree of the correspondence [L].
   - *Where a count already pays:* on prime-free cycles `W = Ω(0)‖f‖² + J(f) + pole term`, with
     `J` the Lévy–Khintchine jump count of the Gamma factor; the count alone pays `|Ω(0)|` and the
     pole up to radius `1/64` [L]. Over `𝔽_q` the Stepanov count pays the primitive `h¹` on every
     Frobenius window of every odd-characteristic hyperelliptic curve [L].
   The open core is a count-valued primitive `h¹` past the first prime.

9. **Weil's correspondence algebra exists over `ℤ`; its positivity is a height.** Hecke graphs, the
   λ-ring with Adams operators, the Rosati involution, Lefschetz traces and the theorem of the
   square are identities [L]. Tate's limit law: Rosati positivity at a cycle ⇔ its integral Rosati
   form has a naive height ⇔ it has a midpoint-convex function (a log-count) at bounded distance
   [L]. For ζ, RH ⇔ every cycle has one. All algebraic identities hold on the golden fake, which has
   no naive height [L].

10. **Precision has three ladders.**
    - One-point: one-sided count ⇔ RH; producers reach the main term, not the square root [L].
    - Conjugate diagonal: Hecke-defect means `O_c(log U)` for every `c < 1/2`; the mean ladder is
      the near-line density ladder (rates `r < 2c*`, `c* ≤ 2/3`), and near-line density holds at
      every rate `r < 1`; `o(log U)` ⇔ critical-scale clustering; one dyadic constant ⇔ RH [L].
    - Census: simple critical `≥ 0.6725`; every further gain is a signed prime-pair surplus beyond
      bandwidth one [L].

11. **Quantization.** RH = an even integer `< 2` per window. Per stabilized window, index `0` ⇔
    `L²` invertibility of the Wiener–Hopf lift ⇔ outer Birkhoff–Zhukovsky–Szegő factorization of
    the collision loop ⇔ disk-unit sectoriality [L]. Theta prefixes have `Θ(N² log N)` strip zeros,
    so the first artifact-free prefix is `≥ c√T` [S].

12. **Selection.** Every prime-set flip is separated, including zero-density twins below `1/4`;
    self-similar star flux selects `Λ`. Frobenius at infinity has four RH-equivalent readings and
    the naive-height form. Every selector is a margin, index or counterterm statement [L].

13. **PM has a determinant, a word trace formula and a coding.** `D(w,λ) = A + ζ(w)B`;
    `D(w,z)D(w,−z) = exp(−Σ even-word traces)`; `D ≠ 0` on `|z| ≤ 1` for `Re w > 2`; even Gauss
    words code the hyperbolic classes of `SL₂(ℤ)` [L]. The Selberg-zeta Euler product and the
    scattering link are not formalized.

14. **Approximation by RH-true objects closes into the Laguerre–Pólya class.** Centered curve
    products are bounded by their real values [L]; their limits are Laguerre–Pólya functions, so
    convergence to `ξ` is the rank/degree sign problem (Σ6) [D].

15. **Heat.** Slice floor `133/200` from sub-Weyl profiles; flow floor `2/3 + ε`; heat Hodge defect
    `N(t)/2` [L].

## 2.1 Obstacles that are just work

| # | Task | Routes served | Why it is work |
|---|---|---|---|
| A1 | Tilted spline from `α < 1/9` to `α < 1/8` on all vectors (split cross payment `c⁹ → c^{8+o(1)}`) | HF, SRT, AIP, ACS | rough regime; collective coercivity to `1/4`, logarithmic confinement and `O(c log c)` top self-form are in hand |
| A2 | `K_est` of the logarithmic profile; explicit horizons `N₀` | HF, SRT, AIP, ACS, RW | constants |
| A3 | Single-`K` completeness of the Steklov/sinc schedule | SRT, HF | one explicit scale |
| A4 | Certified Weil positivity at `½ log 3` and the next prime apertures | RW, EWU, OWU, HF | finite divisor + `{∞,2}` trace identity ⇒ certified Schur complement of dimension `≈ 2e^{2a}` |
| A5 | Close `[S]`: fixed-multiple ratCorr realization, weight strings, semilocal trace and obstructions, Künneth to `181/500`, prefix strip growth | SC, HF, RW, ACS, WD | formalization in progress |
| A6 | Leading term of the extension data in the inherited regime; Jordan-totient limits for every regular-tail profile | HF, AIP, SRT | explicit asymptotics of the cross-conductor pairings |
| A7 | Quantitative depth law `d₀(c)`; explicit star horizons | HF, ACS | effectivization |
| A8 | Finite-`N` tabulation of the gcd strata | HF | exact identities, numerics |
| A9 | Flow threshold `Λ_X` from sub-Weyl profiles | LA, WD | existing machinery |
| A10 | Certified de Bruijn–Newman bound as an index-one heat time | SC-heat, WD | certified numerics |
| A11 | `ΔO = o(log T)` ⇒ density one ⇒ Lindelöf in one statement | WD, SRT | composition |
| A12 | Computable stopping prefix | WD | interval arithmetic |
| A13 | Mixed-jet recovery for `≥ 3` primes | WL, ACS | Dirichlet-jet algebra |
| A14 | Explicit main-term producer | WL | Farkas / rounding |
| A15 | Census: `S_cos(λ)` for `λ ≤ 1`; odd-stabilizer calibration | census, ACS | classical pair estimates |
| A16 | Count reading of the whole prime-free window (interior jumps + pole term) | ACS, HF | the target `W ≥ 0` is known there by estimates |
| A17 | Künneth primitive `h¹` on the finite divisor at small degree | ACS, HF | calibration computation |
| A18 | `𝔽_q(X)` calibration | SC, ACS, RIT | curve coupling, edge and Stepanov count proved |
| A19 | `𝔽₃` elliptic loop chain | ACS | elliptic adeles, intertwining integrals and loop-group cells formalized; assembly remains |
| A20 | Mayer–Selberg identity and scattering link | PM | known mathematics, heavy formalization |
| A21 | Theta Hankel rank 8 strict; ranks 9–10 | TH | finite computation |
| A22 | Hausdorff shifts, Jensen horizons, two-grid degrees | PA, LA, HCF | effectivization |
| A23 | Nine atom-dominated collar moduli | ACT | finite case analysis |
| A24 | Mixed Schur debit; first-prime/coarse/polar costs on fixed cells | AIP, CHMD | fixed-dimensional estimates |
| A25 | Toeplitz minors beyond PF₃₇ | LA | certified computation |

## 2.2 Open mathematical obstacles

Strength: **RH**; **≥qRH**; **LH**; **sub**; **indep.**; **method**.

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Positivity at every fixed multiple `K·c*` (all-aperture Weil positivity) | RH; fixed `K` sub | HF, SRT, AIP, ACT, ACS, SC, RW, EWU, OWU, CHMD |
| B2 | Extension data at the critical exponent (exact leading term) | RH (all `K`) | HF, SRT, AIP, ACS |
| B3 | Critical-scale identification of the fixed-`K` limit form | sub | HF, SRT, AIP, ACS, SC |
| B4 | Joint shell–pole / Gamma-graph payment on growing packets | sub | HF, SRT, AIP, CHMD |
| B5 | Low-conductor spans; conductors above `√N` | sub | HF, SRT, AIP, SC |
| B6 | Exact SOS for the dilation form on one two-prime lattice | RH | HF, SC, ACS, RIT |
| B7 | Cluster exclusion below the Landau height | sub | RW, SRT |
| B8 | HL on the positive locus | RH | HF, TG, SC, WD |
| B9 | Gluing across the coprime stratum (star ascent) | RH | HF, ACS |
| B10 | Cross-tower spectral gap through the archimedean channel | method; uniform RH | HF, AIP |
| B11 | Loop-Eisenstein band-pole noncancellation | RH | HF, ACS, SC |
| B12 | Arithmetic index ceiling uniform in resolution | ≥qRH; RH (tensor) | CHMD, SRT, WD, AID, SC |
| B13–B17 | Heat count `a < 1` (sub); heat horizon `< ½` (≥qRH); window index `0` / sectorial factorization everywhere (RH); `O(T) = o(N(T))` (sub); `ΔO = o(log T)` (LH) | — | WD, LA, TG, SC-heat |
| B40 | Source-faithful realization | RH | RN, PTR, W1C |
| B41 | Odd-sector bound `R ≤ ½` | RH | CHMD, TT |
| B42 | All-rank / all-degree signs (Laguerre–Pólya property of `ξ`) | RH | TH, LA, HCF, PA, GTA; ART |
| B43 | Lower bounds for scheduled prime energies | RH | FU, CFC, RP, SZ, LI, FEL, EGC |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B18 | Polynomial-in-height stabilized prefix (separation input) | indep. | WD, TG, SC |
| B19 | Hecke defect at doubly-log scale | sub | WD |
| B20 | Near-line density at rate `r ≥ 1` (gate beyond `½`) | sub | WD, census |
| B21 | Dyadic mean `o(log U)` ⇔ critical-scale clustering | sub | WD, census |
| B22 | Fixed-scale `E = O(1)` | ≥qRH | WD |
| B23 | One constant over dyadic scales | RH | WD |
| B24 | Arithmetic input beyond counts + linear explicit formula | method | WD, HEF |
| B25 | Count-valued primitive `h¹` / naive height on the correspondence ring | RH; fixed degree sub | ACS, HF, RIT, IRK |
| B26 | Genus law: near radical `(2 + o(1))e^{2a}` (⇒ almost all zeros simple) | indep. | ACS, RW, HF |
| B27 | Logarithmic Serre duality for the split surface | sub | ACS, HF |
| B28 | `ε`-uniform producer | sub / RH | WL |
| B29 | Unconditional square-root source input | RH | WL, MC, PBM, RB, JAS, CTF |
| B30 | Near-band cyclotomic energy | ≥qRH | MC |
| B31 | Signed prime-pair surplus beyond bandwidth one | sub | census, ACS |
| B32 | Bounded coupling on one two-prime lattice | RH | SC, ACS |
| B33 | Cone coupling ⇒ RH (pure implication); unattained width | sub; ≥qRH | SC, ACS, PM |
| B39 | Hermitian structure on the Mayer operator near `Re w = 1` | sub | PM |

### Γ — selection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B34 | Zero–one law `κ ∈ {0, ∞}` | sub | SC, HF, ACS, SRT |
| B35 | Selection at the trivial gauge point | RH | MC, BAG, XN |
| B36 | Frobenius at infinity as an operator (Rosati positivity / naive height) | RH | HF, ACS, PL, CDG, EHT |
| B37 | Unimodular gauges, FE twins, zero-density/irregular twins | sub | HF, ACS, AIP, SRT, SC |
| B38 | Off-line resonance exclusion | RH | PM |
| B44 | Pre-divisor forcing | RH | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |

## 2.3 The three questions to answer next

The corpus has reduced the sign problem of every complete-family route to one regime (the
critical exponent of a degenerating family), the gluing problem to one stratum (the coprime top
stratum, reached only through the archimedean place), and the producer problem to one object (a
count-valued primitive `h¹`, equivalently a naive height on correspondences). The three questions
sit on these three points.

**Q1. Is Weil's primitive form a count past the first prime?**

For a primitive class `f` of the scaling surface the Künneth count splits
`h_K(x) + h_K(−x) − χ(x) = h¹_K(x) + ½δ(f, f)`, and `δ(f, f) = Re W(f, f)` [L]. By Tate's limit law
the target is exact: a function on the integral correspondence ring, nonnegative because it is a
cardinality (a naive height) or a log-count (midpoint convex), at bounded distance from the Rosati
form `ξ ↦ τ_x(ξ ⋆ ξ′)` [L].

In hand [L]:
- on prime-free cycles of radius `≤ 1/64`, `W` is the Lévy–Khintchine jump count of the Gamma factor
  plus the archimedean constant and the pole term, and the count pays both;
- over `𝔽_q` the Stepanov count pays the primitive `h¹` of every hyperelliptic curve in odd
  characteristic; in genus one the degree of `m − nF` is its own naive height (order of a kernel);
- Weil's form is a Markov form whose jump measure carries the prime atoms `Λ(n)/√n δ_{log n}` with
  nonnegative weight; the obstruction is the creation potential `V_N` and the pole;
- the theorem of the square is free; the golden fake satisfies every identity and has no naive
  height;
- the no-gos: cones, bidegree counts, fixed rank, definite counts, Siegel majorants, ordinary
  Poisson pairs for the isotropic count, semilocal positive carriers.

The question in three steps:
1. *Whole prime-free window* (A16, just work): count the interior jumps and the pole term up to
   `a < ½ log 2`.
2. *First Hecke graph* (B25 at fixed degree, sub): for `½ log 2 < a ≤ ½ log 3` the prime jump at
   `log 2` enters with weight `log 2/√2`. Is there an identity
   `W = (Lévy jump count) + (count attached to the graph of T₂) + (manifest squares)` on primitive
   tests of radius `a`? This is the first point where a prime has to be paid by a count.
3. *Decisive negative form:* classify counts with a Poisson-type duality that read the test
   component; if none satisfies `h¹ ≥ 0` on the finite divisor at degree `½ log 3`, the
   Riemann–Roch branch closes.

Why first: it is the only producer type that escapes the doubly exponential ceiling (an identity
plus a count); it is Weil's and Stepanov's producer; every simpler form of it is refuted; and it
has a working foothold at small radius over `ℤ` and a full proof over `𝔽_q`.

**Q2. What are the extension data of the degenerating complete family at the critical exponent?**

In hand [L]: the rescaled limit below `1/8` is the Jordan-totient form, an Euler-factor
polarization `m^β Π_{p∣m} ζ_p(1)/ζ_p(β+1)`; the extension data vanish there at relative rate
`(c⁸(1 + log c)²(log N)^{1/k}/log N)²`; prime dilations act as monodromy by lowering conductors,
with weight strings `p⁷`, `[8]_p` [S]; at every multiple of `(log N)^{1/8}` positivity is RH;
a multiple `K·c*` synthesizes radius-`½ log K` tests on one block; ratCorr Grams are packet Grams at
a fixed multiple [S].

The question: compute the `N → ∞` limit, rescaled by `c⁷`, of `⟨W r_e, r_{e′}⟩` at
`c = K(log N)^{1/8}` for fixed `K`. Is it `J(e)δ_{ee′} + X_K(e, e′)` with `X_K` Weil's form on the
radius-`½ log K` tests synthesized by the block (plus a coercive conductor part)? Is `X_K`
controlled by the dilation monodromy — an SL₂-orbit-type theorem in which the weight strings
polarize the extension data?

Why: the critical exponent is the single place where the complete-family routes, HL, the top gcd
stratum and the constant-factor wall meet [D]. A closed form for `X_K` turns each fixed `K` into an
explicit positivity problem, certifiable at small `K` (A4), collapses C1, C2 (SC through ratCorr),
C4 and C12 onto the degree axis, and decides whether the degeneration language carries a
positivity mechanism of its own (as the SL₂-orbit theorem does in Hodge theory) or only an
inventory.

**Q3. Can the top gcd stratum be paid through the archimedean channel?**

In hand [L/S]: positivity is never semilocal (no `{∞,p}` carrier); links are disconnected, so
coprime atoms couple only through the archimedean place; the gcd stratification is exact and every
successor pair and archimedean overlap lies in `g = 1`; deep stars are positive with margin
`log d − C₀`; the coprime successor gap survives unit dilation beyond `K ≥ Q(Q−1)`; the Hecke orbit
of one generic test under two primes carries the whole defect; over a curve the corresponding
statement is Castelnuovo–Severi on the Frobenius span; a finite affine expander family on `(ℤ/n)²`
is formalized.

The question: prove a cross-tower Poincaré inequality for the archimedean coupling of coprime atoms
— the top stratum `g = 1` bounded by the root defect, the coprime successor gap and the depth
margins of the stars it couples — first on one two-prime lattice (where it is the SOS identity B6),
then uniformly in the horizon (where it is HL, RH).

Why: any producer that answers Q1 or Q2 must still glue, and the corpus has proved that gluing
cannot be local or semilocal. The two-prime restriction is a concrete finite-rank target with a
function-field model (Castelnuovo–Severi) and a cyclic-orbit reduction already in Lean.

## 2.4 A wildly different route

**Verdict: we see none that escapes the three walls.**

Why: every RH-equivalent statement the corpus has met reads the one integer `κ`, and the walls are
walls on producers rather than on formulations:
- estimates fail at the critical exponent and on the near radical (Σ1i, Π16, ceiling);
- soft structure is twin-blind (Γ3); selectors are margins (Γ16);
- local and semilocal pieces carry no positivity (Σ23, Σ25); deformation is free (Σ14);
- tensor amplification is all-or-nothing (Σ13); finite realizations fail (Σ8);
- approximation by RH-true objects closes into the Laguerre–Pólya class (Σ26 → Σ6) [D].

A route far from the current ones therefore needs a producer outside {estimate, count, quantized
integer, exact identity, deformation, selection, realization, approximation}. The distant
directions absent from the corpus all fall back onto a known wall:

| Direction | Producer | Wall it falls on |
|---|---|---|
| Centered curve products (Weil/Honda–Tate numerators converging to `ξ`) | approximation + Hurwitz | real-axis convergence is the Laguerre–Pólya moment property of `ξ` at `½` (Σ6); Honda–Tate realizability puts no arithmetic constraint on the angles [D] |
| Exact extremal certificates from modular forms (Viazovska / Fourier-interpolation magic functions for the Weil LP) | exact dual certificate | the Weil extremal problem has no attained sharp extremizer at finite aperture (near radical, doubly exponential floor); in the limit the extremal measure is the zero divisor, whose crystalline rigidity needs zero-side positivity (Γ8) |
| Effective equidistribution of closed horocycles (Zagier: rate `y^{3/4−ε}` ⇔ RH) by non-spectral dynamics | dynamical contraction / Margulis functions | the error term is the Eisenstein constant term at `ρ/2`: square-root precision (Π); the modular surface selects ζ as in PM |
| Iwasawa-type realization (zeros of `p`-adic L-functions are eigenvalues on Selmer modules) | integral operator realization | no bridge from `p`-adic zeros to complex zeros |
| Discrete Morse theory on the squarefree prime complex (`χ̃ = −M(N)`; the star of `2` is a cone) | combinatorial cancellation | Morse inequalities bound critical cells below by Betti numbers; RH needs cancellation between dimensions, i.e. Π1 |

What would make a route genuinely different: a canonical object built from `ℤ` alone whose
structure theorem (not an inequality) forces `κ = 0` — as the Hodge index theorem on `C × C` does
over `𝔽_q`. The corpus has the algebra of that object (correspondences, λ-ring, theorem of the
square) but not the object. That is the new field of 2.7, not a separate route.

## 2.5 Breakthrough questions below RH and quasi-RH

### 2.5.1 Whole programme — a count pays the first prime
**Question.** Prove Weil positivity on primitive tests of radius `a ≤ ½ log 3` by an identity in
which every term is a cardinality, a Lévy jump count or a manifest square: the archimedean jump
count (Lévy–Khintchine form of the Gamma factor), a count attached to the graph of the first Hecke
correspondence `T₂`, and the pole term (Q1, steps 1–2).
- **Below RH.** It is a finite-aperture statement whose truth is already known by estimates
  (positivity holds through `181/500` and is a certified computation at `½ log 3`).
- **Advance.**
  - It is the first place over `ℤ` where a prime would be paid by a count instead of an estimate:
    a naive height on the first nontrivial correspondences in the sense of Tate's limit law.
  - It tests the producer of the new field (2.7) on a case where the answer is known, and either
    finds the count or isolates the exact obstruction that blocks every count at the first prime.
  - It supplies the calibration data (finite divisor, near radical of dimension `≈ 6`) for the
    general count.

### 2.5.2 Route PM — a zero-free region from the transfer operator
**Question.** With the Mayer–Selberg identity (A20) as input, construct a sesquilinear
(Lewis–Zagier / Krein) structure on eigenfunctions of the regularized transfer operator near
`Re w = 1`, scattering sector included, that makes the eigenvalue-`±1` problem self-adjoint there.
Derive `ζ(1 + it) ≠ 0` and a zero-free region near `Re s = 1` (B39).
- **Below RH.** It gives a classical-type zero-free region.
- **Advance.**
  - PM's positivity results hold for real `w` and for `Re w > 2` (non-vanishing on the closed
    unit disc); cone or contraction methods cannot separate the cusp-form events on `Re w = 1` from
    scattering events just left of it; a Hermitian structure can.
  - It would be the first statement about ζ zeros from PM's own operator, with selection supplied
    by the modular surface, and the template for 2.6.2.

### 2.5.3 Route WD — critical-scale clustering
**Question.** Prove that 100% of the zeros up to `V` lie within `κ/log V` of the line for every
`κ > 0`; equivalently, dyadic means of the unit-window Hecke defect are `o(log U)` at one `c < 1/2`
(B21). Stepping stone: near-line zero density at exponential rate `r ≥ 1` (B20), which carries the
`O_c(log U)` gate beyond `½`.
- **Below RH.** It implies neither Lindelöf nor a zero-free region; every pointwise step on WD's
  ladder is at least qRH, so this mean statement is the route's sub-qRH breakthrough.
- **Advance.**
  - The `O_c(log U)` gate is closed on all of `(0, ½)`, the almost-all corridor is
    `(1 + ε)loglog T/log T`, and the density ladder is an equivalence up to `2/3` [L]; clustering is
    the one remaining mean statement on the ladder.
  - The input must be a mollifier gain that tends to zero on near-line shells: arithmetic acting on
    the conjugate diagonal's mean. Classical density bounds give proportions decaying in `κ`, not
    `o(1)` at fixed `κ`.

### 2.5.4 Route HF — the critical-scale limit at one multiple
**Question.** For one explicit `K₀` with `½ log K₀ − O(1) > ½ log 2`, compute the rescaled
`N → ∞` limit of the complete family at `c = K₀·c*` and identify it as Weil's form at radius
`½ log K₀` plus a coercive conductor part (B3 at one `K`, Q2). Combined with the certified
positivity at that radius (A4), this gives eventual positivity of the complete family at one
multiple that sees the first prime.
- **Below RH.** It is a finite-aperture statement.
- **Advance.**
  - Every proved positivity of the family lies in the inherited regime; one multiple at the
    critical scale is the first exact payment where the extension data are of the order of the
    limit.
  - It tells HF whether its exact identities (Jordan-totient limit, monodromy, packet identity,
    conductor/star duality) decide the sign where residual and margin are of the same order, and
    whether the identification is uniform in `K` (that uniformity is RH).

## 2.6 Breakthrough questions that open the path to RH

### 2.6.1 Whole programme — a naive height on the correspondences of the scaling surface
**Question.** Construct a function `h` on the integral correspondence ring `ℤ[ℚ_{>0}^×]` of the
scaling surface, nonnegative because it is a cardinality or a log-count, with
`|h(ξ) − τ_x(ξ ⋆ ξ′)| ≤ C_x` for every cycle `x` (B25, B36).
- **Why it opens the path.** By Tate's limit law a naive height at bounded distance from the
  integral Rosati form gives Rosati positivity at `x`; Rosati positivity at every cycle is the
  orbit Hodge index, which is RH [L].
- Over `𝔽_q` the function is the degree of the graph, the order of a kernel (genus one) or the
  Stepanov count (hyperelliptic curves) [L]. Over `ℤ` the first instance is the Lévy jump count of
  the Gamma factor on prime-free cycles [L].
- The finite divisor and the near radical say where the count has work to do: on `≈ 2e^{2a}`
  directions at degree `a`, whose number reads the resolved zeros.

### 2.6.2 Route PM — a Krein-definite structure on the resonance strip
**Question.** Extend 2.5.2 to the strip `½ < Re w < 1`: make the transfer operator J-self-adjoint
with `J` definite on the resonant sector, so that eigenvalue `±1` occurs only on `Re w = ½`
(partner saturation forced).
- **Why it opens the path.** With A20, ζ zeros in the strip are eigenvalue-`±1` events of the
  transfer operator; partner saturation is RH [L]; definiteness forces it.
- The structure must come from the operator: no algebraic map takes the critical parabola to a real
  spectrum [L], and positive resonant norms do not select zeros.

### 2.6.3 Route WD — a source-defined sectorial multiplier on every window
**Question.** For every stabilized window, construct from finitely many theta values a nonvanishing
disk multiplier `F` with `Re(F·Λ) > 0` on the unit circle for the integer-theta collision loop `Λ`.
- **Why it opens the path.** Per window, such an `F` is equivalent to index `0`, to `L²`
  invertibility of the Wiener–Hopf lift and to an outer Szegő factorization; index `0` on every
  window is RH [L]. Sectoriality is a sign condition with a multiplier: an `O(1)`-precision
  statement, with no doubly exponential accuracy.
- What remains around it: windows stabilize only at prefixes of size `≥ c√T` [S]; a separation
  input (RH-independent) bounds the prefix polynomially (B18).
- No other route reduces RH to an `O(1)`-precision statement about finitely many computable
  numbers per window.

### 2.6.4 Route HF — gluing across the coprime stratum
**Question.** Prove that the top gcd stratum `g = 1` — every successor pair and the archimedean
overlap of consecutive atoms — is paid at every `N` and every multiple by the root defect, the
coprime successor gap and the depth margins `log d − C₀` of the stars it couples (B9; equivalently
HL on the positive locus, B8; in degeneration language, inheritance of the limit polarization past
the critical exponent, B2).
- **Why it opens the path.** The gcd stratification is exact; deep stars are positive; positivity
  descends; the only unpaid coupling sits in the top stratum [L]. Paying it at every resolution is
  RH.
- Its restriction to one two-prime lattice is the exact SOS identity B6; over a curve it is
  Castelnuovo–Severi on the Frobenius span [L].
- Links are disconnected over `ℤ` and no semilocal carrier exists, so the payment must use the
  archimedean channel; a cross-tower gap (B10) is the missing tool.

## 2.7 Does closing RH need a new field?

**Assessment: yes — an arithmetic Hodge theory of the scaling surface: correspondences whose
degrees are heights, with a degeneration theory and a genus function in place of a genus.**

*Why.* Over `𝔽_q` there are three proofs of RH, and each rests on an object that `ℤ` lacks:
- *Weil (Castelnuovo–Severi):* a surface with correspondences whose intersection numbers are counts.
  Over `ℤ` the surface, the correspondence algebra and the theorem of the square exist; Tate's law
  says the missing input is a naive height, and none is known past the prime-free window.
- *Stepanov–Bombieri:* auxiliary sections whose vanishing is counted. Over `ℤ` integer producers
  reach the main term, never the square root (B28); the analogue of Stepanov's auxiliary sections on
  the scaling surface is not known.
- *Deligne:* tensor powers of a realization in which the zeros are eigenvalues with Euler-product
  tensor powers. Over `ℤ` every tensor amplification is all-or-nothing, and the Künneth square
  carries `ρ + ρ′` without an Euler product.

The other producer types are excluded by proved laws: estimates (ceiling, near radical, critical
exponent), deformation (free and empty), selection (every selector is a margin), local and
semilocal gluing (disconnected links, no semilocal carrier), approximation (Laguerre–Pólya
closure). What is left is an exact count, and no current field supplies it.

*What it is about.*
- The scaling surface of `ℤ`: pole plane `aH + bV`, test classes `f`, correspondences (finitely
  supported measures on the scales: graphs of scalings and Hecke operators), the λ-ring with Adams
  operators.
- Heights of correspondences: functions on `ℤ[ℚ_{>0}^×]` that are cardinalities or log-counts, at
  bounded distance from the Rosati form.
- A cohomology `h⁰, h¹, h²` with `h¹` a dimension, infinite genus organized by a genus function at
  each degree, a finite divisor `D_a` and a near radical.
- Degenerations: the complete Weil family as a degenerating polarized family over the overlap
  parameter, with monodromy (conductor lowering), weight strings and a limit polarization by local
  Euler factors.
- The archimedean place as a Lévy (jump) count, as the source of the finite divisor (Gamma
  dominance) and as the only channel coupling distinct primes.

*What it would be like.*
- Weil's second proof transplanted: correspondences, Rosati involution, Lefschetz trace; Rosati
  positivity obtained because traces of `ξ ⋆ ξ′` are heights in Tate's sense.
- Riemann–Roch with a growing genus: `h⁰ − h¹ + h² = χ` at every degree; `h¹` read on the finite
  divisor; the near radical is the part of `h¹` that low zeros cannot see, and its size records the
  resolution of the zeros.
- Schmid-type degeneration: a nilpotent-orbit theorem (the Jordan-totient limit, proved below the
  critical exponent) and an SL₂-orbit theorem (inheritance of the limit polarization through the
  critical exponent, open).
- The explicit formula as its Lefschetz fixed-point formula; Hasse's bound as square-root
  precision; Frobenius at infinity as the Rosati identification of the reflection and conjugation
  pairings; the window index (Wiener–Hopf index) as its integer invariant.

*Criteria it must meet.*
1. `h⁰` defined from arithmetic counts; `h¹ ≥ 0` because it is a dimension, a cardinality (naive
   height) or a log-count (midpoint convexity).
2. An RR identity at every degree, proved by a Poisson-type duality on lattices whose rank grows
   with the class; the indefinite (split) duality completed logarithmically.
3. Primitive `h¹` of a test class = `½W(f, f)`; for graph classes of correctors a height equal to
   the Lefschetz trace up to a bounded error.
4. Calibrations: over curves it returns `deg(m − nF)`, `N₁`, the Stepanov count and Künneth
   effectivity ⇔ unitarity; on prime-free cycles it returns the Lévy jump count of the Gamma
   factor; its degenerate limit is the Jordan-totient polarization; its genus function is the
   Shannon number plus the resolved-zero defect.
5. It avoids the proved no-gos: cones, bidegree counts, fixed rank, definite counts, Siegel
   majorants at a fixed boost, ordinary Poisson pairs for the isotropic count, semilocal positive
   carriers, separable gluing, finite readings, positive majorants, free deformations.
6. Selection: it fails for the golden fake (no finite divisor, no naive height), prime flips and
   Epstein lattices beyond the self-dual point, and reproduces Weil and Stepanov over `𝔽_q`.
7. Gluing: it is global, with distinct primes coupled through the archimedean place.
8. Consistency with quantization: the defect it forces to zero is the window index.

*Questions it must answer.*
- What set does `τ_x(ξ ⋆ ξ′)` count, up to a bounded error, for a correspondence `ξ` and a cycle `x`?
- What are Stepanov's auxiliary sections on the scaling surface: sections vanishing to high order at
  the fixed points of Hecke correspondences, with controlled height?
- What lattice carries the sections of a test class of degree `a`? Its rank should grow like the
  Shannon number `≈ e^{2a}`; integer Dirichlet polynomials of length `e^{2a}` are the first
  candidate. What metric? The Gamma factor as Gaussian and as Lévy measure.
- How does the prime jump at `log p` enter as a count, and what pays the creation potential
  `−2Σ Λ(n)/√n`?
- What is the logarithmic completion of the isotropic count, and does it commute with boost
  averaging (which restores the Euler product)?
- What is the monodromy weight filtration of the degenerating Weil family, and does it polarize
  the extension data at the critical exponent?
- Why `ζ` and not an Epstein function: the boost-equivariant part of the split count is `ζ ⊗ ζ`,
  and the self-dual point is the only real-zero-free lattice of the boost line.

*Tools it aims to develop.*
- Néron–Tate theory on `ℤ[ℚ_{>0}^×]`: Tate's limit, naive heights, convexity of log-counts.
- Arakelov `h⁰` (van der Geer–Schoof, Bost) on products and on lattices of growing rank; indefinite
  theta series with completions (Zwegers–Vignéras), Siegel–Weil for the split plane.
- Lévy–Khintchine and Dirichlet-form theory for the archimedean place; capacity inequalities.
- Nilpotent-orbit and SL₂-orbit theorems (Schmid, Cattani–Kaplan–Schmid) transplanted to the
  degenerating Weil family.
- Time–frequency concentration (Slepian, Landau–Widom) with zero-resolution corrections for the
  genus function.
- Wiener–Hopf / Szegő factorization and integer-theta Fredholm indices as consistency checks.
- λ-rings, Adams operations and the correspondence calculus of AOG; function-field calibration
  through curve windows, Stepanov counts and elliptic adeles over `𝔽₃`.

*Objects, language, mechanisms.*
- Objects: scaling surface; classes `aH + bV + f`; correspondences `ξ`; normalized graphs; Rosati
  involution; Lefschetz trace; correctors; naive heights; section lattices `Λ_a`; `h⁰, h¹, h²`;
  genus function `g(a)`; finite divisor `D_a`; near radical; degenerating family `W_{c,N}` with
  monodromy, weight strings and limit polarization; extension data; Hodge defect; window index.
- Mechanism A (count): naive height ⇒ Tate limit `≥ 0` ⇒ Rosati positivity ⇒ orbit Hodge index ⇒
  Castelnuovo–Severi ⇒ bounded coupling on one two-prime lattice ⇒ RH.
- Mechanism B (degeneration): monodromy-polarized extension data ⇒ inheritance of the limit
  polarization through the critical exponent ⇒ HL on the positive locus ⇒ RH.

No corpus result shows that such a theory exists for `ζ`. Its first tests are 2.5.1 (a count pays
the first prime) and 2.5.4 (the critical-scale limit at one multiple), where existence is not
obstructed by zeros.
