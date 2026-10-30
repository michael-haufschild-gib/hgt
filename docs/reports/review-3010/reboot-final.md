# Reboot-final: the Lean corpus condensed, and where it points

Status: 30 October 2026. **RH is open.**

- **Sources.** `formal/GaloisForLFunctions`, read through the corpus research tool and in source, plus the four
  review-3010 files named in the task. No web search, builds or axiom audits.
- **Fact log.** Every claim points to [`reboot-final-facts.md`](reboot-final-facts.md):
  - sections G1–G19 hold the facts behind the audit of the two reports;
  - section K holds the corpus condensed by object, with K0 listing the mechanisms.
- **Reading standard.** Every cited item was read in source, statement and proof. For long assemblies that means the
  top-level proof and the named lemmas it combines.
- **Computations.** Two small checks are archived in
  [`computations/2026-10-30-reboot-final-checks`](../../../computations/2026-10-30-reboot-final-checks/README.md).

| Label | Meaning |
|---|---|
| **K*n*, M*n*, G*n*** | Fact-log section or mechanism, with Lean anchors |
| **[P]** | A module whose prose claims more than its Lean proves |
| **(inference)** | This report's reading of several facts together; the facts are named and the step is stated |

---

## 0. Summary

1. **What the laws are made of (K0).** The structural theorems that recur across programmes reduce to eight
   mechanisms applied to the explicit formula:
   - M1 the explicit formula;
   - M2 extraction of exponents from exponential sums;
   - M3 Landau's one-sided argument;
   - M4 archimedean domination at bounded scale;
   - M5 Toeplitz minors and Fejér elimination;
   - M6 the local zero count;
   - M7 the linear algebra of renormalization;
   - M8 symmetry bookkeeping and integer orders.

   "Growth equals depth", "one side suffices", "bounded scale is blind" and "quantization" are these mechanisms, not
   separate phenomena. Three headline obstruction modules prove only interval or norm arithmetic [P]:
   `ContourCrossingObstruction`, `CorrelationBoundsCountNotLocation`, `DiscriminantIsRealitySensitive`.

2. **Where ζ itself enters (§2).** The proofs use ζ-specific content in a short list of places:
   - no real zero in `(0, 1)`, which drives every one-sided criterion;
   - the simple pole at `s = 1`, which defines the positive class and separates the fakes;
   - the archimedean place: domination at bounded scale, and the successor edges, which are the only place a sign
     twin differs from ζ;
   - the discreteness `|h| ≥ 1` of integer shifts, which repays the logarithm in fixed-overlap positivity;
   - cyclotomic integrality: Λ is a log-resultant, and nonvanishing prefixes have norm `≥ 1`;
   - ℚ-independence of `log p`, through two-prime rotation and Kronecker density;
   - the theta radical;
   - the census and density engine.

3. **The compiled picture (§3).**
   - **Clusters.** Three independent instruments have the same worst case, a cluster of `≍ log t` zeros near one
     point, i.e. an approximate multiple zero:
     - the Weil lag family: hiding beyond `V ≍ log T` forces collapse;
     - the heat slice: the detection rate loses `δ → δ²` exactly on clustered zeros;
     - the explicit-formula census: blind exactly at coalescence.
   - **One threshold.** Three programmes meet the same threshold: bandwidth of order one, where the prime length is a
     power of the height (`bandwidth = log X/log T`, `OverlapCoordinates.lean`).
     - TTPC's census is diagonal through bandwidth `1` and stops there.
     - Every fixed overlap of the complete Weil matrix has limiting bandwidth exactly `1`.
     - The cluster collapse of SquareRootThreshold sets in at lag `≍ log T`.

     Past bandwidth one the only new input is the signed correlation of close prime pairs, the Fourier-dual face of
     zero coalescence.

4. **Two solution shapes survive the proof reading (§4).**
   - **A. The coalescent band:** non-coalescence of zeros off the line, together with signed close-prime-pair
     correlations past bandwidth one.
   - **B. The heat pincer:** on one `1/log t` scale, repair is proved from `κ = 17/25` and detection works below
     `κ₀(δ) = δ²/(200(log(3/δ)+1))`. A zero-free strip follows if the two meet.

   Two other shapes fall:
   - prime-phase transcendence: the formalized Baker exponent is exponential in the number of primes;
   - depth at the horizon: the horizon pairing `B_N(ρ)B_N(1−ρ)` has no depth-dependent growth at any order.

   A third, natural regularization (C), stays as a precisely scoped question.

5. **Audit (§5).** The two reports read programme READMEs and stayed inside the positivity frame. They miss the
   mechanisms, the cluster anatomy, the bandwidth-one coincidence, the heat pincer and the selectivity inputs.

---

## 1. Method

- **Harvest.** Module docstring titles of all 3,934 programme modules outside `RHTower`, `HTGeometry` and the
  vendors, plus the 23,457 `RHTower` titles, filtered by content.
- **Relations.** Recurring objects were queried with `scripts/formal_tools.py research`: torsion, horizon, counterterm,
  crystal, cluster, successor, quantum, heat, `Θ`.
- **Proof reading.** Every fact that enters this report was then read in source, statement and proof. This removed
  several title-level readings and corrected others:
  - "positivity through aperture `3/10`" holds because `e^{0.6} < 2`: no prime is read at all;
  - "inside the strip only counts" is prose over the lemma `1 ≤ N → N ≤ S → 1 ≤ S`;
  - "finite off-line sets are visible at a logarithmic aperture" uses a compactness constant that is not effective in
    the configuration;
  - the shallow anti-clustering bound has the order of all zeros and excludes no individual cluster.

---

## 2. What the proofs use

### 2.1 Mechanisms (K0)

| Mechanism | What it does | Where it appears (examples) |
|---|---|---|
| M1 explicit formula | functional = zero sum + archimedean tail + pole | packets, lag structures, orbit correlations, Lefschetz sequences |
| M2 exponent extraction | a sum `Σ c ν^n` that is `O(r^n)` has no seen node above `r` (Vandermonde, residues, discrete Cauchy transforms, Cesàro) | growth = depth in BSU, AOG, HKT, ACS, ART; determination of the configuration |
| M3 Landau | a one-sided bound gives a nonnegative measure; the abscissa sits at the bound because ζ has no real zero in `(0, 1)` | packet sign law, one-sided von Koch, one-sign difference families, one- and two-prime Lefschetz bounds |
| M4 domination | `log(1 + π\|ξ\|/4) > 10 + 68e^a + 2(sinh a − a)` | positivity at bounded aperture, the low-frequency divisor, the `12/25` window |
| M5 Toeplitz/Fejér | `2×2` minors; companion elimination via `(x² + β²)K_{k+1} = cK_k` | sparse deciding families; twin and cluster laws |
| M6 local count | at most `40 log(180\|t\|)` zeros per unit window | the only ζ-input of the hiding laws and of large-height heat repair |
| M7 survival algebra | null cones of counterterms; coupled ranks | the renormalization programmes |
| M8 bookkeeping | conjugate pairs, horizontal segments, integer orders, character sums | even index, transverse quantum, even Abel residues, `−1/p` successor bias |

### 2.2 The ζ-specific inputs

1. **No real zero in `(0, 1)`** (`riemannZeta_real_strip_ne_zero`, via `zeroShift_ne_ofReal`). It is what makes every
   one-sided criterion work (M3).
   - The single exception to one-sidedness anywhere in the corpus is a real positive eigenvalue or real zero.
   - The golden fake curve is exactly that: its outer eigenvalue `φ` is real (K10).
   - The Λ-positive FE fakes are forced to put a pole on the real axis (K10).
2. **The simple pole.** A completed positive system with pole budget one is `Kζ` (Bernstein–Widder plus FE rigidity).
   The entire Λ-positive fake with the exact FE differs from ζ only by a pole of order `3` at `s = 1` (K10).
3. **The archimedean place.**
   - Bounded scale is archimedean (M4).
   - The prime form is gauge-blind: every completely multiplicative `±1` twin, Liouville included, has a prime form
     unitarily equivalent to ζ's. Selectivity can only come from the pole term and the archimedean place
     (`TheFiniteIntersectionIsGaugeBlind`).
   - The archimedean kernel sees a twist exactly on the successor edges `(n, n+1)`, through the connection
     `conj χ(n)χ(n+1)` (`TheSuccessorConnectionIsTheArchimedeanGaugeField`, K8).
4. **Integer discreteness.**
   - In fixed-overlap positivity the gap `|h| ≥ 1` of the successor shells repays `M log c`. The continuum model
     without integer successors has energy `log(1/(2πc)) + β/M → −∞` (`TheIntegralityOfTheShiftRepaysTheLogarithm`).
   - At zeros the successor is unipotent: its defect is holomorphic on `Re s > 0`.
5. **Cyclotomic integrality.**
   - Λ is the intersection number of torsion orbits (Apostol's resultants).
   - Weil's kernel is the renormalized limit of positive torsion energies.
   - Gauss's digamma theorem is the Fourier transform of the torsion energy.
   - A nonvanishing primitive prefix has energy `≥ φ(m)` by norm `≥ 1` (K6).
6. **Independence of `log p`.**
   - Two primes rotate every non-real Frobenius phase (`irrational_log_ratio`).
   - Kronecker density aligns prime phases at some height.
   - Fel'dman's effective Baker bound is formalized. Its exponent is at least `(1000·Σlog p·R)^d`, exponential in the
     number `d` of primes (K5).
7. **The theta radical.** One modular object pins the null directions of the Weil form in three places:
   - the blind Ξ-divisible family of cone uniqueness (G1);
   - the truncated Riemann kernel, which makes the margin `≤ Ce^{12L − πe^{2L−1/2}}`;
   - the theta plateaus that lift any test into the nonnegative cone (K1, K2).
8. **Counting and density** (K11, G2, G12):
   - the local count;
   - the census: `≥ 67.250071%` simple critical, `4/5` of ordinates, `0.8876` simple-or-critical, off-line moment
     `≤ 0.066V`;
   - Selberg's near-line density `e^{−α/28}/α` at depth `α/log T`;
   - fixed-σ density `o(T)`; Guth–Maynard `30/13`; Vinogradov–Korobov.

---

## 3. The compiled picture (inference)

### 3.1 Three scales in the lag (aperture) of a Weil test at height `T`

| Lag `V` | What holds | Fact |
|---|---|---|
| `≲ log log T` | Positivity, by archimedean domination | M4 |
| `≍ log log γ/Θ` | Below it, the trichotomy says a hidden near-top zero needs a twin within `(log log γ)/V` or height `≥ exp exp(cΘV)` | K4 |
| `≍ log T` (the corpus's "square-root threshold") | Beyond it, hiding forces cluster collapse: `p ≤ log γ` companions at geometric radius `e^{−cVδ/p}` | K4 |
| `≍ (log γ)² log log γ/δ` | Every near-top off-line zero is detected | K3 |

- A test of lag `V` reads prime powers up to `e^{V+O(1)}`. The lag `log T` therefore reads primes up to a power of
  `T`, the length at which a Dirichlet polynomial's length matches the height.
- **The same threshold elsewhere.** `SpacingScaleHarmonicAnalysis/OverlapCoordinates.lean` fixes the coordinates:
  overlap `X/T`, bandwidth `log X/log T = 1 + log(overlap)/log T`, and "a fixed overlap greater than one still has
  limiting bandwidth one" [S].
  - TTPC: the census's prime side is valid through `λ = 1` (`X = e^L ≤ T`, `Zeta23FamilyBandwidth`), where the
    certificate is `2/3` (`subthreshold_cert_le_two_thirds`).
  - Complete Weil matrix: horizon `N`, width `c/N`, hence length `N` and height `N/c`. Every fixed `c`, and every RH
    schedule `c_N ≍ L(log L)²`, has bandwidth `1 + o(1)` (inference from the coordinate identities).
  - SquareRootThreshold: collapse sets in once `Vδ/8 ≫ log γ`, i.e. at bandwidth `≍ 1/δ`, which is of order one for
    fixed depth.

### 3.2 One worst case for three instruments

| Instrument | Its worst case, as proved | Fact |
|---|---|---|
| Weil lag family | Beyond `V ≍ log T` a hidden near-top record needs `≥ 3` zeros within `2r`, collapsing to an approximate multiple zero; isolated twins cannot hide | K4 |
| Heat slice | Detection is linear in `δ` under regular local growth; the unconditional rate `δ²/log(3/δ)` loses exactly on "`≍ log t` zeros clustered near `½ + it`" | K9 |
| Explicit-formula census | A double critical zero and a coalesced off-line pair have identical Gram data; every Gram functional is capped at `(2 − κ)N` there | G14 |

**Reading (inference from the three rows).** Each instrument fails on the same configuration, many zeros within a
tiny disc. None of the corpus's local constraints rules it out:
- the local count allows `40 log t` zeros per unit window;
- the shallow anti-clustering and Selberg density bounds have the order of all zeros;
- the census gives proportions.

### 3.3 The duality that ties the threshold to the clusters

TTPC proves that past bandwidth one the only new term in the census is the signed correlation of close prime pairs
`|log(n/m)| ≲ 1/T` (the coalescent band). It reduces that term to a parity-locked Ramanujan stabilizer model plus a
centred stabilizer discrepancy. The model gives negative Ward–Mertens repulsion (G3).

The census's blind spot is zero coalescence (G14). Close prime pairs past bandwidth one and zeros closer than the mean
spacing are the two sides of one form factor, `F(α)` for `α > 1` (inference from the `κ(λ)` formula, G3 and G13).

So the corpus has met one object from three directions:
- the prime side: signed close pairs (TTPC);
- the zero side: coalescence (census, hiding laws, heat);
- the operator side: growing overlap at limiting bandwidth one (complete Weil matrix).

### 3.4 What does not carry the problem

- **Bounded scale** (M4, K2). Aperture `3/10` reads no prime; `12/25` reads only `2`; domination holds to
  `log log T`.
- **Averages** (K2). Height-windowed forms pass model off-line lattices and clusters.
- **Horizons.** `B_N(ρ)B_N(1−ρ) = N^{−1}[N/(ρ−1) − ρJ_N(ρ)][−N/ρ − (1−ρ)J_N(1−ρ)]` with `|J_N| ≤ 1/Re s`. Depth enters
  only through bounded factors (K8, computed from the definitions in `RHTower/EMCarrier.lean`).
- **Transcendence at growing dimension** (K5). The effective Baker exponent grows at least exponentially in the number
  of primes.
- **Renormalization of the torsion germ** (K7):
  - Abel's counterterm is the identity, and coupling does not lower its rank;
  - the spacing regulator has a scalar counterterm;
  - the horizon counterterm has unbounded rank, though its survival cone on class profiles is the class-wise polar
    hyperplane.
- **Prose obstructions** [P]: "every input is separated by the strip", "inside the strip only counts", "reality
  tools lack decidability". These are not theorems of the corpus.

---

## 4. Solution shapes

### A. The coalescent band

**Facts used.**
- K4: the trichotomy, loud twins, tight twins, collapse, the threshold `V ≍ log T`.
- K9: detection is linear in `δ` under regular local growth; the three-radii loss comes from clustering.
- G14: the coalescence blind spot.
- G3: the reduction to the centred stabilizer discrepancy.
- G2: Gabor pinching. The `10^{−8}` beyond `HD(1)` comes from non-orthogonality of three nearby simple ordinates.
- G15: aligned ordinates of short prime polynomials are sparse, `T^{1−1/C+o(1)}` for `X = (log T)^C`.

**Needed statements**, in the corpus's own terms:
1. **Local count at scale `δ`.** Near every point `½ + δ + it`, the number of zeros within distance `δ` is
   `≤ C(δ log t + 1)`, against the corpus's unit-window count `40 log(180|t|)`.
   - In K9 this is the regular-growth hypothesis that gives detection at the linear rate `δ/(96(c+1))`.
   - In K4 it excludes collapse at geometric radius `e^{−cVδ/p}` once `V ≫ log γ`, which lowers the detection lag from
     `(log γ)² log log γ/δ` to `≍ log γ/δ`.
2. **The coalescent band.** A bound for the centred stabilizer discrepancy of signed close prime pairs at
   bandwidth `4/3`, enough for TTPC's `1/18` budget (G3). It is the prime-side form of item 1, on average.

**What A gives, and what it does not.**
- Item 1 makes off-line zeros of depth `δ` detectable at lag `≍ log γ/δ`. That is a refutation statement.
- An RH-type conclusion needs positivity of the lag family up to that lag. That is a pointwise statement about prime
  windows of length up to `T^{O(1/δ)}` at height `T`.
- The corpus proves such positivity only to `log log T` (domination). A therefore localizes the remaining problem: the
  bandwidth window `[log log T, log T/δ]`, with no clusters to hide in.

### B. The heat pincer

**Facts used (K9).**
- Repair: every heated slice coefficient is positive at heat `κ/log t` for `κ ≥ 17/25`. The size-only floor of this
  method is the parabola envelope of the Lindelöf profile, `27/40` with the formalized exponents.
- Detection: an off-line zero of depth `δ` at height `t` is detected at every `κ ≤ κ₀(δ) = δ²/(200(log(3/δ)+1))`.
- Every-height positivity at rate `κ₀(δ₀)` excludes `Re ρ ≥ ½ + δ₀` above `e^{16}` (`re_lt_of_heat_rate_pos`).

**Needed statement.** Slice positivity at heat `κ₀(δ₀)/log t` at every large height `t`, for one `δ₀ < ½`. That
gives a zero-free strip.

**The gap is quantitative and two-sided.**
- The repair argument uses only size bounds for `ξ` and floors near `2/3`.
- The detection argument loses `δ → δ²` to clusters. Even linear detection, `≤ 1/192`, is far below `17/25`.
- Closing the gap needs a non-size input on the repair side. The candidates are positivity structure of the slice
  (Turán layer, K10) and non-coalescence (A1) on the detection side.

### C. A natural regularization (scoped)

**Facts used (K6, K7).**
- The prime side is a renormalized positive torsion energy.
- The survival law and the coupled-rank law hold.
- Abel's identity counterterm survives nothing.
- The horizon counterterm on `p`-adic class profiles is `Σ_j δ_j^{−1}ℓ_j(x)²`, rank `J + 1`, with survival cone
  `ℓ_j = 0`. It is `[p]`-covariant, but its rank is unbounded over all classes.

**Question.** Is there a positive family of arithmetic origin whose renormalized limit is Weil's prime kernel and whose
counterterm has a null cone containing the polar-neutral tests?

**Scope.**
- Under the Abel regulator the answer is no, for every coupling.
- The horizon gives a nontrivial survival cone on each finite set of classes. The corpus does not prove positivity of
  a family renormalized by it.
- By Finsler–Debreu the question is empty without the arithmetic-origin requirement.

---

## 5. The two reports against the compiled picture

| Report claim | Compiled picture | Fact |
|---|---|---|
| Opus: "positivity proofs with margin cannot exist; estimates are the wrong instrument" | Margins exist at bounded scale, for archimedean reasons (M4). The zero-constraining theorems are estimates (census, density, VK, Guth–Maynard). | K2, G2, G12 |
| Opus: cone uniqueness is "the only global theorem" | Cone uniqueness is one of three uses of the theta radical. It fixes the weights, not the sign. | §2.2(7), G1 |
| Opus: "prime-free" RH | The node set must contain every prime power. | G1 |
| Opus: `WindowPositive` on `(0, log 2)` as a first target | Below `log 2` no prime is read; positivity there is pole plus archimedean for every weight. | K2, G5 |
| Opus: `𝔽_q` "has room" | Over `𝔽_q` the only one-sided exception is a real eigenvalue, and ζ has none in `(0, 1)`. | M3, K12 |
| Astra: fixed-overlap positivity is "real progress" | It is positive because integer shifts are discrete (`\|h\| ≥ 1` repays `log c`), and its margin vanishes at the critical overlap. It says nothing about zeros. | K8, G9 |
| Astra: nonlinear theta readings and heat as alternatives | Heat is a quantitative pincer (B) with an explicit two-sided gap; theta is the radical (§2.2). | K9 |
| Both: the walls as obstacles | The walls are the mechanisms M1–M8, and some are prose [P]. The decisive scale is bandwidth one; the decisive configuration is a cluster. | K0, §3 |

**What both got right:**
- Astra: the order of quantifiers decides.
- Opus: the selective structures are the pole, the Gamma factor and the successor. The proofs confirm this and sharpen
  it to the successor edges of the archimedean kernel and the discreteness of the integer shift (§2.2).

---

## 6. Research programme

The corpus's no-go rule applies throughout: if a package fails, record its strongest positive statement.

### WP-A. The coalescent band

- **A1. Local count at scale `δ`.** Prove or refute `#{zeros within δ of ½ + δ + it} ≤ C(δ log t + 1)` from the corpus
  inputs: Riemann–von Mangoldt with its remainder, `rvmRemainder_unbounded`, Selberg near-line density, shallow energy.
  If unconditional, record the best exponent of `δ` and `log t`. If not, record exactly which remainder bound it
  needs.
- **A2. Collapse without clusters.** Re-run `zeta_near_top_cluster_collapse` with A1's count in place of the unit
  count, and state the resulting detection lag explicitly.
- **A3. Heat detection under A1.** Turn `re_xiSliceHeatTransfer_neg_of_regular_growth` into an unconditional theorem
  under A1. Its hypothesis is a growth majorant, which A1 supplies through Jensen.
- **A4. The discrepancy.** Bound the centred stabilizer discrepancy at bandwidth `4/3`
  (`oddEvenShiftPrimeCoalSum_eq_stabilizerModel_add_discrepancy`) within TTPC's `1/18`, or record the best fraction.
- **Falsifier.** A model zero configuration that satisfies the local count, the census proportions and Selberg density
  but carries collapsed clusters at every height. That would show A1 is not a consequence of the corpus inputs.

### WP-B. The heat pincer

- **B1.** Prove that `27/40` is a genuine floor of size-only repair. Show `T_{2m}` can fail for slices obeying the same
  size bounds below that rate; `XiSliceHeatCoshCountermodel` and `XiSliceHeatGaussianSharpThreshold` are the
  starting points.
- **B2.** Find the first non-size input that lowers the repair rate. Candidates: the Turán layer of ξ's Taylor
  coefficients (Lorentzian homogenizations, K10), and slice positivity transported from the Euler region
  (`exists_iteratedDeriv_xiSliceProduct_ge_euler_from`).
- **B3.** Record the pair `(κ_repair, κ_detect(δ))` as a frontier number in each module that moves it.

### WP-C. Regularization

- **C1.** On a finite set of `p`-adic classes, decide whether a positive family of arithmetic origin renormalizes to
  `P_N` with the horizon counterterm `Σ_j δ_j^{−1}ℓ_j²`. The survival law then gives positivity of the limit on the
  class-wise polar hyperplane.
- **C2.** If C1 succeeds for one prime, test two primes. The class structures of `p` and `q` are transverse, and the
  joint survival cone is the intersection.

### WP-D. Corpus hygiene

- Mark modules whose docstrings claim more than their Lean as such, starting with the three [P] modules of K0.
- Every new criterion states its mechanism (M1–M8), its lag or bandwidth scale, and whether its statement constrains
  zeros unconditionally.

---

## 7. What would change this picture

- A theorem excluding collapsed clusters off the line at every height (A1). It would remove the common worst case of
  three instruments.
- A configuration that hides from the lag family beyond `V ≍ log T` without clusters. It would contradict the reading
  of K4.
- A repair rate below `κ₀(δ)` for some `δ < ½`, or a proof that size-only methods cannot go below `27/40`.
- A positive arithmetic family renormalized by the horizon counterterm (C1).
