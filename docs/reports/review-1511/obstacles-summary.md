# RH research: consolidated frontier, open problems and research programmes

**State in one paragraph.** One seed is proved: no zero of `ζ`, of any Dirichlet `L`-function or of any Hecke or ray class `L`-function of `ℚ(ω)` lies in `Re s > 7/8` [SEEDZETA] [MMD_DIR] [HECKESEED] [RAYSEED] [S]; a hypothesis-free proof of `Re s > 20999/24000` for the same families is written in source and not graded by the frontier map [SUBSEED] [SUBDIR] [S]. The corpus reads the zero width `w = Θ − ½` exactly through many rulers, and a ruler calculus makes them one number [RULERS] [LEVERTRANSPORT]. No lever for `ζ` is proved, and five world classes fix what a lever must use: the Dirichlet series, the exact functional equation, the arithmetic of the primes beyond their count, and the Ramanujan size of the Euler parameters [TWOTHIRDSWORLD] [COSH] [EDIT] [PAIRSNOBITE]. The only producer, the cubic probe, has two ladders: its frames stop at `3/5` under factor-by-factor completion while the Möbius sign alone prices frames down to centres `k/(2(k−1)) → ½` [WALLGEN] [SIGNLINE]; its estimates have the published vertex `7/8`, close at `20999/24000` after rescaling, cannot pass `40535/46328` with the present estimates, reach `13/15` only with a better row count, and stop at `5/6` in every Cauchy–Schwarz model [VERTEXPOS] [SUBSEED] [FARKAS] [BALANCED] [SAVING] [S]. The window calculus is a complete finite model of `w` with no producer in gluing form [SUBEULER] [S]. Identity forcing stops at the quartet [QUARTETFORCE]. The half-line problem has an exact Hawking–Page structure off RH, and stability does not exclude it [HPTRANS] [SADDLE] [S]. The tail factors into ZAL, the finite stratum and Landing, all open [THREEATOMS].

Evidence: Lean statements read in source at `3699ff3a33` with the working tree of 15 Nov 2026 ([S] = tagged unintegrated by the frontier map, [W] = untracked working-tree file); [fact log](../../../logs/review-1511-frontier-facts.md). No build or audit was run. **[D]** marks deductions of this report, to be proved before use. Companion reports: [routes](route-obstacles.md), [walls](walls-ledger.md), [faces](route-unification-ledger.md).

**Questions with an answer in Lean.**

| Question | Answer | Lean |
|---|---|---|
| Does the gluing data of the windows (finite prefix, dyadic middles, half-windows) give a doubling factor below `√2`? | No: a sub-Euler model with the same data has best factor `√2`; a factor below `√2` needs a negative fresh-octave form of order `√K`. | [SUBEULER] [TOPOCTAVE] [S] |
| Do the `A₂` cubic multiple Dirichlet series supply the estimates below `7/8`? | No: every convexity, Perron, Kubota-pole and squared-row boundary exceeds `7/8`; Cauchy–Schwarz models have `s = 0`. | [A2CHAIN] [A2REJECT] [A2DOUBLE] [SAVING] |
| Does a rational Euler identity, a Brauer relation or a shifted convolution force a second zero? | No: forcing stops at the quartet; survivor is a ruler on `[½, 9/16)`. | [WITTORD] [BRAUERCANCEL] [SHIFTMARGIN] [SQFRULER] |
| Is the off-line world a thermodynamically unstable black-hole phase? | No: the saddle is stable at every `R`, the weak endpoint always wins, the Legendre intercept is the bare energy. | [SADDLE] [WEAKEND] [LEGENDRE] [S] |
| Does bootstrapping the probe on an assumed zero-free region give a lever? | No [D]: low estimates through the twists return the zero, the high-side count moves by `< 10⁻⁴`. | [TWISTRETURN] [ROWCOUNTAT] |
| Does a finite-aperture Weil certificate separate `ζ` from a deformation with off-line zeros? | No: prime-2 deformations keep the floor at `½log 2` and, near `α = ½`, at `log 2`. | [P2NYQ] [P2LOG2] [S] |
| Does KMS positivity on the modular horizon place the zeros? | No: positive kernels with the same KMS condition have all zeros off the line. | [KMSPOS] [FAKEHORIZON] |
| Is there a heat-time lower bound in the width alone? | No: cosine-defect models of fixed width have heat time `→ 0`. | [HEATSPACING] |
| Does the rescaled probe geometry close below `7/8`? | Yes, at `20999/24000`, for `ζ`, every Dirichlet and every Hecke `L`-function of `ℚ(ω)`. | [SUBPROBE] [SUBHECKE] [SUBSEED] [S] |
| Can a zero satisfy `ζ(ρ) = ζ(ρ/k) = 0`? | Such a coincidence forces `Θ ≥ k/(k+1)`; none occurs for `k ≥ 7`. | [ROOTCOINC] [S] [K7] [S] |

## 2.1 Tasks that are work

Each task has a known method and no unproved sign, rate or uniformity. None of them proves RH.

| # | Task | Concrete output | Inputs | Payoff |
|---|---|---|---|---|
| A1 | **The optimal geometry of the present estimates** | Locate the true vertex of the cubic-probe budget in `(40535/46328, 20999/24000]` and close the probe there with the transport, common-probe and zero-exclusion modules written for `20999/24000`. | [FARKAS] [TRUEVERTEX] [SUBPROBE] [S] | The best seed the present estimate system can give; at most `≈ 1/23164` below `7/8`. Every further step needs a new estimate (2.4, 2.5). |
| A2 | **Integrate the [S] modules** | Grade and integrate the sub-`7/8` half-plane and its detectors, the √2 and top-octave modules, the Hawking–Page phase law, the prime-2 aperture test, the Artin seed, the `log 2` floors, the Kummer Cartier period and the target-extraction modules; transport `20999/24000` to every ruler (`w ≤ 8999/24000`, Mertens exponent, heat threshold, AdS strip `3001/48000`, doubling factors `2^{8999/24000+ε}`) [D]. | [SUBSEED] [WIDTHSUB] [SQRT2] [TOPLOCAL] [HPTRANS] [P2LOG2] [ARTINSEED] [FLOORLOG2] [KUMMERCARTIER] [TARGETFILTER] [ROWCANCEL] | Every statement in the walls ledger becomes [L]; the improved seed on all rulers. |
| A3 | **Isolated double collision off the centre** | One forward time with a double zero `ζ₀ ≠ 0` and no other multiple zero; then `G₊ = W`. A multiple zero off the centre exists at arbitrarily large forward times; order two and isolation remain. | [OFFCENTRE] [DOUBLECOLL] | Decides the sign of `G₊`; with `G₊ = W` every parity mechanism carries no information. |
| A4 | **`Q = 2` fourth ladder step** | Zero excess (or a failing window) at ratio `103⁸/(100⁸/2)` for cutoff two. | [FOURTHRED] [FOURTH] [S] | Completes the ratio-three ladder at every cutoff. |
| A5 | **Seed for every pure cubic field** | Every nontrivial ray class `L`-function of `ℚ(ω)` carries the seed [RAYSEED] [S]; identify the two-dimensional Artin character of each `ℚ(∛m)` with a ray class character of `ℚ(ω)`, as written for `m = 2` [ARTINSEED] [S] [D]. | [RAYSEED] [S] [ARTINSEED] [ARTIN] | Dedekind zeta functions of all pure cubic fields zero-free on `Re s > 7/8`; the first non-abelian family with a seed. |
| A6 | **Effective Siegel from the all-moduli seed** | No real zero of any `L(s,χ)` in `Re s > 7/8`; a short Euler product on `Re s ≥ 7/8 + ε` gives an effective `L(1,χ) ≫ (log log q)^{−1}`, effective class-number lower bounds, prime-number theorem in progressions with error `x^{7/8+ε}` [D, classical]. | [MMD_DIR]; Siegel's theorem is present only ineffectively [SIEGEL] | Conductor-uniform tools for CRF/JAS; the effective Siegel problem. |
| A7 | **Lindelöf right of the seed** | `ζ(σ+it)^{±1} ≪_ε |t|^ε` for `σ ≥ 7/8 + ε` (Borel–Carathéodory, three circles) [D]. | [SEEDZETA] [INVZETA] | Uniform inputs for moment and window routes. |
| A8 | **Heilbronn characters and conductors** | Heilbronn characters from Brauer induction; Aramata–Brauer; Artin conductor exponents [D, classical]. | [BRAUER] [ARTIN] | Multiplicity laws for the Galois programme (2.19). |
| A9 | **Counterexample localization as one theorem** | Positive heat threshold ⇒ off-line zero below an explicit height; aperture visibility; index law ⇒ a window with two negative squares [D]. | [HEATLOC] [HIDDEN] [INDEXLAW] | The chain of 2.20(b) without its first link. |
| A10 | **Seed readings on SRT and PBM** | The two-sided theorems of prime-log windows and the regularized prime series at rate `3/8` [D]. | [SRT] [PBM] | Uniform seed table on all rulers. |

## 2.2 Open mathematical problems

| # | Problem | Exact missing content | Routes | Nature |
|---|---|---|---|---|
| B1 | **A lever or a better seed for `w`** | `Θ ≤ b ⇒ Θ ≤ T(b) < b` for `ζ`, using Dirichlet series, functional equation and unit Euler parameters together [PAIRSNOBITE] | all W-routes (P1, P8) | Classical open. |
| B2 | **The design count `U^{1−δ}`** | The number of rows of the cubic probe in amplitude bin `δ` at most `U^{1−δ+ε}`, giving `13/15` [BALANCED] | producer, all W | Open (2.4). |
| B3 | **A pre-Cauchy–Schwarz saving** | Signed off-diagonal saving `s > 0` in the floor-bin row Gram; `3/4` needs `s ≥ 1/12` [SIGNEDGRAM] [SAVING] | producer, MC, JAS | Open (2.5). |
| B4 | **A sign-line completion** | A completion of a Möbius-signed Gauss monomial of period `k ≥ 7` priced at `k/2` [SIGNPRICE] [SIGNLINE] | producer, MC, JAS | Open (2.21). |
| B5 | **Estimate-free transport** | Every zero of `ζ` in `Re s > 3/5` is a zero of the probe correction (an identity, no estimate) [CORRZERO] [RUNG] | producer, sign-free routes | Open (2.6). |
| B6 | **Complete form at every aperture** | `w = 0` on the log-energy ruler [LOGENERGY0]; the sign of the bare energy [HPEQUIV] [S] | RW, HF, EWU, OWU, ACT, AIP, HAT-C, RN, SZ, SC | RH. |
| B7 | **The fresh-octave form** | A negative form of order `K^β`, `β < 3/8`, from the primes in `(3K, 6K]` on the obstructing direction [TOPOCTAVE] [DOUBLING38IFF] [S] | ACS, RW, HF | A better seed in window form. |
| B8 | **Finite stratum** | Exclude finite positive `κ` for `ζ` [INDEX] | AAL, ACS, ZCG, BAG, PM, W1C | Open; the only Euler–FE world with finite `κ` is archimedean non-tempered [SMALLEIG]. |
| B9 | **Landing / window non-attainment** | Bounded Hadamard threshold [LANDING-TFAE]; or the prime error `o(x^β)` on arbitrarily late windows of one ratio [NONATTAIN] | AAL, ZCG, SRT | Open. |
| B10 | **ZAL** | Bounded dyadic mollified moments at every length `T^θ` [DEPTHLADDER] | WD, MZF, ZCG | Classical: mollifier lengths beyond known ranges. |
| B11 | **Clustering at the resolved height** | Bounded number of deep off-line zeros per unit window, uniformly in height [MARGINDEPTH] | ACS, RW, SRT | Open. |
| B12 | **Prime-weighted cofactor cancellation** | Beat the isolated top residue [COFACTORS] | AAL, BAG, ZCG | Open. |
| B13 | **Heat collisions near time zero** | No real branch time in `(0, 9/128]` [ZCG] [NEWMAN]; a heat law using the density [HEATSPACING] | ZCG, LA, PTR | RH for the first; open for the second. |
| B14 | **A restriction on conjugation** | A relation in `B` excluding noncritical orbits [REFLECTION] [PARTIALFLIP] | Galois, ZCG | Open. |
| B15 | **A selecting gate principle** | A statement about `ζ` false for every non-tempered gate deformation [P2LOG2] [EULERCOLUMN] [S] | PM, HF | Open. |
| B16 | **Pair correlation beyond bandwidth one** | Signed bound on the trans-threshold surplus [SEVENTY] [PROPALT] | census | Classical open. |
| B17 | **Higher source constraints** | All-order flags, quartic charge, character sign [TH] [GTA] [ECP] | TH, PA, GTA, ECP, HCF | RH-equivalent receivers. |
| B18 | **Global arithmetic intersection theory** | Diagonal with logarithmic self-pairings, index theorem, scaling symmetry [DIAGONAL] | ACS, F₁ | Open (the `𝔽₁` problem). |
| B19 | **Unbounded Jensen degree** | Reality in every degree [LA] | LA | RH. |
| B20 | **Forcing without coincidence** | A forcing law for `ζ` outside rational Euler identities [BANDFORCE] | SQF, ZCG | Open. |

## 2.3 Frankenstein routes

**Rule.** An assembly of rulers is a ruler [MEASURING]. A Frankenstein proof must contain a lever, a contracting stage map, or the three atoms, and each piece must fail on the world that lacks its structure.

**Assembly I — the producer chain to the frame centre.** Pieces: (1) the coupled-tower contraction `Θ₀ ≤ max(σ₀, c/(k−1))` for any frame tower with per-level zero transfer [TOWERFIX]; (2) towers on the sign line `(k/2, k)` have values in `(½, K/(2(K−1))]` [SIGNLINE]; (3) the estimate floor `σ₀` of the probe (`7/8` integrated, `20999/24000` written, `> 40535/46328` for the present estimates, `13/15` with B2, `5/6 − s` with B3) [VERTEXPOS] [SUBSEED] [FARKAS] [BALANCED] [SAVING] [S]; (4) every rung transfers to `ζ` and all Dirichlet `L` [LADDERTRANSFER]; (5) covering levers give RH [COVERLEVERS]. If for every `K` a sign-line completion of period `≥ K` exists (B4) and the estimate floor of its probe lies below `K/(2(K−1))` (B2, B3 and beyond), the levers cover `(½, 7/8]` and RH follows [D]. **Missing pieces:** B4 (identity level) and the estimate floor at every period (analytic; `σ₀ → ½` needs `s → 1/3`). This is the only assembly whose pieces all lie on one producer.

**Assembly II — three atoms from three programmes.** ZAL from the depth ladder at every `θ` [DEPTHLADDER]; the finite stratum from the packet dichotomy and the filters [INDEX] [COFACTORS]; Landing from a bounded Hadamard threshold [LANDING-TFAE]. RH ⇔ the three [THREEATOMS]. **Missing:** B10, B8, B9.

**Assembly III — AAL from windows, ZAL from moments.** Window non-attainment of the prime error gives AAL [NONATTAIN]; two-prime cone bounds or prime towers also give AAL [AKLT]; under AAL, RH ⇔ ZAL [AKLT]. **Missing:** non-attainment or the coupling bound; B10.

**Assembly IV — gates.** Euler-column purity ⇔ temperedness [EULERCOLUMN]; RH ⇔ the bare half-line energy is nonnegative [HPEQUIV] [S]; the standalone deficit of a non-tempered gate at aperture `log 2` is `−2 log 2 (cosh((α−½)log 2) − 1)`, zero exactly at the tempered point [P2STANDALONE] [S]. **Missing:** a decomposition of the bare energy into gate terms that are nonnegative for unit gates (2.7). Without it the assembly is a dictionary.

**Assemblies that do not close, with the reason.**

| Assembly | Reason |
|---|---|
| Gluing → doubling law → half-plane | The gluing data support exactly `√2` [SUBEULER] [S]; the fresh-octave form is a reading of `w` [TOPOCTAVE] [D]. |
| `A₂` multiple Dirichlet series → estimates | All rank-two boundaries exceed `7/8` [A2REJECT]. |
| Probe bootstrap on an assumed zero-free region | Twist-based low estimates return the zero; the high-side count is insensitive [TWISTRETURN] [ROWCOUNTAT] [D]. |
| World I → edit → Euler–FE rigidity | Fake-edit defects do not decay [EDITDEFECT]; rigidity needs decay [RIGIDITY]. |
| Rational Euler identities → forcing | Orders preserved, Brauer relations cancel `ζ`, shifted margins `≥ 9/16` [WITTORD] [BRAUERCANCEL] [SHIFTMARGIN]. |
| Hawking–Page stability → exclusion | Stability holds at every `R` with or without RH [SADDLE] [S]. |
| Finite-aperture certificates → RH | Prime-2 deformations pass them [P2LOG2] [S]. |
| Finite heat windows → whole-fibre purity | No whole-fibre intertwiner [HEAT-NOGO]. |
| Gauss towers of mixed completed frames | Value `≥ 3/5` [MIXED]. |
| Any chain of receivers at exponent zero | Each link is RH. |

## 2.4 A breakthrough question below RH and below a new quasi-RH

### Question: is the number of rows of the cubic probe in amplitude bin `δ` at most `U^{1−δ+ε}`?

**Setting.** The compensated cubic probe with scales `X = Z^{lx}`, `Y = Z^{ly}` and slot length `ℓ` has low boundary `5/6 + M/12 − ℓ/6 + (M + ℓ − 1)₊/2`; its high side is controlled bin by bin through a row count `R(δ)` [VERTEXPOS]. With the published count — built from inverse and plain witnesses — the published geometry is a vertex at `7/8` [VERTEXPOS]; rescaling reaches `20999/24000` [SUBSEED] [S], and no geometry of the present estimates passes `40535/46328` [FARKAS] [S]. With the count `U^{1−δ}` in every bin, the balanced geometry `(2/5, 2/5, 1/5)` has low boundary `13/15` and negative high side [BALANCED]; below `13/15` the floor bin blocks every geometry [VERTEXFLOOR]. Every rung of the ladder, `13/15` included, transfers to `ζ` and all Dirichlet `L`-functions [LADDERTRANSFER].

**Question.** Prove that the rows in bin `δ` number at most `U^{1−δ+ε}`.

**Why it is less hard than RH and than a new quasi-RH from scratch.** It is one counting estimate inside an existing proof; continuation, reciprocity, the low side and the transfer are in place. It needs no estimate at exponent zero and no new analytic object.

**Why it is a breakthrough.** It moves the only seed by an estimate, from `20999/24000` to `13/15`, past the ceiling of the present estimates, on `ζ`, every Dirichlet `L`-function and every ruler at once [LEVERTRANSPORT]; it shows that the vertex is a property of the witness count, not of the probe; and it reaches the floor of the design, so that every further step is known to need B3.

**First lemma.** Write the bin condition as a large-values condition for sextic residue sums over `ℤ[ω]` (a row lies in bin `δ` when its prime amplitude is `≍ U^{−δ/2}` times the trivial size) and bound the number of large values by a large-values inequality for the sextic characters of the rows, against the published witness count [ROWCOUNTAT]. The binding bin is `δ = 79/204` [A2CHAIN].

**Rejection test.** If the rows of one bin are phase-coherent in the sense of the dependent sextic twists (row root numbers `G(c)γ₂(c)²`), the large-values count saturates at the witness count; record the exact exponent. Then `13/15` needs a different design.

**Filter.** T1: not RH. T2: decided by a proof or by an explicit excess of rows. T3: consequence written in Lean as rungs of the ladder [LADDERTRANSFER] [BALANCED]. T4: no finite window decides it. T5: false for prime edits (no reciprocity, seed false) [EDIT]. T6: the published count is not refuted. T7: no module proves the count.

## 2.5 A breakthrough in the search for a producer

### Question: do the sextic rows of the probe carry a signed off-diagonal saving before Cauchy–Schwarz?

**Setting.** Cauchy–Schwarz over the column shell bounds the bilinear floor sum by `(Σ|b|²)` times the diagonal plus the signed off-diagonal Gram `Σ_{u₁≠u₂} α(u₁)ᾱ(u₂) Σ_m Φ(u₁,m)Φ̄(u₂,m)`, preserving every phase [SIGNEDGRAM]. Every Cauchy–Schwarz or rank-two model has saving `s = 0` and floor `5/6`; a saving `s` gives `5/6 − s`: `3/4` at `s = 1/12`, `2/3` at `1/6`, `½` at `1/3` [SAVING]. Squaring a row sum loses the finiteness of `W(A₂)` [A2DOUBLE]; low estimates through the twists return the zero [TWISTRETURN].

**Question.** Is `|Σ_{u₁≠u₂} α(u₁)ᾱ(u₂) Σ_m Φ(u₁,m)Φ̄(u₂,m)|` smaller than its absolute majorant by a power of the row length, for the actual sextic rows and amplitudes?

**Why it is the right place.** It is the one input that every producer of the Gauss class needs below `5/6`, and the corpus has no tool for it: the large sieve for cubic and sextic residue symbols (the Heath-Brown type, external) is not in the corpus, and every tool that is (rank-two series, twist expansions, convexity) gives `s = 0` [SAVING] [A2REJECT]. The question uses the size of the coefficients (unit Gauss-sum normalizations), as the shifted-pair world demands [PAIRS].

**What exists.** After subtraction of the reciprocal target, each completed row is a combination of sextic and cubic residue characters with square-root Fourier coefficients, and lattice Poisson bounds its signed error on one modulus [ROWCANCEL] [S]: the cancellation inside a row is proved; the cancellation between rows is the open part.

**First lemma.** For one dyadic shell, write the off-diagonal entry for a pair `(u₁, u₂)` as a complete sextic character sum to modulus `u₁ū₂` over the column variable; separate the pairs where both characters are trivial (no cancellation, with a common phase [D]) and bound their number; apply the Weil bound to the rest. The saving `s` is the exponent by which the exceptional pairs are sparse.

**Payoff.** `s ≥ 1/12` with B2 gives `ζ` zero-free on `Re s > 3/4`; `s ≥ 1/6` gives `2/3`; each transfers [LADDERTRANSFER]. **If the answer is no** (coherent rows): the Gauss producer class is capped at `5/6`, and the W-face needs a producer outside it.

**Filter.** T1–T4 as in 2.4. T5: false for edits and for shifted pairs (no unit normalizations). T6: the escape model and Gram identity are proved [SAVING] [SIGNEDGRAM]. T7: no saving is proved.

## 2.6 Without positivity, Weil positivity or spectral arguments

**Reading of the exclusion.** Excluded: every argument whose engine is the sign of a quadratic or Hermitian form (Weil, windows, Hodge index, PSD, Li, de Branges, joint ancestry, KMS positivity) and every realization of zeros as a spectrum. Kept: exact identities, analytic continuation, Poisson and Voronoi summation, Hadamard factorization, Galois and monodromy, integrality, size estimates used inside identity-driven arguments. The `7/8` and `20999/24000` proofs are of this kind: a probe, its continuation and moment estimates, no sign of a form [SEEDZETA] [SUBSEED] [S].

**What the corpus fixes.** Forcing through rational Euler identities is excluded [WITTORD] [BRAUERCANCEL] [SHIFTMARGIN]; one exact transport between different `L`-functions is proved: the probe correction vanishes in `Re s > ½` exactly where the weight-one sextic Grössencharacter rung vanishes at `6s − 3`, and `Θ_corr = (3 + Θ_rung)/6` both ways [CORRZERO] [RUNG] [RUNG3148]. The link from `ζ` to the correction runs through the probe, which is controlled only above its estimate floor `σ₀`; above `σ₀` every zero of `ζ` is a zero of the correction, because the probe is holomorphic there and `ζ` divides it [D].

### Question: does the probe continue to the centre of its frame by identities alone?

Prove that the compensated cubic probe continues holomorphically to `Re s > 3/5` by exact summation identities (Poisson and Voronoi for the cubic theta coefficients, the functional equations of the Hecke family), with no size estimate. Equivalently: every zero of `ζ` with `Re ρ > 3/5` is a zero of the correction, i.e. `6ρ − 3` is a zero of the rung.

**What a positive answer gives.** An expanding forcing law `x ↦ 6x − 3` from `ζ` into the rung family on `(3/5, 1)`. With a seed for the rung family (the `7/8` machine on weight-one Grössencharacters), `Θ ≤ 31/48` [RUNG3148]; with the same continuation at every level of the coupled tower, `Θ ≤ 3/5` [TOWERFIX] [GROSSENTOWER]; with a sign-line completion of period `k` (2.21), `Θ ≤ k/(2(k − 1))` [SIGNLINE]; covering all periods gives RH [COVERSUB] [D]. Every step is an identity or a transport; no form is signed.

**Why it is the right sign-free question.** It moves the estimate floor out of the zero transport: every bound on `Θ` from this producer is `max(σ₀, frame centre)` [TOWERFIX], so the sign-free content is the frame, and the question asks whether the frame acts without the estimates. It uses the Dirichlet series (theta coefficients), the functional equation (theta reflection) and the arithmetic of the primes (cubic reciprocity) together; prime edits and Euler worlds have no probe.

**First lemma.** Write the probe as a Mellin transform of a finite combination of cubic theta coefficients against the rows; identify the dual side after Poisson summation with a Dirichlet series of the rung family times explicit factors, and compute its abscissa of absolute convergence. If that abscissa is `≤ 3/5`, continuation is exact; if it equals the floor `σ₀`, the floor is a property of the probe, not of the estimates — record the dual series that carries it.

**Filter.** T1 not RH; T2 decided by an identity or by an explicit dual series with abscissa `> 3/5`; T3 consequence through [TOWERFIX] and [RUNG3148]; T4 no finite window; T5 false for edits and Euler worlds; T6 the zero-locus identity of the correction is proved [CORRZERO]; T7 not answered.

## 2.7 Under the hypothesis: RH is a phenomenon of AdS with a modular horizon

**What the corpus fixes.** The functional equation is a KMS condition at inverse temperature one; the KMS state exists whether RH holds or not, and positive kernels with the same KMS condition have all zeros off the line [KMSPOS] [FAKEHORIZON]. The two-boundary strip width reads `w` [ADS]. Causal, Euler, FE, passive, axis-unitary prime-2 deformations ring down arbitrarily slowly [ADS-NOGO] and pass the certified aperture `log 2` [P2LOG2] [S]. The confined half-line state has an exact Hawking–Page transition at `W₀` off RH; stability, outerness, cyclicity and endpoint competition hold with or without RH; RH ⇔ the bare energy is nonnegative [HPTRANS] [SADDLE] [WEAKEND] [HPEQUIV] [S]. The standalone energy of a prime-2 gate at aperture `log 2` is exactly `−2 log 2 (cosh((α − ½) log 2) − 1)`: negative for every non-unitary gate, zero at the unitary one [P2STANDALONE] [S].

Every physical axiom formalized is satisfied by a fake. The one physical property no fake has is the unitarity of the prime gates: every Euler–FE countermodel of the corpus has a non-unitary gate at some place [TEMPERED] [P2FACTOR] [SMALLEIG] [D].

### Question: is the bare horizon energy a sum of gate energies, each nonnegative exactly when its gate is unitary?

Find a decomposition `E_bare = Σ_p E_p + E_∞` of the bare half-line energy, with `E_p` built from the local factor at `p` together with an assigned share of the pole and Gamma terms, such that `E_p ≥ 0` whenever the gate at `p` has unit parameters and `E_∞ ≥ 0` for the Riemann Gamma factor. With [HPEQUIV] this gives RH.

**The door (decidable, not RH).** (1) For one gate, the standalone ladder energy is the template: compute `E_p` for a single deformed gate at every aperture and show that it vanishes identically at the unitary point (the corpus has it at `log 2` [P2STANDALONE] [S]). (2) For finite products of gates with the Riemann Gamma factor, prove or refute that the cross terms between gates vanish after the pole is distributed — the explicit formula is linear in the contacts, so the question is whether a signed regrouping exists; the sign twin, which differs from `ζ` in the sign of one contact, is the test the regrouping must fail [TWIN] [DIPOLE]. (3) Check the fake horizons: they have no gates and `E_∞` alone; their off-line zeros show where `E_∞` cannot be nonnegative by itself [FAKEHORIZON].

**Why it opens the path.** It replaces an all-aperture sign by a local sign at each gate, which is exactly where every fake differs from `ζ` (R11). If step (2) fails, the physical route has no local form and reduces to the W- and I-faces.

## 2.8 Under the hypothesis: RH is a problem of topology or geometry

**What the corpus fixes.** The neutral windows carry the index: some window has `r` negative squares iff `r ≤ 1 + κ` [INDEXLAW]. Doubling a window is local: the true window of ratio `6K+1` is the un-updated glued matrix minus the fresh contacts `k ∈ [3K+2, 6K+1]`, which act only on the end-to-end block `(R, 2R] × ((3K+1)R, (6K+1)R]` [TOPLOCAL] [S]; the un-updated glued matrix has two negative squares up to a shift of order `√K` [TOPJUMP] [S]; a doubling factor below `√2` forces the fresh block to remove one of them [TOPOCTAVE] [S]. Haynsworth inertia and response matrices are in the corpus (AGZ window gluing).

### Question: is there an index theorem for the doubling step?

Prove that the number of negative squares removed in the step `K → 2K` equals the signature of a finite octave form — the Schur complement of the end-to-end block, built from the primes in `(3K, 6K]` — and identify a deformation class of contact data in which that signature is invariant and which contains both `ζ` and a model whose octave signatures are computable.

**What it gives.** `κ` becomes a sum of local octave signatures plus a boundary term at the certified ratio, the shape of an Atiyah–Patodi–Singer formula; RH becomes the vanishing of every octave signature beyond the first, and a homotopy within the invariance class to a model with vanishing signatures proves it. The sub-Euler model, whose best factor is `√2` [SUBEULER] [S], is the test: its octave signatures do not cancel the jump, so it must lie outside the invariance class.

**First lemma.** Apply Haynsworth inertia to `N(6K+1) = N(3K+1) − F_K` with `F_K` supported on the end-to-end block [TOPLOCAL] [S], and write the inertia difference as the inertia of an explicit `R × 3KR` octave form.

## 2.9 Does RH need a new field of mathematics?

The corpus does not prove that existing mathematics is insufficient. It proves that readings of `w` cannot move it [MEASURING]; that every structure of `ζ` taken without one other has worlds realizing every abscissa a mechanism would exclude [TWOTHIRDSWORLD] [COSH] [EDIT] [PAIRSNOBITE]; that the complete Euler–FE structure with unit multiplicities is rigid [RIGIDITY]; and that every Euler–FE countermodel is non-tempered somewhere, while a single tempered Euler column is pure [EULERCOLUMN] [TEMPERED] [SMALLEIG] [D]. A proof must act where Euler product, exact functional equation, unit Euler parameters and integral primes are all present. No current field organizes mechanisms by that requirement.

### Tempered selection theory

**Subject.** `L`-data with four structures — Euler product, exact functional equation, local parameters of unit size at every place (finite and archimedean), integral generalized primes — and the location of their zeros as a function of the data. The field studies which zero-location statements are monotone in the temperedness exponents of the local parameters.

**Objects.** Worlds (Euler worlds, cosh models, prime edits, shifted pairs, prime-2 deformations, compact Selberg zeta functions); local Euler columns and their purity; temperedness exponents `θ_v` (Ramanujan exponent at a finite place, exceptional parameter at the archimedean place); gate energies; `Θ`, `Θ∞` and `κ` as functions on the space of data.

**Language.** Gate, unitary gate, temperedness defect, joint use, world test, purity of a column, rigidity point.

**Criteria.** Every theorem names the structures it uses; a mechanism is admitted only if it fails on every world missing one structure; every result is a purity law (zeros pinned by temperedness), a rigidity law (data pinned), or a transfer law (location moved by a stated amount per unit of temperedness defect).

**Questions.** Does the abscissa of an Euler–FE datum of degree two exceed `Θ` by at most its temperedness exponent, as the shifted pairs attain [PAIRSABS]? Is there a gate-local energy (2.7)? Does the purity of tempered Euler columns [EULERCOLUMN] propagate to the global zeros along a deformation that keeps the exact functional equation? Are the off-line zeros of a finite gate deformation of `ζ` with exact functional equation exactly the zeros of its non-tempered gates and of `ζ` [P2FACTOR] [D]?

**Tools.** Euler-column purity; the world theorems as acceptance tests; Euler–FE rigidity; the ruler calculus restricted to tempered families; gate energies at finite aperture.

**First theorems that would count.** A transfer law `Θ(F) − ½ ≤ C·θ(F) + (Θ − ½)` on a degree-two class containing the shifted pairs, proved with the size of the coefficients; a gate-local energy identity at one aperture.

## 2.10 Does an AAL proof or falsification need a new field?

**What the corpus fixes.** AAL fails exactly at a finite top layer [AAL-LAYER]; then `ψ(x) − x = x^β T(log x) + O(x^{β−η})` with `T` a nonzero trigonometric polynomial, attained on every late window [FINOSC]; non-attainment on arbitrarily late windows of one ratio gives AAL [NONATTAIN]; AAL ⇔ every line has at most one or infinitely many zeros to its right [UNITGAPAAL]; in world I an edit removes the layer [WORLDI], and fake-edit defects do not decay [EDITDEFECT].

### Finite-oscillation arithmetic

**Subject.** Arithmetic error terms at their top rate: when can the Chebyshev error, the Mertens function or a prime trace be, at its top rate, a finite trigonometric oscillation in `log x`? AAL is the statement that it never is.

**Objects.** Top layers; finite oscillations `x^β T(log x)`; attainment windows; prime-phase boxes; edits removing a layer; cofactor currents and their filters [COFACTORS].

**Questions.** (1) Can a finite oscillation at rate `β > ½` coexist with the equidistribution of prime phases on late windows? (2) What is the finest window on which a finite oscillation is attained, and does a sieve lower bound for primes on that window contradict attainment? (3) For falsification: which finite top layers are consistent with the exact functional equation, the trace functional equation and the quartet Galois constraints [REGIMEA] [KLEIN]?

**Criteria.** Every statement compares an error with its own rate (no exponent claimed); AAL and ZAL kept apart; every mechanism tested on Euler worlds, where finite layers exist.

**Tools.** Bohr almost periodicity; Kronecker–Weyl equidistribution of `t log p`; Landau's one-sided theorem; non-attainment receivers [NONATTAIN]; cofactor filters [COFACTORS]; world-I edits.

## 2.11 Under the exclusion of positivity and spectra: a new field

### Reciprocity transport theory

**Subject.** Exact zero transport between `L`-functions of different families produced by reciprocity: probes, corrections and rungs of metaplectic covers, frames `(c, k)` acting as `b ↦ (c + b)/k`, towers of frames, and their prices in Stickelberger arithmetic. No sign of a form, no spectrum.

**Objects.** Probes and corrections [CORRZERO]; rungs and frame abscissae [RUNG]; towers [TOWERFIX]; Stickelberger prices and the sign line [SIGNPRICE] [SIGNLINE]; completed and joint theta series; estimate floors.

**Language.** Frame, centre, price, sign line, completion cost, rung, tower, estimate floor, exact transport.

**Criteria.** Every transport is an identity or a continuation; every price is computed in Stickelberger arithmetic; every result fails for prime edits and Euler worlds; the excluded class of rational Euler identities is the boundary [WITTORD] [BRAUERCANCEL].

**Questions.** Exact continuation of the probe to its frame centre (2.6); joint completions on the sign line (2.21); rung seeds for every level of a tower; whether towers on the sign line reach `½` with uniformly controlled rungs.

**Tools.** Cubic and sextic theta series, Kubota–Patterson reciprocity, Poisson and Voronoi summation over `ℤ[ω]`, Stickelberger valuations [STICKEL], tower contraction.

## 2.12 Under the AdS modular-horizon hypothesis: a new field

### Gate thermodynamics of the arithmetic horizon

**Subject.** The modular horizon with prime gates as local scatterers: the KMS structure fixed by the functional equation [KMSPOS], the Hawking–Page phase law [HPTRANS] [S], and the contribution of each gate to the free energy.

**Objects.** Gates (local Euler factors as local S-matrices) and their unitarity; gate energies [P2STANDALONE] [S]; bare and confined energies; the Hawking–Page point `W₀`; fake horizons without gates [FAKEHORIZON]; prime-2 deformations [ADS-NOGO].

**Language.** Gate, unitary gate, gate energy, bare energy, Legendre intercept, transition point, latent jump, fake horizon.

**Criteria.** Exact divisor, pole and Gamma factors retained; every principle separates `ζ` from prime-2 deformations and from fake horizons; no physical axiom replaces an estimate.

**Questions.** Gate-local energy (2.7); additivity of gate energies over finite gate sets; the latent jump at `W₀` as a function of the gates; ringdown rate as a gate quantity, with the deformation law `(1 − α)/2` as calibration [ADS-NOGO].

**Tools.** KMS and thermofield constructions [THERMOFIELD]; Legendre duality of the confining energy [LEGENDRE] [S]; Euler-column purity [EULERCOLUMN].

## 2.13 Under the topology/geometry hypothesis: a new field

### Octave index theory of the window tower

**Subject.** The neutral windows as a two-parameter family (ratio, block size) of finite Hermitian matrices, the localization of the doubling step on the end-to-end block, and the index as a sum of local octave invariants.

**Objects.** Neutral windows [INDEXLAW]; doubling steps and fresh octaves [TOPLOCAL] [S]; un-updated glued matrices and their jump [TOPJUMP] [S]; octave forms (Schur complements of end-to-end blocks); margins and their rates [MARGINSINF]; sub-Euler models [SUBEULER] [S].

**Language.** Octave, octave form, octave signature, jump, invariance class, boundary term at the certified ratio.

**Criteria.** Every invariant computed from the literal contacts; the sub-Euler model and the sign twin as tests [SUBEULER] [TWIN]; no crossing-free deformation assumed [DEFORM].

**Questions.** The index theorem for the doubling step (2.8); invariance classes of octave data; the octave signature of `ζ` at the first octaves past the certified ratio.

**Tools.** Haynsworth inertia, Schur complements, response matrices, Green calculus [GREEN], floor-graph norms [FLOORNORM] [S].

## 2.14 A research programme to construct `𝔽₁`

**Aim.** A geometry in which `Spec ℤ` has a square with the actual arithmetic diagonal, in which one inequality on that square is a theorem of the geometry, and in which the Euler parameters are unitary for a structural reason. Not a one-element field: `0 ≠ 1` excludes that.

**What the corpus fixes.** Frobenius graphs meet in their contact ideals, the first prime contacts are `(2)` and `(3)` [CONTACT] [CONTACT-EX]; integral ghost Witt vectors have `F_kV_k = k`, `V_kF_k ≠ k` [WITT]; a completion of window couplings with one negative square forces logarithmic self-pairings [DIAGONAL]; the neutral index is `≤ 1 + κ` [INDEXLAW]; Artin completions, Brauer induction [ARTIN] [BRAUER]; the seed for every ray class function of `ℚ(ω)` [RAYSEED] [S]; the Kummer calibration curves are maximal, `#C = Q² + 1 + 2Qg`, with parity classification and Cartier vanishing after one constant-field period [KUMMERMAX] [KUMMERPARITY] [KUMMERCARTIER] [S]; the window calculus alone has no producer [SUBEULER] [S].

| Stage | Content | Gate |
|---|---|---|
| F1 Calibration | The Kummer curve in window language; Weil's inequality for it derived from the curve's geometry, not from the explicit formula | The step that uses Frobenius is named; its analogue on `Spec ℤ` is the target object. |
| F2 Diagonal | The logarithmic self-pairing derived from contact order and an archimedean boundary datum, compatible under gluing | Reproduces [DIAGONAL] without copying the Weil matrix. |
| F3 Unitarity | A structure on the square that makes every Euler parameter of unit size (for curves: Frobenius unitary on `H¹` after normalization) | Fails for shifted pairs and prime-2 gates [TEMPERED] [P2FACTOR]. |
| F4 Symmetry | A correspondence on the square scaling the neutral form by a factor `≠ 1` on a nonzero subspace, or a no-go in a stated class | Either outcome; the no-go reduces `𝔽₁` to a language for ACS. |
| F5 Index | Index law as a theorem of the geometry, functorial under refinement | Agrees with [INDEXLAW]. |
| F6 Reciprocity | Conductors and Artin characters as cycles; the seed as an intersection inequality on the family of `ℚ(ω)` [RAYSEED] [S] | Index statements for Dedekind squares. |

**Acceptance tests.** Recover `(1,2) = (2)`, `(1,3) = (3)`; explain the negative diagonal; separate `Λ` from the sign twin [TWIN]; fail for Euler worlds and non-tempered models. **Stop rule.** If F1 shows that the curve proof uses only the explicit formula, the window calculus is a ruler in both settings and F3 is the whole programme.

## 2.15 A research programme to close WD

**The route.** WD reads `w` through Möbius polynomials and mollified moments: at one height [WD]; through cofinal long moments with one exponent `K` [WD-LONG]; and through the slope loss of the stage map `θ ↦ 2θ`, whose least value is `2w`, with loss `3/4` unconditional and `8999/12000` from the written seed [SLOPE] [SLOPE34] [WIDTHSUB] [S] [D]. The depth ladder gives depth `< 1/(2θ) + ε` from bounded dyadic moments at length `T^θ` [DEPTHLADDER]; mollifiers of length `T^θ` have moment `≥ 1 + 1/(8 + 6θ)` [NECLEN].

**Diagnosis.** WD is a complete ruler; closing it needs a slope loss below the seed's, which is a better seed, and loss `0` for unbounded `θ`, which is RH.

| Stage | Content | Gate |
|---|---|---|
| D1 Seed table | Instantiations on every WD ruler | Done at `3/8` [RULERS]; transport of `8999/24000` is work. |
| D2 Stage map | A slope law with explicit loss | Exact: least loss `2w` [SLOPE]. |
| D3 Negative moments | Two-sided long-mollifier / negative-moment link | Separates RH forms from simple-zero forms. |
| D4 ZAL engine | Bounded dyadic moments at every `θ > 1` | ZAL (Assembly II). |
| D5 Signed off-diagonal | One off-diagonal term of a long moment with a signed bound beating its absolute budget, using `|μ| ≤ 1` | Shifted pairs have unbounded Möbius coefficients; the bound must fail for them [PAIRS]. |
| D6 Decision | No candidate for D5 | WD stays a ruler and the ZAL engine. |

**Closure criteria.** Common `K`, unbounded `θ`, `θ`-dependent constants, cofinal heights, the arithmetic mollifier itself [WD-LONG].

## 2.16 A research programme to close ACS

**The route.** RH ⇔ bounded margins ⇔ a gap at every cutoff ⇔ doubling factor one [ACS] [GAPRH] [DOUBLINGONE]; the margin rate at polynomial block size is `w` and the best doubling factor `2^w` [MARGINSINF] [DOUBLING]; a factor in `(1, 2^{3/8})` exists iff `w < 3/8` [DOUBLING38IFF] [S], so the written seed gives such factors [WIDTHSUB] [D] [S]. Every bounded-weight model has the factor `√2`, and the gluing data cannot do better [SQRT2] [SUBEULER] [S]; the fresh octave acts only on the end-to-end block [TOPLOCAL] [S].

**Reading.** The window calculus is a complete finite model of `w` and `κ`. It has no producer in gluing form; its fresh-octave form is a reading of `w`. ACS closes only by importing a producer or an index theorem.

| Stage | Content | Gate |
|---|---|---|
| C1 Converse rate law | Margin `≥ −C K^{w+ε}` | Done [MARGINDEPTH] [MARGINPOLY] [MARGINRULER]. |
| C2 Doubling | Factor below `√2` from gluing data | Excluded [SUBEULER] [S]; survivor: the fresh-octave form. |
| C3 Octave index | Index theorem for the doubling step (2.8) | `κ` as a sum of octave signatures. |
| C4 Certificates | `Q = 2` fourth step [FOURTHRED] [S] | Finite apertures do not separate `ζ` from deformations [P2LOG2] [S]. |
| C5 Critical state | Hawking–Page structure (exact) [HPTRANS] [S] | The sign of the bare energy. |
| C6 Clustering | Remove `1 + log R` | The margin ruler at all block sizes. |
| C7 Acid test | Gap of the Kummer-calibration windows by stage maps | Names the step that needs Frobenius (F1 of 2.14). |

**Decision record.** ACS is retired as a producer. Survivors: index law, margin and doubling rulers, ratio ladder, first-step dipole, top-octave locality.

## 2.17 A research programme to close ZCG

**The route.** RH ⇔ forward and mirror loops transport alike at every positive nonbranch time [ZCG]; `Λ ≤ 9/128` [NEWMAN]; `G₊` has index `≤ 2`, proper iff one parity law [HEAT-PARITY]; proper forces `8 | N(t)` [HEAT-EIGHT]; an odd number of nonreal quartets gives `G₊ = W` [ODDQUART]; an isolated off-centre double collision gives `G₊ = W` [DOUBLECOLL]; `N(t) ≤ 1` at times accumulating at `0` gives RH [HEATUNIT]; finite windows are heat monodromies, fibres are not [HEAT-FINITE] [HEAT-NOGO]; width alone gives no heat-time bound [HEATSPACING]. ZCG is sign-free.

| Stage | Content | Gate |
|---|---|---|
| Z1 Sign of `G₊` | A3 | `G₊ = W` closes every parity mechanism. |
| Z2 Arithmetic content | Isolated-quartet regimes: negative radicand, partial flips, Klein action [REGIMEA] [PARTIALFLIP] [KLEIN] | One invariant of the arithmetic group respected by heat continuation. |
| Z3 Heat law with density | A two-sided heat-time law in width and spacing for `ξ` | Turns `Λ` into a ruler. |
| Z4 Transport | The estimate-free transport of 2.6 | A forcing law into the rung family. |
| Z5 Finite stratum | With B8 | ZCG closes with Landing and ZAL. |

**Rejection tests.** Whole-fibre intertwiners; global conjugation by one finitary heat element; "large monodromy implies real zeros": excluded or empty.

## 2.18 A research programme to close MC/JAS

**The route.** Möbius Hilbert form subpolynomial ⇔ RH [MC]; the signal is a Möbius sum and a ruler [SIGNAL] [SIGNAL-WIDTH]; dressed PSD at level one ⇔ RH [JAS]; a signal bound `O(Z^b)` gives level `b + ½ + ε` [SIGNAL-JAS]. MC and JAS are W-face rulers fed by the cubic producer.

| Stage | Content | Gate |
|---|---|---|
| M0 Seeds | `7/8` [L]; `20999/24000` written [SUBSEED] [S] | Integration (A2). |
| M1 Present estimates | Optimal geometry in `(40535/46328, 20999/24000]` (A1) | Ceiling of the present estimate system. |
| M2 Row count | The count `U^{1−δ}` (2.4) | `13/15`. |
| M3 Cross-row saving | Signed off-diagonal Gram saving (2.5); per-row cancellation exists [ROWCANCEL] [S] | `5/6 − s`. |
| M4 Target extraction | Minimum-energy filters and Poisson restoration [MINFILTER] [POISSONPROJ] [S] | Long weighted rows. |
| M5 Frames | Sign-line completion at period `≥ 7` (2.21) | Frame centre `k/(2(k−1))`. |
| M6 Exact transport | Continuation to the frame centre (2.6) | Removes the estimate floor from the transport. |

**Rejection tests.** Principal averaging [AVERAGE]; more Gauss factors in the same completion budget [WALLGEN]; rank-two series [A2REJECT]; reversible sewing [RFHM].

## 2.19 A research programme: Galois theory of the zeros

A finite polynomial cannot have infinitely many distinct roots; the algebraic object is a compatible family of finite equations. **Fixed.** Complete-fibre traces give monic polynomials with the centred zeros as roots [FIBRES]; mixed traces satisfy `T_t(n) = n·T_t(1/n)` [MIXEDTRACE]; `E/B` is a compositum of finite Galois layers [PRIME-FIBRES]; orbit size = residue degree [ORBIT]; `Re ρ = ½` iff `p^{2Re ρ} ∈ B` and an automorphism realizes the reflection [REFLECTION]; conjugation central iff ordinate values lie in `B` [CONJCENTRAL]; quartet criterion [QUARTET]; orbits leave quartets only through same-ordinate off-line quartets [LEAVEQUART]; square relations carry an even number of critical heights [SQREL]; an isolated off-line quartet has a negative radicand at every prime, square class ⇔ no partial flip, traces symmetric under `(Re ρ − ½) ↔ i Im ρ`, Klein action at a shared critical ordinate [REGIMEA] [PARTIALFLIP] [TRACEFACTOR] [KLEIN]; finite windows match heat monodromy, fibres do not [HEAT-FINITE] [HEAT-NOGO].

| Stage | Content | Gate |
|---|---|---|
| G1 Sign of `G₊` | A3 | Whether heat monodromy adds a constraint. |
| G2 Representation ring | Heilbronn characters, Aramata–Brauer, conductors (A8) | Multiplicity laws across Galois groups. |
| G3 Cross-height relations | Algebraic relations among traces of different heights [TRACE-INDEP] | Presentation of `B`. |
| G4 Partial flips | Decide whether an isolated off-line quartet admits a partial flip in `Gal(E/B)`, using the swap symmetry of its traces [TRACEFACTOR] | A forced square class at off-line heights. |
| G5 Restriction on conjugation | A relation in `B` from the Euler product separating the reflection lift from conjugation | The only door to location in this theory. |

**Limit.** The theory locates zeros only through the position of conjugation relative to the reflection.

## 2.20 A programme assuming RH is false

The assumption guides the search; a disproof must concern the actual `ζ`.

**The three worlds.** F (`0 < κ < ∞`), S (ZAL, Landing fails), D (ZAL fails) [THREEATOMS]. **Constraints on an off-line zero `ρ = ½ + δ + iγ`.** `|δ| ≤ 3/8` [MMD_STRIP], `≤ 8999/24000` written [WIDTHSUB] [S]; no coincidence `ζ(ρ/k) = 0` for `k ≥ 7` [K7] [S]; `ζ(½ + iγ)` flattened to order `δ²` [FLATTEN]; `Λ ≥ δ²/(200 log γ)` above `e^{1600}` [NEWMANLOW]; multiplicity `≤ ((3/(8π))cos((4π/3)δ) + ε) log γ` [MULT]; density `30/13` [DENSITY]; at most `1 − 0.6725` off the simple critical class [CENSUS]; each right zero adds a negative square to some window [INDEXLAW]; the half-line state has a Hawking–Page point at a finite `W₀` [HPTRANS] [S]; off AAL the prime error is a finite oscillation attained on every late window [FINOSC]; an isolated off-line quartet at a pure height has negative radicand at every prime [REGIMEA].

**(a) Proving falsity analytically.** A noncomputational disproof is a structural lower bound for one gap quantity: window binding beyond pole capacity [POLECAP]; two negative squares [INDEXLAW]; a violated integer lag inequality [INTLAG]; a nonreal Jensen root [JENSEN]; a positive heat threshold [HEATLOC]. The direction with content: make the half rulers two-sided (mass-normalized floor, heat with density, long-mollifier/negative moments, margin at all block sizes), so that a lower bound for a moment, a heat constant or a margin becomes an off-line zero.

**(b) A concrete counterexample without computation.** World F is the natural target: a finite configuration of quartets, consistent with the Galois regimes (negative radicands, partial-flip criterion, Klein action at shared ordinates) [REGIMEA] [PARTIALFLIP] [KLEIN], with `8 | N(t)` if `G₊` is proper and `G₊ = W` if the number of quartets is odd [HEAT-EIGHT] [ODDQUART], and with a finite oscillation of the prime error [FINOSC]. The prime-2 deformations show the shape such a world takes when a gate is non-unitary: ladders of off-line zeros spaced `2π/log p`, invisible below the Nyquist aperture `½log p` [P2NYQ] [S]. [D] A counterexample for `ζ`, whose gates are unitary, cannot arise from such a ladder; the localization chain (A9) lacks its first link, a structural positive lower bound for one gap quantity.

**AAL distinction.** One off-line zero falsifies RH, not AAL; falsifying AAL needs a finite top layer above the tail abscissa [AAL-LAYER].

## 2.21 The one big question

### Does a Möbius-signed Gauss monomial of period `k ≥ 7` have a completion priced on the sign line?

**Setting.** Every Möbius-signed Gauss monomial over `𝔽_p` has a conjugate of Stickelberger defect at least `½`; monomials of length at most three are priced exactly `k/2` at period `k`; frames `(k/2, k)` have centre `k/(2(k−1))`, and towers on this sign line take values in `(½, K/(2(K−1))]`, with wall `½` not attained [SIGNCOST] [SIGNPRICE] [SIGNLINE] [SIGNWALL]. The completed Gauss pairings, which complete each factor by its own theta series, cost `c ≥ 2k/3 − 1` and are priced at least at the sign line [PRICE] [PRICEABOVE]; the two lines meet at `k = 6`, which is the wall `3/5` of the whole completed class, mixed towers included [GAUSS] [WALLGEN].

**Question.** Construct, for some `k ≥ 7`, a joint completion of a Möbius-signed monomial — one automorphic object (a theta series on a higher metaplectic cover, a coefficient of a Weyl-group multiple Dirichlet series, or a Jacobi-sum family) completing all factors at once — whose functional equation prices the frame at `c = k/2`; or prove that every completion in a stated class costs `c ≥ 2k/3 − 1`.

**Why it is less hard than AAL, RH and quasi-RH.** It is a question about Gauss sums and the functional equations of explicit theta-type objects; it contains no analytic estimate and no statement about zeros.

**Why it decides several routes at once.**
1. *If yes:* the frame ladder of the producer is not capped at `3/5`: frames with centres `7/12, 4/7, …` exist, and with a completion at every period the frame side of Assembly I reaches `½` [SIGNLINE] [COVERSUB]. The remaining obstacle of MC, JAS, WL, WD, SQF, CHMD and every W-ruler fed by the producer is then the estimate ladder alone (2.4, 2.5, 2.6).
2. *If no (a cost theorem):* the Gauss producer class is capped at `3/5` whatever estimates are proved; every W-route that relies on it is retired as a route to RH and survives only as a ruler, and the W-face needs a producer outside Möbius-signed Gauss monomials.
3. Either way it fixes the target of 2.6: exact continuation to the frame centre is worth `½ + O(1/k)` or `3/5`.

**First lemma.** Compute the Stickelberger price of the coefficients of the `A₂` cubic multiple Dirichlet series as a function of the period, with its Weyl-group functional equations as the completion; the corpus has its convexity and reflection data [A2CHAIN] and the valuation of every prime-field Gauss sum [STICKEL]. The rank-two series fails the estimate ladder [A2REJECT]; its frame price is not computed, and it is the first joint completion available.

**Filter.** T1 not RH; T2 decided by a construction or a cost theorem; T3 consequence written in Lean (tower values on the sign line [SIGNLINE], covering criterion [COVERSUB]); T4 no finite window; T5 frames of centre below `2/3` fail on Euler worlds, so the mechanism must use the functional equation of the completion [FRAMEWORLD]; T6 Stickelberger pricing and the sign line are proved; T7 the corpus records that realizing the price needs a different completion and has none.

<!-- source references -->
[A2CHAIN]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheRankTwoMultipleDirichletSeriesConvexityHull.lean#L504
[A2DOUBLE]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheRankTwoMultipleDirichletSeriesConvexityHull.lean#L779
[A2REJECT]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheRankTwoMultipleDirichletSeriesConvexityHull.lean#L696
[AAL-LAYER]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheFailureOfTheAbscissaLawIsAFiniteLayer.lean#L33
[ACS]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/AUniformLowerBoundOnTheMarginOfTheWindowMatricesForcesTheRiemannHypothesis.lean#L505
[ADS]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/TheEternalAdSPrimeMarkedDictionary.lean#L884
[ADS-NOGO]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/CausalIdentitiesCannotForceQuarterRingdown.lean#L1600
[AKLT]: ../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/PrimeTowersAndConeCouplingProduceAsymptoticAbscissaLaw.lean#L306
[ARTIN]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/EveryArtinLFunctionHasACompletionWithAFunctionalEquation.lean
[ARTINSEED]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheArtinFunctionOfTheCubeRootsOfTwoCarriesTheSeed.lean#L147
[AVERAGE]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheAverageRowIsBlindToTheTarget.lean#L148
[BALANCED]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L541
[BANDFORCE]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/ExpandingForcingLawsRulersAndTheRiemannHypothesis.lean#L154
[BRAUER]: ../../../formal/GaloisForLFunctions/RHTower/Artin/ArtinBrauerInductionTheorem.lean#L206
[BRAUERCANCEL]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/WittMonomialsShiftedConvolutionsAndBrauerCancellation.lean#L497
[CENSUS]: ../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/CriticalLineZeroProportion.lean#L1042
[COFACTORS]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheGrowingFilterReachesPolynomiallyManyCofactors.lean#L1
[CONJCENTRAL]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ConjugationIsCentralAtAZeroIffItsOrdinateValueLiesInThePrimeTraceField.lean#L279
[CONTACT]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheConductorOfTwoGraphsIsTheirContact.lean#L22
[CONTACT-EX]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheFirstTwoPrimeContactIdeals.lean#L14
[CORRZERO]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/GrossencharacterLFunctionsHaveZerosInTheRightHalfStrip.lean#L621
[COSH]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L142
[COVERLEVERS]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/ExpandingForcingLawsRulersAndTheRiemannHypothesis.lean#L352
[COVERSUB]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L438
[DEFORM]: ../../../formal/GaloisForLFunctions/EdgeHodgeTheory/TheIndexComputedByDeformation.lean#L107
[DENSITY]: ../../../formal/GaloisForLFunctions/RHTower/PrimeShortIntervalsSeventeenThirtiethsUnconditional.lean#L25
[DEPTHLADDER]: ../../../formal/GaloisForLFunctions/SelectiveArithmetic/TheCancellationAndDepthLadder.lean#L67
[DIAGONAL]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheCouplingsOfAWindowAreNotMixedAreasAndTheIndexForcesLogarithmicSelfPairings.lean#L268
[DIPOLE]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheDipoleOfWeilsGreenMatrixCarriesTheFirstOverlapStep.lean#L364
[DOUBLECOLL]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheTurnAroundAnIsolatedDoubleCollisionOffTheCentreIsTheExchangeOfTwoPairs.lean#L162
[DOUBLING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L217
[DOUBLING38IFF]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L771
[DOUBLINGONE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheLossOfTheMarginIsBoundedOrPolynomial.lean#L81
[ECP]: ../../../formal/GaloisForLFunctions/RHTower/Representation/EndpointCharacterCriterion.lean#L62
[EDIT]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L186
[EDITDEFECT]: ../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/TheWorldOneScenarioTable.lean#L38
[EULERCOLUMN]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/RamanujanIsRealityOfAnEulerColumn.lean#L91
[FAKEHORIZON]: ../../../formal/GaloisForLFunctions/ArithmeticScatteringHolography/TheKMSStripOfTheHorizon.lean#L322
[FARKAS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheTrueVertexBelowSevenEighths.lean#L328
[FIBRES]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheFieldOfCompleteFibreTraces.lean#L486
[FINOSC]: ../../../formal/GaloisForLFunctions/FloorFreeArithmetic/ThePrimeNumberTheoremIsNotAttainedOnWindows.lean#L68
[FLATTEN]: ../../../formal/GaloisForLFunctions/ArithmeticDiscreteness/TheDepthOfAnFEPairIsReadOnTheLine.lean#L113
[FLOORLOG2]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheTwoPrimeWindowHasAPositiveWeilFloorAtEveryBlockSize.lean#L48
[FLOORNORM]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing.lean#L97
[FOURTH]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheTwoPrimeWindowAndRatioThreeHoldAtEveryBlockSize.lean#L285
[FOURTHRED]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheTwoPrimeWindowAndRatioThreeHoldAtEveryBlockSize.lean#L310
[FRAMEWORLD]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L166
[GAPRH]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheGroundEnergyOfAnApertureIsAGapOfEveryWindowInsideIt.lean#L408
[GAUSS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L595
[GREEN]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheContinuumGreenKernelIsTheLimitOfTheTowerAndIsNegativeOnlyAlongTheCharge.lean
[GROSSENTOWER]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheCubicProbeIsACoupledTowerReachingThreeFifths.lean#L1577
[GTA]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean#L293
[HEAT-EIGHT]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ARealCollisionOfMassNotDivisibleByEightGivesEverySignedPermutation.lean#L165
[HEAT-FINITE]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheArithmeticGroupActsOnContinuedWindowsOfZerosAsHeatMonodromy.lean#L81
[HEAT-NOGO]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheArithmeticGroupIsAHeatMonodromyOnFiniteWindowsButNotOnAFibre.lean#L62
[HEAT-PARITY]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheForwardMonodromyGroupIsProperExactlyWhenItsTurnsObeyOneParityLaw.lean#L204
[HEATLOC]: ../../../formal/GaloisForLFunctions/RHTower/XiSliceHeatThresholdVerificationHeight.lean#L94
[HEATSPACING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheHeatTimeIsTheWidthTimesTheSpacing.lean#L109
[HEATUNIT]: ../../../formal/GaloisForLFunctions/FloorFreeArithmetic/TheHeatFlowHasTheCountOfItsLimit.lean#L60
[HECKESEED]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean#L602
[HIDDEN]: ../../../formal/GaloisForLFunctions/WindowVisibilityLaw/ShallowClusterExclusionAndTaperedCrystalBarrier.lean#L1179
[HPEQUIV]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L352
[HPTRANS]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L440
[INDEX]: ../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheFiniteStratumIsThePacketIndexDichotomy.lean#L85
[INDEXLAW]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheIndexOfTheNeutralPartIsOnePlusTheNumberOfZerosRightOfTheLine.lean#L166
[INTLAG]: ../../../formal/GaloisForLFunctions/RHTower/WeilLagFunctionInteger.lean#L541
[INVZETA]: ../../../formal/GaloisForLFunctions/RingdownOfTheCubicCover/UnconditionalScatteringResonanceBounds.lean#L246
[JAS]: ../../../formal/GaloisForLFunctions/RHTower/JointAncestryLevelOneCapstones.lean#L35
[JENSEN]: ../../../formal/GaloisForLFunctions/VerifiedHeightRungs/TheJensenPolynomialsThroughDegree31922AreRealRooted.lean#L21
[K7]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L212
[KLEIN]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/GaloisClosureAndMixedTracesOfAnIsolatedQuartet.lean#L445
[KMSPOS]: ../../../formal/GaloisForLFunctions/ArithmeticScatteringHolography/TheKMSStripOfTheHorizon.lean#L125
[KUMMERCARTIER]: ../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/FunctionField/KummerCartierConstantPeriod.lean
[KUMMERMAX]: ../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/FunctionField/KummerMaximalCount.lean
[KUMMERPARITY]: ../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/FunctionField/KummerParityClassification.lean
[LA]: ../../../formal/GaloisForLFunctions/FiniteFreeProbability/FiniteFreeDeBruijnNewman.lean#L466
[LADDERTRANSFER]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheCubicCoverSpecializationOfTheBindingBin.lean#L344
[LANDING-TFAE]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean#L145
[LEAVEQUART]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/AnOrbitLeavesItsQuartetOnlyThroughAnotherOffLineQuartetOfTheSameOrdinate.lean#L43
[LEGENDRE]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L212
[LEVERTRANSPORT]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L85
[LOGENERGY0]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWidthIsTheRateOfTheWeilFloorInTheLogarithmicEnergy.lean#L441
[MARGINDEPTH]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesSinksAtTheRateOfTheWidth.lean#L789
[MARGINPOLY]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesSinksAtTheRateOfTheWidth.lean#L810
[MARGINRULER]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesIsARulerAtPolynomialBlockSize.lean#L782
[MARGINSINF]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesIsARulerAtPolynomialBlockSize.lean#L804
[MC]: ../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean#L219
[MEASURING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L79
[MINFILTER]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/PhaseExtraction/MinimumTargetWeights.lean#L229
[MIXED]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/MixedTowersOfLeversStayAboveTheBestCentre.lean#L419
[MIXEDTRACE]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheMixedPrimeTracesSatisfyTheFunctionalEquation.lean
[MULT]: ../../../formal/GaloisForLFunctions/SquareRootThreshold/SechMultiplicityEnvelope.lean#L91
[NECLEN]: ../../../formal/GaloisForLFunctions/ArithmeticProduction/TheNecessaryLengthOfAMollifier.lean#L716
[NEWMAN]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L155
[NEWMANLOW]: ../../../formal/GaloisForLFunctions/RHTower/Heat/TheHeatDetectionRateIsQuadraticInTheDepth.lean#L520
[NONATTAIN]: ../../../formal/GaloisForLFunctions/FloorFreeArithmetic/ThePrimeNumberTheoremIsNotAttainedOnWindows.lean#L151
[ODDQUART]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/AnOddNumberOfQuartetsOfNonrealZerosAtARealTimeGivesEverySignedPermutation.lean#L372
[OFFCENTRE]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ACollisionAwayFromTheCentreExistsAtAForwardTime.lean#L625
[ORBIT]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheDegreeOfTheResidueFieldOfAZeroIsTheSizeOfItsOrbit.lean#L50
[P2FACTOR]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/CausalIdentitiesCannotForceQuarterRingdown.lean#L95
[P2LOG2]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/PrimeTwoDeformedApertureLogTwoTest.lean#L278
[P2NYQ]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/PrimeTwoDeformedApertureLogTwoTest.lean#L169
[P2STANDALONE]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/PrimeTwoDeformedApertureLogTwoTest.lean#L233
[PAIRS]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L295
[PAIRSABS]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L259
[PAIRSNOBITE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L267
[PARTIALFLIP]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/GaloisClosureAndMixedTracesOfAnIsolatedQuartet.lean#L308
[PBM]: ../../../formal/GaloisForLFunctions/RHTower/RegularizedLogZetaAbscissa.lean#L402
[POISSONPROJ]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TargetProjection/SexticPoissonProjection.lean#L249
[POLECAP]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/TheBindingEnergyOfAWindowIsAtMostItsPoleCapacity.lean#L251
[PRICE]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L383
[PRICEABOVE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheGaussPairingsArePricedAboveTheSign.lean#L126
[PRIME-FIBRES]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheFibreFieldsOverThePrimeTracesAreFiniteGaloisAndGenerateTheSpectralField.lean#L1
[PROPALT]: ../../../formal/GaloisForLFunctions/RHTower/Zeta23SeventyPercentOrSimpleNearLine.lean#L21
[QUARTET]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheOrbitOfAZeroLiesInItsQuartetIffItsWidthAndOrdinateValuesSolveAQuadraticOverThePrimeTraceField.lean#L281
[QUARTETFORCE]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/TheClosedConfigurationsOfHalvingAndDoubling.lean#L120
[RAYSEED]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRayClassFunctionOfTheEisensteinFieldCarriesTheSeed.lean#L130
[REFLECTION]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ALiftOfTheReflectionIsConjugationExactlyWhereTheWeightLiesInThePrimeTraceField.lean#L55
[REGIMEA]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/GaloisClosureAndMixedTracesOfAnIsolatedQuartet.lean#L247
[RFHM]: ../../../formal/GaloisForLFunctions/RHTower/JointAncestryAllPrimeReversibleRFHMSewingNoGo.lean#L37
[RIGIDITY]: ../../../formal/GaloisForLFunctions/EulerFETransportTheory/DecayingFunctionalEquationsDetermineThePrimes.lean#L486
[ROOTCOINC]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L174
[ROWCANCEL]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/PhaseExtraction/SmoothArithmeticRowCancellation.lean#L214
[ROWCOUNTAT]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L436
[RULERS]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L55
[RUNG]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCorrectionOfTheCubicProbeCarriesTheAbscissaOfItsRung.lean#L126
[RUNG3148]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCorrectionOfTheCubicProbeCarriesTheAbscissaOfItsRung.lean#L167
[SADDLE]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L660
[SAVING]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheRankTwoMultipleDirichletSeriesConvexityHull.lean#L830
[SEEDZETA]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean#L631
[SEVENTY]: ../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/TotientGridGaussianRegularization.lean#L637
[SHIFTMARGIN]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/WittMonomialsShiftedConvolutionsAndBrauerCancellation.lean#L426
[SIEGEL]: ../../../formal/GaloisForLFunctions/RHTower/SiegelTheorem.lean#L108
[SIGNAL]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSignalOfTheZetaKernelIsAMoebiusSum.lean#L1
[SIGNAL-JAS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSignalExponentIsThePositivityLevel.lean#L165
[SIGNAL-WIDTH]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSignalExponentIsTheZeroAbscissa.lean#L212
[SIGNCOST]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMoebiusSignCostsHalfAUnitAtSomePlace.lean#L188
[SIGNEDGRAM]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheFloorBinBilinearGramIdentity.lean#L138
[SIGNLINE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheShortMoebiusMonomialsPayExactlyHalf.lean#L139
[SIGNPRICE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheShortMoebiusMonomialsPayExactlyHalf.lean#L97
[SIGNWALL]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheShortMoebiusMonomialsPayExactlyHalf.lean#L157
[SLOPE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestSlopeLossOfTheLongMomentsIsTwiceTheWidth.lean#L110
[SLOPE34]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestSlopeLossOfTheLongMomentsIsTwiceTheWidth.lean#L95
[SMALLEIG]: ../../../formal/GaloisForLFunctions/CompactHyperbolicSurfaces/SmallEigenvalueZeta.lean#L25
[SQFRULER]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/WittMonomialsShiftedConvolutionsAndBrauerCancellation.lean#L268
[SQREL]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ASquareRelationAmongHeightRadicandsHasAnEvenNumberOfCriticalHeights.lean#L33
[SQRT2]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L149
[SRT]: ../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/ScaleLocality/PrimeLogarithmicWindows.lean#L145
[STICKEL]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheGaussSumsOfAPrimeFieldCarryStickelbergersValuation.lean#L316
[SUBDIR]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean#L141
[SUBEULER]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L319
[SUBHECKE]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean#L34
[SUBPROBE]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsHighTransport.lean#L1231
[SUBSEED]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/SubSevenEighthsZeroFreeHalfPlane.lean#L147
[TARGETFILTER]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheNonprincipalFilterRecoversTheTarget.lean#L161
[TEMPERED]: ../../../formal/GaloisForLFunctions/RHTower/NonTemperedShiftedZetaPairCountermodel.lean
[TH]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaHermiteTraceFlag.lean#L250
[THERMOFIELD]: ../../../formal/GaloisForLFunctions/HTGeometry/Thermofield/PrimeLogApplications.lean
[THREEATOMS]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean#L68
[TOPJUMP]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L472
[TOPLOCAL]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing.lean#L650
[TOPOCTAVE]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWindowGluingDoublingFactorStopsAtRootTwo.lean#L663
[TOWERFIX]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L1140
[TRACE-INDEP]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheTracesOfRationallyIndependentHeightsAreAlgebraicallyIndependent.lean#L201
[TRACEFACTOR]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/GaloisClosureAndMixedTracesOfAnIsolatedQuartet.lean#L372
[TRUEVERTEX]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheTrueVertexBelowSevenEighths.lean#L109
[TWIN]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheFirstOverlapStepOfWeilsFormFailsForTheSignTwin.lean#L744
[TWISTRETURN]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L780
[TWOTHIRDSWORLD]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L95
[UNITGAPAAL]: ../../../formal/GaloisForLFunctions/FloorFreeArithmetic/NonAttainmentGivesTheAbscissaLaw.lean#L117
[VERTEXFLOOR]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L499
[VERTEXPOS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean#L333
[WALLGEN]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/MixedTowersOfLeversStayAboveTheBestCentre.lean#L525
[WD]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TheWidthIsReadInOneWindow.lean#L85
[WD-LONG]: ../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/LongMoebiusSecondMomentRigidity.lean#L659
[WEAKEND]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ArithmeticHawkingPagePhaseStructure.lean#L182
[WIDTHSUB]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/EulerDilationAndRootCoincidenceExclusion.lean#L60
[WITT]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/Witt/RaynaudOperatorBoundary.lean#L19
[WITTORD]: ../../../formal/GaloisForLFunctions/ZeroForcingCalculus/WittMonomialsShiftedConvolutionsAndBrauerCancellation.lean#L182
[WORLDI]: ../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/AFiniteLayerCanBeEditedAway.lean#L136
[ZCG]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheForwardMonodromyDeterminesTheReflectionAndTheConjugationOfTheZeros.lean#L186
