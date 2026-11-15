# RH research: consolidated frontier, open problems and research programmes

**State in one paragraph.** The corpus proves one seed: no zero of `ζ`, of any Dirichlet `L`-function, or of the Hecke family of `ℚ(ω)` lies in `Re s > 7/8` [MMD] [MMD_DIR] [MMD_HECKE]. It reads the zero width `w = Θ − ½` exactly through many rulers, and a formal ruler calculus shows that these readings are one number: the seed passes to all of them, and a lever on one is a lever on all [RULERS] [LEVERTRANSPORT]. No lever for `ζ` is proved. The only producer class has a proved wall at `3/5`, also under mixing, composition and minima [GAUSS] [WALLGEN]; its estimates stop at the vertex `7/8` [VERTEX]. Levers valid on Euler products without a functional equation cannot bite below `2/3`, levers valid on functional equations without a Dirichlet series bite nowhere, and the seed fails for prime edits with a power count rate [EULERWORLD] [COSH] [EDIT]. The index face counts the zeros right of the line exactly and its margin is a ruler of `w` [INDEXLAW] [MARGINSINF]. The tail face factors RH into ZAL, the finite stratum and Landing, all open [THREEATOMS].

Evidence: Lean statements read in source at `cf08f8dfc5` with the working tree of 15 Nov 2026 ([W] = untracked working-tree module, [S] = tagged unintegrated by the frontier map); [working log](../../../logs/review-1511-working-log.md). No build or audit was run. Statements marked **[D]** are deductions of this report, to be proved before use. Companion reports: [routes](route-obstacles.md), [walls](walls-ledger.md), [faces](route-unification-ledger.md).

## 2.1 Tasks that are work

Each task has a known method and no unproved sign, rate or uniformity. None of them proves RH.

| # | Task | Concrete output | Inputs | Payoff |
|---|---|---|---|---|
| A1 | **Effective Siegel from the all-moduli seed** | No real zero of any `L(s,χ)` in `Re s > 7/8` is immediate; a short Euler product on `Re s ≥ 7/8 + ε` gives an effective lower bound for `L(1,χ)` of the shape `≫ (log log q)^{−1}`, effective class-number lower bounds, PNT in progressions with error `x^{7/8+ε}` and explicit `q`-dependence, least prime in a progression [D]. | [MMD_DIR]; Siegel is present only ineffectively [SIEGEL] | Conductor-uniform tools for the family routes (CRF, JAS); the classical Siegel problem in effective form. |
| A2 | **Lindelöf right of the seed** | `ζ(σ+it)^{±1} ≪_ε |t|^ε` for `σ ≥ 7/8 + ε` (Borel–Carathéodory, three circles) [D]. | [MMD], polynomial bound for `1/ζ` [INVZETA] | Uniform inputs for moment and window routes. |
| A3 | **Sign of the heat monodromy group** | One forward time with a double zero `ζ₀ ≠ 0` and no other multiple zero; then `G₊ = W` [DOUBLECOLL]. A multiple zero off the centre exists at arbitrarily large forward time [OFFCENTRE]; missing: exact order two and isolation (local analysis on the model loop). | [OFFCENTRE] [DOUBLECOLL] [MOD8] | Decides the sign of the forward monodromy group; with `G₊ = W` the parity mechanism (`8 | N(t)`) carries no information, and ZCG must use arithmetic input. |
| A4 | **`Q = 2` fourth ladder step** | Zero excess (or an explicit failing window) at ratio `103⁸/(100⁸/2) ≈ 3.2099` for cutoff two [FOURTHRED]. | [FOURTH] [LOGLADDER] | Completes the ratio-three ladder at every cutoff. |
| A5 | **Next-aperture certificate** | A rational certificate past the prime-square contact (aperture `½log 5`), in the method of the `log 2` certificate. Existence is not guaranteed: the certificate exists iff the floor is positive there. | [EVENLOG2] [ODDLOG2] [EDGE] | Extends the certified range of RW, EWU, OWU, ACS. |
| A6 | **Grössencharacter rung** | The `7/8` machine for the weight-one sextic Grössencharacter family of `ℚ(ω)`. The frame is a ruler between abscissas: the correction has abscissa `(3 + Θ_rung)/6`, and `7/8` for the rung is the same statement as `31/48` for the correction [RUNG] [RUNG3148] [W]. | [CORRZERO] [GROSSENTOWER] | A seed for the rung family is what the frame tower lacks; it lowers the frame wall below `2/3` and does not move `Θ` (the estimates bind at `7/8`). |
| A7 | **Heilbronn characters and Artin conductors** | Heilbronn characters from Brauer induction; Aramata–Brauer; Artin conductor exponents [D, classical]. | [BRAUER] [ARTIN] | Multiplicity laws across Galois groups (2.19). |
| A8 | **Counterexample localization as one theorem** | Assemble: a positive heat threshold puts an off-line zero below an explicit height [HEATLOC]; the visibility law gives the aperture; the index law gives the window with two negative squares [INDEXLAW] [D]. | [HEATLOC] [HIDDEN] [INDEXLAW] | The chain of 2.20(b), lacking only its first link. |
| A9 | **Integrate the working-tree rulers** | Wire the modules proving the margin ruler at polynomial block size, the doubling ruler (best factor `2^w`) and the rung ruler; carry the factor `1 + log R` through the ACS consumers. | [MARGINRULER] [DOUBLING] [RUNG] [W] | ACS and frame statements become width statements. |
| A10 | **Seed instantiations not in Lean** | Seed readings at `3/8` on the prime-log windows and the regularized prime series, in the form of their two-sided theorems (the Weil-lag reading exists in `TheSevenEighthsStripControlsTheCompletedWaves`) [D]. | [SRT] [PBM] | Uniform seed table across the rulers. |

Moving any ruler below `3/8`, an aperture to infinity, a degree to infinity, or a finite stratum to the empty set is research (2.2).

## 2.2 Open mathematical problems

| # | Problem | Exact missing content | Routes | Nature |
|---|---|---|---|---|
| B1 | **A lever or a second seed for `w`** | A theorem `Θ ≤ b ⇒ Θ ≤ T(b) < b` for `ζ`, or a zero-free half-plane by a mechanism other than the cubic family | all W-routes (P1, P8) | Classical open problem: no zero-free strip `Re s > 1 − δ` is known in the literature beyond the corpus seed. |
| B2 | **Estimates below the vertex `7/8`** | Row count in the binding bin (`13/15`), row mean square at generic size (`5/6`), a signed off-diagonal saving before Cauchy–Schwarz (`5/6 − s`) [VERTEX] [ESCAPE] [SIGNEDGRAM] | producer, MC, JAS | Open; each is a family mean-value problem. |
| B3 | **A source outside the Gauss class** | Möbius sign and independent reflection at frame centre `< 3/5` [GAUSS] [PRICE] | producer | Open (fable question). |
| B4 | **Complete form at every aperture** | `w = 0` on the logarithmic-energy ruler [LOGENERGY0] | RW, HF, EWU, OWU, ACT, AIP, HAT-C, RN, SZ, SC | RH. |
| B5 | **A doubling law from the gluing data** | The best doubling factor of the margin is `2^w` [DOUBLING] [W]; open: a proof of any factor `< √2` by the gluing calculus without the seed, any factor `< 2^{3/8}` at all, or an a priori gap on bound windows [GAP] | ACS, RW, HF | Open; a second producer if solved (2.4). |
| B6 | **Finite stratum** | Exclude finite positive index for `ζ` [INDEX] | AAL, ACS, ZCG, BAG, PM, W1C | Open; not implied by any width bound `> 0`. |
| B7 | **Landing** | Bounded Hadamard threshold as `σ ↓ ½` [LANDING-TFAE] | AAL, ZCG, SRT | Open. |
| B8 | **ZAL** | E.g. bounded dyadic mollified moments at every length exponent `θ > 1` (depth ladder) [DEPTHLADDER] | WD, MZF, ZCG | Classical: mollifier lengths beyond the known ranges are open. |
| B9 | **Critical-state exclusion** | An arithmetic property incompatible with the outer, cyclic, Laplace zero-free state; endpoint sign [HF] [ENDPOINT] | HF, RW, ACS | Open. |
| B10 | **Clustering at the resolved height** | Bounded number of deep off-line zeros per unit window, uniformly in height [MARGINDEPTH] | ACS, RW, SRT | Open (local density type). |
| B11 | **Prime-weighted cofactor cancellation** | Beat the isolated top residue [COFACTORS] | AAL, BAG, ZCG | Open. |
| B12 | **Heat collisions near time zero** | No real branch time in `(0, 9/128]` [ZCG] [NEWMAN] | ZCG, LA, PTR | RH. |
| B13 | **A restriction on conjugation** | An arithmetic relation in `B` that excludes noncritical orbits [REFLECTION] [CONJCENTRAL] | Galois, ZCG | Open. |
| B14 | **A physical selection principle with a rate** | Distinguish integral unit-multiplicity gates from prime-2 deformations and bound the decay [ADS-NOGO] | PM | Open. |
| B15 | **Prime pairs beyond bandwidth one** | Signed bound on the trans-threshold surplus (`70%` needs `I ≤ 7/45` at bandwidth `4/3`) [SEVENTY] [PROPALT] | census | Classical: pair correlation beyond `|α| ≤ 1` is open. |
| B16 | **Higher source constraints** | All-order flags, quartic charge decay, endpoint-character sign [TH] [GTA] [ECP] | TH, PA, GTA, ECP, HCF | RH-equivalent receivers. |
| B17 | **A global arithmetic intersection theory** | Diagonal with logarithmic self-pairings, index theorem, a symmetry that scales the form [DIAGONAL] | ACS, F₁ | Open (the `𝔽₁` problem). |
| B18 | **Unbounded Jensen degree** | Reality in every degree without heat shift [LA] | LA | RH. |

## 2.3 Frankenstein routes

**Rule.** An assembly of rulers is a ruler [MEASURING]. A Frankenstein proof must contain a lever, a contracting stage map, or the three atoms. Routes that only exchange RH-equivalent endpoints supply nothing.

**Assembly I — the window producer: gluing → doubling law → half-plane.** The margin of the neutral windows is an exact ruler of `w` at polynomial block size [MARGINSINF] [W], and so is its doubling factor: a doubling law with factor `λ` gives `w ≤ log₂ λ`, the best factor is `2^w`, and `w = 0` iff every factor above one occurs [DOUBLINGHP] [DOUBLING] [DOUBLINGRH] [W]. The window form is Weil's explicit formula, so it uses the Euler product and the functional equation together — the property the worlds theorems demand of any lever [EULERWORLD] [COSH]. The Green calculus shows that the first overlap step is carried by the sign of the prime-2 contact, through the dipole, and that no contact-sign-blind bound proves it [DIPOLE] [GREEN]. **Missing piece:** a doubling law derived from the gluing data alone (2.4). Every other piece is a theorem, and the missing piece is a statement about finite matrices.

**Assembly II — three atoms from three programmes.** RH ⇔ ZAL ∧ `FiniteOffLine → RH` ∧ Landing [THREEATOMS]. ZAL: bounded dyadic mollified moments at length `T^θ` give eventual depth `< 1/(2θ) + ε` [DEPTHLADDER]; at every `θ` this is ZAL [D]. Finite stratum: the packet index counts distinct right zeros [INDEX]; the growing filter isolates a finite top layer with controlled remainder [COFACTORS]. Landing: a bounded Hadamard threshold [LANDING-TFAE]. **Missing pieces:** moments beyond every known length (B8), prime-weighted cofactor cancellation (B11), a landing mechanism (B7). Each piece belongs to a different route, so partial progress is independent.

**Assembly III — AAL from cones, ZAL from moments.** Bounded undamped coupling on a two-prime cone, or bounded prime towers, give AAL, and under AAL RH ⇔ ZAL [AKLT]. With the ZAL engine of Assembly II this is a two-input proof. **Missing:** the coupling bound and the moments.

**Assemblies that do not close, with the reason.**

| Assembly | Reason |
|---|---|
| World I → edit → Euler–FE rigidity | In world I an edit removes the top layer with a larger zero-free half-plane [WORLDI]; rigidity needs a decaying pointwise functional-equation defect [RIGIDITY], and the defect of such an edit is not small in any decaying sense [WZCROW]. |
| Finite heat windows → whole-fibre purity | Whole-fibre intertwining is impossible [HEAT-NOGO]; uniform nonreal continuation already forces finite support [HEAT-UNIFORM], which then needs B6. |
| Any chain of receivers at exponent zero | Each link is RH; no partial estimate passes. |
| Gauss towers of mixed frames | Value `≥ 3/5` [MIXED]. |

## 2.4 A breakthrough question below RH and below a new quasi-RH

### Question: can the gluing calculus of the windows prove a zero-free half-plane on its own?

**Setting.** A level law assigns to each ratio `3K + 1`, at block size `ρ(K)` with `K¹⁰ ≤ ρ(K) ≤ K^A`, a shift `a(K)` after which the neutral window has at most one negative square; a doubling law with factor `λ` is a monotone level law with `a(2K) ≤ λ·a(K) + c`. The corpus proves, with no hypothesis on zeros: a doubling law with factor `λ > 1` gives `w ≤ log₂ λ` [DOUBLINGHP]; the best factor is exactly `2^w` [DOUBLING]; every factor above `2^{3/8}` occurs, through the seed [DOUBLING38]; `w = 0` iff every factor above one occurs [DOUBLINGRH] [W]. The trivial factor of the calculus is `√2`.

**Question.** Prove a doubling law with some factor `λ < √2` from the gluing calculus alone — Green matrices of the dyadic middle, overlap steps, contact dipoles, the `log 2` floor — without using the cubic family.

**Why it is less hard than RH and than a new quasi-RH.** Any `λ < √2` answers it; for `λ ∈ (2^{3/8}, √2)` the conclusion is already true, so the question asks for a mechanism, not for a new exponent. It concerns finite matrices with entries built from `Λ`, the pole and the Gamma kernel.

**Why it is a breakthrough.** It would be a second producer, independent of cubic reciprocity, and the first centred one: the window is symmetric under the functional equation, a gluing step has no frame cost, so the Gauss wall `3/5` does not apply [WALLGEN]. The window form is the explicit formula, so the mechanism uses the Dirichlet series and the functional equation together, as the worlds theorems require [EULERWORLD] [COSH]. By ruler transport its half-plane holds on every W-route [LEVERTRANSPORT]. Any improvement of its factor below `2^{3/8}` is an improvement of quasi-RH; factor `1` is RH [DOUBLINGRH].

**First lemma.** The first overlap step is carried by the dipole `2w⟨W₀e, 𝒢_D Ce⟩` of the Green matrix of the middle; no bound blind to the sign of the contact proves it [DIPOLE]; the continuum Green kernel is negative only along the charge [GREEN]. Prove a contraction of the conditional coupling at the balanced split of every ratio with a constant below the trivial one; the contact dipole is the term that must carry it, since the sign twin differs from `ζ` exactly there [TWIN] [D].

**If the answer is no** (a model with the same gluing data and best factor `√2`): ACS, RW, HF, HAT-C, EWU, OWU, ACT, AIP and SC are retired as producers in their gluing form and stay rulers; the frontier contracts to the producer ladder (2.5), the lever (2.21) and the atoms.

**Filter.** T1: not RH for `λ > 1`. T3: [DOUBLINGHP] turns `λ` into a half-plane. T5: fails for the sign twin [TWIN]. T6: dipole, Green kernel, ladder are named. T7: the doubling ruler and the best factor are theorems [W]; no theorem derives a factor from the gluing data alone.

## 2.5 A breakthrough in the search for a producer

### Question: do the multiple Dirichlet series of the cubic cover of `GL₃` supply the estimates that stop the seed at `7/8`?

The producer has two ladders. The frame ladder (identities) ends at `3/5` [GAUSS]. The estimate ladder binds first: `7/8` is a vertex where three estimates meet — the low bound, the row count in the bin `δ = 79/204`, the dual length of the reflected rows — and every geometry with low boundary below `7/8 − 1/4000` has a positive high exponent [VERTEX]. Below that: `13/15` needs a different row count in the binding bin, `5/6` the row mean square at its generic size, and escape below the free floor needs a bilinear signed saving `s > 0` in the row Gram, with half-plane `½ + (5/12)(4/5 − (12/5)s)` at order six [ESCAPE] [SIGNEDGRAM] [D]. All three missing inputs are **family mean values** of cubic Gauss sums with their signs.

Weyl-group multiple Dirichlet series of metaplectic Eisenstein series on covers of `GL_r` are the classical objects whose double meromorphic continuation and group of functional equations encode exactly such family mean values (for the cubic cover of `GL₃`: twisted first moments of cubic `L`-series over `ℚ(ω)`). The corpus contains the cubic cover of `GL₂` only (the MMD source) and no multiple Dirichlet series.

**Question, sharpened.** Does the `A₂` cubic multiple Dirichlet series, continued in both variables with its Weyl-group functional equations, give (a) the row count in the binding bin, (b) the row mean square at generic size, or (c) a signed off-diagonal saving `s ≥ 1/12` in the row Gram of the cubic probe?

**Payoff.** (a) gives a seed `13/15`, (b) `5/6`, (c) with `s = 1/12` the half-plane `3/4` and with `s = 1/6` `2/3` [D]. Each is an unconditional improvement of quasi-RH for `ζ` and every Dirichlet `L`-function, by the same transfer as the existing seed [MMD_DIR].

**Why this is the right place to look.** The seed fails for prime edits with a power count rate [EDIT]: its proof uses the arithmetic of the rational primes beyond the count, namely cubic reciprocity. Multiple Dirichlet series carry the same reciprocity one rank higher and produce signed family averages before any norm is taken — the step every corpus no-go identifies as missing (norms are blind to parity, phase and target [AVERAGE]).

**First lemma.** Identify the corpus row sums of the binding bin with a specialization of the `A₂` series, and compute the exponent its two-variable continuation gives for that specialization, against the published row count.

**Rejection test.** If the two-variable continuation reproduces only absolute (norm) bounds for the specialization, the class of multiple Dirichlet series at rank two is excluded for the estimate ladder; record the boundary exponent.

## 2.6 Without positivity, Weil positivity or spectral arguments

**Reading of the exclusion.** Excluded: every argument whose engine is the sign of a quadratic or Hermitian form (Weil, windows, Hodge index, PSD, Li, de Branges, joint ancestry) and every realization of zeros as a spectrum. Kept: exact identities, analytic continuation, Hadamard factorization, Galois and monodromy, integrality, counting; inequalities used as estimates inside an identity-driven argument.

### Question: does one off-line zero of `ζ` force a second zero, by an exact identity that uses `ζ`'s own functional equation, without a coincidence hypothesis?

A **forcing law** is a theorem: if `ζ(ρ) = 0` with `Re ρ > ½`, then some explicit `φ(ρ)` is a zero of `ζ` (or of an explicitly related Dirichlet series known to be regular there). The corpus has two instances of this shape, both conditional: a halving pair `ζ(ρ) = ζ(ρ/2) = 0` forces the zero `1 − ρ/2` and so `Θ ≥ 2/3` [HALVING]; an orbit of the prime-trace Galois group leaves its quartet only through another off-line quartet of the same ordinate [LEAVEQUART].

**What a positive answer gives.** If `Re φ(ρ) > Re ρ` (depth expansion), iterating from any off-line zero exceeds the seed after finitely many steps: RH [D]. If `φ` expands only on a band, a gap law — the question of 2.21, reached with no positivity.

**Why it is the right sign-free question.** The worlds theorems say a lever needs the Dirichlet series and the functional equation together [EULERWORLD] [COSH]. A forcing law is the sign-free form of that joint use: the Euler product supplies the identity, the functional equation supplies the reflection that closes the orbit. The Galois layers supply the bookkeeping: the off-line zeros of one height pair up under `ρ ↦ 1 − ρ̄`, so the product of the reflection radicands of a height is a negative non-square in `B` (for some prime) whenever a critical zero sits at that height [RADICAND], and square relations among heights carry an even number of critical heights [SQREL].

**First lemma.** For the identities `Σλ(n)n^{−s} = ζ(2s)/ζ(s)` and `Σμ(n)²n^{−s} = ζ(s)/ζ(2s)`, combined with the functional equation, determine the complete set of zero configurations that are closed under the induced transport. Halving pairs force `Θ ≥ 2/3` [HALVING]; decide whether a single quartet with no partner can be closed under the transport.

**Filter.** T5: on cosh models the Dirichlet-series identity is absent; on Euler worlds the reflection is absent. T7: no forcing law without coincidence is in the corpus.

## 2.7 Under the hypothesis: RH is a phenomenon of AdS with a modular horizon

**What the corpus fixes.** The eternal-AdS prime-marked correlator is analytic on the strip of width `δ` iff all zeros satisfy `Re ρ ≤ 1 − 2δ`; `δ = 1/16` unconditionally; `δ = 1/4` is RH [ADS]. Causal, Euler, FE, passive, unitary prime-2 deformations ring down arbitrarily slowly [ADS-NOGO]. The critical threshold of the arithmetic window energy is infinite iff RH; off RH it is attained by a unique outer cyclic critical state [HF] [POLAR]; the confinement energy is strictly concave and selects an endpoint, with no endpoint sign [ENDPOINT] [ENDPOINT-BOUND]. The thermodynamic endpoint competition is the mechanism of the AdS Gauss–Bonnet phase structure [THERMO]; the prime-log carrier has a thermofield realization [THERMOFIELD].

### Question: is the off-line world the black-hole phase of an arithmetic Hawking–Page transition, and is that phase thermodynamically excluded?

Read the window energy as a free energy at inverse temperature given by the aperture, the critical threshold as the transition temperature, the critical half-line state as the black-hole saddle and the polar (pole-dominated) configuration as thermal AdS. RH is the statement that the transition never happens (threshold `+∞`).

**Concrete form.** (1) Identify the source-tilted confinement energy whose minimum sits at an endpoint with the actual critical threshold (the corpus proves the endpoint selection but not this identification [ENDPOINT]). (2) Prove the endpoint sign: the thermal endpoint wins at every confinement scale. (3) Show that the would-be black-hole saddle — unique, outer, cyclic, Laplace zero-free [HF-OUTER] [HF-CYCLIC] [HF-BOUNDARY] — has the specific heat of a small AdS black hole (negative), so it cannot be the minimizer it is defined to be.

**Why it opens the path.** It replaces an all-aperture positivity statement by a statement about one saddle with fully known structure, and it is a dynamical principle that the prime-2 deformations do not inherit automatically: the deformations change the gate at 2 and with it the free energy, so (2) is a source-selective statement — the property R5 asks for.

**Test.** Compute the sign of the endpoint competition on the certified window `log 2`, where the floor is known [FLOORLOG2] [S], and on the deformed system of [ADS-NOGO] at the same aperture; the principle must separate them.

## 2.8 Under the hypothesis: RH is a problem of topology or geometry

**What the corpus fixes.** The index of the neutral windows is `1 + κ` at most and attains every value up to it [INDEXLAW]; along the aperture the index grows exactly at null modes [NULLMODES]; the margin, the depth of the second negative square, sinks at rate `w` [MARGINSINF] [W]; deforming a Hermitian form to a positive one without crossing is equivalent to its positivity [DEFORM]. So the zeros right of the line are eigenvalue crossings of an explicit family of finite matrices over a parameter space (aperture, ratio, block size, cutoff).

### Question: is there a spectral-flow formula for the window family whose local density is computable from the explicit formula and integrates to zero?

Spectral flow counts crossings with sign; for the aperture family it equals the index growth `κ` [D]. An Atiyah–Patodi–Singer type formula would write it as the integral of a local density (the variation of an `η`-type invariant built from the prime contacts, the pole and the Gamma kernel) plus boundary terms at the certified range (ratio `< 4`, aperture `≤ log 2`, where the flow vanishes [OVERLAP] [FLOORLOG2]).

**Why it opens the path.** Positivity is then not proved directly: it follows from the vanishing of a topological integral, for which symmetry arguments are available — the functional equation acts on the parameter space as a reflection, and the density may be odd under it. Crossing-free deformation is excluded as a shortcut [DEFORM]; a spectral-flow formula is a different statement, because it counts crossings instead of forbidding them.

**First test.** Write the density on the first resonant apertures, where the prime-square contact enters [EDGE], and check it against the certified index one; then compute it for the sign twin, where the first overlap step fails [TWIN] — the density must see the contact sign [DIPOLE].

## 2.9 Does RH need a new field of mathematics?

The corpus does not prove that existing mathematics is insufficient. It does prove three structural facts that no existing field organizes: readings of `w` cannot move it [MEASURING]; every partial structure of `ζ` — Euler product without functional equation, functional equation without Dirichlet series, prime counts with a power rate — admits worlds that realize every abscissa the mechanism would exclude [EULERWORLD] [COSH] [EDIT]; and the complete structure is rigid — a decaying pointwise functional-equation defect with unit multiplicities forces the rational primes [RIGIDITY], while positive real weights allow arbitrarily slow defects with off-line zeros [SLOWDEFECT]. A proof must therefore use the full structure at a point where the structure is rigid. The field this calls for is:

### Rigidity-to-location theory (deformation theory of arithmetic `L`-data)

**Subject.** The space of arithmetic `L`-data — Euler data (norms, multiplicities, local factors), functional-equation data (Gamma factor, conductor, root number), count data (error rates) — with `ζ` as a point, and the zero configuration, the width and the index as functions on that space. The field studies how the location of zeros depends on the data near a rigid point.

**Objects.** Worlds (Euler worlds, cosh models, two-sided prime edits, Beurling systems, positive-weighted systems, compact Selberg data); defect functionals (pointwise and mean functional-equation defects, count defect, multiplicity defect); zero maps `data ↦ configuration`; the abscissa `Θ`, tail abscissa `Θ∞` and index `κ` as functions; topologies on data in which these functions are or are not semicontinuous.

**Language.** Rigid point, defect topology, modulus of location (how far zeros move per unit defect), world (a datum on which a mechanism is tested), joint use (a mechanism invisible on every world missing one structure).

**Criteria.** (i) Every theorem states the defect topology. (ii) A mechanism is admitted only if it fails on each world missing one structure — the worlds theorems are acceptance tests. (iii) Results are either rigidity (data pinned), location (zeros pinned), or transfer (a modulus of location).

**Questions.** What is the modulus of continuity of `Θ` at `ζ` in each defect topology? Between the mean-square topology (fakes exist [WZCROW]) and the pointwise-decay topology (only `ζ` [RIGIDITY]), where does location become forced? Is the index `κ` upper semicontinuous at `ζ` in some topology in which `ζ` is approximable by data with `κ = 0` (then W1C-type closure gives RH [W1C])? Which identities of `ζ` survive every deformation that keeps rigidity, and do they force zeros (2.6)?

**Tools to develop.** Edit calculus with exact balance laws; Tauberian transfer between defect sizes and zero displacement; semicontinuity of indices under locally uniform convergence [W1C]; Euler–FE rigidity with explicit moduli; the ruler calculus restricted to subfamilies.

**First theorems that would count.** A modulus of location for Beurling systems with pointwise defect `O((1 + |t|)^{−a})` uniform in `a` as `a ↓ 0`; the threshold topology separating fakes from rigidity.

## 2.10 Does an AAL proof or falsification need a new field?

**What the corpus fixes.** AAL fails exactly at a finite nonempty top layer [AAL-LAYER]. In world I an edit of the rational primes with a power count rate removes the layer and has a strictly larger zero-free half-plane; hence AAL follows if no such edit has a larger zero-free half-plane than `ζ`, and no edit law decides this [WORLDI]. Euler worlds realize every pair `Θ∞ < Θ < 2/3` [TWOTHIRDSWORLD]; under AAL, RH ⇔ ZAL [AKLT].

### Extremal arithmetic of prime systems

**Subject.** Variational problems on the space of prime systems (rational primes with two-sided edits, Beurling systems) with a fixed count rate: maximize the zero-free half-plane, the tail abscissa gap `Θ − Θ∞`, or the layer mass. AAL is a statement that `ζ` admits no improving direction that removes a finite layer.

**Objects.** Edits `e` with count `Ax + O(x^β)`; edit zeta functions `ζ_e`; the layer carrier `L(s) = ∏(s − ρ_j)(s − ρ̄_j)`; the factorization `(s − 1)ζ_e L = (s − 1)ζ · C e^{H}` [WORLDI]; the functional `e ↦ Θ(ζ_e)`.

**Questions.** (1) First variation: how does `Θ(ζ_e)` change under a single prime insertion or deletion near a top layer? (2) Is `ζ` a local maximum of the zero-free half-plane among edits with count error `O(x^β)` for some `β < 1`? (3) What does the improving edit of world I cost in the functional equation, and does the exact functional equation of `ζ` forbid that cost? (4) For falsification: construct a finite layer for `ζ` by proving that an extremal edit exists with larger zero-free half-plane — the mirror problem.

**Criteria.** Statements relative to `ζ` (the docstring of [WORLDI] records that no edit law decides AAL); every extremality claim tested on Euler worlds without functional equation, where layers exist [EULERWORLD]; distinguishing AAL from ZAL in every theorem.

**Tools.** Greedy and signed grouped edits with square-root discrepancy; balance laws of two-sided edits; Hadamard factorization relative to a layer; variational derivatives of abscissae (Landau-type arguments for one-sided coefficients); the finite-layer filters of ELT [COFACTORS].

**What it must answer.** Whether AAL is an extremal principle of the rational primes, and if not, which finite layer is consistent with the exact functional equation.

## 2.11 Under the exclusion of positivity and spectra: a new field

### Zero-forcing calculus

**Subject.** Exact identities among Dirichlet series with Euler product (dilations, quotients, convolutions, twists), combined with functional equations, as **transport maps on zero configurations**: a zero at `ρ` forces a zero or a contradiction at `φ(ρ)`. The field classifies forcing maps, their orbits, and the configurations closed under them. No quadratic form, no spectrum.

**Objects.** Identity relations `R(F₁,…,F_m) = 0` of finite complexity; forcing maps `φ_R`; coincidence varieties (configurations on which a map is defined, e.g. halving pairs [HALVING]); closed configurations; Galois orbits of `p^ρ` over the prime-trace field `B` and their quartet structure [QUARTET] [LEAVEQUART]; square classes of height radicands [RADICAND] [SQREL].

**Language.** Forcing map, coincidence, closure, expansion (`Re φ(ρ) > Re ρ`), contraction, orbit type (pair, Klein, partial flip, leaving the quartet) [INVOLUTIONS].

**Criteria.** Every forcing law uses an identity of `ζ` and its functional equation, and fails on cosh models and Euler worlds; every result is exact (no estimate whose sign is the content).

**Questions.** (1) Classify forcing maps of bounded complexity. (2) Is there a forcing map without coincidence hypothesis? (3) Is any forcing map expanding on a band (gap law) or on all of `(½, 7/8]` (RH)? (4) Do the Galois constraints (quartets, square classes, mixed traces with `T_t(n) = n·T_t(1/n)` [MIXEDTRACE]) turn coincidence hypotheses into forced coincidences?

**Tools.** Mellin and Hadamard factorization; transcendence of prime powers at zeros (three prime exponentials algebraic iff the exponent is rational); finite Galois layers [PRIME-FIBRES]; monodromy of the heat cover as a second source of orbit constraints [HEAT-FINITE].

**First result that would count.** A forcing law with no coincidence hypothesis, even non-expanding.

## 2.12 Under the AdS modular-horizon hypothesis: a new field

### Arithmetic black-hole thermodynamics

**Subject.** Phase structure of arithmetic ensembles built from the prime-marked horizon: free energies indexed by aperture (inverse temperature) and confinement (volume); saddles (ground states, the critical half-line state); transitions (critical thresholds); stability (concavity, specific heat).

**Objects.** The window energies and their critical thresholds [POLAR]; the confinement ground energy, strictly concave, with endpoint selection [ENDPOINT] [ENDPOINT-BOUND]; the critical state (unique, outer, cyclic, Laplace zero-free) [HF] [HF-OUTER] [HF-CYCLIC] [HF-BOUNDARY]; the two-boundary correlator and its strip [ADS]; thermofield and BTZ realizations of the prime-log carrier [THERMOFIELD]; prime-2 deformations [ADS-NOGO].

**Language.** Phase, saddle, transition temperature, specific heat, endpoint competition, gate (local factor), quantized gate (integral unit-multiplicity factor).

**Criteria.** Exact `ξ` divisor and multiplicities on the boundary; pole and Gamma factors retained; the `ζ`/Bianchi distinction kept [BIANCHI]; every principle separates the arithmetic system from the prime-2 deformations; no physical axiom stands in for an estimate.

**Questions.** Is the off-line world a black-hole phase (2.7)? What is its specific heat? Does gate quantization (integrality, unit multiplicity) have a thermodynamic signature that the deformations lack? Is the ringdown rate a thermodynamic quantity (a gap of the transfer operator at the transition)?

**Tools.** Endpoint competition under a source; concavity and Legendre duality; KMS and thermofield purification; Euler–FE rigidity as the statement that quantized gates with exact duality are the rational primes [RIGIDITY].

## 2.13 Under the topology/geometry hypothesis: a new field

### Index theory of the explicit formula

**Subject.** Families of explicit-formula quadratic forms (windows, apertures, ratios, cutoffs, heat times) over parameter spaces, and their topological invariants: index, spectral flow, null-mode walls, `η`-type invariants.

**Objects.** The neutral window family and its index `≤ 1 + κ` [INDEXLAW]; null modes and index growth along the aperture [NULLMODES]; the margin as the depth of the second negative square, a ruler of `w` [MARGINSINF] [W]; Green matrices and the continuum Green kernel [GREEN]; the heat cover with its monodromy group [ZCG].

**Language.** Wall (null-mode locus), crossing, spectral flow, local index density, boundary contribution at the certified region, reflection of the parameter space by the functional equation.

**Criteria.** Every invariant is computed from the literal explicit formula (prime contacts, pole, Gamma kernel); a crossing-free deformation is never assumed [DEFORM]; the sign twin must have nonzero flow where the first step fails [TWIN].

**Questions.** A spectral-flow formula (2.8); parity of crossings under the functional-equation reflection; whether walls can be crossed by one parameter without being crossed by another (a monodromy of walls); whether the index face and the heat cover have one common topological invariant.

**Tools.** Spectral flow and `η`-invariants for families of finite Hermitian matrices with explicit entries; Schur complements and Green calculus; transversality of crossings; the step-sample transfer between continuous and finite forms [STEPS].

## 2.14 A research programme to construct `𝔽₁`

**Aim.** A geometry in which `Spec ℤ` has a square with the actual arithmetic diagonal and in which one inequality on that square is a theorem of the geometry. Not a one-element field: `0 ≠ 1` excludes that.

**What the corpus fixes.** Two Frobenius graphs meet in their contact ideal, with the first prime contacts `(2)` and `(3)` [CONTACT] [CONTACT-EX]; in integral big-Witt ghosts `F_kV_k = k` but `V_kF_k ≠ k` [WITT]; a completion of window couplings with one negative square forces logarithmic self-pairings `≥ m log m − 2m` on runs of blocks [DIAGONAL]; the neutral index is `≤ 1 + κ` [INDEXLAW]; every Artin `L`-function has a completion with a functional equation, Brauer induction is proved [ARTIN] [BRAUER]; the Kummer calibration has its places, intrinsic rational counts, differential orders at every finite place and local regularity criteria [KUMMER-COUNT] [KUMMER-DIFF] [KUMMER-REG].

**Stages and gates.**

| Stage | Content | Gate |
|---|---|---|
| F1 Calibration | The Kummer function field written in the window language: contacts, diagonal, windows, Riemann–Hurwitz from the differential orders | Weil's inequality for the calibration proved inside the window calculus, with Frobenius as the only extra structure. |
| F2 Diagonal | The logarithmic self-pairing derived from contact order and an archimedean boundary datum, compatible under gluing | Reproduces [DIAGONAL] on every run without copying the Weil matrix. |
| F3 Symmetry | A correspondence on the square of `ℤ` that scales the neutral form by a factor `≠ 1` on a nonzero subspace, or a theorem that none exists in a stated class | Either outcome; the no-go collapses the programme into ACS. |
| F4 Count | A Riemann–Roch count on windows of ratio `< 4` with a quadratic term reproducing the `10⁻¹³` floor structurally [FLOORLOG2] | Structural constant equals the certificate. |
| F5 Index | Index law as a theorem of the geometry, functorial under refinement | Agrees with [INDEXLAW]. |
| F6 Reciprocity | Conductors and squares of number rings (Artin, Heilbronn) | Index statements for Dedekind squares. |

**Acceptance tests.** Recover `(1,2) = (2)`, `(1,3) = (3)` and prime-square contacts; explain the negative diagonal; separate `Λ` from the sign twin [TWIN]; pass the worlds tests — the geometry must not exist for Euler worlds without functional equation [EULERWORLD].

**Stop rule.** If F1 fails, the window calculus is not the carrier; if F3 ends in the no-go, `𝔽₁` is a language for ACS and adds no inequality.

## 2.15 A research programme to close WD

**The route.** WD reads `w` through Möbius polynomials and mollified moments: at one height for all prefix lengths [WD]; on one unit window; through cofinal long moments with one exponent `K` for arbitrarily large length exponent `θ` (two-sided slope law, pure and mollified versions equivalent) [WD-LONG]. These are rulers [RULERS]. The seed gives `|M_X(½+it₀)| = O(X^{3/8+ε})`, `∫₀¹|ζM_X|² = O(X^{3/4+2ε})`, long moments `T^{4+3θ/4}` and `T^{6+3θ/4}` [RULERS]. The depth ladder gives eventual depth `< 1/(2θ) + ε` from bounded dyadic moments at length `T^θ`, `θ > ½` [DEPTHLADDER]; real unit-bounded mollifiers of length `T^θ` have normalized moment `≥ 1 + 1/(8 + 6θ)` [NECLEN].

**Diagnosis.** WD as a ruler is complete. Closing WD as a proof needs a lever on its ruler: an estimate at exponent below `3/8`, ultimately at `0`. The route's own content cannot supply it (measuring is not moving [MEASURING]).

| Stage | Content | Gate |
|---|---|---|
| D1 Seed table | Instantiations at `3/8` on every WD ruler | Done for prefixes, window, moments [RULERS]. |
| D2 Stage map in `θ` | An inequality from length `T^θ` to `T^{2θ}` with an explicit loss | Any loss below the seed slope is a better quasi-RH; slope zero with one `K` is RH. |
| D3 Negative moments | Make the long-mollifier/negative-moment link two-sided | Separates the forms of the slope law that are RH from those that also need simple zeros. |
| D4 ZAL engine | Bounded dyadic moments at every `θ > 1` | Gives ZAL (Assembly II); needs lengths beyond every known mollifier range. |
| D5 Signed off-diagonal | One off-diagonal term of a long moment with a signed bound beating its absolute budget in a genuinely long range | First evidence that WD's own sums carry a lever. |
| D6 Decision | If D2 and D5 have no candidate | Retire WD as a producer; keep it as a ruler and as the ZAL engine. |

**Closure criteria.** Common `K`, unbounded `θ`, `θ`-dependent constants allowed, cofinal heights, the arithmetic mollifier itself. A universal constant over all `θ, T` is false [WD-LONG]. **Rejection tests.** Coefficient-norm bounds, short weights and density-only corridors leave finite or shallow exceptions.

## 2.16 A research programme to close ACS

**The route.** RH ⇔ the neutral-window margins are bounded below [ACS]; ⇔ at each cutoff `Q ≥ 2` the windows of index one have a common gap `c_Q > 0` [GAPRH] [GAP]. The index law counts right zeros [INDEXLAW]; the margin exponent at polynomial block size equals `w` [MARGINSINF] [W]; with no hypothesis the margin depth is `C(1+log K)²K^{3/8}(1+log R)` [MARGIN38]. Certified: ratio `≤ 3` for `Q ≥ 2`, `< 4` for `Q ≥ 3` at every block size [LOGLADDER]; the first overlap step separates `ζ` from the sign twin through the dipole of the Green matrix [TWIN] [DIPOLE]. Excluded: fixed-rank absolute gluing [RANK-WALL], bare dilation gap [TREE-GAP], uniform positive gap at unbounded aperture under RH [MARGIN-DECAY].

**Reading.** ACS is a continuity method whose openness is proved (thin tails [GAP]) and whose closedness is RH. Its margin is an exact ruler of the width: the window calculus is a complete finite model of `w`, built from the explicit formula, so it uses the Euler product and the functional equation together — the joint use every lever requires.

| Stage | Content | Gate |
|---|---|---|
| C1 Converse rate law | Margin `≥ −C K^{w+ε}` | Done: every block size with `1 + log R` [MARGINDEPTH]; polynomial block size exactly [MARGINPOLY] [MARGINRULER] [W]. |
| C2 Stage map | A doubling law `a(2K) ≤ λ·a(K) + c` derived from the gluing data, seeing the contact signs | Best factor is `2^w` [DOUBLING] [W]; a gluing proof of any `λ < √2` is a second producer, of `λ < 2^{3/8}` a better seed, of every `λ > 1` RH (2.4). |
| C3 Acid test | Prove the gap of the windows of the Kummer calibration by stage maps, without Weil's theorem | If the calculus cannot prove the gap where it is true, C2 is not pursued in this calculus. |
| C4 Certificates | `Q = 2` fourth step [FOURTHRED]; prime-square aperture | Extends the certified base. |
| C5 Critical state | Identities of the possible limit state (dilation, reflection, cyclicity) tested against the prime weights [HF] | One identity the actual source violates closes the method (wall U5). |
| C6 Clustering | Remove `1 + log R` (wall U9) | The margin ruler at all block sizes. |

**Closure record if A2 ends in a fake with `λ = √2`.** Negative: the gluing calculus produces no half-plane. Survivors: index law, openness, floors through ratio four, margin ruler, first-step dipole.

## 2.17 A research programme to close ZCG

**The route.** RH ⇔ forward loops and mirror loops transport the zeros alike at every positive real nonbranch time [ZCG]; `Λ ≤ 9/128`, so only `0 < t ≤ 9/128` is open [NEWMAN]. The forward group `G₊` has index `≤ 2` in the finitely supported signed permutations; it is proper iff its turns obey one parity law [HEAT-PARITY]; a proper group forces `8 | N(t)` at every real `t > 0` [HEAT-EIGHT] and one residue class `2` or `6 mod 8` at all simple centre times [MOD8]; an odd number of nonreal quartets at one real time gives `G₊ = W` [ODDQUART]. A forward multiple zero off the centre exists at arbitrarily large forward time [OFFCENTRE]; one isolated double one gives `G₊ = W` [DOUBLECOLL]. Arithmetic automorphisms act on finite continued windows as heat monodromies [HEAT-FINITE]; whole fibres are excluded [HEAT-NOGO]; a uniform injective nonreal continuation of all off-line zeros forces finitely many [HEAT-UNIFORM].

| Stage | Content | Gate |
|---|---|---|
| Z1 Sign of `G₊` | Isolated double collision off the centre (task A3) | Expected `G₊ = W`; then the heat cover has no invariant beyond transitivity and all parity mechanisms close. |
| Z2 Arithmetic content | Identify data retained under continuation of finite windows but invisible to `W` (the prime-trace orbit types [QUARTET] [INVOLUTIONS]) | One invariant of the arithmetic group that heat monodromy must respect. |
| Z3 Time-zero control | Quantitative shrinking of the specialization interval for growing windows | A bound turning finite-window specialization into finite off-line support under explicit tail assumptions. |
| Z4 Finite stratum | Combine with B6 | ZCG then closes with Landing and ZAL (Assembly II). |

**Rejection tests.** A whole-fibre intertwiner; global conjugation by one finitary heat element; "large monodromy implies real zeros". All three are excluded or empty.

## 2.18 A research programme to close MC/JAS

**The route.** MC: Möbius Hilbert form subpolynomial ⇔ RH [MC]; the zeta-kernel signal is a smoothed Möbius sum and a ruler: `Θ ≤ b` iff the signal is `O(Z^{b'})` for every `b' > b` [SIGNAL] [SIGNAL-WIDTH]. JAS: dressed PSD at level one ⇔ RH [JAS]; a signal bound `O(Z^b)` gives large-prime level `b + ½ + ε` [SIGNAL-JAS]; the ancestry abscissa is `0` or `≥ 1 +` the largest depth, with no hypothesis [RULERS]. The seed gives signal exponent `7/8` and level `11/8 + ε`.

**Diagnosis.** MC and JAS are W-face rulers fed by one producer. The producer's frames end at `3/5` [GAUSS] [WALLGEN]; its estimates stop at the vertex `7/8` [VERTEX]; truncation and averaging walls are proved [TRUNCATION] [AVERAGE]; incomplete reciprocity keeps the phases with a subcubic defect saving [INCOMPLETE].

| Stage | Content | Gate |
|---|---|---|
| M1 Estimates below the vertex | Row count in the binding bin; row mean square at generic size; signed off-diagonal saving [VERTEX] [ESCAPE] [SIGNEDGRAM] | Seeds `13/15`, `5/6`, `5/6 − s` (2.5). |
| M2 Family mean values | Multiple Dirichlet series of the cubic cover of `GL₃` as the source of M1 | First specialization matched to the corpus row sums. |
| M3 Target-preserving extraction | Extraction weights that cancel the continued family residue and keep the `ρ⁻¹` target mode | Strict saving over the sixth-power scale for the signed aggregate. |
| M4 Frame | A source outside the Gauss class; the corpus explores Serre's `Q₈` representation (induction from `C₄`, ramification at 2, 5, 41) with local epsilon factors unpaid [Q8SRC] | Frame centre `< 3/5`, or a classification excluding it. |
| M5 Lever | Combine M1–M4 with the functional equation of `ζ` (2.21) | A lever transported to all W-rulers. |

**Rejection tests.** Principal averaging; more Gauss factors in the same budget; dropping the first sextic layer while claiming its target; reversible sewing [RFHM].

## 2.19 A research programme: Galois theory of the zeros

A finite polynomial cannot have infinitely many distinct roots; the algebraic object is a compatible family of finite equations. **Fixed.** Complete-fibre traces give monic polynomials with the centred zeros as roots [FIBRES]. The prime-trace field `B` (generated by mixed traces with `T_t(n) = n·T_t(1/n)` [MIXEDTRACE]) and the field `E` of prime values `p^ρ`: `E/B` is the compositum of finite Galois layers, one per height, each of even degree [PRIME-FIBRES]; the degree of the residue field of a zero is its orbit size [ORBIT]. Criteria: `Re ρ = ½` iff `p^{2Re ρ} ∈ B` and an automorphism realizes the reflection [REFLECTION]; conjugation is central iff every ordinate value lies in `B` [CONJCENTRAL]; the group acts on a quartet through the Klein group iff the width value lies in `B` [INVOLUTIONS]; the orbit lies in the quartet iff the width and ordinate values solve a quadratic over `B` [QUARTET]; an orbit leaves its quartet only through another off-line quartet of the same ordinate [LEAVEQUART]; square relations among height radicands carry an even number of critical heights [SQREL] [RADICAND]. Heat comparison holds on finite windows only [HEAT-FINITE] [HEAT-NOGO].

| Stage | Content | Gate |
|---|---|---|
| G1 Sign of `G₊` | Task A3 | Decides whether heat monodromy adds any constraint. |
| G2 Representation ring | Heilbronn characters from Brauer induction; Aramata–Brauer; zeros of order one belong to one abelian character [BRAUER] [ARTIN] [D] | Multiplicity laws across Galois groups. |
| G3 Cross-height relations | Algebraic relations among traces of different heights (trace functions of `ℚ`-independent heights are independent as functions [TRACE-INDEP]) | Presentation of `B`. |
| G4 A restriction on conjugation | A relation in `B` derived from the Euler product that separates the reflection lift from conjugation | The only door to location in this theory. |
| G5 Forcing | Use G3 and the quartet criteria inside the zero-forcing calculus (2.11) | A forced coincidence of ordinates or its exclusion. |

**Limit stated precisely.** The theory locates zeros only through the position of conjugation relative to the reflection; orders and multiplicities are governed by G2, location by G4.

## 2.20 A programme assuming RH is false

The assumption guides the search; a final disproof must concern the actual `ζ`.

**The three worlds.** F: finitely many off-line zeros (finite positive index); S: ZAL with Landing failing; D: ZAL failing [THREEATOMS]. **Constraints on an off-line zero `ρ = ½ + δ + iγ`.** `|δ| ≤ 3/8` [MMD_STRIP]; `ζ(½ + iγ)` is flattened to order `δ²` for `|δ| ≤ 1/16` [FLATTEN]; `Λ ≥ δ²/(200 log γ)` for `γ ≥ e^{1600}` [NEWMANLOW]; density exponent `30/13` [DENSITY]; at most `1 − 0.6725` of zeros off the simple critical class [CENSUS]; each right zero adds one negative square to some window [INDEXLAW]; in world I an edit with larger zero-free half-plane exists [WORLDI].

**(a) Proving falsity analytically.** Strategies with a finite certificate:

| Certificate | Statement that would decide | Lean |
|---|---|---|
| Window binding beyond pole capacity | A window whose binding energy exceeds `√ρ − 1/√ρ + log ρ` carries an off-line zero | [POLECAP] [POLECAPRH] |
| Window with two negative squares | Index law | [INDEXLAW] |
| Integer violating the lag inequality | RH ⇔ the inequality for every `n ≥ 2` (a `Π⁰₁` form) | [INTLAG] |
| Nonreal Jensen root | Degree `> 31922` | [JENSEN] |
| Positive heat threshold | Off-line zero below `e^{100/λ}` | [HEATLOC] |

A noncomputational disproof is a structural lower bound for one of these quantities. The research direction with content: **make the half rulers two-sided** — the mass-normalized Weil floor, the heat bound `Λ ≤ w²/2`, the long-mollifier/negative-moment link (D3 of 2.15), the margin at all block sizes (C6 of 2.16): a two-sided ruler turns a lower bound for a moment, a heat constant or a margin into an off-line zero. And **the mirror of 2.10**: an extremal edit with larger zero-free half-plane would describe world I.

**(b) A concrete counterexample without computation.** A counterexample is specified by a region and a proof of a zero inside: a rational rectangle in `½ < Re s < 7/8` with a proved argument-principle count. The localization chain exists in pieces — heat threshold → height bound [HEATLOC]; aperture visibility [HIDDEN]; index → window [INDEXLAW] — and lacks its first link, a structural positive lower bound for one gap quantity (task A8 assembles the rest). World F is the natural target: a finite configuration of quartets, closed under the zero-forcing transport (2.6/2.11), consistent with the Galois quartet criteria and with `8 | N(t)` if `G₊` is proper [HEAT-EIGHT]. Such a configuration is a candidate counterexample described by finitely many algebraic data; its existence is the open question.

**AAL distinction.** One off-line zero falsifies RH, not AAL; falsifying AAL needs a finite top layer strictly above the tail abscissa [AAL-LAYER].

## 2.21 The one big question

### Is there an interval of exponents that the abscissa of `ζ` provably avoids?

Find `½ < b₁ < b₂ ≤ 7/8` and prove, with no hypothesis on zeros, that `Θ ∉ (b₁, b₂)`. Equivalently, prove one **lever** for `ζ`: a map `T` on exponents with `Θ ≤ b ⇒ Θ ≤ T(b)` and `T(b) < b` for `b ∈ (b₁, b₂)` (a lever is a gap law [MIXED]).

**Why it is less hard than RH, quasi-RH and AAL.** RH implies it. It does not imply any half-plane: if `Θ` is below `b₁` or above `b₂`, nothing changes. It needs no estimate at exponent zero and no improvement of the vertex `7/8`.

**Why it kills, establishes and unblocks.** It establishes the lever route, which no programme of the corpus has opened; it unblocks wall P8 on all W-routes at once; a classification showing that no identity of bounded complexity forces zeros without coincidence (2.6, 2.11) would retire the identity-driven lever programmes and leave the producer ladder (2.5) and the window producer (2.4) as the only ways to move `w`.

**What a positive answer gives.**
1. It is the first lever. By lever transport it is simultaneously a gap law on every ruler: Möbius partial sums cannot have growth exponent in `(b₁, b₂)`, unit windows and long moments cannot have slopes in the corresponding band, the window margin cannot sink at those rates, the AdS strip width cannot lie in `(½ − b₂/2, ½ − b₁/2)` [LEVERTRANSPORT] [ADS] [D].
2. The worlds theorems force its proof to use the Dirichlet series and the functional equation of `ζ` together: if `b₂ ≤ 2/3` an Euler world realizes every abscissa in the band [EULERWORLD]; cosh models realize every abscissa [COSH]. A proof would therefore exhibit the joint mechanism that every route lacks.
3. Iteration criterion [D]: if a family of such levers covers `(½, 7/8]` with a monotone envelope, its wall is `½` and RH follows; the question isolates the first step of that programme.

**Templates in the corpus.** (i) Halving descent: if `ζ(ρ) = ζ(ρ/2) = 0`, the functional equation makes `1 − ρ/2` a zero, of real part `1 − Re ρ/2`; hence any halving pair forces `Θ ≥ 2/3` [HALVING]. This is a forcing law `ρ ↦ 1 − ρ/2`, conditional on a coincidence; off RH some right zero is not halved. (ii) Frames: a correction at the dilated argument `ks − c` transfers a zero-free region of the correction to `ζ` with `T(b) = (c + b)/k` [TOWERFIX]; the cubic frame is exact in both directions between the correction and its Grössencharacter rung [RUNG], so a band-limited lever needs a source whose correction has a zero-free region proved only when `Θ ∈ (b₁, b₂)`.

**First lemma to test.** Classify the zero-transport maps of the exact identities with Euler product in the corpus — `ζ(2s)/ζ(s)`, `ζ(s)²/ζ(2s)`, the squarefree partition [MSC], the cubic frame [CORRZERO] — and determine whether any of them, combined with `ξ(s) = ξ(1 − s)`, sends a rightmost zero at `Re ρ = b ∈ (b₁, b₂)` to a forced zero or pole of a series known to be regular there (the seed for Dirichlet `L`-functions is available as the regularity input [MMD_DIR]).

**Filter.** Not RH-equivalent (T1); decided by proof (T2); consequence is a theorem on every ruler (T3); no finite window decides it (T4); false on Euler worlds and cosh models for suitable bands (T5); the input — an identity using the functional equation — is named and not refuted (T6); EDCS defines gap laws but proves none for `ζ` (T7).

<!-- source references -->
[AAL-LAYER]: ../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/AbscissaLaws/TheFailureOfTheAbscissaLawIsAFiniteLayer.lean#L33
[ACS]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/AUniformLowerBoundOnTheMarginOfTheWindowMatricesForcesTheRiemannHypothesis.lean#L505
[ADS]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/TheEternalAdSPrimeMarkedDictionary.lean#L884
[ADS-NOGO]: ../../../formal/GaloisForLFunctions/BlackHoleRingdown/CausalIdentitiesCannotForceQuarterRingdown.lean#L1600
[AKLT]: ../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/PrimeTowersAndConeCouplingProduceAsymptoticAbscissaLaw.lean#L306
[ARTIN]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/EveryArtinLFunctionHasACompletionWithAFunctionalEquation.lean
[AVERAGE]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/TheAverageRowIsBlindToTheTarget.lean#L148
[BIANCHI]: ../../../formal/GaloisForLFunctions/RingdownOfTheCubicCover/EternalBianchiBoundaryDictionaryAndWardObstruction.lean#L469
[BRAUER]: ../../../formal/GaloisForLFunctions/RHTower/Artin/ArtinBrauerInductionTheorem.lean#L206
[CENSUS]: ../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/CriticalLineZeroProportion.lean#L1042
[COFACTORS]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheGrowingFilterReachesPolynomiallyManyCofactors.lean#L1
[CONJCENTRAL]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ConjugationIsCentralAtAZeroIffItsOrdinateValueLiesInThePrimeTraceField.lean#L279
[CONTACT]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheConductorOfTwoGraphsIsTheirContact.lean#L22
[CONTACT-EX]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheFirstTwoPrimeContactIdeals.lean#L14
[CORRZERO]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/GrossencharacterLFunctionsHaveZerosInTheRightHalfStrip.lean#L621
[COSH]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L138
[DEFORM]: ../../../formal/GaloisForLFunctions/EdgeHodgeTheory/TheIndexComputedByDeformation.lean#L107
[DENSITY]: ../../../formal/GaloisForLFunctions/RHTower/PrimeShortIntervalsSeventeenThirtiethsUnconditional.lean#L25
[DEPTHLADDER]: ../../../formal/GaloisForLFunctions/SelectiveArithmetic/TheCancellationAndDepthLadder.lean#L67
[DIAGONAL]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheCouplingsOfAWindowAreNotMixedAreasAndTheIndexForcesLogarithmicSelfPairings.lean#L268
[DIPOLE]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheDipoleOfWeilsGreenMatrixCarriesTheFirstOverlapStep.lean#L364
[DOUBLECOLL]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheTurnAroundAnIsolatedDoubleCollisionOffTheCentreIsTheExchangeOfTwoPairs.lean#L162
[DOUBLING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L217
[DOUBLING38]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L191
[DOUBLINGHP]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L178
[DOUBLINGRH]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean#L251
[ECP]: ../../../formal/GaloisForLFunctions/RHTower/Representation/EndpointCharacterCriterion.lean#L62
[EDGE]: ../../../formal/GaloisForLFunctions/FrustratedArithmeticDirichletForms/TheEdgeLawCrossesOneBetweenLogFiveAndLogSix.lean#L295
[EDIT]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L175
[ENDPOINT]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ConfiningSourceEndpointSelection.lean#L1
[ENDPOINT-BOUND]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ConfiningSourceEndpointSelection.lean#L24
[ESCAPE]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheMetaplecticVoronoiExponentInvariants.lean#L587
[EULERWORLD]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L77
[EVENLOG2]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheEvenWeilFormHasAFloorAtApertureLogTwo.lean#L4126
[FIBRES]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheFieldOfCompleteFibreTraces.lean#L486
[FLATTEN]: ../../../formal/GaloisForLFunctions/ArithmeticDiscreteness/TheDepthOfAnFEPairIsReadOnTheLine.lean#L113
[FLOORLOG2]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheTwoPrimeWindowHasAPositiveWeilFloorAtEveryBlockSize.lean#L48
[FOURTH]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheTwoPrimeWindowAndRatioThreeHoldAtEveryBlockSize.lean#L285
[FOURTHRED]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheTwoPrimeWindowAndRatioThreeHoldAtEveryBlockSize.lean#L310
[GAP]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheBoundRangeEndsOnlyWhereTheGapOfTheBoundWindowsCloses.lean#L308
[GAPRH]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheGroundEnergyOfAnApertureIsAGapOfEveryWindowInsideIt.lean#L408
[GAUSS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L595
[GREEN]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheContinuumGreenKernelIsTheLimitOfTheTowerAndIsNegativeOnlyAlongTheCharge.lean
[GROSSENTOWER]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheCubicProbeIsACoupledTowerReachingThreeFifths.lean#L1577
[GTA]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean#L293
[HALVING]: ../../../formal/GaloisForLFunctions/ArithmeticHolographyOfTheModularHorizon/HalvingDescentAndShimuraZeros.lean#L40
[HEAT-EIGHT]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ARealCollisionOfMassNotDivisibleByEightGivesEverySignedPermutation.lean#L165
[HEAT-FINITE]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheArithmeticGroupActsOnContinuedWindowsOfZerosAsHeatMonodromy.lean#L81
[HEAT-NOGO]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheArithmeticGroupIsAHeatMonodromyOnFiniteWindowsButNotOnAFibre.lean#L62
[HEAT-PARITY]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheForwardMonodromyGroupIsProperExactlyWhenItsTurnsObeyOneParityLaw.lean#L204
[HEAT-UNIFORM]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/AUniformSpecializationOfTheOffLineZerosForcesThemToBeFinite.lean#L29
[HEATLOC]: ../../../formal/GaloisForLFunctions/RHTower/XiSliceHeatThresholdVerificationHeight.lean#L94
[HF]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateIsUniqueUpToSign.lean#L96
[HF-BOUNDARY]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateHasNoBoundaryLaplaceZero.lean#L149
[HF-CYCLIC]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateIsCyclic.lean#L59
[HF-OUTER]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineLaplaceMultiplierIsOuter.lean#L45
[HIDDEN]: ../../../formal/GaloisForLFunctions/WindowVisibilityLaw/ShallowClusterExclusionAndTaperedCrystalBarrier.lean#L1179
[INCOMPLETE]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/IncompleteReciprocityRetainsPhasesWithSubcubicSaving.lean#L1
[INDEX]: ../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheFiniteStratumIsThePacketIndexDichotomy.lean#L85
[INDEXLAW]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheIndexOfTheNeutralPartIsOnePlusTheNumberOfZerosRightOfTheLine.lean#L166
[INTLAG]: ../../../formal/GaloisForLFunctions/RHTower/WeilLagFunctionInteger.lean#L541
[INVOLUTIONS]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheGroupActsOnAZeroThroughTheTwoInvolutionsIffItsWidthValueLiesInThePrimeTraceField.lean
[INVZETA]: ../../../formal/GaloisForLFunctions/RingdownOfTheCubicCover/UnconditionalScatteringResonanceBounds.lean#L246
[JAS]: ../../../formal/GaloisForLFunctions/RHTower/JointAncestryLevelOneCapstones.lean#L35
[JENSEN]: ../../../formal/GaloisForLFunctions/VerifiedHeightRungs/TheJensenPolynomialsThroughDegree31922AreRealRooted.lean#L21
[KUMMER-COUNT]: ../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/FunctionField/KummerIntrinsicRationalCount.lean
[KUMMER-DIFF]: ../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/FunctionField/KummerFiniteDifferentialOrders.lean
[KUMMER-REG]: ../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/FunctionField/KummerLocalRegularityCriterion.lean
[LA]: ../../../formal/GaloisForLFunctions/FiniteFreeProbability/FiniteFreeDeBruijnNewman.lean#L466
[LANDING-TFAE]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean#L145
[LEAVEQUART]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/AnOrbitLeavesItsQuartetOnlyThroughAnotherOffLineQuartetOfTheSameOrdinate.lean#L43
[LEVERTRANSPORT]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L85
[LOGENERGY0]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheWidthIsTheRateOfTheWeilFloorInTheLogarithmicEnergy.lean#L441
[LOGLADDER]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheTwoPrimeWindowAndRatioThreeHoldAtEveryBlockSize.lean#L322
[MARGIN-DECAY]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/UnderTheRiemannHypothesisTheMarginOfALongWindowTendsToZero.lean#L442
[MARGIN38]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesSinksAtTheRateOfTheWidth.lean#L800
[MARGINDEPTH]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesSinksAtTheRateOfTheWidth.lean#L789
[MARGINPOLY]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesSinksAtTheRateOfTheWidth.lean#L810
[MARGINRULER]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesIsARulerAtPolynomialBlockSize.lean#L719
[MARGINSINF]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheMarginOfTheWindowMatricesIsARulerAtPolynomialBlockSize.lean#L741
[MC]: ../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean#L219
[MEASURING]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L79
[MIXED]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/MixedTowersOfLeversStayAboveTheBestCentre.lean#L419
[MIXEDTRACE]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheMixedPrimeTracesSatisfyTheFunctionalEquation.lean
[MMD]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean#L631
[MMD_DIR]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean#L637
[MMD_HECKE]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean#L602
[MMD_STRIP]: ../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/Detector/QuasiRiemannHypothesis.lean#L674
[MOD8]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheTurnsOfAProperForwardMonodromyGroupObeyAParityLaw.lean#L128
[MSC]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmGammaSewnSquarefreeXiConormalBridge.lean#L87
[NECLEN]: ../../../formal/GaloisForLFunctions/ArithmeticProduction/TheNecessaryLengthOfAMollifier.lean#L716
[NEWMAN]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L155
[NEWMANLOW]: ../../../formal/GaloisForLFunctions/RHTower/Heat/TheHeatDetectionRateIsQuadraticInTheDepth.lean#L520
[NULLMODES]: ../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/NullModesForceApertureIndexGrowth.lean
[ODDLOG2]: ../../../formal/GaloisForLFunctions/WindowTowerOfSpecZ/TheOddWeilFormHasAFloorAtApertureLogTwo.lean#L3943
[ODDQUART]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/AnOddNumberOfQuartetsOfNonrealZerosAtARealTimeGivesEverySignedPermutation.lean#L372
[OFFCENTRE]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ACollisionAwayFromTheCentreExistsAtAForwardTime.lean#L625
[ORBIT]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheDegreeOfTheResidueFieldOfAZeroIsTheSizeOfItsOrbit.lean#L50
[OVERLAP]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheTwoPrimeWindowAndRatioThreeHoldAtEveryBlockSize.lean#L273
[PBM]: ../../../formal/GaloisForLFunctions/RHTower/RegularizedLogZetaAbscissa.lean#L402
[POLAR]: ../../../formal/GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/WholeSpaceCriticalThresholdEqualsPolarThreshold.lean#L256
[POLECAP]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/TheBindingEnergyOfAWindowIsAtMostItsPoleCapacity.lean#L251
[POLECAPRH]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/TheBindingEnergyOfAWindowIsAtMostItsPoleCapacity.lean#L239
[PRICE]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L383
[PRIME-FIBRES]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheFibreFieldsOverThePrimeTracesAreFiniteGaloisAndGenerateTheSpectralField.lean#L1
[PROPALT]: ../../../formal/GaloisForLFunctions/RHTower/Zeta23SeventyPercentOrSimpleNearLine.lean#L21
[Q8SRC]: ../../../formal/GaloisForLFunctions/RHTower/SerreQ8MonomialSourceLaw.lean
[QUARTET]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheOrbitOfAZeroLiesInItsQuartetIffItsWidthAndOrdinateValuesSolveAQuadraticOverThePrimeTraceField.lean#L281
[RADICAND]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheReflectionRadicalsOfOneHeightCarryTheParityOfItsZeros.lean#L337
[RANK-WALL]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/TheBindingOfTheTwoHalvesOfAWindowOfRatioFourHasRankProportionalToTheBlockSize.lean#L929
[REFLECTION]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ALiftOfTheReflectionIsConjugationExactlyWhereTheWeightLiesInThePrimeTraceField.lean#L55
[RFHM]: ../../../formal/GaloisForLFunctions/RHTower/JointAncestryAllPrimeReversibleRFHMSewingNoGo.lean#L37
[RIGIDITY]: ../../../formal/GaloisForLFunctions/EulerFETransportTheory/DecayingFunctionalEquationsDetermineThePrimes.lean#L486
[RULERS]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/EveryRulerCarriesTheSeedAndEveryLever.lean#L55
[RUNG]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCorrectionOfTheCubicProbeCarriesTheAbscissaOfItsRung.lean#L126
[RUNG3148]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheCorrectionOfTheCubicProbeCarriesTheAbscissaOfItsRung.lean#L167
[SEVENTY]: ../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/TotientGridGaussianRegularization.lean#L637
[SIEGEL]: ../../../formal/GaloisForLFunctions/RHTower/SiegelTheorem.lean#L108
[SIGNAL]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSignalOfTheZetaKernelIsAMoebiusSum.lean#L1
[SIGNAL-JAS]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSignalExponentIsThePositivityLevel.lean#L165
[SIGNAL-WIDTH]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSignalExponentIsTheZeroAbscissa.lean#L212
[SIGNEDGRAM]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheFloorBinBilinearGramIdentity.lean#L138
[SLOWDEFECT]: ../../../formal/GaloisForLFunctions/EulerFETransportTheory/ArbitrarilySlowDefectsOfPositiveWeightedSystems.lean#L569
[SQREL]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/ASquareRelationAmongHeightRadicandsHasAnEvenNumberOfCriticalHeights.lean#L33
[SRT]: ../../../formal/GaloisForLFunctions/SurfaceOfSpecZ/ScaleLocality/PrimeLogarithmicWindows.lean#L145
[STEPS]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/StepSamplesCarryWeilsFormOfALipschitzPacket.lean
[TH]: ../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaHermiteTraceFlag.lean#L250
[THERMO]: ../../../formal/GaloisForLFunctions/HTGeometry/Thermodynamics/EndpointSourceSwitch.lean
[THERMOFIELD]: ../../../formal/GaloisForLFunctions/HTGeometry/Thermofield/PrimeLogApplications.lean
[THREEATOMS]: ../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheLandingLawForZeta.lean#L68
[TOWERFIX]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/MoebiusSignedGaussPairingsEndAtThreeFifths.lean#L1140
[TRACE-INDEP]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheTracesOfRationallyIndependentHeightsAreAlgebraicallyIndependent.lean#L201
[TREE-GAP]: ../../../formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/TheDilationProcessHasNoGap.lean#L174
[TRUNCATION]: ../../../formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/FamilyContinuationRestoresTheGaussWallsUnderTruncation.lean#L1101
[TWIN]: ../../../formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheFirstOverlapStepOfWeilsFormFailsForTheSignTwin.lean#L744
[TWOTHIRDSWORLD]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/LeversThatBiteFailInTheWorlds.lean#L92
[VERTEX]: ../../../formal/GaloisForLFunctions/FamilyContinuationTheory/TheSevenEighthsGeometryIsAVertex.lean
[W1C]: ../../../formal/GaloisForLFunctions/InfiniteRankPurityTheory/TheIndexIsSemicontinuous.lean#L96
[WALLGEN]: ../../../formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/MixedTowersOfLeversStayAboveTheBestCentre.lean#L525
[WD]: ../../../formal/GaloisForLFunctions/MultiscaleMollifiedZetaField/TheWidthIsReadInOneWindow.lean#L85
[WD-LONG]: ../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/NearLineLogMean/LongMoebiusSecondMomentRigidity.lean#L659
[WITT]: ../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/Witt/RaynaudOperatorBoundary.lean#L19
[WORLDI]: ../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/AFiniteLayerCanBeEditedAway.lean#L136
[WZCROW]: ../../../formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/TheWorldOneScenarioTable.lean#L72
[ZCG]: ../../../formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheForwardMonodromyDeterminesTheReflectionAndTheConjugationOfTheZeros.lean#L186
