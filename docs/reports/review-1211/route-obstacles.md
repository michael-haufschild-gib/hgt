# Route obstacles — status quo

Scope: the 38 live route formulations, the 12 route candidates and the supporting programmes. For each route: the path, what is established, the obstacles that are **(a) just work**, and the obstacles that are **(b) open mathematics nobody has a solution to**.

**Corpus checkpoint:** `b98864a8e1` with its working tree (2026-11-12). Fact log: `logs/review-1211-status-quo-facts.md` (identifiers such as `FC-T1`, `CR4`, `AG-L2`, `PC1`, `WZ2`, `GZ1`, `CAM1` are its entries; `D1–D8` are its deductions; §6 lists the baseline declarations re-read for this report). Companions: [obstacles-summary.md](obstacles-summary.md) (A/B lists, ideation, the one question), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ), [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem).

**Live** means source observable, proved RH-sufficient receiver and explicit open estimate. **Candidate** means the source-to-receiver step is missing. HJ is PA; the BSY criterion of FEL belongs to CTF; PCS, DR, PW-B are retired labels.

**Evidence.**
- `[L*]` Lean statement read at the declaration for this report (module named, or fact-log identifier).
- `[F]` stated by the frontier map; `[KR]` stated by the scoped-obstruction ledger; both read in full. `[S]` a module the frontier map grades unfinished or unintegrated.
- `[D]` deduction made here from `[L*]` statements; not a Lean theorem. `[C]` classical mathematics quoted from memory, not in the corpus. `[A]` assessment.
- `[X]` the external theorem cached in the repository (OpenAI, 30 September 2026), taken as proved: every Dirichlet `L`-function, ζ included, and every finite-order Hecke `L`-function over `ℚ(√−3)` is zero-free in `Re s>7/8`; so `Θ≤7/8`. The Lean graph proves only `zetaZeroAbscissa ≤ 1` unconditionally (`RHTower/ZetaZeroAbscissa.zetaZeroAbscissa_le_one`); the native steps of `[X]` are just work (A118). **Natively** refers to the Lean graph.

**Strength.** RH; ≥qRH (implies a zero-free half-plane, Lindelöf or ZAL; open where it gives a half-plane below `7/8`); AAL; sub (implies neither a half-plane nor AAL); method; producer; indep.

**Labels.** `A*` just-work items and `B*` open problems are listed in [obstacles-summary.md](obstacles-summary.md) §2.1–2.2. `(unverified)` marks A items whose difficulty is not established. Σ, Π, Γ refer to [walls-ledger.md](walls-ledger.md).

**Notation.** `Θ=sup Re ρ`; `Θ∞=inf{σ≥½: finitely many zeros have Re ρ>σ}`; `w=Θ−½` the zero width. **ZAL** `Θ∞=½`; **AAL** `Θ=Θ∞`; **B13** finitely many off-line zeros ⇒ none; **Landing** ZAL ⇒ finitely many off-line zeros; **World I** ¬AAL (a finite isolated top layer); **World II** AAL ∧ ¬ZAL (a tail). `2Re S(log p)` is the prime trace (lag structure of the cubic spline at `log p`); a **logarithmic window** at `T` is `{p: |log p−T|≤32 log(T+2)}`. The **restricted Weil form** at aperture `a` acts on tests supported in `[−a,a]`; its **index** `negativeRank a E` and **nullity** `weilNullity a E` at energy `E`; a **resonant aperture** has nonzero nullity; the two **charges** of a vector are its coefficients at the two poles; `μ(a)` is the ground energy and `μ₀(a)` the floor on charge-free vectors. A **step packet** is constant on the blocks `(a,a+1]`; its **block matrix** is `d(a)+d(b)+δ_{ab}ϱ(a)−J(a,b)−C_Q(a,b)` (degrees, density, jets, floor-map contacts) and its **neutral part** is the block matrix without the product of the two charges. The **power tail** at `0<a≤½` is the comb form `F_a(N)` of the power divisor; `a=½` is the **critical comb**. A **system** is a weight system with a mass; the **trivial aperture** is `log log(mass)+o(1)`; the **Liouville twist** is `w(p^k)=(−1)^k log p`. The **signal** of a kernel `G` is `(1/2π)∫G(2+it)Z^{2+it}dt`. The **probe** is the cubic-theta sum of `[X]` over `K=ℚ(ζ₃)`; its **correction** is `H_η`; its **twist order** is `n=6`; `R₀` is the row exponent of its floor bin. A **two-sided edit** is the system of the rational primes with some primes deleted and some doubled; it is a **fake** at `β` if its count is `Ax+O(x^β)` and its zeta function continues to `Re s>½` with a zero there that ζ lacks.

## 0. The picture

| Fact | Evidence | Consequence |
|---|---|---|
| RH ⇔ `2Re S(log p)≥−K` at the primes of arbitrarily late logarithmic windows outside `Ce^{δT}` primes per window; ⇔ the upper side alone; ⇔ `ℕ`-counts on surviving prime rays with quadratic limit the plane defect; ⇔ one growth exponent for all even local moments; ⇔ the two-bump comb limit at each such prime; `Θ<1` ⇔ the floor `−Kp^α`, `α<½` | [L*] (`ScaleLocality/ExceptionalLogarithmicWindows`, `UpperPrimeLogarithmicWindows`, `CountsOnExceptionalLogarithmicWindows`, `LocalTensorMoments`, `HFP/OneInequalityPerPrimeOnTheComb`, `PrimeLogarithmicWindows.quasiRH_iff_prime_logarithmic_power_windows`) | one inequality per prime on sparse windows |
| For every nonnegative `R=o(log T)` a simple tempered configuration with logarithmic unit counts and unattained top has late windows of radius `R(T)` above every floor; a density-matched one for some `R→∞` | [L*] (`EveryPrescribedSublogarithmicRadiusMissesTheMinimalFace`, `TheMinimalFaceSurvivesZetaDensity`) | no window below the logarithmic radius decides |
| RH ⇔ the neutral part of the step-packet matrix of every window `(R,R+J]`, `R≤J`, has exactly one negative square; the block matrix has `r` negative squares on some window iff `ζ` has `≥r` zeros right of the line, the neutral part iff `≥r−1` | [L*] (`riemannHypothesis_iff_forall_hermNegIndex_neutralWindow_eq_one`, `exists_le_hermNegIndex_blockWindow_iff`, `exists_le_hermNegIndex_neutralWindow_iff`) | RH is the Hodge index theorem of explicit finite matrices |
| The finite-scale Hodge index holds on every window of ratio `≤103/50` at every block size (margin `1/5000`), on the first step packets of ratios 4 and 7 (`1/20`, `1/100`), and every ratio is nonnegative on thin step packets | [L*] (AG-F5–AG-F8) | the first windows with the contacts of two and three primes are certified at their first block sizes |
| The index of the restricted Weil form at aperture `b` is the sum of the nullities of the resonant apertures below `b`; it is the number of crossings of the path of aperture conormals (Lagrangian, independent of the primes) with the graph of Weil's operator; its supremum at energy zero is the number of zeros right of the line; RH ⇔ no crossing | [L*] (AG-L1–AG-L3) | the Morse index of the sign problem is a Maslov index; the far end of the path carries the zeros |
| Below the pole-vanishing floor `μ₀(a)` every null mode is charged and the index is the crossing number of a path of Lagrangian planes in the fixed space `ℂ²×ℂ²`, split into an even and an odd line; ground modes are charged iff `μ(a)<μ₀(a)` | [L*] (AG-L5–AG-L8) | B104 has the exact form `μ(a)=μ₀(a)` |
| The critical comb `F_{½}(N)` has growth exponent exactly the zero width; it never converges; RH ⇔ subpolynomial growth ⇔ absolute logarithmic Abel integrability; for `0<a<½`: Abel integrable ⇔ `a+w≤½` | [L*] (PC1–PC5) | the width is read on one explicit sequence |
| `Θ≤7/8`; `Θ<1⇔Θ∞<1`; the world `Θ=Θ∞=1` is excluded; RH ⇔ ZAL ∧ B13 ∧ Landing; B13 ⇔ the packet index is `0` or `∞` | [X]; [L*] (`QuasiRHIsATailLaw`, `TheFiniteStratumIsThePacketIndexDichotomy`) | a failure of RH is world I or world II with top `≤7/8` |
| AAL ⇔ at most one or infinitely many zeros right of every line; non-attainment on windows, of `ψ(x)−x`, at the primes, one moment exponent for all orders: each gives AAL | [L*] (FFA §6 of the log) | AAL is a unit gap |
| Two-sided edits of the rational primes with a count rate realize: a non-real pair alone on top at every count exponent `β>½`; every finite layer with multiplicities; an isolated pair above an infinite half-scale tail; every configuration that approaches the line; every sparse configuration; zeros symmetric about the line in a strip `c<Re s<1−c`; a finite layer of ζ edited away | [L*] (WZ1, WZ4–WZ7) | Euler product over the rational primes, integer norms and a count rate constrain no finite layer, no landing, no sparse tail |
| A fake whose count exponent is below a fake zero is balanced (doubled and deleted primes of one exponent) or has a real zero on top; an odd zero of the edit exponential at `ρ` needs `Re ρ≤2max(β,c₀,θ/3)`; the floor of prime edits with a count rate is `≥13/30` | [L*] (WZ2–WZ4) | below `√x` only balanced edits can fake with a non-real top |
| A countable Beurling system whose critical-line functional-equation defect is `L¹`, or `L²` and polynomially bounded, is the rational primes | [L*] (`IntegrableFunctionalEquationsDetermineThePrimes`, `beurlingSystem_rigidity_of_finiteEnergy_theta_defect`) | every fake that continues to the line has a non-integrable FE defect [D] (D5) |
| The cubic probe is a coupled tower: a zero `ρ` of `L(s,η)` with estimates below `Re ρ` forces a zero of a sextic Grössencharacter `L`-function at `6ρ−3`; with all estimates at all tower levels `Θ≤max(σ₀,3/5)`; `7/12` under GRH for the weight-one sextic Grössencharacters; the continued correction has infinitely many zeros in `7/12≤Re s<2/3` | [L*] (FC-T1–FC-T3) | the frame of the one producer ends above `½` |
| In the probe's budget, square-root cancellation across the rows of the floor bin (`R₀=½`) gives the twist exponent `(n−4)/(n−1)`, the half-plane `1−2/n=2/3`: exactly the uncoupled wall of the frame | [L*] (`signedGram_phase_endpoints`); [D] (D1) | the producer, fully evaluated, stops at `2/3` |
| The root number of a row is `G(u)γ₂(u)²` with `γ₂³=μ·u/\|u\|`; short columns are incoherent to every order; the short sextic Gram is diagonal; the average row is target-free; the Gram of two rows is a completed sum twisted by the root numbers | [L*] (CR1–CR6) | the floor bin reduces to the first moment of sextic Gauss sums against a column |
| Every one-structure and most two-structure models exist; the Euler product with the functional equation as an identity identifies the rational primes | [L*] (FFA, APD, EFT, WZC) | a proof of AAL, ZAL, B13 or Landing must use the Euler product with the FE as an identity, or with a count below the floor [D] (D5) |
| The centered zero field `L` of ζ is algebraic and normal over the complete-fibre source field `K`; `L=K` ⇔ RH; identity and conjugation are the only Euclidean-continuous source automorphisms | [L*] (GZ1); [F] | RH is a statement about one Galois group |
| RH through `exp(exp(C·a))` gives the sign on `[−a,a]`; `C` is not explicit; positivity at aperture `a` confines zeros with `T₀≤\|γ\|≤2πe^a` to depth `<exp(−c log³\|γ\|)` | [L*] (`exists_doubleExp_windowPositive`, `zeta_depth_lt_of_positive_aperture_closed_form`) | each window is a finite-height statement |
| Displaced twisted second moments for `θ<½` with main terms and a power saving; a positive proportion `κ=(1−log(18/5)/(13/10))/4` of critical zeros of odd multiplicity; `0.67250071` simple critical zeros in the objects of `Zeta23` | [L*] (`exists_interval_twistedMoment_le`, `eventually_critical_odd_fiber_proportion_from_short_twisted_moment`, `simple_critical_proportion_ge_67250071`) | the in-law half of the near-line picture is native |
| The Goss zeta function at `z∈ℤ_p∖ℕ` has simple zeros of strictly decreasing norms in the base field | [L*] (`gossZeta_riemannHypothesis`) | one Riemann hypothesis is proved by dominance, with no sign |

## 1. Mechanism classes

| Class | Mechanism | Status |
|---|---|---|
| M1 Signed criticality | primes pay the archimedean–polar deficit by sign | exact on every window; a window at aperture `a` follows from verification to `exp(exp(Ca))` |
| M2 Calibration | window cones, feasible sets, margins | feasible sets nonempty at every aperture ⇔ RH; they converge to `Λ` [L*] |
| M3 Canonical flow | `L, q, Ψ` of the Weil chain | RH ⇔ `Ψ` locally bounded on precontact intervals [L*] |
| M4 Reflection | Krein forms, ringdown, horocycles, cavity energies | sharp receivers; horocycle exponents `1−Θ/2`, filtered `1−Θ∞/2` |
| M5 Square-root cancellation | prime counts, long moments, squarefree counts | receivers closed; estimates open |
| M6 Continuation | heat, cosine, Jensen | collision-free flow ⇔ RH [L*]; the flow has the count of its limit [L*] |
| M7 Zero geometry | cameras, box cameras, Blaschke factors | a near-top cluster with a fixed depth deficit is visible or has a deep companion [L*/doc] (CAM1); prime cost of the adaptive profile open [F] |
| M8 Finite-layer receiver | filters, currents, non-attainment, tangent data | complete in world I; four sectors of the trace |
| M9 Production | integer stencils, Stepanov | rate = Mertens level [L*]; `p^{11/12}` at one prime [F] |
| M10 Count | `ℕ`-counts with quadratic Tate limit | hyperelliptic curves [L*]; over ℤ the sections count linearly [L*] |
| M11 Orbit at finite time | prime phases, returns, resonators | under `Θ≤b` heavy returns need `log t≥cy^{1−b}` [L*] |
| M12 Critical compactness | thresholds, pole channel, half-line ground states | three-way classification [L*] |
| M13 Topology of the prime complex | orientation cover | centred count `M(N)=Ω_±(√N)` [L*] |
| M14 Infinite-rank elimination | towers, thick sets | attained top + thick count ⇔ RH [F] |
| M15 Prime-degree sampling | logarithmic windows | complete receiver [L*] |
| M16 Intersection on half-products | adelic carrier, Green kernels | glued diagonal refuted [KR]; critical adelic inverse unbounded [KR] |
| M17 Absolute geometry | square, contacts, paths, rings, tails | forced data; exact index for Hecke characters, Dedekind zeta functions, one non-abelian Artin character, quotients of `L`-functions [L*] |
| M18 FE rigidity | Hamburger, defects | `L¹` or `L²` FE defect forces the rational primes [L*] |
| M19 Exceptional-coordinate atoms | ZAL, B13, Landing, DH | RH = ZAL ∧ B13 ∧ Landing [L*]; all open for ζ |
| M20 Families and monodromy | covers, class characters | fixed-part laws [F] |
| M21 Index and limits | index law, unit gaps | index-one limits give RH; no approximant with a gap [L*] |
| M22 Separation and dominance | ordinate injectivity, ultrametric Newton polygons, zero field | receiver for ξ; proof for the Goss zeta function [L*]; `L=K` ⇔ RH [F] |
| M23 Hodge lattice at finite scale | step packets, neutral part, block matrices | RH ⇔ one negative square of the neutral part on every window; certified on short windows and first blocks [L*] |
| M24 Constituents | bounded and Wiener classes | none with a zero [L*] |
| M25 The ladder | mass, aperture, rung | sizes to rung `1−o(1)` [L*] |
| M26 Family continuation | two estimates, reciprocal kernels, reciprocity | `Re s>7/8` [X]; in Lean the frame, the corrections, the budget, the coupled tower to `3/5` [L*] |
| M27 Dressed positivity | lag aggregate at a level | level one ⇔ RH; level `σ` from a signal bound [L*] |
| M28 Floor-free receivers | homogeneous, unit gap, certificate, amplification, symmetrization | each kind has a receiver and a kill [L*] |
| M29 Models of the count and of the Euler product | deletions, two-sided edits, characters | fakes at every count exponent above `½`, with a real top (deletions) or a non-real pair alone (two-sided edits) [L*] |
| M30 Index in the aperture | Morse = Maslov index; polar Lagrangian | RH ⇔ no crossing; B104 ⇔ `μ=μ₀` [L*] |
| M31 Coherence of reciprocity families | modes, columns, root numbers, signed Gram | short columns incoherent, average row target-free, long columns = sextic Gauss-sum moments [L*]; coherent at `R₀=2/3` [C] |
| M32 Galois theory of zeros | zero field, source field, Euclidean topology | `L=K` ⇔ RH [F]; no restriction forcing `L=K` |
| Amplifiers | Diophantine repulsion, integrality, Turán, positive annihilators | amplify or reshape a certificate, produce none [KR] |

## 2. Shared obstacle blocks

### S1. Complete Weil family at the critical curve
Routes: HF, SRT, AIP, ACS (atomic), SC. Programmes: CACT, AHD, CSAR, ACPL, ADT, RAPT, AGZ (polar Lagrangian).

Established:
- `0<R_PD=R_PSD=R_polar=R_halfline≤W=R_prim=R_high=inf_A windowThreshold(A)`, each infinite iff RH [F]; three-way classification: RH, or `R_polar<W`, or `R_polar=W` finite with every critical half-line ground state polar-orthogonal [L*] (`polarPaymentCriticalThreshold_windowThreshold_classification`).
- On the aperture side the orthogonal case is a neutral null mode: ground null modes are all charged iff `μ(a)<μ₀(a)`; below `μ₀` the index is the crossing number of the polar Lagrangian; unconditional for apertures `≤½(log 2+1/50)` and energies `<1/20` [L*] (AG-L6).
- Complete tilted-spline matrix positive definite for every exponent below `1/8` eventually, uniformly in `1≤c≤(log N)^α` [L*] (`eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_one_eighth`); through one small fixed multiple of `(log N)^{1/8}` [F].

| | Obstacle | Strength |
|---|---|---|
| A9, A13 | constants of the eighth-root horizon; near-gcd charges (unverified) | — |
| B6, B101 | full-space sign at every critical multiple; polar payment at every ratio | RH |
| B104 | whether `μ(a)=μ₀(a)` can occur, at the critical aperture in particular (a charge-free ground state solving the unforced equation) | method |
| B123 | correlated arithmetic pairings dominating the depleted kernel | method |

### S2. Window tower, canonical flow, aperture path
Routes: RW, EWU, OWU, ACT, CHMD, TT (odd), SZ, RN, LI, HF, ACS, SRT. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, CHT, AIF, VHR, WVL, SA, ACCE, AGZ.

Established:
- RH ⇔ `W≥0` on every window [F] ⇔ `Ψ` locally bounded on precontact intervals [L*] ⇔ feasible weights at every aperture [L*] (`not_riemannHypothesis_iff_empty_aperture`) ⇔ no crossing of the aperture path [L*] (AG-L2).
- Index law: `negativeRank b E = Σ_{a<b} weilNullity a E`; the index is also the number of eigenvalues below `E`; two monotone paths of a rectangle of apertures and energies meet equally many null modes [L*] (AG-L1, AG-L4).
- Nullities are not all even: a short aperture has a simple ground mode [L*] (AG-L9).
- Verification: `∃C`, RH through `exp(exp(Ca))` ⇒ the sign on `[−a,a]`, `a≥1` [L*]; `C` is not explicit in the statement.
- Selectivity: for `2a<log 2` feasibility does not depend on the weights [L*] (`feasible_iff_of_lt_half_log_two`); with the pole plane `|w(n)|≤√n(log(1+1/r)+C)` [L*]; the floor `1/5000` on tests of length `181/250` [L*] (AG-F7 basis).
- Certificates: every system feasible beyond some aperture has `|λ(n)−Λ(n)|≤ε` [L*] (`exists_aperture_forall_abs_weight_sub_le`).
- Confinement: positivity at aperture `a` confines every zero with `T₀(c)≤|γ|≤2πe^a` to depth `<exp(−c log³|γ|)` [L*].

| | Obstacle | Strength |
|---|---|---|
| A1–A3, A6 | certified verification past 67, numeric heights, first-window membership, cone widths | — |
| A142 | an explicit constant in the verification rate | — |
| A140 | the sign on windows of half-width below `½log 5` (unverified) | — |
| A117 | end points of the feasible interval of `w(2)` on the first selective window | — |
| B1, B2, B4, B5 | sign on every window; bounded `Ψ` to contact; outer predictors; kick admission | RH |
| B3, B16, B17 | variation of `r` free of `1/μ`; decay law of the margin; signed ground states past `log ρ` | sub / method |

### S3. Prime-degree sampling and scale locality
Routes: ACS, SRT, WL, HF, ZCG, PM (count door), HAT-C. Programmes: SOSZ, CDGeo, FFA, ShortIntervalPrimesInProgressions.

Established: the minimal face in its five forms (§0); floors at every length `(k+1)π/67` give AAL [L*] (`asymptoticAbscissaLaw_of_lengthDependent_floors`, prime version); one-sided floors on windows of one length have finite-stratum models [L*]; counter-configurations at every sub-logarithmic radius [L*]; every interval `(x,x+x^θ]`, `θ=1−1/(16(14·10⁷+12))`, contains a prime of every reduced class [L*] (`eventually_exists_prime_short_interval_mod`); Siegel–Walfisz in windows `h≥x/(log x)^H` [L*/doc] (SI1').

| | Obstacle | Strength |
|---|---|---|
| A58 | effective gap iteration (unverified) | — |
| B130 | the bound on any decisive sample; `Kp^σ`, `σ<½`, is a zero-free strip | RH (≥qRH at `p^σ`) |
| B144 | separation of the deep off-line ordinates | sub |

### S4. Continuation, index, constituents
Routes: ZCG, LA, PTR, HCF, PA, GTA, XN, WD, TH. Candidate: W1C. Programmes: NGF, FFP, ADO, AES, IRP, CTZ, GaloisTheoryOfZeros.

Established: RH ⇔ every zero of every `H_t`, `t>0`, is simple [L*] (`riemannHypothesis_iff_forall_zeros_simple`); `N(t)≤1` on times accumulating at `0` gives RH [L*]; `N_d≤300√(d log d)` for `log d≥6.1·10⁶` [F]; centered Jensen roots form quartets, `N_d=4Q_d`, `Q_d` exhausts the off-line divisor, discriminants are nonnegative unconditionally [L*/doc] (GZ1); ξ a locally uniform limit of entire functions with `≤κ` right zeros has `≤κ` [L*]; no bounded Dirichlet or Wiener constituent with a zero [L*]; the prime lag is positive definite ⇔ RH [L*].

| | Obstacle | Strength |
|---|---|---|
| A19, A20 | heat horizon with an explicit height; Jensen rung past `d⁴≪T log T` (unverified) | — |
| B22–B25 | outer Jensen roots; `N_d` bounded; collisions at small time; frequency below one | RH / ≥qRH |
| B124 | finite initial depth budgets of the heat divisor | ≥qRH to RH |
| B146 | an independent family of bounded index converging to ξ | RH (producer) |
| B27, B47 | runs of simple critical zeros; multiplicity by a non-size input | sub |

### S5. Near-line geometry, long moments, census, cameras
Routes: WD, CTF, MC, TG. Programmes: CDG, APR, MZF, AIF, IGP, TransThresholdPairCorrelation.

Established: RH ⇔ the Möbius-mollified second moment is subpolynomial; a cofinal bound with fixed `K` and unbounded `θ` suffices [F]; twisted moments below the square root and the positive critical proportion [L*]; positivity cost of a pair-correlation certificate `>13/10` [L*] (`positivity_test_cost_gt_thirteen_tenths`); squared right-depth moment `o(V)` [KR]; box cameras of order `n`: mass `2A`, geometric exterior loss `1/(hg)` per box, prime cost `8T(log T)²` uniform in the order, every eligible cluster with a fixed depth deficit visible or with a deep companion [doc] (CAM1); adaptive clusters pay their complete exterior mass without separation [F].

| | Obstacle | Strength |
|---|---|---|
| A18 | twisted moments past the square root [C] | — |
| A147 | logarithmic two-point Chowla: Matomäki–Radziwiłł for `λχ` and the final assembly [C]; in Lean: entropy decrement, circle method, the prime kernel off the major arcs [L*] (CL1') | — |
| B57 | depth density `o(T)` (first moment) | sub |
| B58–B61 | `D_win`; cluster wall (pointwise prime cost of the adaptive profile); Green moments at deep zeros; a detector past the last scale | sub |
| B62, B66 | cofinal long moment; near-unit holomorphic budgets | RH |
| B150 | a form factor bounded by `4` on `(1,10/9)` | sub |

### S6. Production, precision, the Mertens level
Routes: WL, MC, SQF, PBM, RB, JAS, CTF, FU, CFC, RP. Programmes: ASRP, APR, AGT, AKLT, AE, AAD, RAC, MMD, SPAL, HWV, RIAC, ALST.

Established: `c₁/(√K(1+log K))≤bestRate K≤exp(−(log K)^α)`, `α<3/5`; a polynomial rate ⇔ a Mertens power saving [L*] (`exists_hasRate_rpow_iff_mertens`); centred cover count `M(N)=Ω_±(√N)` [L*]; Type-II bounds are sign-blind [KR]; Stepanov at one prime `p^{11/12}` [F]; VK zero-free region for nonprincipal Dirichlet `L`-functions [doc] (MR1); twisted Chebyshev sums `≤N/(log X)^A` for `log N≥(log X)^θ`, `θ>2/3` [S].

| | Obstacle | Strength |
|---|---|---|
| A30, A33, A46 | best stencil exponent under RH; cubic residue coefficients; singular indices | — |
| B48–B54 | the deciding input at square-root precision and its classical faces | RH |
| B55, B67 | polynomial stencil rate; parity at power saving | ≥qRH to RH |
| B15 | pointwise savings past Vinogradov–Korobov in the Lean graph | sub |
| B56 | `Θ<1⇒Θ=½`; with `[X]` it is RH | RH |
| B106 | a correspondence on the orientation cover with bounded local indices | RH |

### S7. Reflection, carriers, the modular horizon
Routes: PM, HAT-C. Candidate: W1C. Programmes: RIT, BHR, ASH, AHMH, CTH, IRP, HAT, STCC.

Established: RH ⇔ every compact pulse rings down at the quarter rate [L*] (`riemannHypothesis_iff_pulse_ringdown`); a rate `δ` ⇔ `Re ρ≤1−2δ` (pulse rate ⇔ horocycle rate, `pulse_ringdown_iff_horocycle_rate`); AAL ⇔ no Euler polynomial filter accelerates the horocycle rate [L*]; the tower of height `N` is `log′(Λ(s)/Λ(s+N))` plus Robin and polar terms [L*]; at every fixed height the energy floor is RH [F]; no Maass cusp form with `0<λ<3/16` on any congruence subgroup [L*] (`selberg_three_sixteenths_congruence`); the hyperelliptic defect is an `ℕ`-count quadratic on rays [L*]; on the cubic cover: unfolding of `θ²` against incomplete Eisenstein series, the scattering coefficient with a simple pole at `4/3`, the log term in its constant Laurent coefficient, the cube frequencies of `θ²` factoring as `ζ_K(3w−1)` [doc] (ST1–ST3).

| | Obstacle | Strength |
|---|---|---|
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | — |
| A54 | cusp expansion for Bianchi resolvents | — |
| A148 | global continuation of the cubic Eisenstein series and the regularized Rankin–Selberg of `θ²` [C] | — |
| B68, B71 | independent reflection Krein positivity; universal decay and the horizon rates | RH |
| B87 | a count with Tate limit `Q`, defined without `Q` | RH |
| B147 | Shimura nonvanishing for one eigenform | indep. |
| B114, B117, B171 | partner involution; a regulator with a gap before the limit; a form of signature `(1,∞)` | producer |
| B178 | a relaxation rate beyond the tempered exponent from a principle of the horizon | producer |

### S8. The exceptional coordinate: two worlds and three atoms
Routes: BAG, ZCG, JAS (shell), SC (undamped), WL (thick runs), ACS (sampling), LA (finite support), RW (polar ground energy). Programmes: ZCG AbscissaLaws, ELT, EFT, IWT, IRW, IRP, APD, AAD, TAPO, FFA, SPAL, WZC.

Established:
- `Θ≤7/8` [X]; `Θ<1⇔Θ∞<1`, and `¬(Θ<1)` ⇔ `Θ=Θ∞=1` ∧ AAL [L*]; RH ⇔ ZAL ∧ B13 ∧ Landing [F]/[L*]; B13 ⇔ packet index `0` or `∞` [L*].
- World I receivers and instruments (§0); in world I, `ψ(x)−x=O(x^β)` is attained on every window [L*]; filters reduce the growing-order current to centred cofactors `≤3t^{71}` with filtered error `≤2h^d exp(−at/8)` [L*].
- Model theory over the rational primes (WZ1–WZ7): every finite layer, an isolated pair above a half-scale tail, landing failure, sparse tails, removal of a finite layer, a non-real pair alone on top at every count exponent above `½`.
- Laws of the models: balance or real top below a fake zero; parity of orders above `2max(β,c₀,θ/3)`; additions paid in full; count floor `(1−θ)/(4(2−θ))` for thin edits [L*/doc] (WZ2, WZ3, WZ7).
- The one-structure models without an Euler product: FE with Gamma factor, residue one and the count within one, with off-line zeros approaching the line and no landing [L*] (`exists_riemann_gamma_counting_model_without_landing`); the meromorphic Euler firewall [L*].

| | Obstacle | Strength |
|---|---|---|
| A120 | a finite nonempty stratum with both structures: Selberg zeta functions of surfaces with a small eigenvalue [C] | — |
| A144 | tangent data under additive twists (unverified) | — |
| B13, B138, B141 | finite stratum; landing; Deuring–Heilbronn for ζ | sub |
| B83, B170 | AAL; non-attainment for ζ | sub / AAL |
| B89, B112, B128 | bounded aligned return; FE into vertical transport; replication by another mechanism | sub |
| B145 | the prime-weighted centred type-II current at a growing isolated mode | AAL [D] |
| B110, B126, B127 | thick crude count; sampling set; lag recurrence | AAL |
| B157 | which structure of ζ that a Selberg-type zeta function lacks excludes a finite stratum | method |
| B183 | a fake with count exponent `β<½` and a non-real pair alone on top (must be balanced) | method |
| B186 | the size of the critical-line FE defect of a fake (the FE axis) | method |
| — | ZAL | ≥qRH |

### S9. Prime orbit at finite time
Routes: BAG, TH, SRT. Candidate: S3. Programmes: PTT, TAPO, TTPO, CDGeo, ALST.

Established: near-total returns need `log t>(log y)^{3/2−ε}` [F]; under `Θ≤b`, `c·y^{1−b}≤log t` [L*] (`heavy_return_bound_of_halfPlane`), so `y^{1/8}` [X]; under `Θ<1` the return transfer ⇔ RH [L*]; resonator means for `κ<2σ−1` [L*]; `T^c` separated returns, `c>(30/13)(1−σ)`, exclude a zero right of `σ` [L*].

| | Obstacle | Strength |
|---|---|---|
| A24 | certified scans (unverified) | — |
| B46, B97, B137, B121 | proportional saving at length `(log X)^{2K}`; first return past VK; collective depth floor; freezing control | sub |
| B148 | the transfer of S3 | RH (the strip is [X]) |

### S10. The diagonal, counts, absolute geometry, finite scale
Routes: ACS, HF, HAT-C, PM (count), LI. Programmes: SOSZ, HAT, AGZ, HFP, AE, RIAC, HHAC, CTH, LST, KPA.

Established:
- Forced data: `CombBezoutShift c ⇔ c≤0 ∧ RH`; a contact changed at its price is RH at every parameter [L*] (`combBezoutWith_contactAt_price_iff`).
- Index: exact count of right zeros for ζ with Dirichlet characters, Dedekind zeta functions, class characters, the degree-two Artin character of `ℚ(∛2,ω)/ℚ` and `ζ_{ℚ(∛2)}` (`forall_negIndex_cubeRootsOfTwo_eq_zero_iff`); a virtual configuration counts zeros and poles; `W_{ζ_L}−W_{ζ_K}` has no negative square ⇔ equal right zeros and on the line Dedekind's divisibility; the neutral form of a number ring has the index of its zeta function plus one [L*] (AG-V1–AG-V3).
- Finite scale: block matrix = charges + potential + Dirichlet form with attracting jets and contacts; the ground vector of the neutral part has one sign and is charged [doc] (AG-F4); RH ⇔ one negative square of the neutral part on every window [L*]; RH ⇔ a positive mass floor on every ratio window [L*] (`riemannHypothesis_iff_ratioWindow_positive_mass_floor`); short windows, first blocks of ratios 4, 7, thin packets certified [L*]; a margin above one scale `R` with `log R≥E_Q+2C_Q²/μ₀+μ₀` transfers to every refinement [L*] (`packetForm_refined_ge_half_of_margin`).
- Power tails: §0.
- Sections: the sections of the first `N` graphs in aligned boxes number the volume over `N!` [L*].

| | Obstacle | Strength |
|---|---|---|
| A28, A41, A48 | reciprocal-quadric traces; count law for plane quartics [C]; Hasse–Weil tests | — |
| A146 | the sign of `𝔚_4` and `𝔚_7` at every block size: certified margins between the first block size and the transfer threshold (`log R` about `2.5·10⁴` at ratio 4) (unverified) | — |
| A150 | Brauer induction, extending the quotient index law to every Artin character [C] | — |
| A141 | the half-plane `[X]` for fields containing `ζ₃` and every ray class character (unverified) | — |
| A152 | ordinary comb convergence at an unattained subcritical boundary: the contact-prefix convolution and its finite-part constant (unverified; pieces [S]) | — |
| B87, B88 | a count on the rays defined without `Q`; the sign of the comb finite part | RH |
| B149, B169 | Bézout from a property of the object; a doubling with a canonical height | RH (producer) |
| B152 | the sign on step packets at every ratio and block size | RH |

### S11. Families, rigidity, exactness
Routes: ACS (tensor), ECP, HF, SC, BAG. Programmes: AWT, AK, ALST, SignFreePurityMechanisms, EFT, SEL.

Established: fixed-part laws [F]; countable Beurling systems with an `L¹` or polynomially bounded `L²` FE defect are the rational primes; small `L¹` defect identifies the primes up to an explicit height [L*]/[KR]; positive continuous prime measures keep every zero [KR]; the Goss Riemann hypothesis [L*].

| | Obstacle | Strength |
|---|---|---|
| B86 | positivity of the endpoint character at unbounded rank | RH |
| B80 | FE twins with off-line zeros in the full class | sub |

### S12. The scale, the level, the signal, the probe
Routes: RW, HF, ACS, SRT (rungs); JAS, MC, WL, S3 (legs). Programmes: SA, FCT, MMD, CRF, STCC, RHTower `QuasiRH*`.

Established:
- Sizes and the ladder [L*] (SA §6 of the log): the trivial aperture `log log q+o(1)`; at height `t` dominated systems fail at `log log t+log(π/2)+η`; one theorem for saving, rung, companion and mollifier depth; exceptional heights of measure `≤T^{1−1/(2κ)+ε}`; three rungs under a half-plane; level one gives AAL and `Θ=½`.
- Level and signal: `Θ≤b` ⇔ signal `O(Z^{b′})`; a bound `O(Z^b)` gives the level `b+½+ε` [L*].
- Frame: `Θ≤σ₀` from two estimates with reciprocal kernels and a holomorphic nonvanishing correction [L*]; the probe's correction factorizes as `L^S(6s−3,ψ₆η⁶)·E` with `E` holomorphic and nonvanishing on `Re s>½` for every `S`; the frame premise at `½<σ≤2/3` is a zero-free half-plane of the phase `L`-function [L*/doc] (FC-T3, CR8).
- Coupled tower and its reach (FC-T1); Grössencharacter `L`-functions of every weight `6k` continue, are nonzero on `Re w≥1` and have infinitely many zeros in `½≤Re w<1` [doc] (FC-T2, FC-T4).
- Budget: the room `[13/15,7/8]` of the estimates; the floor-bin curve with landmarks `13/15`, `5/6`, `7/9`, `2/3` (D1); sieve terms; corners of the three sign-carrying designs `(κ,n)=(2,6),(3,4),(4,3)`: `8/9`, `25/28`, `49/54` [L*].
- Coherence (CR1–CR8): short columns and the short Gram cancel to every order; the average row is target-free; the long columns are first moments of the root numbers `G(u)γ₂(u)²`; the uncompleted correction has no wall.

| | Obstacle | Strength |
|---|---|---|
| A118 | the theorem `[X]` in the native graph (Poisson series and continuation, removal of the cube sum, uniform savings, theta-row reflection, sextic sieve, zero detector); first target the balanced design at `11/12` | — |
| A138 | the corollaries of `Θ≤7/8` as unconditional statements | — |
| A149 | the function-field calibration of the floor bin over `𝔽_q[T]`, `q≡1 mod 6`: Kubota series rational, the floor bin evaluated exactly (unverified) | — |
| B174 | the row count of the binding bin `δ=79/204` | a half-plane in `[13/15,7/8)` |
| B185 | the long columns: a power saving in the first moment of `G(u)γ₂(u)²` against a dual column, uniformly in the column | a half-plane in `(2/3,13/15)`; below `5/6` for `R₀<5/6` |
| B187 | a Möbius-signed source whose square-root endpoint is the line | producer |
| B180 | the reflection of the completed theta row without Eisenstein series | method |
| B160, B161 | `JasDressedPSD 1`; a signal bound below `7/8` | RH; a half-plane below `7/8` |
| B159 | a rung `κ≥4/3` with a saving that fails for the Liouville twist | a half-plane below `7/8` |
| B156 | arithmetic cluster exclusion on a rung | method |

### S13. Floor-free receivers and their kills
Routes: every route (as a filter). Programmes: FFA, WZC.

Established [L*]: floor `½` of count-invariant mechanisms; unit gap; certificates converge to `Λ`; amplification is a sup bound; linear statistics and differentiable functions of finitely many are not monotone under projection; positivity on the line of the pole only; add-only systems vanish at their real abscissa; translates at a finite layer have only the zero limit; floor of prime edits with a count rate `≥13/30`.

| | Obstacle | Strength |
|---|---|---|
| B170 | non-attainment for ζ | AAL |
| B171 | a form of signature `(1,∞)` from the places in which the right zeros are a symmetric spectrum | RH (producer) |
| B172 | a functional decreasing under projection that is not a function of finitely many linear statistics | producer |
| B173 | a two-sided subexponential bound of the trace on late windows of one length | AAL |

## 3. Live routes

Receiver statements follow the frontier map unless marked.

### WL — Weil lag
- **Path:** bounded prime-deficit critical energy, or positive definiteness of the prime lag, or an attained top with an `O(√X)` deviation on a thick set → RH.
- **Established:** RH ⇔ the prime lag is positive definite on `ℝ` [L*]; RH ⇔ attained top ∧ thick `O(√X)` deviation [F]; endpoint energy bounded ⇔ RH [F].
- **(a)** A30. **(b)** B49 (endpoint energy), B48 (deciding input), B110 (attained top with the thick estimate), B1.

### RW — Restricted Weil ground energy
- **Path:** `μ(a)≥0` at every aperture → RH; equivalently feasible weights at every aperture; equivalently no crossing of the aperture path.
- **Established:** RH ⇔ `Ψ` locally bounded [L*]; ⇔ feasible weights at every aperture [L*]; index law, Maslov form and far end (AG-L1–AG-L3) [L*]; feasible systems converge to `Λ` [L*]; verification rate [L*]; polar Lagrangian below `μ₀` [L*].
- **(a)** A1–A3, A16, A117, A140, A142.
- **(b)** B1, B2, B4, B18; B104 for the polar channel.

### FU — Signed prime scheduling
- **Path:** signed Möbius history → one-sided sampled Abel bound → RH. **Established:** either one-sided bound on `A(j^m)/j^m` ⇔ RH [F].
- **(a)** none. **(b)** complete-history bounds across advancing clocks (B42).

### CFC — First-clock lower bound
- **Path:** first-clock source bounded below on a tail → RH. **Established:** exact tail criterion [F].
- **(a)** none. **(b)** the lower bound with prime, archimedean and endpoint terms (B42).

### RP — History floor
- **Path:** eventual linear floor of the normalized history → RH. **Established:** linear-floor criterion; sublinear floors impossible [F]/[KR].
- **(a)** none. **(b)** high-LCM pairs, moving core, singular terms in one floor (B42).

### PA — Prime–archimedean passivity (HJ alias)
- **Path:** prime−Gamma response sign → RH. **Established:** calibrated Hausdorff-row sign above explicit cutoffs; the remaining entries ⇔ RH [F].
- **(a)** A1. **(b)** signs below the explicit shift uniformly in the degree (B31).

### MC — Möbius cancellation
- **Path:** half-power Möbius cancellation → RH.
- **Established:** damped critical energy, fixed-height prefixes, mollifier zero-freeness each characterize RH [F]; centred cover count `M(N)` [L*]; the signal of the zeta kernel is a smoothed Möbius sum whose exponent is the zero abscissa [L*]; the cube identity and the sign law [L*]; the coupled tower and the probe's reach (FC-T1, D1); logarithmic Liouville correlations reduce to prime dilates and the prime kernel off the major arcs is bounded [L*] (CL1'); VK region for Dirichlet `L` [doc]; tangent data of `μ` and `λ` in world I [F].
- **(a)** A33, A46, A118, A147.
- **(b)** B48, B50, B15, B106; B161; B174, B185, B187. RH needs a source other than the cubic probe [F] (D1, D2).

### SQF — Weighted squarefree count
- **Path:** a one-sided `O(t^{−¼−ε})` bound of `Σμ(n)²e^{−nt}−6/(π²t)` → RH. **Established:** either one-sided law ⇔ RH; `Ω_±(t^{−1/4})` [F].
- **(a)** none. **(b)** the quarter-power bound for one sign (B48 family).

### TT — Theta tail / Wold
- **Path:** bounded weighted endpoint energy at each `0<t<½` → RH. **Established:** RH ⇔ a bound `C_t` for every `t`; uniform bound on a shrinking band [F].
- **(a)** none. **(b)** `C_t` at every fixed `t` (B34).

### LA — Jensen line anchor
- **Path:** Jensen polynomials real-rooted, or sublinear root height → RH.
- **Established:** RH ⇔ infinitely many Jensen degrees real-rooted [F]; `N_d≤300√(d log d)` [F]; quartet exhaustion `N_d=4Q_d`, nonnegative discriminants [L*/doc]; at each fixed degree finitely many bad shifts [F].
- **(a)** A20, A1. **(b)** B22; B23 then B13, B138; B124.

### ZCG — Zero-configuration geometry / heat descent / abscissa laws
- **Path:** no positive-time collision → RH; or a decisive prime-window floor; or ZAL ∧ B13 ∧ Landing.
- **Established:** collision exclusion ⇔ RH [L*]; blocks S3, S4, S8, S13; four sectors of the trace [L*]; cameras and box cameras [L*]/[doc]; the prime error retains a complete right-substrip zero trace with a globally bounded power-saving remainder [doc] (PC7); the model theory of world I over the rational primes (WZ1–WZ7).
- **(a)** A19, A120, A144, A151.
- **(b)** B24, B25, B47, B27, B124; B130; B145, B170; B13, B138, B141; B59; B183, B186.

### TG — Topological sub-unit gate
- **Path:** cubic defect trace norm `<1` → integer zero count vanishes → RH. **Established:** exact integer trace; endpoint and Gaussian central-gap receivers [F].
- **(a)** none. **(b)** trace norm below one on every formation rectangle (B38).

### HF — Hodge / complete cells
- **Path:** complete arithmetic form `≥0` → Hodge index → RH.
- **Established:** S1, S10; RH ⇔ one negative square of the neutral part on every window [L*]; exact index for Hecke characters, number rings, one non-abelian Artin character and quotients [L*]; three-way classification [L*].
- **(a)** A9, A13, A141, A146, A150.
- **(b)** B6, B101, B104, B123, B8, B41, B10, B87, B88, B149, B152.

### HAT-C — Arithmetic-clock Green energy
- **Path:** one clock, or one fixed scattering height → energy floor → `W≥0` on packets ⇔ RH.
- **Established:** the clock lies below Weil's form; a floor at one cutoff per large aperture gives RH [L*]; the tower is the completed-zeta quotient [L*]; at every fixed height RH ⇔ the corrected-energy floor [F].
- **(a)** none. **(b)** the floor at one fixed height on all apertures (B1).

### CHMD — Causal hyperbolic–modular duality
- **Path:** bounded prime wave, or the odd half-threshold bound → RH. **Established:** wave and Doob receivers; normalized decay [F].
- **(a)** none. **(b)** either side of the unnormalized wave bound; the complete odd sign (B35, B4).

### TH — Theta moment positivity
- **Path:** signed center-mixed jets → all-rank Hankel positivity → RH.
- **Established:** ranks `≤14`; rank `N` from verified height `41+6(N+2)log(N+2)`; the adaptive critical Dirichlet sum is `ζ(½+ib)` up to `O(|b|^{−½})` [F].
- **(a)** A4, A5, A24, A42. **(b)** B102, B20, B21.

### RN — Theta renewal
- **Path:** exclusion of joint nodes, or the theta-ground energy comparison → RH. **Established:** two-ended formula recovers Ξ with multiplicities [F].
- **(a)** none. **(b)** B36.

### WD — Ward / collision / long moments
- **Path:** cofinal long-mollifier moments, or collision bounds → RH.
- **Established:** RH ⇔ subpolynomial mollified moment; cofinal bound with fixed `K`, unbounded `θ` suffices [F]; twisted moments for `θ<½` and the positive proportion [L*]; dyadic boundedness at `θ>1` confines depth to `<1/(2θ)+ε` [L*] (`cancellation_and_depth_ladder`).
- **(a)** A18. **(b)** B62, B57–B61, B63.

### LI — Paired Li / Cayley ladders
- **Path:** subexponential lower bound of the clock response, or the Cayley–Li sign → RH.
- **Established:** RH ⇔ ladder sign on primitive vectors; `λ_n≥0` for `n≤314`; paired Li coefficients are limits of comb tails [F].
- **(a)** A1. **(b)** B43.

### SZ — Suzuki screw
- **Path:** rectangular Ward defect bounded below → RH. **Established:** completed Abel source bounded ⇔ RH; VK saving [F].
- **(a)** none. **(b)** B37, B1.

### PM — Physical model
- **Path:** scattering source → reflection Krein sign, ringdown rate, cavity rate or a count → RH.
- **Established:** S7.
- **(a)** A26, A54, A148. **(b)** B68, B71, B87; B147; B114, B117, B171; B178.

### PTR — Cosine source
- **Path:** no exceptional point of the cosine producers on the open depth band → RH.
- **Established:** RH ⇔ strict Laguerre sign at every `0<h<½`; ZAL gives finite nonreal defects [F]; no bounded or Wiener constituent with a zero [L*].
- **(a)** none. **(b)** B29, B69.

### JAS — Joint ancestry
- **Path:** level-one dressed positivity on large primes; or subpower moving-window control → RH.
- **Established:** RH ⇔ `JasDressedPSD 1` [F]; level one gives AAL and `Θ=½` [L*] (`levelOne_abscissa_laws`); a signal bound `O(Z^b)` gives the level `b+½+ε` [L*]; with `[X]` the level `11/8+ε`; the completed cubic bootstrap cannot supply the half-power input [F]/[KR].
- **(a)** A118, A138. **(b)** B160, B161 (through B174, B185), B51.

### CTF — Chronological tail / Báez–Duarte
- **Path:** unit-bounded rows, BSY sign, cut-kernel mass → RH. **Established:** the three criteria [F].
- **(a)** none. **(b)** B52, B66, B91.

### HCF — Heat trace
- **Path:** two prime-log heat grids nonnegative at every degree → RH. **Established:** two-grid criterion [F].
- **(a)** A1. **(b)** B30.

### XN — Newton discs
- **Path:** line-centred self-map discs covering every zero → RH. **Established:** coverage and margin criteria [F].
- **(a)** none. **(b)** B32.

### BAG — Self-return
- **Path:** uniform head-target density → RH; transport → AAL.
- **Established:** strong recurrence ⇔ RH [F]; graded returns exclude zeros [L*]; translates at a finite layer have only the zero limit [L*]; resonator means [L*].
- **(a)** none. **(b)** B72, B83, B89, B97, B137, B145.

### EWU — Even sector
- **Path:** even blind minimum `≥0` at every aperture → RH. **Established:** blind minimum `≥1/20` for `a≤(log 2+1/50)/2` [F].
- **(a)** A1–A3. **(b)** B4, B17, B44.

### GTA — Schur charge
- **Path:** cofinally small quartic charge → RH. **Established:** compactness criteria [F].
- **(a)** none. **(b)** B33.

### OWU — Odd sector
- **Path:** odd positivity with the polar hyperplane → RH. **Established:** odd criterion; unit-window floors [F].
- **(a)** A1–A3, A6. **(b)** B4, B17, B44.

### PBM — Regularized abscissa
- **Path:** convergence of the pole-regularized series right of `½` → RH. **Established:** exact equivalence [F].
- **(a)** none. **(b)** B53.

### RB — Robin / Nicolas
- **Path:** eventual extremal inequality → RH. **Established:** eventual criteria [F].
- **(a)** none. **(b)** B54.

### SRT — Lag localization
- **Path:** the prime two-bump sign on a decisive sample → RH. **Established:** S3 [L*]; prime packet rungs from verified heights [F].
- **(a)** A9. **(b)** B130, B6, B101, B104.

### ACT — Single shift
- **Path:** the variation inequality at one shift → RH. **Established:** receiver; `{2,3,4}` kicks below `991/1000` of the Lévy energy for `2c<log 5` [F].
- **(a)** A7, A140. **(b)** B44, B4.

### AIP — Incidence
- **Path:** global incidence allocation → RH. **Established:** exact allocation; VK signed cost [F].
- **(a)** A9, A13. **(b)** B45, B101, B104.

### SC — Stokes / Witt–Krein
- **Path:** bounded Gaussian-damped coupling, or glued index `≤1` → RH. **Established:** bounded damped coupling ⇔ RH; glued index `=κ_ζ+1`; undamped coupling on a two-prime cone gives AAL [F].
- **(a)** none. **(b)** the damped bound; sublinear tensor loss (B39); ZAL for the undamped branch; B104.

### ACS — Castelnuovo–Severi on the degree points
- **Path:** the comb sign, the neutral-part index on every window, subpolynomial critical-comb growth, or critical Abel integrability → RH.
- **Established:** S10; §0 (finite-scale index, short windows, first blocks, thin packets, critical comb).
- **(a)** A28, A41, A48, A141, A146, A150, A152.
- **(b)** B152, B149, B169, B88, B87; B130; B28; B13.

### ECP — Endpoint character positivity
- **Path:** endpoint jets → class functions → PSD character Grams at every rank ⇔ RH. **Established:** projections nonnegative; Toeplitz minors through order 200 [F].
- **(a)** none. **(b)** B86.

## 4. Candidates

Each needs its source-to-receiver step (B81). Dormant pending a source mechanism: SEC, CDC/BSH, APF, EWJ, RFHM, WBF.

| Candidate | Established | (a) | (b) |
|---|---|---|---|
| S3 | a strip excludes heavy identity returns; under `Θ<1` the transfer ⇔ RH [L*] | none | B148: with `[X]` the transfer is RH |
| SEC | Fock boundedness at every strip parameter ⇔ `Re s=½` [F] | none | a ζ-selective bound from the Sonin source |
| CDC/BSH | marked prices agree iff `Re s=½` [F] | none | descent on actual zero fibres |
| APF | prime/grade trace reconstruction [F] | none | full-divisor exhaustion |
| EGC | zero-pair contour; explicit count error [F] | none | height-fibre isolation |
| EWJ | all-depth reporter [F] | none | faithful endpoint admission |
| FEL | KL accounting [F] | none | a predeclared history forcing the BSY sign |
| IRK | finite idempotent traces [F] | none | projective lift identifying trace with Chern charge |
| MSC | `L²` discrepancy; conormal transport [F] | none | Sonin/Weil sign landing |
| RFHM | support source; creation [F] | none | an RH-sufficient orientation law |
| W1C | index-one approximants or an index-one realization give RH [L*] | none | B146, B171 |
| WBF | Gram recovers magnitudes and phase class [F] | none | arithmetic stream and Ξ landing |

## 5. Supporting programmes

| Programme | Established | (a) | (b) |
|---|---|---|---|
| AGZ | forced data; paths; exact index for Hecke characters, number rings, one Artin character, virtual configurations; finite-scale index law; short windows and first blocks certified; thin packets; Morse = Maslov index; polar Lagrangian; power and critical combs [L*] | A146, A150, A152 | B104, B149, B169, B88, B87, B152 |
| HFP | mass floors on ratio windows; robust index; Li tails [L*] | — | B152 |
| WZC | two-sided edits: every finite layer, pair alone above `√x`, tails, landing failure, sparse configurations, layer removal; balance, parity, additions, count floor; floor of prime edits `≥13/30` [L*] | A151 | B183, B186 |
| CRF | short columns, short Gram, average row, completed pair Gram, root numbers `Gγ₂²`, wall = phase `L`-function, wall = price of completion [L*] | A149 | B185, B187 |
| STCC | unfolding of `θ²`, scattering coefficient across `4/3`, cube frequencies of `θ²` [doc] | A148 | B180 |
| FCT | frame, corrections, coupled tower to `3/5`, zero transfer, budget, signed-Gram curve, twist-family law [L*] | A118, A138 | B161, B174 |
| MMD | cube identity, cubic reciprocity, cubic Eisenstein residue, quadratic sieve over `ℤ[ω]` [L*]/[F] | A33, A118 | — |
| GaloisTheoryOfZeros | zero field over the source field; Jensen quartets; Euclidean topology [L*/doc] | — | an independent restriction forcing `L=K` |
| FFA | floors; receivers and kills of every off-scale kind; tangent data [L*] | A144 | B170–B173 |
| SPAL | count rigidity; integer-norm fakes above and below `½`; the real top of a deletion [L*] | — | — |
| EFT / APD | FE rigidity with `L¹`/`L²` defects; firewall; Hamburger rigidity [L*] | — | B186 |
| SA | trivial aperture; ladder; exceptional heights; three rungs; deep zeros at ζ density [L*] | A117 | B159, B156 |
| ELT | atoms; filters; growing-order reduction [L*] | — | B141, B145, B138, B13 |
| CTZ, IRP | no bounded or Wiener constituent; index semicontinuity [L*] | — | B146 |
| MZF / CDG | twisted moments; positive proportion; cameras and box cameras [L*]/[doc] | A18 | B62, B57, B59 |
| LogarithmicChowla, PrimeExponentialSums, MatomakiRadziwill | entropy decrement; circle method; prime kernel off major arcs; VK region for Dirichlet `L` [L*]/[doc]; twisted Chebyshev [S] | A147 | — |
| ShortIntervalPrimesInProgressions | primes in `(x,x+x^θ]` in every class; Siegel–Walfisz in windows [L*] | — | — |
| SignFreePurityMechanisms | Goss Riemann hypothesis [L*] | — | a norm for ξ |
| HAT | clock; tower; unbounded critical inverse [L*]/[KR] | A54 | B88, B117 |
| BHR / AHMH / ASH / CTH | ringdown ⇔ strip; horocycle exponents; filters; hyperelliptic count [L*] | A26, A41 | B68, B71, B87, B147, B178 |
| TTPO / PTT / TAPO / CDGeo | returns; resonator means [L*]/[F] | A24 | B46, B97, B137 |
| ALST / AAD / RAC / APR | Stepanov degrees; producer rates; cut kernel; parity blindness [L*]/[F]/[KR] | A30 | B48, B55, B67 |
| AHD / CACT | thresholds, classification; positivity below the eighth root [L*] | A9, A13 | B104, B123 |
| VHR / TCS | height 67; double-exponential window height [L*] | A1–A5, A142 | — |
| Census (IGP, TTPC) | `0.67250071`; positivity cost [L*] | — | B150, B57 |

## 6. Decisive wall per route

| Wall | Routes |
|---|---|
| The minimal face `P(p)≤A(p)+K` on logarithmic windows off power-thin exceptions | ACS, SRT, WL, HF, ZCG, HAT-C, PM (count) |
| Σ: the sign on every window = no crossing of the aperture path = one negative square of the neutral part on every window = feasible weights at every aperture | RW, EWU, OWU, ACT, CHMD, SZ, RN, AIP, SC, LI, TT (odd), HF, HAT-C, ACS |
| Σ: continuation at small time; theta heads | ZCG (heat), PTR, LA, GTA, XN, HCF, PA, TH |
| Π: square-root precision; long moments past the height | WL, MC, SQF, PBM, RB, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| One scale, one producer: `[X]` at `7/8`; the cubic probe's estimates reach `2/3` with square-root cancellation and its frame `3/5` with estimates beyond it; no other source | JAS; MC (signal); S3; ACS (tails); every graded receiver |
| Γ: reflection and count | PM, ECP |
| The exceptional coordinate: world I needs the Euler product with the FE as an identity or with a count below the floor; world II is the scale | BAG, ZCG, JAS shell, SC undamped, WL thick runs, LA finite support |
| The dark range: prime sums shorter than the Vinogradov length; polynomials longer than the height | every route at all heights; BAG; WD |
| Missing source landing | the twelve candidates |
