# Route obstacles — status quo

Scope: the 38 live route formulations, the 12 route candidates and the supporting programmes. For each route: the path, what is established, the obstacles that are **(a) just work**, and the obstacles that are **(b) open mathematics nobody has a solution to**.

**Corpus checkpoint:** `dd55ee70d9` (2026-11-12), working-tree sources included. Fact log: `logs/review-1211-rev2-facts.md` (cited as "log §n"; every entry is a Lean statement read at its declaration). Companions: [obstacles-summary.md](obstacles-summary.md) (A/B lists, ideation, the one question), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ), [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem).

**Live** means source observable, proved RH-sufficient receiver and explicit open estimate. **Candidate** means the source-to-receiver step is missing. HJ is PA; the BSY criterion of FEL belongs to CTF; PCS, DR, PW-B are retired labels.

**Evidence.**
- `[L*]` Lean statement read at the declaration for this report and recorded in the fact log.
- `[doc]` content of a module docstring whose theorem names were read but not every statement.
- `[F]` stated by the [frontier map](../rh-current-frontier-map.md); `[KR]` stated by the [scoped-obstruction ledger](../rh-killed-routes.md). `[S]` a module the frontier map grades unfinished or unintegrated.
- `[card]` proved on the pipeline card `docs/drafts/pipeline/2-fully-proven/b186-critical-line-fe-defect-of-fake-zeros.md`; no Lean declaration.
- `[D]` deduction made here from `[L*]` statements; not a Lean theorem. `[C]` classical mathematics quoted from memory, not in the corpus. `[A]` assessment.
- `[X]` the external theorem cached in the repository (OpenAI, 30 September 2026), taken as proved: every Dirichlet `L`-function, ζ included, and every finite-order Hecke `L`-function over `ℚ(√−3)` is zero-free in `Re s>7/8`; so `Θ≤7/8`. The Lean graph proves `zetaZeroAbscissa ≤ 1` unconditionally (`RHTower/ZetaZeroAbscissa.zetaZeroAbscissa_le_one`) and `beta ≤ 7/8` from a uniform continuation margin (`beta_le_seven_eighths_of_uniform_margin`, log §16); the native steps of `[X]` are just work (A118). **Natively** refers to the Lean graph.

**Strength.** RH; ≥qRH (implies a zero-free half-plane, Lindelöf or ZAL; open where it gives a half-plane below `7/8`); AAL; sub (implies neither a half-plane nor AAL); method; producer; indep.

**Labels.** `A*` just-work items and `B*` open problems are listed in [obstacles-summary.md](obstacles-summary.md) §2.1–2.2. `(unverified)` marks A items whose difficulty is not established. Σ, Π, Γ refer to [walls-ledger.md](walls-ledger.md).

**Notation.** `Θ=sup Re ρ`; `Θ∞=inf{σ≥½: finitely many zeros have Re ρ>σ}`; `w=Θ−½` the zero width. **ZAL** `Θ∞=½`; **AAL** `Θ=Θ∞`; **B13** finitely many off-line zeros ⇒ none; **Landing** ZAL ⇒ finitely many off-line zeros; **World I** ¬AAL (a finite isolated top layer); **World II** AAL ∧ ¬ZAL (a tail). `2Re S(log p)` is the prime trace; a **logarithmic window** at `T` is `{p: |log p−T|≤32 log(T+2)}`. The **restricted Weil form** at aperture `a` acts on tests supported in `[−a,a]`; its **index** `negativeRank a E` and **nullity** `weilNullity a E` at energy `E`; the two **charges** of a vector are its coefficients at the two poles; `μ(a)` is the ground energy and `μ₀(a)` the floor on charge-free vectors. A **step packet** is constant on the blocks `(a,a+1]`; its **block matrix** is `d(a)+d(b)+δ_{ab}ϱ(a)−J(a,b)−C_Q(a,b)` (degrees, density, jets, floor-map contacts) and its **neutral part** is the block matrix without the product of the two charges. A **bound state** of a window is a negative square of its neutral part. For a symmetric matrix `A` that is nonnegative on the kernel of a charge vector `u`, with `Aa=u`, the **susceptibility** is `u·a`. The **critical half-line state** at a finite critical ratio `W₀=inf_A windowThreshold(A)` is a unit vector supported on `u<0` with nonpositive truncated Weil form at every cutoff (`IsCriticalHalfLineGroundState`). The **power tail** at `0<a≤½` is the comb form `F_a(N)` of the power divisor; `a=½` is the **critical comb**. A **system** is a weight system with a mass; the **trivial aperture** is `log log(mass)+o(1)`; the **Liouville twist** is `w(p^k)=(−1)^k log p`. The **signal** of a kernel `G` is `(1/2π)∫G(2+it)Z^{2+it}dt`. The **probe** is the cubic-theta sum of `[X]` over `K=ℚ(ζ₃)`; its **correction** is `H_η`; its **twist order** is `n=6`; `R₀` is the row exponent of its floor bin. A **two-sided edit** is the system of the rational primes with some primes deleted and some doubled; it is a **fake** at `β` if its count is `Ax+O(x^β)` and its zeta function continues to `Re s>½` with a zero there that ζ lacks. The **FE defect** `g` of a system is its critical-line functional-equation defect in the Hamburger strip class (`HamburgerStripDefect`, log §3); ζ has `g=0`.

## 0. The picture

| Fact | Evidence | Consequence |
|---|---|---|
| RH ⇔ `2Re S(log p)≥−K` at the primes of arbitrarily late logarithmic windows outside `Ce^{δT}` primes per window; ⇔ the upper side alone; ⇔ `ℕ`-counts on surviving prime rays; ⇔ one growth exponent for all even local moments; ⇔ copositivity of the prime planes; `Θ<1` ⇔ the floor `−Kp^α`, `α<½` | [L*] (log §8, §15) | one inequality per prime on sparse windows |
| Prescribed sublogarithmic windows do not bound the class; a density-matched configuration survives on the minimal face | [L*] (`exists_classZ_prescribed_sublogarithmic_windows_bddBelow_beyond_every_bound`, `densityMatchedMinimalFace_counts`) | no window below the logarithmic radius decides |
| RH ⇔ the neutral part of the step-packet matrix of every window `(R,R+J]`, `R≤J`, has exactly one negative square; the block matrix has `r` negative squares on some window iff ζ has `≥r` zeros right of the line, the neutral part iff `≥r−1`; the pole adds one negative square | [L*] (log §8, §14, §22) | RH is the Hodge index theorem of explicit finite matrices |
| The neutral part has exactly one negative square on every window with `R≤J`, `50J≤53R`, at every block size (margin `1/5000` of the block matrix); on narrow windows `16J≤R` it has at most one; the first step packets of ratio four have margins `1/20` and `1/100`; every ratio is nonnegative on thin step packets | [L*] (log §2, §8, §14) | certified: ratio `≤103/50`, narrow windows, first blocks |
| Two matrices, each nonnegative on the kernel of its charge vector, coupled through the product of the charges, have exactly one negative square iff the product of their susceptibilities is `≥1`, and exactly two if both susceptibilities are negative with product `<1`; the union of two adjacent windows holds at most the bound states of this model with potentials lowered by the excess couplings | [L*] (`hermNegIndex_glued_eq_one`, `hermNegIndex_glued_eq_two`, `hermNegIndex_neutralWindow_add_le_glued`) | the induction step of the finite-scale index is one inequality between two numbers |
| The index of the restricted Weil form at aperture `b` is the sum of the nullities of the apertures below `b` and the number of eigenvalue crossings; the crossing multiplicity is a Lagrangian intersection number; its supremum at energy zero is the number of zeros right of the line | [L*] (log §14) | the Morse index of the sign problem is a Maslov index |
| Below the polar ground energy every crossing is charged and the rank is at most two; no neutral null vector at the ground energy iff the ground energy is below the polar ground energy; on windows with `4J≤R` a ground vector of the block matrix has one sign and both charges nonzero of one sign | [L*] (log §2, §14) | B104 is settled at finite scale on narrow windows |
| RH, or a finite critical ratio `W₀` with a critical half-line state: zero full energy, the weak equation against the whole energy domain, unique up to sign, Laplace transform nonzero on `Re z>0`. RH, or `R_polar<W₀`, or the state is orthogonal to the polar source | [L*] (log §1, §13) | a failure of RH has one canonical extremal function |
| The critical comb `F_{½}(N)` has growth exponent the zero width and never converges; RH ⇔ subpolynomial growth ⇔ absolute logarithmic Abel integrability; for `0<a<½`: Abel integrable ⇔ `a+w≤½`, convergent ⇔ every zero has `Re ρ<1−a`; the Laguerre tails of the comb tend to the paired Li coefficients | [L*] (log §2, §8, §11, §14) | the width and the Li coefficients are read on one explicit sequence |
| `Θ≤7/8`; `Θ<1⇔Θ∞<1`; `¬(Θ<1)` ⇔ both abscissas equal one; RH ⇔ ZAL ∧ B13 ∧ Landing; B13 ⇔ the packet index is `0` or `∞`; AAL ⇔ at most one or infinitely many zeros right of every line | [X]; [L*] (log §15) | a failure of RH is world I or world II with top `≤7/8` |
| Two-sided edits of the rational primes with a count rate realize: a non-real pair alone on top at every count exponent above the pair; every finite layer; an isolated pair above an infinite half-scale tail; zeros decreasing to the line; zeros rising to a line; sparse configurations; zeros symmetric in a strip; a finite layer of ζ edited away | [L*] (log §9, §18) | Euler product over the rational primes, integer norms and a count rate constrain no finite layer, no landing, no sparse tail |
| A fake at `β≤½` is balanced or has a real zero on top; a zero of the edit exponential at `Re ρ>2max(β,c₀,θ/3)` has even order; `(1−θ)Re ρ≤2β(2−θ)`; the floor of prime edits with a count rate is `≥13/30` | [L*] (log §9, §18) | the count sees a fake zero only below half its real part |
| A countable Beurling system whose FE defect is `L¹`, or `L²` and polynomially bounded, is the rational primes. Two unequal coefficients give an Abel floor: `g` does not tend to zero. A fake two-sided edit has `∫‖g‖²e^{−\|t\|/T}≥(A²/(256πp₀))T log T` and `g` is not `≤c√log\|t\|` | [L*] (log §3, §8, §10) | every fake has a non-decaying FE defect; the constant is that of the least deleted prime |
| `Θ=1` with AAL, or `Θ<1` and for every `½<β₀<3/2−Θ`, `ζ(β₀+iγ₀)≠0`, `β₀<β_c<1` a two-sided edit that is a fake at `β_c` with the pair `β₀±iγ₀`, `‖g(t)‖≤K_ε\|ζ(½+2it)\|(1+\|t\|)^ε`, mean square `≤C_εT^ε` | [L*] (`frontier_dichotomy`, log §12) | with `[X]`: fake zeros cost a defect between `√log` and `T^ε` in mean; the reflection decides only up to a decaying error |
| `F(s)=(1−2^{ρ−s})(1−2^{ρ̄−s})`, `ρ=¾+i`: real integer weights, bounded count, bounded defect, `F(ρ)=0≠ζ(ρ)`, Abel floor `≥1/12` | [L*] (`signedPoly_fake`, `fake_abelMass_floor`) | boundedness of the defect selects nothing among signed weights; decay does |
| The cubic probe is a coupled tower: a zero `ρ` of `L(s,η)` with estimates below `Re ρ` forces a zero of a sextic Grössencharacter `L`-function at `6ρ−3`; with all estimates `Θ≤max(σ₀,3/5)`; `7/12` under sextic GRH; the continued correction has infinitely many zeros in `7/12≤Re s<2/3`. For every `6r`-periodic Gauss pairing the uncoupled boundary is `2/3` and the coupled fixed point is `(4r−1)/(6r−1)≥3/5`, equal to `3/5` iff `r=1` | [L*] (log §6, §16) | the frame of the one producer ends above `½`, at every period |
| In the probe's budget, square-root cancellation across the rows of the floor bin gives the half-plane `1−2/n=2/3` | [L*] (`signedGram_phase_endpoints`); [D] | the producer, fully evaluated, stops at `2/3` |
| The root number of a row is `G(u)γ₂(u)²`; short columns are incoherent; the average row is target-free; `Σ_I N(I)^{−w}τ(I)²` factors as `ζ_K(3w−1)` times a squarefree sum; `M·D` has a double pole at `4/3` with coefficient `108π³r³`, the rotated correlation `54π³r³`, the squarefree combination a simple pole | [L*] (log §6, §16, §22) | the untwisted main term of the long columns is a theorem |
| The centered zero field `L` is algebraic and normal over the fibre source field `K`; conjugation is central; orbits are finite; critical zeros are fixed; an embedding fixing the prime trace field `B` sends a zero to a zero with centered real part `±` the original; `K_even⊆ℝ` ⇔ RH ⇔ the reflection field `H` equals `B` | [L*] (log §4, §21) | RH is the triviality of a group of sign families |
| RH through `exp(exp(C·a))` gives the sign on `[−a,a]`; `C` is not explicit; positivity at aperture `a` confines zeros with `T₀≤\|γ\|≤2πe^a` to depth `<exp(−c log³\|γ\|)` | [L*] (log §8) | each window is a finite-height statement |
| A zero at height `T` of depth `≥exp(−c log³(T/2π))` has a finite cluster and a test in the aperture `λ log(T/2π)/2` with complete multiplicity-weighted exterior mass `≤¼` | [L*] (`exists_zeta_cluster_with_complete_exterior_mass`) | isolation of a deep zero needs no separation hypothesis |
| For `χ≠1`: `Σ_{k<X}\|Σ_{X+k<n≤X+k+h}λ(n)χ(n)\|²≤εh²X` for `h≥h₀(ε)`, `X≥X₀(h)`. For `χ=1`: top-scale blocks `≤(log X)^{−3}` on `(log X)^{19}≤2π\|w\|≤X` | [L*] (log §5, §17) | Matomäki–Radziwiłł for twisted Liouville is native; the principal character lacks its low frequencies |
| Displaced twisted second moments for `θ<½`; a positive proportion of critical zeros of odd multiplicity; `0.67250071` simple critical zeros in the objects of `Zeta23` | [L*] (log §8) | the in-law half of the near-line picture is native |
| The Goss zeta function at `z∈ℤ_p∖ℕ` has simple zeros of strictly decreasing norms | [L*] (`gossZeta_riemannHypothesis`) | one Riemann hypothesis is proved by dominance, with no sign |
| The Brauer elementary monomial virtual characters generate the virtual characters of a finite group | [L*] (`brauer_induction`) | the index of an Artin character is one reciprocity law away (A154) |

## 1. Mechanism classes

| Class | Mechanism | Status |
|---|---|---|
| M1 Signed criticality | primes pay the archimedean–polar deficit by sign | exact on every window; a window at aperture `a` follows from verification to `exp(exp(Ca))` [L*] |
| M2 Calibration | window cones, feasible sets, margins | feasible sets nonempty at every aperture ⇔ RH; they converge to `Λ` [L*] |
| M3 Canonical flow | `L, q, Ψ` of the Weil chain | RH ⇔ `Ψ` locally bounded on precontact intervals [F] |
| M4 Reflection | Krein forms, ringdown, horocycles, cavity energies | sharp receivers; pulse rate = horocycle rate [L*]; exponents `1−Θ/2`, filtered `1−Θ∞/2` [F] |
| M5 Square-root cancellation | prime counts, long moments, squarefree counts | receivers closed; estimates open |
| M6 Continuation | heat, cosine, Jensen | collision-free flow ⇔ RH [L*]; finitely many non-real zeros at every positive time, infinitely many at every negative time [L*] |
| M7 Zero geometry | cameras, Blaschke factors | adaptive clusters pay their complete exterior mass [L*]; pointwise prime cost at the selected centres open [F] |
| M8 Finite-layer receiver | filters, currents, non-attainment, tangent data | complete in world I [F] |
| M9 Production | integer stencils, Stepanov | rate = Mertens level [L*]; `p^{11/12}` at one prime [F] |
| M10 Count | `ℕ`-counts with quadratic Tate limit | hyperelliptic curves [F]; over ℤ the sections count linearly [L*] |
| M11 Orbit at finite time | prime phases, returns, resonators | under `Θ≤b` heavy returns need `log t≥cy^{1−b}` [L*] |
| M12 Critical compactness | thresholds, pole channel, the critical half-line state | three-way classification; the state is unique, solves the weak equation and has a zero-free Laplace transform on `Re z>0` [L*] |
| M13 Topology of the prime complex | orientation cover | centred count `M(N)=Ω_±(√N)` [F] |
| M14 Infinite-rank elimination | towers, thick sets | attained top + thick count ⇔ RH [F] |
| M15 Prime-degree sampling | logarithmic windows | complete receiver [L*] |
| M16 Intersection on half-products | adelic carrier, Green kernels | glued diagonal refuted [KR]; critical adelic inverse unbounded [KR] |
| M17 Absolute geometry | square, contacts, paths, rings, tails | forced data; exact index for Dedekind zeta functions, one non-abelian Artin character, quotients and their powers [L*] |
| M18 FE rigidity | Hamburger, defects | `L¹`/`L²` defect forces the rational primes; every fake has a non-decaying defect; fakes with subpolynomial defect energy under `Θ<1` [L*] |
| M19 Exceptional-coordinate atoms | ZAL, B13, Landing, DH | RH = ZAL ∧ B13 ∧ Landing [L*]; all open for ζ |
| M20 Families and monodromy | covers, class characters | fixed-part laws [F] |
| M21 Index and limits | index law, unit gaps | index-one limits give RH; no approximant with a gap [F] |
| M22 Separation and dominance | ordinate injectivity, ultrametric Newton polygons | receiver for ξ [F]; proof for the Goss zeta function [L*] |
| M23 Hodge lattice at finite scale | step packets, neutral part, block matrices | RH ⇔ one negative square of the neutral part on every window; certified on ratio `≤103/50`, narrow windows, first blocks [L*] |
| M24 Constituents | bounded and Wiener classes | none with a zero [F] |
| M25 The ladder | mass, aperture, rung | sizes to rung `1−o(1)` [L*] |
| M26 Family continuation | two estimates, reciprocal kernels, reciprocity | `Re s>7/8` [X]; in Lean the frame, the budget, the coupled tower to `3/5`, the barrier `(4r−1)/(6r−1)` of every `6r`-periodic pairing, the conditional receiver at `7/8` [L*] |
| M27 Dressed positivity | lag aggregate at a level | level one ⇔ RH [F]; level one gives AAL and `Θ=½` [L*] |
| M28 Floor-free receivers | homogeneous, unit gap, certificate, amplification, symmetrization | each kind has a receiver and a kill [L*]/[F] |
| M29 Models of the count and of the Euler product | deletions, two-sided edits, signed grouped edits, signed weights | fakes at every count exponent above the pair; with subpolynomial FE defect under `Θ<1`; with bounded defect among signed weights [L*] |
| M30 Index in the aperture | Morse = Maslov index; polar Lagrangian | RH ⇔ no crossing; below the polar ground energy every crossing is charged [L*] |
| M31 Coherence of reciprocity families | modes, columns, root numbers, signed Gram, theta-square series | short columns incoherent, average row target-free; double pole of the theta-square series at `4/3` [L*] |
| M32 Galois theory of zeros | zero field, source field, prime trace field, reflection field | `K_even⊆ℝ` ⇔ `H=B` ⇔ RH; orbits lie in `{±δ}`; no automorphism besides conjugation is known [L*] |
| M33 Bound states and gluing | potentials, couplings, susceptibilities | gluing law (one bound state ⇔ `αβ≥1`); sink count; narrow windows [L*]; susceptibilities of actual windows open (B189) |
| Amplifiers | Diophantine repulsion, integrality, Turán, positive annihilators | amplify or reshape a certificate, produce none [KR] |

## 2. Shared obstacle blocks

### S1. Complete Weil family at the critical curve
Routes: HF, SRT, AIP, ACS (atomic), SC. Programmes: CACT, AHD, CSAR, ACPL, ADT, RAPT, AGZ (polar Lagrangian).

Established:
- `0<R_PD=R_PSD=R_polar=R_halfline≤W=R_prim=R_high=inf_A windowThreshold(A)`, each infinite iff RH [F]; three-way classification: RH, or `R_polar<W`, or `R_polar=W` finite with a polar-orthogonal critical state [L*] (`polarPaymentCriticalThreshold_windowThreshold_classification`, `criticalHalfLine_weakEquation_classification`).
- The critical half-line state at `W₀`: zero full energy; mixed energy zero against the whole energy domain; unique up to sign; `∫F(u)e^{zu}du≠0` on `Re z>0` (a Laplace zero `a+ib` with `a>0` lowers the energy by a paired reflection that leaves the prime, Gamma and pole terms unchanged); the reflected state is a logarithmic convolution of one `L²` half-line source; a charged state gives `R_polar<W₀` [L*] (log §1, §13).
- The Gamma and prime forms are quadratic polynomials along real variations of their actual domains, half-line states included [L*] (log §11).
- On the aperture side: no neutral null vector at the ground energy iff `μ(a)<μ₀(a)`; below `μ₀` the index is the number of charged crossings; unconditional for apertures `≤½(log 2+1/50)` and energies `<1/20` [L*] (log §14). On windows with `4J≤R` a ground vector of the block matrix is charged [L*].
- Complete tilted-spline matrix positive definite for every exponent below `1/8` eventually [L*] (`eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_one_eighth`).

| | Obstacle | Strength |
|---|---|---|
| A9, A13 | constants of the eighth-root horizon; near-gcd charges (unverified) | — |
| B6, B101 | full-space sign at every critical multiple; polar payment at every ratio | RH |
| B104 | whether the critical half-line state is charged (`∫F·polarSourceProfile≠0`); zeros of its Laplace transform on `Re z=0` | method |
| B123 | correlated arithmetic pairings dominating the depleted kernel | method |

### S2. Window tower, canonical flow, aperture path
Routes: RW, EWU, OWU, ACT, CHMD, TT (odd), SZ, RN, LI, HF, ACS, SRT. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, CHT, AIF, VHR, WVL, SA, ACCE, AGZ.

Established:
- RH ⇔ `W≥0` on every window [F] ⇔ feasible weights at every aperture [L*] (`not_riemannHypothesis_iff_empty_aperture`, `riemannHypothesis_iff_feasible_at_every_aperture`) ⇔ no eigenvalue crossing along the aperture [L*] (log §14).
- Index law: `negativeRank` at aperture `b` = sum of nullities below `b` = number of eigenvalues below the energy [L*]; nullities are not all even: a short aperture has a single simple null mode [L*] (`exists_single_simple_null_mode`).
- Verification: `∃C`, RH through `exp(exp(Ca))` ⇒ the sign on `[−a,a]`, `a≥1` [L*]; `C` is not explicit.
- Selectivity: for `2a<log 2` feasibility does not depend on the weights [L*] (`feasible_iff_of_lt_half_log_two`); the margin `1/5000` on windows with `50J≤53R` [L*].
- Certificates: every system feasible beyond some aperture has `|λ(n)−Λ(n)|≤ε` [L*] (`exists_aperture_forall_abs_weight_sub_le`).
- Confinement: positivity at aperture `a` confines every zero with `T₀(c)≤|γ|≤2πe^a` to depth `<exp(−c log³|γ|)` [L*].
- Objects of a failure: RH fails iff an odd bound state exists, iff a defective hard-edge block exists, iff `Re ξ′/ξ` is negative somewhere right of the line, iff a negative definite Markov plane exists [L*] (log §20).

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

Established: the minimal face in its forms (§0); floors at every length `(k+1)π/67` give AAL [L*] (`asymptoticAbscissaLaw_of_lengthDependent_floors`); one-sided floors on windows of one length have finite-stratum models [F]; counter-configurations at prescribed sublogarithmic windows [L*]; every interval `(x,x+x^θ]`, `θ=1−1/(16(14·10⁷+12))`, contains a prime of every reduced class [L*].

| | Obstacle | Strength |
|---|---|---|
| A58 | effective gap iteration (unverified) | — |
| B130 | the bound on any decisive sample; `Kp^σ`, `σ<½`, is a zero-free strip | RH (≥qRH at `p^σ`) |
| B144 | separation of the deep off-line ordinates | sub |

### S4. Continuation, index, constituents
Routes: ZCG, LA, PTR, HCF, PA, GTA, XN, WD, TH. Candidate: W1C. Programmes: NGF, FFP, ADO, AES, IRP, CTZ, GaloisTheoryOfZeros.

Established: RH ⇔ every zero of every `H_t`, `t>0`, is simple [L*]; non-real zeros are finite in number at every positive time and infinite at every negative time; under RH the zeros at positive time are real and simple [L*] (log §20); `N_d≤300√(d log d)` for `log d≥6.1·10⁶` [F]; Jensen discriminants are nonnegative unconditionally and the folded nonreal census exhausts the off-line divisor [L*] (log §4); the generic centred polynomial of degree `d` has the full symmetric group [L*] (`centeredGaloisEquiv`); no bounded Dirichlet or Wiener constituent with a zero [F]; the prime lag is positive definite ⇔ RH [F].

| | Obstacle | Strength |
|---|---|---|
| A19, A20 | heat horizon with an explicit height; Jensen rung past `d⁴≪T log T` (unverified) | — |
| B22–B25 | outer Jensen roots; `N_d` bounded; collisions at small time; frequency below one | RH / ≥qRH |
| B124 | finite initial depth budgets of the heat divisor | ≥qRH to RH |
| B146 | an independent family of bounded index converging to ξ | RH (producer) |
| B27, B47 | runs of simple critical zeros; multiplicity by a non-size input | sub |
| B190 | the orbit of a zero with irrational real part; an automorphism of the zero field besides conjugation | method |

### S5. Near-line geometry, long moments, census, cameras
Routes: WD, CTF, MC, TG. Programmes: CDG, APR, MZF, AIF, IGP, TransThresholdPairCorrelation, MatomakiRadziwill, LogarithmicChowla.

Established: RH ⇔ the Möbius-mollified second moment is subpolynomial; a cofinal bound with fixed `K` and unbounded `θ` suffices [F]; twisted moments below the square root and the positive critical proportion [L*]; positivity cost of a pair-correlation certificate `>13/10` [L*]; squared right-depth moment `o(V)` [KR]; adaptive clusters with complete exterior mass `≤¼`; at fixed centre and width the late-lag exterior mass is the boundary-depth mass; centred camera prime mean square `≤C·T·exp(−2b(y−c log T))` [L*] (log §11); short-interval mean squares of `λχ`, `χ≠1`, and the reduction of logarithmic correlations of `λ` to prime dilates with the prime kernel bounded off the major arcs [L*] (log §5).

| | Obstacle | Strength |
|---|---|---|
| A18 | twisted moments past the square root [C] | — |
| A147 | logarithmic two-point Chowla: for the principal character the low-frequency mean square `\|τ\|<(log X)^{19}` with reciprocal weights (twisted partial sums `o(N)` for `2\|τ\|≤√N` are written [S]), the assembly of the restricted ladder with Parseval, the transfer to `V(b/s,T)` [C] | — |
| B57 | depth density `o(T)` (first moment) | sub |
| B58–B61 | `D_win`; pointwise prime cost of the adaptive profile at its selected centres; Green moments at deep zeros; a detector past the last scale | sub |
| B62, B66 | cofinal long moment; near-unit holomorphic budgets | RH |
| B150 | a form factor bounded by `4` on `(1,10/9)` | sub |

### S6. Production, precision, the Mertens level
Routes: WL, MC, SQF, PBM, RB, JAS, CTF, FU, CFC, RP. Programmes: ASRP, APR, AGT, AKLT, AE, AAD, RAC, MMD, SPAL, HWV, RIAC, ALST.

Established: `c/(√K(1+log K))≤bestRate K≤exp(−(log K)^α)` [F]; a polynomial rate ⇔ a Mertens power saving [L*] (`exists_hasRate_rpow_iff_mertens`); centred cover count `M(N)=Ω_±(√N)` [F]; Type-II bounds are sign-blind [KR]; Stepanov at one prime `p^{11/12}` [F]; the twisted Chebyshev sums of ζ are `≤K/(log X)^4` for `(log X)^{19}≤|τ|≤X`, `log K≥(log X)^{0.92}` [L*] (`exists_zetaChebyshev_le`).

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

Established: RH ⇔ every compact pulse rings down at the quarter rate; pulse rate ⇔ horocycle rate [L*]; AAL ⇔ no Euler polynomial filter accelerates the horocycle rate [F]; the tower of height `N` is the quotient `Λ(s)/Λ(s+N)`, with a unit gap iff RH [L*] (`towerQuotient_unit_gap_iff`); the cusp spectrum has the Weyl order `cΛ≤N(Λ)≤CΛ` [L*] (`weyl_law_order`); no Maass cusp form with `0<λ<3/16` on any congruence subgroup [L*]; the hyperelliptic defect is an `ℕ`-count quadratic on rays [F]; on the cubic cover the theta-square series factors, with a double pole at `4/3`, and the rotated correlations read only the layers `m≥2` [L*] (log §6, §16).

| | Obstacle | Strength |
|---|---|---|
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | — |
| A54 | cusp expansion for Bianchi resolvents | — |
| A148 | the layers `m=0,1` of the theta-square series and the target component of a twisted column [C] | — |
| B68, B71 | independent reflection Krein positivity; universal decay and the horizon rates | RH |
| B87 | a count with Tate limit `Q`, defined without `Q` | RH |
| B147 | Shimura nonvanishing for one eigenform | indep. |
| B114, B117, B171 | partner involution; a regulator with a gap before the limit; a form of signature `(1,∞)` | producer |
| B178 | a relaxation rate beyond the tempered exponent from a principle of the horizon | producer |
| B188 | the Kuznetsov–Kloosterman mechanism of Selberg's `3/16` applied to the scattering resonances | producer |

### S8. The exceptional coordinate: two worlds and three atoms
Routes: BAG, ZCG, JAS (shell), SC (undamped), WL (thick runs), ACS (sampling), LA (finite support), RW (polar ground energy). Programmes: ZCG AbscissaLaws, ELT, EFT, IWT, IRW, IRP, APD, AAD, TAPO, FFA, SPAL, WZC.

Established:
- `Θ≤7/8` [X]; `Θ<1⇔Θ∞<1` [L*]; RH ⇔ ZAL ∧ B13 ∧ Landing [L*]/[F]; B13 ⇔ packet index `0` or `∞` [L*].
- World I receivers and instruments: in world I `ψ(x)−x=O(x^β)` is attained on every window; filters reduce the growing-order current to centred cofactors [F].
- Model theory over the rational primes (log §9, §18): every finite layer, an isolated pair above a half-scale tail, landing failure, sparse tails, removal of a finite layer, a non-real pair alone on top at every count exponent above the pair.
- Laws of the models: balance or real top at count exponents `≤½`; parity of orders above `2max(β,c₀,θ/3)`; `(1−θ)Re ρ≤2β(2−θ)`; the greedy pair twin has `β≥Re ρ/2` [L*].
- The FE axis (log §3, §12): every fake has a non-decaying defect; fake edits have defect energy `≥cT log T` with `c` depending on the least deleted prime; under `Θ<1` fake edits with defect energy `≤C_εT^{1+ε}` exist for `½<β₀<3/2−Θ`; among signed real weights a bounded defect has a fake [L*]. For unweighted countable systems a defect `O(|t|^{−½+ε})` forces the rational primes [card].
- The one-structure models: FE with Gamma factor, residue one and the count within one, with off-line zeros approaching the line and no landing [L*] (`exists_riemann_gamma_counting_model_without_landing`); the meromorphic tempered Euler one-off [doc].

| | Obstacle | Strength |
|---|---|---|
| A120 | a finite nonempty stratum with both structures: Selberg zeta functions of surfaces with a small eigenvalue [C] | — |
| A144 | tangent data under additive twists (unverified) | — |
| A153 | Lean statements for the card's Theorems II.1, II.3 and Corollary III.2; the Euler weights of II.2(b) are `hasProd_signedPoly` [S] | — |
| A157 | the Perron count of the signed grouped edit left of `½` (unverified) | — |
| A155 | the order law at every multiple: divisibility by `k` of the order of a zero of the edit exponential above `k` times the count exponent, `k≥3` (unverified) | — |
| B13, B138, B141 | finite stratum; landing; Deuring–Heilbronn for ζ | sub |
| B83, B170 | AAL; non-attainment for ζ | sub / AAL |
| B89, B112, B128 | bounded aligned return; FE into vertical transport; replication by another mechanism | sub |
| B145 | the prime-weighted centred type-II current at a growing isolated mode | AAL [D] |
| B110, B126, B127 | thick crude count; sampling set; lag recurrence | AAL |
| B157 | which structure of ζ that a Selberg-type zeta function lacks excludes a finite stratum | method |
| B183 | a fake with count exponent `β<½` and a non-real pair alone on top (must be balanced) | method |
| B191 | a fake with subpolynomial defect energy at `β₀≥3/2−Θ`; the order of the least defect energy between `T log T` and `T^{1+ε}` | method |
| — | ZAL | ≥qRH |

### S9. Prime orbit at finite time
Routes: BAG, TH, SRT. Candidate: S3. Programmes: PTT, TAPO, TTPO, CDGeo, ALST.

Established: near-total returns need `log t>(log y)^{3/2−ε}` [F]; under `Θ≤b`, `c·y^{1−b}≤log t` [L*] (`heavy_return_bound_of_halfPlane`), so `y^{1/8}` [X]; under `Θ<1` the return transfer ⇔ RH [F]; resonator means for `κ<2σ−1`; `T^c` separated returns, `c>(30/13)(1−σ)`, exclude a zero right of `σ` [F].

| | Obstacle | Strength |
|---|---|---|
| A24 | certified scans (unverified) | — |
| B46, B97, B137, B121 | proportional saving at length `(log X)^{2K}`; first return past VK; collective depth floor; freezing control | sub |
| B148 | the transfer of S3 | RH (the strip is [X]) |

### S10. The diagonal, counts, absolute geometry, finite scale
Routes: ACS, HF, HAT-C, PM (count), LI. Programmes: SOSZ, HAT, AGZ, HFP, AE, RIAC, HHAC, CTH, LST, KPA, RHTower/Artin.

Established:
- Forced data: `CombBezoutShift c ⇔ c≤0 ∧ RH`; `CombBezout ⇔ RH ∧ w=Λ`; a contact altered and paid at its price is RH at every parameter [L*] (log §8, §14).
- Index: exact count of right zeros for Dedekind zeta functions, the degree-two Artin character of `ℚ(∛2,ω)/ℚ` and `ζ_{ℚ(∛2)}`; a virtual configuration counts zeros and poles; `W_{ζ_L}−W_{ζ_K}` has no negative square ⇔ Dedekind's divisibility on the line; the neutral form of a number ring has the index of its zeta function plus one; `n` copies of a quotient have the index of the quotient [L*] (log §2, §8, §14). Hecke and class characters [F].
- Brauer induction for finite groups; Artin induction with rational coefficients [L*] (log §7). The reciprocity law for induced one-dimensional characters is not in the corpus.
- Finite scale: RH ⇔ one negative square of the neutral part on every window; certified ranges of §0; at a fixed ratio `Q` the block matrix has at most `(Q−1)⌈e^{E_Q}⌉` negative squares at every block size, at most `300000` at ratio four; RH ⇔ a positive mass floor on every ratio window; a margin above one scale transfers to every refinement [L*] (log §8).
- Bound states: gluing law; comparison with lowered potentials; index `≤1+#{blocks with potential <−λJ}` when all couplings are `≥λ`; narrow windows; charged one-sign ground vectors [L*] (log §2).
- Power tails and Li coefficients: §0. The contacts of a number ring are its point counts over the finite fields [L*] (`idealContact_prime_pow_eq_natCard_ringHom`). The sections of the first `N` graphs in aligned boxes number the volume over `N!` [L*] (`card_sections_alignedBox`).

| | Obstacle | Strength |
|---|---|---|
| A28, A41, A48 | reciprocal-quadric traces; count law for plane quartics [C]; Hasse–Weil tests | — |
| A146 | the sign of `𝔚_4` and `𝔚_7` at every block size: certified margins up to the transfer threshold, or an explicit verification rate (A142) (unverified) | — |
| A154 | the reciprocity law for monomial characters, giving the index of every Artin character [C] | — |
| A156 | the susceptibilities of the certified windows; the gluing criterion tested inside the certified range (unverified) | — |
| A141 | the half-plane `[X]` for fields containing `ζ₃` and every ray class character (unverified) | — |
| B87, B88 | a count on the rays defined without `Q`; the sign of the comb finite part | RH |
| B149, B169 | Bézout from a property of the object; a doubling with a canonical height | RH (producer) |
| B152 | one negative square of the neutral part at every ratio and block size | RH |
| B189 | the gluing law on actual windows: susceptibility product `≥1` for adjacent windows, first at ratio four | method; sub at each ratio |

### S11. Families, rigidity, exactness
Routes: ACS (tensor), ECP, HF, SC, BAG. Programmes: AWT, AK, ALST, SignFreePurityMechanisms, EFT, SEL.

Established: fixed-part laws [F]; FE rigidity and the FE axis (S8); positive continuous prime measures keep every zero with `L¹∩L²` defects [doc]; the Goss Riemann hypothesis [L*].

| | Obstacle | Strength |
|---|---|---|
| B86 | positivity of the endpoint character at unbounded rank | RH |
| B80 | FE twins with off-line zeros in the full class | sub |

### S12. The scale, the level, the signal, the probe
Routes: RW, HF, ACS, SRT (rungs); JAS, MC, WL, S3 (legs). Programmes: SA, FCT, MMD, CRF, STCC, RHTower `QuasiRH*`.

Established:
- Sizes and the ladder: the trivial aperture `log log q+o(1)`; exceptional heights on a rung; three rungs under a half-plane; level one gives AAL and `Θ=½` [L*] (log §8, §19).
- Frame: `Θ≤σ₀` from two estimates with reciprocal kernels for every Hecke character [L*] (`zetaZeroAbscissa_le_of_two_estimates`, `heckeHalfPlane_of_family_corrected_signal`); the correction factorizes through a Grössencharacter `L`-function at `6s−3` [L*] (`probeCorrection_eq_grossen_mul_residual`).
- Coupled tower: zero transfer `ρ↦6ρ−3`; reach `max(σ₀,3/5)`; `7/12` under sextic GRH; the barrier of every `6r`-periodic Gauss pairing [L*] (log §16).
- Budget: the binding bin `δ=79/204`; sieve threshold; corners `8/9` and `49/54` of the designs `(2,6)` and `(4,3)` [L*] (log §16); `25/28` for `(3,4)` [F].
- Coherence: root numbers `G(u)γ₂(u)²`, incoherent short columns, target-free average row, completed pair Gram [L*] (log §16); the theta-square series and its poles [L*] (log §6).
- Port of `[X]` [L*]/[F]: `beta ≤ 7/8` from a uniform continuation margin; centred exceptional rows; source-shell energies; the long radial energy bounded by shorter retained energies, which are hypotheses.

| | Obstacle | Strength |
|---|---|---|
| A118 | the theorem `[X]` in the native graph: the retained-energy induction, the character-uniform signed and ramified detector saving, the uniform continuation margin | — |
| A138 | the corollaries of `Θ≤7/8` as unconditional statements | — |
| A149 | the function-field calibration of the floor bin over `𝔽_q[T]`, `q≡1 mod 6` (unverified) | — |
| B174 | the row count of the binding bin `δ=79/204` | a half-plane in `[13/15,7/8)` |
| B185 | the long columns: a power saving in the first moment of `G(u)γ₂(u)²` against a dual column, uniformly in the column | a half-plane in `(2/3,13/15)` |
| B187 | a Möbius-signed pairing outside the `6r`-periodic Gauss pairings whose coupled fixed point is below `3/5`, or whose uncoupled boundary is the line | producer |
| B180 | the reflection of the completed theta row without Eisenstein series | method |
| B160, B161 | `JasDressedPSD 1`; a signal bound below `7/8` | RH; a half-plane below `7/8` |
| B159 | a rung `κ≥4/3` with a saving that fails for the Liouville twist | a half-plane below `7/8` |
| B156 | arithmetic cluster exclusion on a rung | method |

### S13. Floor-free receivers and their kills
Routes: every route (as a filter). Programmes: FFA, WZC.

Established: a Green–Weil energy floor gives RH; the tower quotient has a unit gap iff RH; normalizations of translates tend to zero; linear statistics are not monotone under projection [L*] (log §19); certificates converge to `Λ` [L*]; floor of prime edits with a count rate `≥13/30` [L*]; floor `½` of count-invariant mechanisms, amplification as a sup bound, positivity on the line of the pole only [F].

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
- **Established:** RH ⇔ the prime lag is positive definite; RH ⇔ attained top ∧ thick `O(√X)` deviation; endpoint energy bounded ⇔ RH [F].
- **(a)** A30. **(b)** B49 (endpoint energy), B48 (deciding input), B110 (attained top with the thick estimate), B1.

### RW — Restricted Weil ground energy
- **Path:** `μ(a)≥0` at every aperture → RH; equivalently feasible weights at every aperture; equivalently no crossing along the aperture.
- **Established:** feasible weights at every aperture ⇔ RH; index law and its Lagrangian form; far end = right zeros; feasible systems converge to `Λ`; verification rate; charged crossings below the polar ground energy [L*] (S2).
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
- **Path:** prime−Gamma response sign → RH. **Established:** calibrated Hausdorff-row sign above explicit cutoffs; the other entries ⇔ RH [F].
- **(a)** A1. **(b)** signs below the explicit shift uniformly in the degree (B31).

### MC — Möbius cancellation
- **Path:** half-power Möbius cancellation → RH.
- **Established:** damped critical energy, fixed-height prefixes, mollifier zero-freeness each characterize RH [F]; the coupled tower and its barrier at every period [L*]; short-interval mean squares of `λχ` for `χ≠1`; for `χ=1` the top-scale blocks above polylogarithmic frequencies, the ladder master inequality on a frequency set, and twisted partial sums `o(N)` for `2|τ|≤√N` [S]; logarithmic correlations of `λ` reduce to prime dilates with a bounded prime kernel off the major arcs [L*] (log §5, §17).
- **(a)** A33, A46, A118, A147.
- **(b)** B48, B50, B15, B106; B161; B174, B185, B187. RH needs a source other than the cubic probe [F]; [L*] (log §16).

### SQF — Weighted squarefree count
- **Path:** a one-sided `O(t^{−¼−ε})` bound of `Σμ(n)²e^{−nt}−6/(π²t)` → RH. **Established:** either one-sided law ⇔ RH; `Ω_±(t^{−1/4})` [F].
- **(a)** none. **(b)** the quarter-power bound for one sign (B48 family).

### TT — Theta tail / Wold
- **Path:** bounded weighted endpoint energy at each `0<t<½` → RH. **Established:** RH ⇔ a bound `C_t` for every `t`; uniform bound on a shrinking band [F].
- **(a)** none. **(b)** `C_t` at every fixed `t` (B34).

### LA — Jensen line anchor
- **Path:** Jensen polynomials real-rooted, or sublinear root height → RH.
- **Established:** RH ⇔ infinitely many Jensen degrees real-rooted; `N_d≤300√(d log d)` [F]; nonnegative discriminants and quartet exhaustion [L*] (log §4); the zero field and its criteria (S4, §0).
- **(a)** A20, A1. **(b)** B22; B23 then B13, B138; B124; B190.

### ZCG — Zero-configuration geometry / heat descent / abscissa laws
- **Path:** no positive-time collision → RH; or a decisive prime-window floor; or ZAL ∧ B13 ∧ Landing.
- **Established:** collision exclusion ⇔ RH [L*]; blocks S3, S4, S8, S13; adaptive cameras with complete exterior mass [L*]; the model theory of world I over the rational primes and the FE axis [L*] (log §3, §9, §12, §18).
- **(a)** A19, A120, A144, A153, A155, A157.
- **(b)** B24, B25, B47, B27, B124; B130; B145, B170; B13, B138, B141; B59; B183, B191.

### TG — Topological sub-unit gate
- **Path:** cubic defect trace norm `<1` → integer zero count vanishes → RH. **Established:** exact integer trace; endpoint and Gaussian central-gap receivers [F].
- **(a)** none. **(b)** trace norm below one on every formation rectangle (B38).

### HF — Hodge / complete cells
- **Path:** complete arithmetic form `≥0` → Hodge index → RH.
- **Established:** S1, S10; RH ⇔ one negative square of the neutral part on every window; exact index for number rings, one non-abelian Artin character and quotients; the critical half-line state with its uniqueness and its zero-free Laplace transform [L*].
- **(a)** A9, A13, A141, A146, A154, A156.
- **(b)** B6, B101, B104, B123, B8, B41, B10, B87, B88, B149, B152, B189.

### HAT-C — Arithmetic-clock Green energy
- **Path:** one clock, or one fixed scattering height → energy floor → `W≥0` on packets ⇔ RH.
- **Established:** a Green–Weil energy floor gives RH [L*]; the tower is the completed-zeta quotient [L*]; at every fixed height RH ⇔ the corrected-energy floor [F].
- **(a)** none. **(b)** the floor at one fixed height on all apertures (B1).

### CHMD — Causal hyperbolic–modular duality
- **Path:** bounded prime wave, or the odd half-threshold bound → RH. **Established:** wave and Doob receivers; RH fails iff an odd bound state exists [L*]; normalized decay [F].
- **(a)** none. **(b)** either side of the unnormalized wave bound; the complete odd sign (B35, B4).

### TH — Theta moment positivity
- **Path:** signed center-mixed jets → all-rank Hankel positivity → RH.
- **Established:** ranks `≤14`; rank `N` from verified height `41+6(N+2)log(N+2)` [F]; the critical partial sum of half the height is `ζ(½+ib)` up to `O(|b|^{−½})` [doc] (log §11).
- **(a)** A4, A5, A24, A42. **(b)** B102, B20, B21.

### RN — Theta renewal
- **Path:** exclusion of joint nodes, or the theta-ground energy comparison → RH. **Established:** two-ended formula recovers Ξ with multiplicities [F].
- **(a)** none. **(b)** B36.

### WD — Ward / collision / long moments
- **Path:** cofinal long-mollifier moments, or collision bounds → RH.
- **Established:** RH ⇔ subpolynomial mollified moment; cofinal bound with fixed `K`, unbounded `θ` suffices [F]; twisted moments for `θ<½` and the positive proportion [L*]; dyadic boundedness at `θ>1` confines depth to `<1/(2θ)+ε` [L*] (`cancellation_and_depth_ladder`).
- **(a)** A18, A147. **(b)** B62, B57–B61, B63.

### LI — Paired Li / Cayley ladders
- **Path:** subexponential lower bound of the clock response, or the Cayley–Li sign → RH.
- **Established:** RH ⇔ ladder sign on primitive vectors; `λ_n≥0` for `n≤314` [F]; the Laguerre tails of the comb tend to the paired Li coefficients [L*] (`tendsto_combForm_laguerreTail_div`); without RH negative and positive paired Li indices recur in windows of bounded length [L*] (`exists_window_re_xiLiPaired_neg_and_pos_of_not_riemannHypothesis`).
- **(a)** A1. **(b)** B43.

### SZ — Suzuki screw
- **Path:** rectangular Ward defect bounded below → RH. **Established:** completed Abel source bounded ⇔ RH; VK saving [F].
- **(a)** none. **(b)** B37, B1.

### PM — Physical model
- **Path:** scattering source → reflection Krein sign, ringdown rate, cavity rate or a count → RH.
- **Established:** S7.
- **(a)** A26, A54, A148. **(b)** B68, B71, B87; B147; B114, B117, B171; B178, B188.

### PTR — Cosine source
- **Path:** no exceptional point of the cosine producers on the open depth band → RH.
- **Established:** RH ⇔ strict Laguerre sign at every `0<h<½`; ZAL gives finite nonreal defects; no bounded or Wiener constituent with a zero [F].
- **(a)** none. **(b)** B29, B69.

### JAS — Joint ancestry
- **Path:** level-one dressed positivity on large primes; or subpower moving-window control → RH.
- **Established:** RH ⇔ `JasDressedPSD 1` [F]; level one gives AAL and `Θ=½` [L*] (`levelOne_abscissa_laws`); a signal bound `O(Z^b)` gives the level `b+½+ε`; with `[X]` the level `11/8+ε` [F]; the completed cubic bootstrap stops at `max(σ₀,3/5)` [L*].
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
- **Established:** strong recurrence ⇔ RH [F]; RH ⇔ relative compactness of the orbit, and of its bubbles [L*] (log §11); normalizations of translates at a finite layer tend to zero [L*].
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
- **Established:** S10; §0 (finite-scale index, certified ranges, gluing law, critical comb, Li tails).
- **(a)** A28, A41, A48, A141, A146, A154, A156.
- **(b)** B152, B189, B149, B169, B88, B87; B130; B28; B13.

### ECP — Endpoint character positivity
- **Path:** endpoint jets → class functions → PSD character Grams at every rank ⇔ RH. **Established:** projections nonnegative; Toeplitz minors through order 200 [F].
- **(a)** none. **(b)** B86.

## 4. Candidates

Each needs its source-to-receiver step (B81). Dormant pending a source mechanism: SEC, CDC/BSH, APF, EWJ, RFHM, WBF.

| Candidate | Established | (a) | (b) |
|---|---|---|---|
| S3 | a strip excludes heavy identity returns; under `Θ<1` the transfer ⇔ RH [F] | none | B148: with `[X]` the transfer is RH |
| SEC | Fock boundedness at every strip parameter ⇔ `Re s=½` [F] | none | a ζ-selective bound from the Sonin source |
| CDC/BSH | marked prices agree iff `Re s=½` [F] | none | descent on actual zero fibres |
| APF | prime/grade trace reconstruction [F] | none | full-divisor exhaustion |
| EGC | zero-pair contour; explicit count error [F] | none | height-fibre isolation |
| EWJ | all-depth reporter [F] | none | faithful endpoint admission |
| FEL | KL accounting [F] | none | a predeclared history forcing the BSY sign |
| IRK | finite idempotent traces [F] | none | projective lift identifying trace with Chern charge |
| MSC | `L²` discrepancy; conormal transport [F] | none | Sonin/Weil sign landing |
| RFHM | support source; creation [F] | none | an RH-sufficient orientation law |
| W1C | index-one approximants or an index-one realization give RH [F] | none | B146, B171 |
| WBF | Gram recovers magnitudes and phase class [F] | none | arithmetic stream and Ξ landing |

## 5. Supporting programmes

| Programme | Established | (a) | (b) |
|---|---|---|---|
| AGZ | forced data; exact index for number rings, one Artin character, virtual configurations, quotients and powers; contacts = point counts; finite-scale index law; certified ratio `≤103/50`, narrow windows, first blocks, thin packets; uniform index bound at each ratio; index law in the aperture; charged crossings; gluing law, lowered potentials, sink count, charged ground vectors; power and critical combs; Li coefficients as Laguerre tails [L*] | A146, A154, A156 | B104, B149, B169, B88, B87, B152, B189 |
| AHD / CACT | thresholds; classification; the critical half-line state (weak equation, uniqueness, zero-free Laplace transform, causal coordinates); positivity below the eighth root [L*] | A9, A13 | B104, B123 |
| HFP | mass floors on ratio windows [L*] | — | B152 |
| WZC | two-sided edits: every finite layer, pair alone, tails, landing failure, sparse configurations, layer removal; balance, parity, count floor; floor `≥13/30`; twin defects; signed grouped edits; the frontier dichotomy [L*] | A153, A155, A157 | B183, B191 |
| EFT / APD / SPAL | FE rigidity with `L¹`/`L²` defects; Abel floors; `T log T` defect energy of fake edits; signed fakes with bounded defect; positive density of integer-norm fakes [L*]; Euler weights of the signed fake [S] | A153 | B191 |
| CRF | short columns, short Gram, average row, completed pair Gram, root numbers [L*] | A149 | B185, B187 |
| STCC | theta-square series: factorization over cube frequencies, double pole at `4/3`, rotated correlation, squarefree combination, three-divisible layer [L*] | A148 | B180 |
| FCT | frame, coupled tower to `3/5`, zero transfer, barrier of `6r`-periodic pairings, budget, sign law [L*] | A118, A138 | B161, B174, B187 |
| MMD | cube identity [F]; conditional receiver at `7/8`; centred exceptional rows; source shells; radial comparison [L*] | A33, A118 | — |
| GaloisTheoryOfZeros | zero field over the source field; prime trace and reflection fields; Kummer relations of the widths; rational orbits; centralizer of prime translations; Jensen equations; transcendence limits [L*] | — | B190; a restriction forcing `H=B` |
| RHTower/Artin | Brauer induction; Artin induction [L*] | A154 | — |
| FFA | floors; receivers and kills of the off-scale kinds [L*]/[F] | A144 | B170–B173 |
| SA | trivial aperture; ladder; exceptional heights [L*] | A117 | B159, B156 |
| ELT | atoms; filters; growing-order reduction [F] | — | B141, B145, B138, B13 |
| CTZ, IRP | no bounded or Wiener constituent; index semicontinuity [F] | — | B146 |
| MZF / CDG | twisted moments; positive proportion; centred cameras; boundary exterior mass [L*] | A18 | B62, B57, B59 |
| MatomakiRadziwill, LogarithmicChowla, PrimeExponentialSums | short-interval mean squares of `λχ`, `χ≠1`; Route T for ζ above polylogarithmic frequencies; ladder on a frequency set; prime-shift reduction; prime kernel off major arcs [L*]; twisted Liouville partial sums at low frequencies [S] | A147 | — |
| ShortIntervalPrimesInProgressions | primes in `(x,x+x^θ]` in every class [L*] | — | — |
| SignFreePurityMechanisms | Goss Riemann hypothesis [L*] | — | a norm for ξ |
| HAT | clock; tower; unbounded critical inverse [F]/[KR] | A54 | B88, B117 |
| BHR / AHMH / ASH / CTH | ringdown ⇔ strip; pulse rate = horocycle rate; Weyl order; `3/16` [L*]; filters; hyperelliptic count [F] | A26, A41 | B68, B71, B87, B147, B178, B188 |
| TTPO / PTT / TAPO / CDGeo | returns; resonator means [F] | A24 | B46, B97, B137 |
| ALST / AAD / RAC / APR | Stepanov degrees; producer rates; cut kernel; parity blindness [F]/[KR] | A30 | B48, B55, B67 |
| VHR / TCS | height 67 [F]; double-exponential window height [L*] | A1–A5, A142 | — |
| Census (IGP, TTPC) | `0.67250071`; positivity cost [L*] | — | B150, B57 |

## 6. Decisive wall per route

| Wall | Routes |
|---|---|
| The minimal face `P(p)≤A(p)+K` on logarithmic windows off power-thin exceptions | ACS, SRT, WL, HF, ZCG, HAT-C, PM (count) |
| Σ: the sign on every window = no crossing along the aperture = one bound state of every window = feasible weights at every aperture; in gluing form, a susceptibility product `≥1` at every ratio | RW, EWU, OWU, ACT, CHMD, SZ, RN, AIP, SC, LI, TT (odd), HF, HAT-C, ACS |
| Σ: the critical half-line state: its existence is the failure of RH; its charge is B104 | HF, SRT, AIP, SC |
| Σ: continuation at small time; theta heads | ZCG (heat), PTR, LA, GTA, XN, HCF, PA, TH |
| Π: square-root precision; long moments past the height | WL, MC, SQF, PBM, RB, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| One scale, one producer: `[X]` at `7/8`; the cubic probe's estimates reach `2/3` with square-root cancellation; every `6r`-periodic Gauss pairing has frame `≥3/5`; no other source | JAS; MC (signal); S3; ACS (tails); every graded receiver |
| Γ: reflection and count | PM, ECP |
| The exceptional coordinate: world I needs the Euler product with the reflection up to a decaying error, or a count below half the real part of the layer; world II is the scale | BAG, ZCG, JAS shell, SC undamped, WL thick runs, LA finite support |
| The dark range: prime sums shorter than the Vinogradov length; polynomials longer than the height; the low frequencies of the principal character | every route at all heights; BAG; WD; MC |
| Missing source landing | the twelve candidates |
