# Route obstacles — status quo

Scope: the 38 live route formulations, the 12 route candidates and the supporting programmes. For each route: the path, what is established, the obstacles that are **(a) just work**, and the obstacles that are **(b) open mathematics nobody has a solution to**.

**Corpus checkpoint:** `fdc9cfc40f` (2026-11-13), working-tree sources included. Fact log: `logs/review-1311-status-quo-facts.md` (cited as "log §n"). Companions: [obstacles-summary.md](obstacles-summary.md) (A/B lists, ideation, the one question), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ), [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem).

**Live** means source observable, proved RH-sufficient receiver and explicit open estimate. **Candidate** means the source-to-receiver step is missing. HJ is PA; the BSY criterion of FEL belongs to CTF; PCS, DR, PW-B are retired labels.

**Evidence.**
- `[L*]` Lean statement read at its declaration for this report and recorded in the fact log with file and line.
- `[doc]` content of a module docstring whose theorem names were read but not every statement.
- `[F]` stated by the [frontier map](../rh-current-frontier-map.md) at the checkpoint; `[KR]` stated by the [scoped-obstruction ledger](../rh-killed-routes.md). `[S]` a module the frontier map grades unfinished or unintegrated.
- `[D]` deduction made here from `[L*]` statements; not a Lean theorem. `[C]` classical mathematics quoted from memory, not in the corpus. `[A]` assessment.
- `[X]` the half-plane `7/8`, taken as proved: every Dirichlet `L`-function, ζ included, and every Hecke `L`-function of the family over `ℚ(√−3)` is zero-free in `Re s>7/8`; so `Θ≤7/8`. It is cached in the repository as an external theorem (OpenAI, 30 September 2026). In the Lean source it is stated without hypotheses: `riemannZeta_ne_zero_of_seven_eighths_lt_re`, `DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`, `riemannZeta_zero_mem_quasiRH_strip`, `ProbeFinalAssemblyUnconditional.hecke_nonzero` (`MetaplecticMobiusDescent/WeightedCubicResidualFourierTests.lean`; statements and final assembly read, log §4.14). The frontier map grades this source `[S]`: an unconditional statement in source, not a verified theorem; validating the complete producer and dependency chain is just work (A118). Consequences of `[X]` on the receivers of the scale are deductions `[D]`: no receiver is stated in Lean with the half-plane inserted (A138). **Natively** refers to the Lean graph.

**Strength.** RH; ≥qRH (implies a zero-free half-plane, Lindelöf or ZAL; open where it gives a half-plane below `7/8`); AAL; sub (implies neither a half-plane nor AAL); method; producer; indep.

**Labels.** `A*` just-work items and `B*` open problems are listed in [obstacles-summary.md](obstacles-summary.md) §2.1–2.2. `(unverified)` marks A items whose difficulty is not established. Σ, Π, Γ refer to [walls-ledger.md](walls-ledger.md).

**Notation.** `Θ=sup Re ρ`; `Θ∞=inf{σ≥½: finitely many zeros have Re ρ>σ}`; `w=Θ−½` the zero width. **ZAL** `Θ∞=½`; **AAL** `Θ=Θ∞`; **B13** finitely many off-line zeros ⇒ none; **Landing** ZAL ⇒ finitely many off-line zeros; **World I** ¬AAL (a finite isolated top layer); **World II** AAL ∧ ¬ZAL (a tail). `2Re S(log p)` is the prime trace; a **logarithmic window** at `T` is `{p: |log p−T|≤32 log(T+2)}`. The **restricted Weil form** at aperture `a` acts on tests supported in `[−a,a]`; its **index** and **nullity** at an energy; the two **charges** of a vector are its coefficients at the two poles. A **step packet** is constant on the blocks `(a,a+1]`. The **block matrix** of a window `(R,R+J]` at modulus `Q` is the Weil form on step packets; it is the product of the two charges plus the **neutral part** `neutralWindow Q R J`, and the neutral part is a potential plus the Dirichlet form of a weighted graph on the blocks. The weights of that graph are the **jets** (archimedean) and the **contacts**: block `b` meets block `⌊b/k⌋` with weight `Λ(k)/k`, `2≤k≤Q` (`floorContact`). A **bound state** of a window is a negative square of its neutral part. The **ratio** of a window is `(R+J)/R`; the **block size** is `R`. A **contact weight** `ω(k)` multiplies the contact of `k`; the true weights are `ω≡1`; the **Liouville twist** multiplies the contact of `p^j` by `(−1)^j`. For a symmetric matrix `A` nonnegative on the kernel of a charge vector `u`, with `Aa=u`, the **susceptibility** is `u·a`. The **half-constant plane** of a window of ratio four is spanned by the packets constant on `(R,2R]` and on `(2R,4R]`. The **critical half-line state** at a finite critical ratio `W₀=inf_A windowThreshold(A)` is a unit vector supported on `u<0` with nonpositive truncated Weil form at every cutoff. The **power tail** at `0<a≤½` is the comb form of the power divisor; `a=½` is the **critical comb**. A **system** is a weight system with a mass; the **trivial aperture** is `log log(mass)+o(1)`. The **signal** of a kernel `G` is `(1/2π)∫G(2+it)Z^{2+it}dt`. The **probe** is the cubic-theta sum of `[X]` over `ℚ(ζ₃)`; its **twist order** is `n=6`. A **two-sided edit** is the system of the rational primes with some primes deleted and some doubled; it is a **fake** at `β` if its count is `Ax+O(x^β)` and its zeta function continues to `Re s>½` with a zero there that ζ lacks. The **FE defect** `g` of a system is its critical-line functional-equation defect in the Hamburger strip class; ζ has `g=0`. The **heat family** is `H_τ(z)=∫Φ(x)e^{τx²}e^{izx}dx`, `H_0=Ξ`; a **forward time** has `Re τ>0`; a **branch time** is a `τ` at which `H_τ` has a multiple zero; the **heat cover** is the zero set `{(τ,z): H_τ(z)=0}` over the time plane; the **forward monodromy group** at `τ` consists of the permutations of the zeros of `H_τ` obtained by transport along loops of forward times avoiding the branch times.

## 0. The picture

| Fact | Evidence | Consequence |
|---|---|---|
| RH ⇔ `2Re S(log p)≥−K` at the primes of arbitrarily late logarithmic windows, outside `Ce^{δT}` primes per window; ⇔ the upper side alone; ⇔ counts on surviving prime rays; ⇔ copositivity of the prime planes; `Θ<1` ⇔ a power floor. For two fixed primes `p≠q` and any `r>0`: RH ⇔ the trace is bounded below at the lags `k log p+l log q` within `r√T` of arbitrarily late `T` | [L*] (log §4.8, §4.9, §4.10, §4.12) | one inequality per prime on sparse windows; two primes suffice |
| Prescribed sublogarithmic windows do not bound the class; a density-matched configuration survives on the minimal face | [L*] (log §4.10) | no window below the logarithmic radius decides |
| RH ⇔ on every window `(R,R+J]`, `R≤J`, `R+J≤QR`, disjointly supported nonnegative packets `x,y` with `N(x,x)<0` satisfy `N(x,x)N(y,y)≤N(x,y)²` ⇔ every eigenvector of the neutral part with negative eigenvalue has one sign. The supremum of the index of the neutral part is one plus the number of zeros right of the line. The off-diagonal entries of the neutral part are negative | [L*] (`riemannHypothesis_iff_forall_wells_bound`, `riemannHypothesis_iff_forall_bound_state_one_sign`; log §4.1, §4.7) | RH is a Hodge index inequality between positive packets without common blocks: a binding inequality |
| Certified: exactly one bound state for `R≤J`, `50J≤53R` at every block size; none on narrow windows `16J≤R`, where the neutral part is positive definite and the potential exceeds one; margins `1/20` on the first step packets of ratio four; at most `300000` negative squares of the block matrix at ratio four | [L*] (log §4.7, §4.9, §4.10) | certified range: ratio `≤103/50`, narrow windows, first blocks |
| Gluing. Two matrices, each nonnegative on the kernel of its charge vector, coupled through the product of the charges, hold one bound state iff the product of the susceptibilities is `≥1`. For the halves `(R,2R]`, `(2R,4R]` of a window of ratio four, charges below the couplings with nonnegative lowered halves and susceptibility product `≥1` exist iff `R=1`; for `H≥64` every charge pair leaves `≥2` negative squares in the lowered model; every rank-`r` model of the coupling with `600(r+1)≤H` has lowered index `≥2`; at `R=2` rank two glues with zero excess | [L*] (`hermNegIndex_glued_eq_one`, `halves_of_ratio_four_glue_iff_eq_one`, `two_le_hermNegIndex_lowered_model_of_rank`; log §4.1, §4.9) | the binding between the two halves of a window has rank proportional to the block size; no fixed number of charges carries the induction |
| Contacts. With the contact of 2 weighted in `[−4,0]` every window with `J≥2R` has `≥2` bound states; with the contacts of 2 and 3 weighted in `[−5/2,19/40]` every window with `J≥3R` has `≥2`; the Liouville twist gives `≥2` for `J≥2R`. On the half-constant plane at ratio four the neutral part is `−(Ds²+2(J+K_ω)st+2Dt²)` with `K_ω=ω(2)log 2+ω(3)(log 3)/3`; the true weights give a positive direction | [L*] (log §4.1, §4.10) | the true weights of the contacts of 2 and 3 are what holds a window of ratio three or four together |
| Below ratio two the contacts vanish; the atomic intersection form of ζ is hyperbolic at small widths for every completely multiplicative sign twin | [L*] (`contactW_eq_zero_of_window`, `weilQuad_eq_arch_of_primeFree`); [doc] (log §4.11) | no unconditional sign theorem of the corpus uses a prime contact [D] |
| The index of the restricted Weil form at an aperture is the sum of the nullities below it and the number of eigenvalue crossings; below the polar ground energy every crossing is charged; on windows with `4J≤R` a ground vector of the block matrix has one sign and both charges nonzero of one sign | [L*] (log §4.10) | the Morse index of the sign problem is a Maslov index |
| RH, or a finite critical ratio with a critical half-line state. At every confinement ratio the unit-mass floor is attained, the minimizer is unique up to sign and its Laplace transform has no zero on `Re z>0`; the floor is strictly concave in the inverse ratio. At the critical ratio the state has no Laplace zero on `Re z≥0`, its multiplier is outer, its causal translates are dense, it has mass on every terminal interval; the floor has derivative `−a(W₀)∫F²e^{−8u}/W₀`. Strong confinement: `\|λ−a−log a\|≤K` | [L*] (log §4.2) | a failure of RH has one canonical extremal function; every property proved for it holds on both sides of the charge question |
| The critical comb has growth exponent the zero width and never converges; RH ⇔ subpolynomial growth ⇔ absolute logarithmic Abel integrability at every damping; the Laguerre tails of the comb tend to the paired Li coefficients | [L*] (log §4.10) | the width and the Li coefficients are read on one explicit sequence |
| `Θ≤7/8`; `Θ<1⇔Θ∞<1`; RH ⇔ ZAL ∧ B13 ∧ Landing; B13 ⇔ the packet index is `0` or `∞`; AAL ⇔ at most one or infinitely many zeros right of every line | [X]; [L*] (log §4.10) | a failure of RH is world I or world II with top `≤7/8` |
| Two-sided edits of the rational primes with a count rate realize: a non-real pair alone on top; every finite layer; sparse configurations; zeros on a vertical line; zeros rising to a line; zeros symmetric in a strip; a finite layer of ζ edited away | [L*] (log §4.10, §4.12) | Euler product over the rational primes, integer norms and a count rate constrain no finite layer |
| A fake at `β≤½` is balanced or has a real zero on top; even order above twice the count exponent; `(1−θ)Re ρ≤2β(2−θ)`; floor of prime edits `≥13/30` | [L*] (log §4.8, §4.10) | the count sees a fake zero only below half its real part |
| FE rigidity. A countable Beurling system with unit multiplicities, `Σnorm^{−3/2}<∞`, in the Hamburger strip class, whose defect is `O((1+\|t\|)^{−a})` for some `a>0`, is the rational primes: same counting measure, same zeta function, a norm-preserving bijection of labels. Positive real weights: for every `Φ→∞` a system with prescribed off-line zeros `1−μ±iγ`, count `Ax+O(x^{4/5})` and defect `≤Φ(\|t\|)`. Real weights on the integers: a fake has an Abel floor and no decaying defect; a signed fake on the powers of 2 has bounded defect. A fake two-sided edit has defect energy `≥(A²/(256πp₀))T log T` | [L*] (`beurlingSystem_rigidity_of_decaying_defect`, `exists_positiveWeighted_beurling_slow_defect`, `fake_abelMass_floor`, `signedPoly_fake`; log §4.3) | among unit multiplicities any decay selects ζ; among positive weights no growth bound short of boundedness does |
| `Θ=1` with AAL, or `Θ<1` and for every `½<β₀<3/2−Θ` a fake edit with the pair `β₀±iγ₀` and mean-square defect `≤C_εT^ε` | [L*] (`frontier_dichotomy`; log §4.10) | the reflection decides only up to a decaying error |
| The cubic probe is a coupled tower: a zero `ρ` forces a zero of a sextic Grössencharacter `L`-function at `6ρ−3`; with all estimates `Θ≤max(σ₀,3/5)`; `7/12` under sextic GRH; every `6r`-periodic Gauss pairing has coupled fixed point `(4r−1)/(6r−1)≥3/5`, with equality iff `r=1`; square-root cancellation across the rows of the floor bin gives `2/3` | [L*] (log §4.6, §4.8, §4.10); [D] | the one producer stops above `½` at every period |
| The centred zero field is algebraic and normal over the fibre source field; `K_even⊆ℝ` ⇔ RH ⇔ the reflection field equals the prime trace field. The degree-`2n` centred Jensen equation has the full signed-permutation group over its coefficient field, or a nonzero rational relation holds among its normalized moments. Every ordering of the squared-width field induces complex conjugation iff every squared width is a sum of squares | [L*] (log §4.4, §4.10) | RH is the triviality of a group of sign families |
| Heat cover. RH ⇔ no branch time is real and positive. Every zero of the centre value `H_τ(0)` has `Re τ>0`; the central branch times are infinitely many and none is real. On a box `t₀≤Re τ`, `‖τ‖≤T₀` the far zeros are simple and the branch times are finitely many. No zero escapes along a path of forward times; transport along a branch-free forward path is a bijection of fibres. The forward monodromy group commutes with `z↦−z` and is the same group at every base time. The turn around a collision carries each Hermite sheet to the opposite sheet and has order two; every forward branch time gives a nontrivial element; a centre time gives an element that exchanges some zero `z≠0` with `−z`; a collision away from the centre would give an element that moves a pair. Complex conjugation of the fibre over a positive real non-branch time is an element of the group; RH ⇔ it is the identity at every such time; RH holds if every element preserves every pair `{z,−z}` | [L*] (`riemannHypothesis_iff_forall_pos_not_mem_branchTimes`, `fibreConj_mem_forwardMonodromy`, `riemannHypothesis_iff_fibreConj_eq_one`, `IsCollision.exists_transports_turn`, `forwardMonodromy_ne_bot`, `riemannHypothesis_of_forwardMonodromy_preserves_pairs`; log §4.4, §4.9, §4.11, §4.13, §4.14) | the sign of every zero is a monodromy of one cover; RH is the triviality of one element at each real time |
| `0` is a limit of real branch times, or along every short real segment across `0` infinitely many nonreal zeros escape | [L*] (log §4.4) | the time of ζ is on the boundary of the region in which transport is defined |
| RH through `exp(exp(C·a))` gives the sign on `[−a,a]`; `C` is not explicit. The explicit window height contains `exp(winE+2π)` and `48^{2n}`; the margin transfer at ratio four needs `log R≥2.5·10⁴` at the proved margin. The verified height is 67 | [L*] (log §4.7, §4.11); [D] (log §5) | each window is a finite-height statement; no finite procedure of the corpus reaches the index at ratio four |
| `(log x)^{−1}Σ_{n≤x}λ(n)λ(n+h)/n→0` for every `h≥1`; `Σ_{X≤m<2X}\|Σ_{m<n≤m+h}λ(n)\|²≤εh²X` | [L*] (`tendsto_logAvg_liouville_shift`; log §4.5) | logarithmic two-point Chowla and Matomäki–Radziwiłł are native |
| Displaced twisted second moments for `θ<½`; a positive proportion of critical zeros; `0.67250071` simple critical zeros in the objects of `Zeta23`; positive proportions of runs of four and of five consecutive simple critical zeros | [L*] (log §4.8, §4.9, §4.10) | the in-law half of the near-line picture is native |
| A zero of depth `≥exp(−c log³(T/2π))` has a finite cluster and a test with complete exterior mass `≤¼` | [L*] (log §4.10) | isolation of a deep zero needs no separation hypothesis |
| `N_d=4Q_d`; `sup 4Q_d` is the off-line multiplicity; at each Jensen degree finitely many shifts fail real-rootedness | [L*] (log §4.9) | the Jensen census counts quartets |
| Every Artin Euler product is a product of integer powers of Euler products of linear characters of Brauer-elementary subgroups, on `Re s>1`; the reciprocity law holds for cyclotomic characters; the Artin map is onto; the norm index of a cyclic extension modulo a congruence subgroup is computed up to one cohomological index, and the degree divides the norm index `[K^×:N L^×·(K^×∩W_k∩P)·K_S]`; the Artin map over an intermediate field is the Artin map of the norm | [L*] (log §4.5, §4.9, §4.11, §4.13, §4.14) | the index of an Artin character is one reciprocity law away (A154) |
| No Maass cusp form with `0<λ<3/16` on any congruence subgroup; none in `(0,¼)` for levels dividing `N²`, `N≤25`; `y^{1/4}θ` is a square-integrable eigenfunction of the weight-`½` Laplacian with eigenvalue `3/16` | [L*] (`selberg_status`; log §4.9) | `3/16` is sharp for every argument whose inputs hold in weight `½` |
| The inner field is bounded at infinity; bounded inner field ⇔ depth density `O(T)` | [L*] (log §4.9) | Selberg's density is the bounded inner field; vanishing is open |
| The Goss zeta function at `z∈ℤ_p∖ℕ` has simple zeros of strictly decreasing norms | [L*] (log §4.10) | one Riemann hypothesis is proved by dominance, with no sign |

## 1. Mechanism classes

| Class | Mechanism | Status |
|---|---|---|
| M1 Signed criticality | primes pay the archimedean–polar deficit by sign | exact on every window; a window at aperture `a` follows from verification to `exp(exp(Ca))` [L*] |
| M2 Calibration | window cones, feasible sets, margins | feasible sets nonempty at every aperture ⇔ RH; they converge to `Λ` [L*] |
| M3 Canonical flow | `L, q, Ψ` of the Weil chain | RH ⇔ `Ψ` bounded on the precontact portion of every finite interval [F] |
| M4 Reflection | Krein forms, ringdown, horocycles, cavity energies | sharp receivers; pulse rate = horocycle rate [L*]; exponents `1−Θ/2`, filtered `1−Θ∞/2` [F] |
| M5 Square-root cancellation | prime counts, long moments, squarefree counts | receivers closed; estimates open; logarithmic two-point Chowla proved [L*] |
| M6 Continuation | heat, cosine, Jensen | RH ⇔ no positive real branch time [L*]; finitely many branch times on forward boxes [L*] |
| M7 Zero geometry | cameras, Blaschke factors | adaptive clusters pay their complete exterior mass [L*]; pointwise prime cost at the selected centres open [F] |
| M8 Finite-layer receiver | filters, currents, non-attainment, tangent data | complete in world I [F] |
| M9 Production | integer stencils, Stepanov | rate = Mertens level [L*]; `p^{11/12}` at one prime [F] |
| M10 Count | `ℕ`-counts with quadratic Tate limit | hyperelliptic curves [F]; over ℤ the sections count linearly [L*] |
| M11 Orbit at finite time | prime phases, returns, resonators | under `Θ≤b` heavy returns need `log t≥cy^{1−b}` [L*] |
| M12 Critical compactness | thresholds, pole channel, the critical half-line state | three-way classification; the state is unique, outer, cyclic, stable; its charge is undecided [L*] |
| M13 Topology of the prime complex | orientation cover | centred count `M(N)=Ω_±(√N)` [F] |
| M14 Infinite-rank elimination | towers, thick sets | attained top + thick count ⇔ RH [F] |
| M15 Prime-degree sampling | logarithmic windows, two-prime lags | complete receiver [L*] |
| M16 Intersection on half-products | adelic carrier, Green kernels | glued diagonal refuted [KR]; critical adelic inverse unbounded [KR] |
| M17 Absolute geometry | square, contacts, paths, rings, tails | forced data; exact index for the zeta functions of abelian number rings, quotients of `L`-functions, relative squares and powers [L*] |
| M18 FE rigidity | Hamburger, defects | among unit multiplicities any decaying defect forces the rational primes; among positive weights arbitrarily slow defects with off-line zeros [L*] |
| M19 Exceptional-coordinate atoms | ZAL, B13, Landing | RH = ZAL ∧ B13 ∧ Landing [L*]; all open for ζ |
| M20 Families and monodromy | covers, class characters | fixed-part laws [F] |
| M21 Index and limits | index law, unit gaps | index-one limits give RH; no approximant with a gap [F] |
| M22 Separation and dominance | ordinate injectivity, ultrametric Newton polygons | receiver for ξ [F]; proof for the Goss zeta function [L*] |
| M23 Hodge lattice at finite scale | step packets, neutral part, block matrices | RH ⇔ the Hodge inequality on positive packets without common blocks; certified on ratio `≤103/50`, narrow windows, first blocks [L*] |
| M24 Constituents | bounded and Wiener classes | none with a zero [F] |
| M25 The ladder | mass, aperture, rung | sizes to rung `1−o(1)` [L*] |
| M26 Family continuation | two estimates, reciprocal kernels, reciprocity | `Re s>7/8` [X], stated without hypotheses in source [S]; the frame, the budget, the coupled tower to `3/5`, the barrier of every `6r`-periodic pairing [L*] |
| M27 Dressed positivity | lag aggregate at a level | level one ⇔ RH [L*]; constant-vector signs on infinitely many dyadic prime shells give AAL [L*] |
| M28 Floor-free receivers | homogeneous, unit gap, certificate, amplification, symmetrization | each kind has a receiver and a kill [L*]/[F] |
| M29 Models of the count and of the Euler product | deletions, two-sided edits, signed weights, positive weights | fakes at every count exponent above the pair; with slow defects among positive weights; with bounded defect among signed weights [L*] |
| M30 Index in the aperture | Morse = Maslov index; polar Lagrangian | RH ⇔ no crossing; below the polar ground energy every crossing is charged [L*] |
| M31 Coherence of reciprocity families | modes, columns, root numbers, signed Gram, theta-square series | short columns incoherent, average row target-free; double pole of the theta-square series at `4/3` [L*] |
| M32 Galois theory of zeros | zero field, source field, prime trace field, reflection field, Jensen equations, orderings | `K_even⊆ℝ` ⇔ `H=B` ⇔ RH; Jensen group full or moments dependent; orderings criterion [L*] |
| M33 Bound states and gluing | potentials, couplings, susceptibilities, response matrices | gluing law; rank-one gluing of the halves of ratio four only at block size one; binding rank proportional to the block size [L*] |
| M34 Selective binding | the contacts of 2 and 3 in the neutral part | weakened or Liouville-twisted contacts create a second bound state at ratio three and four [L*]; the sign with the true contacts open (B192) |
| M35 Monodromy of the heat cover | branch times, transport, forward monodromy | conjugation of the zeros is a forward monodromy; RH ⇔ it is trivial; every forward branch time acts nontrivially; the group contains an element exchanging some `z≠0` with `−z`; a group preserving every pair `{z,−z}` gives RH [L*]; exchanges and generators open (B193) |
| Amplifiers | Diophantine repulsion, integrality, Turán, positive annihilators | amplify or reshape a certificate, produce none [KR] |

## 2. Shared obstacle blocks

### S1. Complete Weil family at the critical curve
Routes: HF, SRT, AIP, ACS (atomic), SC. Programmes: CACT, AHD, CSAR, ACPL, ADT, RAPT, AGZ (polar Lagrangian), HTGeometry/HardyBoundary.

Established:
- `0<R_PD=R_PSD=R_polar=R_halfline≤W=R_prim=R_high=inf_A windowThreshold(A)`, each infinite iff RH [F]; `polarPaymentCriticalThreshold=⊤ ⇔ RH` [L*]; three-way classification: RH, or `R_polar<W`, or `R_polar=W` finite with every critical state orthogonal to the polar source [L*] (log §4.2).
- The half-line energy branch: at every `R>0` an attained unit-mass minimizer, unique up to sign, with Laplace transform zero-free on `Re z>0`; the floor strictly concave in `t=1/R`; the eighth-exponential mass of the minimizers strictly decreasing in `t` [L*] (log §4.2).
- At the critical ratio `W₀`: floor zero; derivative `−a(W₀)∫F²e^{−8u}/W₀`; weighted and polar stability (distance² and the square of the polar pairing difference are `≤C|a(R)−a(W₀)|`); Laplace transform nonzero on `Re z≥0`; outer multiplier; cyclic under causal translations; positive mass on every terminal interval; a charged state gives `R_polar<W₀`; polar residual bounded by the critical energy [L*] (log §4.2).
- Strong confinement, `a=a(R)→∞`: `λ(R)−a−log a→μ`, the infimum of logarithmic Fourier energy plus `8∫(−u)F²` on a dilation-stable logarithmic domain; rescaled minimizers approach this floor, `a·δ_R→1`, and `a·∫(−u)F²→1/8`, uniformly over the minimizers [L*] (`universal_softLogarithmic_confinement_limit`; [completed proof and Lean audit](../../drafts/pipeline/3-formalized/universal-soft-logarithmic-confinement-limit.md)). The Gamma-symbol normalization, first-moment spectral bound, and vanishing arithmetic remainder supply the matching variational limits. Attainment of `μ` and convergence to a limiting profile remain open.
- The complete tilted-spline matrix is positive definite for every exponent below `1/8` eventually [L*] (log §4.9).
- On the aperture side: below the polar ground energy the index is the number of charged crossings; on windows with `4J≤R` a ground vector of the block matrix is charged [L*] (log §4.10).

| | Obstacle | Strength |
|---|---|---|
| A9, A13 | constants of the eighth-root horizon; near-gcd charges (unverified) | — |
| A158 | attainment of the limiting infimum and convergence of the rescaled profiles (unverified); the energy, excess, and width limits are verified and integrated | — |
| B6, B101 | full-space sign at every critical multiple; polar payment at every ratio | RH |
| B104 | whether the critical half-line state is charged; first step a Green or boundary-trace identity linking the motion of the wall to the charge | method |
| B123 | correlated arithmetic pairings dominating the depleted kernel | method |

### S2. Window tower, canonical flow, aperture path
Routes: RW, EWU, OWU, ACT, CHMD, TT (odd), SZ, RN, LI, HF, ACS, SRT. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, CHT, AIF, VHR, WVL, SA, ACCE, AGZ.

Established:
- RH ⇔ feasible weights at every aperture [L*] ⇔ every aperture crossing number is zero [L*]; RH, or a unique ground-energy crossing [L*] (log §4.8, §4.10).
- Index law: index at an aperture = sum of nullities below it = number of eigenvalues below the energy; a short aperture has a single simple null mode [L*] (log §4.10).
- Verification: `∃C`, RH through `exp(exp(Ca))` ⇒ the sign on `[−a,a]`; `windowPositiveAt_of_rhVerifiedThrough` with the explicit `windowHeight a` [L*] (log §4.7, §4.11).
- Selectivity: for `2a<log 2` feasibility does not depend on the weights [L*]; every system feasible beyond some aperture has weights within `ε` of `Λ` [L*] (log §4.10).
- Margin law: RH ⇔ `bestMargin→0` on the window cone [L*] (log §4.8).
- Confinement: positivity at aperture `a` confines zeros with `T₀≤|γ|≤2πe^a` to depth `<exp(−c log³|γ|)` [L*] (log §4.10).
- Objects of a failure: an odd bound state; a defective hard-edge block; a point right of the line with `Re ξ′/ξ<0`; a negative definite Markov plane [L*] (log §4.10).
- Prime entry: for `2c<log 5` only `{2,3,4}` enter and their outward kicks cost `<991/1000` of the Lévy energy [F].

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

Established: the minimal face in its forms (§0); the two-prime form at radius `r√T` [L*]; RH ⇔ the Weil lag function is bounded above on `{k log p+l log q}` [L*] (log §4.9); floors at every length `(k+1)π/67` give AAL [L*]; counter-configurations at prescribed sublogarithmic windows [L*] (log §4.10); deep separation with a floor on prime windows of length `80/δ+1` gives `Re ρ≤½+c` [L*] (log §4.8); primes of every reduced class in short intervals [L*] (log §4.10).

| | Obstacle | Strength |
|---|---|---|
| A58 | effective gap iteration (unverified) | — |
| B130 | the bound on any decisive sample; `Kp^σ`, `σ<½`, is a zero-free strip | RH (≥qRH at `p^σ`) |
| B144 | separation of the deep off-line ordinates | sub |

### S4. Continuation, index, constituents, the heat cover
Routes: ZCG, LA, PTR, HCF, PA, GTA, XN, WD, TH. Candidate: W1C. Programmes: NGF, FFP, ADO, AES, IRP, CTZ, GaloisTheoryOfZeros.

Established:
- RH ⇔ every zero of every `H_t`, `t>0`, is simple [L*] ⇔ no positive real branch time [L*] ⇔ conjugation of the fibre is the identity at every positive real non-branch time [L*] (log §4.4, §4.10, §4.13).
- Structure of the cover over forward times: local collisions are Hermite sheets [doc]; far zeros simple and branch times finite on boxes; no escape; bijective transport; a forward path from every positive real non-branch time to the time `1/8`, at which all zeros are real; forward monodromy commutes with `z↦−z`; the groups at two base times are isomorphic; transport depends only on the homotopy class of the forward path, and a loop in a convex set of forward times without branch times transports every zero to itself (`transports_of_homotopy`, `transports_self_of_convex`; working tree) [L*] (log §4.9, §4.11, §4.13, §4.14).
- Local monodromy in the group: the turn around a collision at a forward time transports each sheet to the opposite sheet and has order two; every forward branch time gives an element `≠1` at every base time; a centre time gives an element with `σp=−p≠p`, so the group is not trivial; a multiple zero `z₀≠0` at a forward time gives an element with `σp≠p`, `σp≠−p`; if every element preserves every pair `{z,−z}`, RH holds [L*] (log §4.14). No declaration asserts a multiple zero `z₀≠0` at a forward time.
- At the time of ζ: real branch times accumulate at `0`, or infinitely many nonreal zeros escape across `0` [L*] (log §4.4).
- Jensen: `N_d=4Q_d`; `N_d` eventually the number of off-line zeros if that is finite; `N_d=0` for `2·10⁷d⁴≤T log T` under verification to `T`; finitely many exceptional shifts at each degree [L*] (log §4.8, §4.9); `N_d≤300√(d log d)` for `log d≥6.1·10⁶` [F].
- Heat depth: an initial squared-depth bound ⇔ the heat upper depth energy bounded at all positive times [L*] (log §4.8).
- No bounded Dirichlet or Wiener constituent with a zero [F].

| | Obstacle | Strength |
|---|---|---|
| A19, A20 | heat horizon with an explicit height; Jensen rung past `d⁴≪T log T` (unverified) | — |
| B22–B25 | outer Jensen roots; `N_d` bounded (⇔ finite off-line support); collisions at small time; frequency below one | RH / ≥qRH |
| B124 | finite initial depth budgets of the heat divisor | ≥qRH to RH |
| B146 | an independent family of bounded index converging to ξ | RH (producer) |
| B27, B47 | longer runs of simple critical zeros than five; multiplicity by a non-size input | sub |
| B190 | the orbit of a zero with irrational real part under the embeddings fixing the prime trace field | method |
| B193 | the forward monodromy group of the heat cover: whether a collision away from the centre exists at a forward time (it gives an element that moves a pair; a group without such elements gives RH [L*]); its generators; transitivity on pairs; control of transport as `τ→0` | method |

### S5. Near-line geometry, long moments, census, cameras
Routes: WD, CTF, MC, TG. Programmes: CDG, APR, MZF, AIF, IGP, TransThresholdPairCorrelation, MatomakiRadziwill, LogarithmicChowla.

Established: RH ⇔ the Möbius-mollified second moment is subpolynomial; a cofinal bound with fixed `K` and unbounded `θ` suffices [F]; twisted moments below the square root and the positive critical proportion [L*]; positivity cost of a pair-correlation certificate `>13/10` [L*]; adaptive clusters with complete exterior mass `≤¼`; centred camera prime mean square [L*] (log §4.10, §4.12); short-interval mean squares of `λ` and of `λχ`; logarithmic two-point Chowla [L*] (log §4.5); runs of four and five consecutive simple critical zeros [L*]; bounded inner field ⇔ depth density `O(T)` [L*] (log §4.9).

| | Obstacle | Strength |
|---|---|---|
| A18 | twisted moments past the square root [C] | — |
| B57 | depth density `o(T)` (vanishing inner field) | sub |
| B58–B61 | `D_win`; pointwise prime cost of the adaptive profile at its selected centres; Green moments at deep zeros; a detector past the last scale | sub |
| B62, B66 | cofinal long moment; near-unit holomorphic budgets | RH |
| B150 | a form factor bounded by `4` on `(1,10/9)` | sub |

### S6. Production, precision, the Mertens level
Routes: WL, MC, SQF, PBM, RB, JAS, CTF, FU, CFC, RP. Programmes: ASRP, APR, AGT, AKLT, AE, AAD, RAC, MMD, SPAL, HWV, RIAC, ALST.

Established: the deciding input at square-root precision: no subset of the count class contains the Liouville weight, is stable under perturbations `εn^η`, `η<½`, or is decided by finite prefixes; the prime number theorem and short-interval laws hold for `Λ+εn^η` while the count fails [L*] (log §4.8); a polynomial stencil rate ⇔ a Mertens power saving [L*] (log §4.10); centred cover count `M(N)=Ω_±(√N)` [F]; Type-II bounds are sign-blind [KR]; Stepanov at one prime `p^{11/12}` [F]; logarithmic correlations of `λ` vanish at every fixed shift [L*].

| | Obstacle | Strength |
|---|---|---|
| A30, A33, A46 | best stencil exponent under RH; cubic residue coefficients; singular indices (unverified) | — |
| B48–B54 | the deciding input at square-root precision and its classical faces | RH |
| B55, B67 | polynomial stencil rate; parity at power saving | ≥qRH to RH |
| B15 | pointwise savings past Vinogradov–Korobov in the Lean graph | sub |
| B56 | `Θ<1⇒Θ=½`; with `[X]` it is RH | RH |
| B106 | a correspondence on the orientation cover with bounded local indices | RH |

### S7. Reflection, carriers, the modular horizon
Routes: PM, HAT-C. Candidate: W1C. Programmes: RIT, BHR, ASH, AHMH, CTH, IRP, HAT, STCC.

Established: RH ⇔ every compact pulse rings down at the quarter rate; a strip `Re ρ≤1−2δ` ⇔ pulse decay at rate `δ`; pulse rate ⇔ horocycle rate [L*] (log §4.10, §4.12); AAL ⇔ no Euler polynomial filter accelerates the horocycle rate [F]; the tower quotient has a unit gap iff RH [L*]; the cusp spectrum has the Weyl order [L*]; `selberg_status` [L*] (log §4.9); every zero with `Re ρ>0` is seen by a pair of Hecke forms; one form seeing all right zeros forces `ζ(ρ/2)≠0` [L*] (log §4.8); the theta-square series on the cubic cover has a double pole at `4/3` and the rotated correlations read only the three-divisible layer [L*] (log §4.10).

| | Obstacle | Strength |
|---|---|---|
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | — |
| A54 | cusp expansion for Bianchi resolvents (unverified) | — |
| A148 | the layers `m=0,1` of the theta-square series and the target component of a twisted column [C] | — |
| B68, B71 | independent reflection Krein positivity; universal decay and the horizon rates | RH |
| B87 | a count with Tate limit `Q`, defined without `Q` | RH |
| B147 | Shimura nonvanishing for one eigenform | indep. |
| B114, B117, B171 | partner involution; a regulator with a gap before the limit; a form of signature `(1,∞)` | producer |
| B178 | a relaxation rate beyond the tempered exponent from a principle of the horizon | producer |
| B188 | a mechanism for the scattering resonances whose inputs fail in weight `½`: the Kuznetsov–Kloosterman mechanism of `3/16` is sharp at `3/16` | producer |

### S8. The exceptional coordinate: two worlds and three atoms
Routes: BAG, ZCG, JAS (shell), SC (undamped), WL (thick runs), ACS (sampling), LA (finite support), RW (polar ground energy). Programmes: ZCG AbscissaLaws, ELT, EFT, IWT, IRW, IRP, APD, AAD, TAPO, FFA, SPAL, WZC.

Established:
- `Θ≤7/8` [X]; `Θ<1⇔Θ∞<1`; RH ⇔ ZAL ∧ B13 ∧ Landing; B13 ⇔ packet index `0` or `∞` [L*] (log §4.8, §4.10).
- World I receivers: in world I `ψ(x)−x=O(x^β)` is attained on every window; filters reduce the growing-order current to centred cofactors [F]; under `Θ∞<Θ` tangent data of `μ` and `λ` [L*] (log §4.7).
- Model theory over the rational primes: §0 [L*].
- Laws of the models: balance or real top at `β≤½`; parity above `2max(β,c₀,θ/3)`; `(1−θ)Re ρ≤2β(2−θ)` [L*].
- The FE axis: §0. The scenario table of world I: an integer-norm fake edit with a count rate has a defect that is not Abel-sublinear, not `o(1)`, not power-decaying, not bounded, not `≤c√log|t|`; if `½<β₀<3/2−Θ` a fake edit has mean defect below `cT^{2α}` at arbitrarily large `T`; with positive real weights the defect is `<c|t|^α` eventually, unconditionally; the least deleted prime can be arbitrarily large at a fixed zero [L*] (log §4.3).
- One-structure models: FE with the Riemann Gamma factor and the count within one, without landing [L*] (log §4.10).

| | Obstacle | Strength |
|---|---|---|
| A120 | a finite nonempty stratum with both structures: Selberg zeta functions of surfaces with a small eigenvalue [C] | — |
| A144 | tangent data under additive twists (unverified) | — |
| A157 | the Perron count of the signed grouped edit left of `½` (unverified) | — |
| A155 | the order law at every multiple `k≥3` (unverified) | — |
| B13, B138, B141 | finite stratum; landing; Deuring–Heilbronn for ζ | sub |
| B83, B170 | AAL; non-attainment for ζ | sub / AAL |
| B89, B112, B128 | bounded aligned return; FE into vertical transport; replication by another mechanism | sub |
| B145 | the prime-weighted centred type-II current at a growing isolated mode | AAL [D] |
| B110, B126, B127 | thick crude count; sampling set; lag recurrence | AAL |
| B157 | which structure of ζ that a Selberg-type zeta function lacks excludes a finite stratum | method |
| B183 | a fake with count exponent `β<½` and a non-real pair alone on top (must be balanced) | method |
| B191 | a unit-multiplicity fake with subpolynomial defect energy at `β₀≥3/2−Θ`; the order of the least defect energy between `T log T` and `T^{1+ε}`; whether a bounded defect forces the rational primes among unit multiplicities | method |
| — | ZAL | ≥qRH |

### S9. Prime orbit at finite time
Routes: BAG, TH, SRT. Candidate: S3. Programmes: PTT, TAPO, TTPO, CDGeo, ALST.

Established: near-total returns need `log t>(log y)^{3/2−ε}` [F]; under `Θ≤b`, `c·y^{1−b}≤log t` [L*] (log §4.10); under `Θ<1` the return transfer ⇔ RH [F]; resonator means for `κ<2σ−1`; `T^c` separated returns, `c>(30/13)(1−σ)`, exclude a zero right of `σ` [F].

| | Obstacle | Strength |
|---|---|---|
| A24 | certified scans (unverified) | — |
| B46, B97, B137, B121 | proportional saving at length `(log X)^{2K}`; first return past VK; collective depth floor; freezing control | sub |
| B148 | the transfer of S3 | RH (the strip is [X]) |

### S10. The diagonal, counts, absolute geometry, finite scale, binding
Routes: ACS, HF, HAT-C, PM (count), LI. Programmes: SOSZ, HAT, AGZ, HFP, AE, RIAC, HHAC, CTH, LST, KPA, ALG, RHTower/Artin.

Established:
- Forced data: `CombBezoutShift c ⇔ c≤0 ∧ RH`; `CombBezout ⇔ RH ∧ w=Λ`; `CombBezoutWith δ c ⇔ RH ∧ sup symbol ≤c`; a contact paid at its price is RH at every parameter [L*] (log §4.8, §4.10).
- Index: exact count of right zeros for Dedekind zeta functions of abelian rings, quotients, relative squares, powers, virtual configurations [L*] (log §4.10).
- Artin: Brauer induction; `L(s,Ind σ)=L(s,σ)`; `L(s,ρ)=ΠL(s,τ_i)^{n_i}`; every Artin Euler product a product of integer powers of abelian Euler products; reciprocity for cyclotomic characters and for a linear character whose Artin map is trivial on a ray; Artin map onto; norm index `≤[L:K]`; Herbrand quotients of the `S`-units and of `L^×/W_k`; norm index modulo a congruence subgroup for cyclic extensions; norms positive at ramified real places; `H¹(G,W_k)=0` for cyclic `G`; the second inequality in unit form for cyclic extensions (`card_dvd_index_norm_sup_congruence_sup_sUnits`); `j(Frob_w)=Frob_v^{f(w|v)}` and `j((𝔅,M/E))=(N_{E/K}𝔅,M/K)` for `K⊂E⊂M` (`map_artinMap_eq_artinMap_idealNormHom`) [L*] (log §4.5, §4.9, §4.11, §4.13, §4.14). Triviality of the Artin map on a ray for a general abelian extension is not in the corpus.
- Finite scale: the Hodge inequality form of RH; certified ranges; uniform index bound at each ratio; margin transfer to every refinement above the threshold `log R≥E_Q+2C_Q²/μ₀+μ₀` [L*] (log §4.10).
- Decomposition: the block form is twice the product of charge and weighted charge, plus a potential, plus the Dirichlet form of a graph with positive weights; a ground-state transform identity for symmetric matrices [L*] (log §4.13).
- Gluing: general law; brackets by lowered and raised potentials; response-matrix inertia for several charges; sum of the indices of two windows raised by their couplings `≤` index of the union; rank-one failure beyond block size one; rank law; narrow windows glue trivially and their susceptibility criterion is satisfied by opposite-sign spike charges with arbitrary product [L*] (log §4.1, §4.9).
- Binding: weakened and twisted contacts (§0) [L*]; contacts from a block `a` to blocks below `4a` sum to `≤log 2+log 3` [L*] (log §4.9).
- Metzler dichotomy: for a Metzler form with positive row sums and connected support, one positive square ⇔ the trickle-down inequality ⇔ hyperbolic links; the stability regime ends at the Robin–Euler threshold; the coupled kernel is entrywise nonnegative in some gauge iff `χ(p)=1` for every prime `p≤N` [doc] (log §4.11).
- Power tails and Li coefficients: §0.

| | Obstacle | Strength |
|---|---|---|
| A28, A41, A48 | reciprocal-quadric traces; count law for plane quartics [C]; Hasse–Weil tests (unverified) | — |
| A154 | the reciprocity law for a general abelian extension: the passage from the second inequality in unit form (in Lean for cyclic extensions) to ideal classes, Artin's lemma, triviality of the Artin map on a ray [C] | — |
| A141 | the half-plane `[X]` for fields containing `ζ₃` and every ray class character (unverified) | — |
| B87, B88 | a count on the rays defined without `Q`; the sign of the comb finite part | RH |
| B149, B169 | Bézout from a property of the object; a doubling with a canonical height | RH (producer) |
| B152 | one bound state at every ratio and block size | RH |
| B192 | the first selective sign: one bound state of `(R,3R]` and of `(R,4R]` at every block size, proved from the contacts of 2 and 3 | sub (a finite-height statement at each ratio); method |

### S11. Families, rigidity, exactness
Routes: ACS (tensor), ECP, HF, SC, BAG. Programmes: AWT, AK, ALST, SignFreePurityMechanisms, EFT, SEL.

Established: fixed-part laws [F]; RH ⇔ sublinear tensor exponent [L*] (log §4.12); FE rigidity and the FE axis (§0, S8); the Goss Riemann hypothesis [L*].

| | Obstacle | Strength |
|---|---|---|
| B86 | positivity of the endpoint character at unbounded rank | RH |
| B80 | FE twins with off-line zeros in the full class | sub |

### S12. The scale, the level, the signal, the probe
Routes: RW, HF, ACS, SRT (rungs); JAS, MC, WL, S3 (legs). Programmes: SA, FCT, MMD, CRF, STCC, RHTower `QuasiRH*`.

Established:
- Sizes and the ladder: trivial aperture `log log q+o(1)`; at aperture `≥log log q+η` the Liouville system form is below `−K‖F‖²`; exceptional heights on a rung; three rungs under a half-plane; level one gives the abscissa laws [L*] (log §4.8, §4.10).
- Frame: `Θ≤σ₀` from two estimates with reciprocal kernels; the correction factorizes through a Grössencharacter `L`-function at `6s−3` [L*] (log §4.10).
- Coupled tower: zero transfer `ρ↦6ρ−3`; reach `max(σ₀,3/5)` given the estimates; `7/12` under sextic GRH; barrier of every `6r`-periodic Gauss pairing [L*] (log §4.6, §4.8).
- Budget: binding bin endpoint exponent `−7/30672` at `7/8`, positive if the boundary is `≤7/8−1/4000`; corner `8/9` of the design `(2,6)` [L*] (log §4.8, §4.12).
- Signal: `Θ≤b ⇔` the signal is `≪Z^{b′}` for every `b′>b` [L*] (log §4.8).
- Coherence: root numbers, incoherent short columns, target-free average row; theta-square series and its poles [L*] (log §4.10).
- The half-plane in source: `ζ(s)≠0` and `L(s,χ)≠0` for `Re s>7/8`; every zero of ζ with `Re s>0` has `Re s∈[1/8,7/8]`. The assembly runs from the certified detector bands through the inverse, marked plain and unmarked plain moment batches and the common probe to `beta ≤ 7/8` for the Hecke family, and from the Hecke family to the Dirichlet characters by norm base change (statements and assembly read, log §4.14). The statements carry no hypothesis; the frontier map grades the chain as written and not verified [S].

| | Obstacle | Strength |
|---|---|---|
| A118 | validation of the complete producer and dependency chain of the hypothesis-free `7/8` assembly (`ProbeFinalAssemblyUnconditional.common_probe`, `riemannZeta_zero_mem_quasiRH_strip`) [S] | — |
| A138 | the corollaries of `Θ≤7/8` on the receivers of the scale as Lean statements (rung `κ<4/3`, return bound, ringdown rate `1/16`, comb growth `3/8`): no receiver is stated with the half-plane inserted | — |
| A149 | the function-field calibration of the floor bin over `𝔽_q[T]`, `q≡1 mod 6` (unverified) | — |
| B174 | the row count of the binding bin | a half-plane in `[13/15,7/8)` |
| B185 | the long columns: a power saving in the first moment of the root numbers against a dual column, uniformly in the column | a half-plane in `(2/3,13/15)` |
| B187 | a Möbius-signed pairing outside the `6r`-periodic Gauss pairings whose coupled fixed point is below `3/5`, or whose uncoupled boundary is the line | producer |
| B180 | the reflection of the completed theta row without Eisenstein series | method |
| B160, B161 | `JasDressedPSD 1`; a signal bound below `7/8` | RH; a half-plane below `7/8` |
| B159 | a rung `κ≥4/3` with a saving that fails for the Liouville twist | a half-plane below `7/8` |
| B156 | arithmetic cluster exclusion on a rung | method |

### S13. Floor-free receivers and their kills
Routes: every route (as a filter). Programmes: FFA, WZC.

Established: a Green–Weil energy floor gives RH; the tower quotient has a unit gap iff RH; normalizations of translates at a finite layer tend to zero; monotonicity under every small split forces a concave real trace of the gradient symbol [L*] (log §4.8, §4.10); certificates converge to `Λ` [L*]; floor of prime edits with a count rate `≥13/30` [L*].

| | Obstacle | Strength |
|---|---|---|
| B170 | non-attainment for ζ | AAL |
| B171 | a form of signature `(1,∞)` from the places in which the right zeros are a symmetric spectrum | RH (producer) |
| B172 | a functional decreasing under projection that is not a function of finitely many linear statistics | producer |
| B173 | a two-sided subexponential bound of the trace on late windows of one length | AAL |

## 3. Live routes

Receiver statements follow the frontier map at the checkpoint unless marked `[L*]`.

### WL — Weil lag
- **Path:** bounded prime-deficit critical energy, or positive semidefiniteness of every finite Gram matrix of the prime lag, or an attained top with an `O(√X)` deviation on a thick set → RH.
- **Established:** endpoint energy bounded ⇔ RH ⇔ first-band growth `O_ε(N^{1+ε})`; RH ⇔ attained top ∧ thick `O(√X)` deviation; RH ⇔ every finite Gram matrix of the prime lag is positive semidefinite; on a bounded full lag progression accessibility of an isolated right mode replaces top attainment [F]. RH ⇔ the Weil lag function is bounded above on `{k log p+l log q}` [L*] (log §4.9).
- **(a)** A30. **(b)** B49 (endpoint energy), B48 (deciding input), B110 (attained top with the thick estimate), B1.

### RW — Restricted Weil ground energy
- **Path:** `μ(a)≥0` at every aperture → RH; equivalently feasible weights at every aperture; equivalently no crossing along the aperture; equivalently `Ψ` bounded on the precontact portion of every finite interval.
- **Established:** feasible weights at every aperture ⇔ RH; index law and its Lagrangian form; RH or a unique ground-energy crossing; feasible systems converge to `Λ`; verification rate; charged crossings below the polar ground energy [L*] (S2). Floor `1/(20000·2^k)` through `a_k`, `a₀>181/500`; restoring bound of the actual chain; RH ⇔ relative compactness of every Weil orbit correlation [F].
- **(a)** A1–A3, A16, A117, A140, A142.
- **(b)** B1, B2, B4, B18; B104 for the polar channel. Bounds strictly before contact do not suffice: the variation constants retain the inverse ground energy [F].

### FU — Signed prime scheduling
- **Path:** signed Möbius history → one-sided sampled Abel bound → RH. **Established:** for fixed `m≥1` either one-sided bound on `A(j^m)/j^m` ⇔ RH; one controlled sample per backward window of length `N^{1−δ}` suffices [F].
- **(a)** none. **(b)** complete-history bounds across advancing clocks (B42); fixed-horizon payment does not control cross-clock debt [F].

### CFC — First-clock lower bound
- **Path:** first-clock source bounded below on an aperture tail → RH. **Established:** exact tail criterion; ¬RH forces unboundedness below on every tail [F].
- **(a)** none. **(b)** the lower bound with prime, archimedean and endpoint terms (B42).

### RP — History floor
- **Path:** eventual linear floor of the normalized history → RH. **Established:** linear-floor criterion; low-LCM and copied-diagonal payment; a sublinear floor is impossible [F].
- **(a)** none. **(b)** high-LCM pairs, moving core, singular-domain terms in one floor (B42).

### PA — Prime–archimedean passivity (HJ alias)
- **Path:** prime−archimedean response sign → RH. **Established:** calibrated Hausdorff-row sign for `r≥min(C₀(k+1)²,S(k))` with explicit cutoffs; exterior scalar-diagonal criterion with discharged radius `218/25` [F].
- **(a)** A1. **(b)** signs below the explicit shift uniformly in the degree; these entries ⇔ RH (B31).

### MC — Möbius cancellation
- **Path:** half-power Möbius cancellation → RH.
- **Established:** damped critical energy, fixed-height prefixes, mollifier zero-freeness each characterize RH [F]; `tendsto_logAvg_liouville_shift`: logarithmic two-point Chowla at every fixed shift; short-interval mean squares of `λ` and `λχ` [L*] (log §4.5); the coupled tower and its barrier at every period [L*] (log §4.6, §4.8).
- **(a)** A33, A46, A118.
- **(b)** B48, B50, B15, B106; B161; B174, B185, B187. Logarithmic correlation decay supplies no half-power rate; the bootstrap of the probe cannot pass `3/5`; RH needs a different source or transfer [F].

### SQF — Weighted squarefree count
- **Path:** a one-sided `O(t^{−¼−ε})` bound of `Σμ(n)²e^{−nt}−6/(π²t)` → RH. **Established:** either one-sided law ⇔ RH; `Ω_±(t^{−1/4})`; the `k`-free ladder detects the strip `Re s>1−1/k` [F].
- **(a)** none. **(b)** the quarter-power bound for one sign (B48 family).

### TT — Theta tail / Wold
- **Path:** bounded weighted endpoint energy at each `0<t<½` → RH. **Established:** RH ⇔ a bound `C_t` for every `t`; uniform bound on a shrinking band [F].
- **(a)** none. **(b)** `C_t` at every fixed `t` (B34); the shrinking band does not reach a fixed positive `t` [F].

### LA — Jensen line anchor
- **Path:** Jensen polynomials real-rooted, or sublinear root height → RH.
- **Established:** RH ⇔ infinitely many Jensen degrees real-rooted; reversed Jensen roots with `|Re z|≤√(d log d)/100` are real for large `d`; `N_d≤300√(d log d)` [F]; `N_d=4Q_d` with `sup 4Q_d` the off-line multiplicity; finitely many exceptional shifts at each degree; nonnegative discriminants; Jensen group full or moments dependent [L*] (log §4.4, §4.9, §4.10).
- **(a)** A20, A1. **(b)** B22; B23 then B13, B138; B124; B190. Bounded nonreal multiplicity gives only finite off-line support [F].

### ZCG — Zero-configuration geometry / heat descent / abscissa laws
- **Path:** no positive real branch time → RH; or a decisive prime-window floor; or ZAL ∧ B13 ∧ Landing.
- **Established:** RH ⇔ no positive real branch time ⇔ fibre conjugation is the identity at every positive real non-branch time; forward monodromy group; far zeros simple, branch times finite on boxes; no escape and bijective transport over forward times; central branch times infinitely many and nonreal; every forward branch time a nontrivial monodromy; a pair-preserving group gives RH; the dichotomy at `0` [L*] (log §4.4, §4.9, §4.11, §4.13, §4.14); adaptive cameras [L*]; the model theory of world I and the FE axis [L*] (log §4.3, §4.10).
- **(a)** A19, A120, A144, A155, A157.
- **(b)** B24, B25, B47, B27, B124; B130; B145, B170; B13, B138, B141; B59; B183, B191; B193. Group membership and reflection commutation do not make conjugation trivial; triviality of the whole forward monodromy group is refuted [KR]; forward non-escape gives no uniform control as `τ→0` [F].

### TG — Topological sub-unit gate
- **Path:** cubic defect trace norm `<1` → integer zero count vanishes → RH. **Established:** exact integer trace; enclosed multiplicity `≤` trace norm; endpoint and Gaussian central-gap receivers [F].
- **(a)** none. **(b)** trace norm below one on every formation rectangle (B38); a scalar prime budget below one is not a trace-norm bound [F].

### HF — Hodge / complete cells
- **Path:** complete arithmetic form `≥0` → Hodge index → RH.
- **Established:** S1, S10; the critical half-line energy branch (attainment, uniqueness, concavity, derivative, stability, outer, cyclic) and the universal strong-confinement energy, excess, and width limits [L*]; RH ⇔ the Hodge inequality on positive packets without common blocks [L*]; exact index for number rings, quotients and powers [L*].
- **(a)** A9, A13, A141, A154, A158.
- **(b)** B6, B101, B104, B123, B8, B41, B10, B87, B88, B149, B152, B192. Stability does not determine the polar pairing of the state; cyclicity in `L²` is not density in the energy norm; the strong-confinement regime `R→0` does not settle the sign at `R→∞` [F].

### HAT-C — Arithmetic-clock Green energy
- **Path:** one clock, or one fixed scattering height → energy floor → `W≥0` on packets ⇔ RH.
- **Established:** a Green–Weil energy floor gives RH [L*] (log §4.10); at any fixed height the corrected energy plus the nonnegative jump tail equals `W`; `E_r≤W` at every cutoff [F].
- **(a)** none. **(b)** the corrected-energy floor at one fixed height on all apertures (B1); the sign of the tail alone does not bound the energy [F].

### CHMD — Causal hyperbolic–modular duality
- **Path:** bounded prime wave, or the odd half-threshold bound → RH. **Established:** wave and Doob receivers; RH fails iff an odd bound state exists [L*] (log §4.10); normalized decay `O(exp(−√log Y/92160000))` [F].
- **(a)** none. **(b)** either side of the unnormalized wave bound; the complete odd sign (B35, B4).

### TH — Theta moment positivity
- **Path:** signed center-mixed jets → all-rank Hankel positivity → RH.
- **Established:** rank 14 positive definite for `0<a≤½` [L*] (log §4.7); rank `N` from verified height `41+6(N+2)log(N+2)`; adaptive head payment of the omitted pair sum; the critical Dirichlet sum of half the height approximates `ζ(½+ib)` [F].
- **(a)** A4, A5, A24, A42. **(b)** B102, B20, B21: the signed adaptive-head payment at every aperture and degree [F].

### RN — Theta renewal
- **Path:** exclusion of joint nodes, or the theta-ground energy comparison → RH. **Established:** two-ended formula recovers Ξ with multiplicities; full-divisor zeros are the joint nodes [F].
- **(a)** none. **(b)** B36.

### WD — Ward / collision / long moments
- **Path:** cofinal long-mollifier moments, or collision bounds → RH.
- **Established:** RH ⇔ subpolynomial mollified moment; cofinal bound with fixed `K`, unbounded `θ` suffices; finite Fejér means are signed logarithmic collision forms [F]; twisted moments for `θ<½` and the positive proportion; dyadic boundedness at `θ>1` confines depth to `<1/(2θ)+ε` [L*] (log §4.10); logarithmic two-point Chowla [L*].
- **(a)** A18. **(b)** B62, B57–B61, B63. WD needs unbounded `θ` with a `θ`-independent exponent; the proved moment sits at `θ=13/50` [F].

### LI — Paired Li / Cayley ladders
- **Path:** subexponential lower bound of the clock response, or the Cayley–Li sign → RH.
- **Established:** RH ⇔ ladder sign on primitive vectors [doc] (log §4.11); `λ_n≥0` for `n≤314` [F]; the Laguerre tails of the comb tend to the paired Li coefficients; without RH negative and positive paired Li indices recur in windows of bounded length [L*] (log §4.10).
- **(a)** A1. **(b)** B43: a sign uniform in `n`.

### SZ — Suzuki screw
- **Path:** rectangular Ward defect bounded below → RH. **Established:** completed Abel source bounded ⇔ RH; `|A_N|≤C√N·exp(−c·vkScale(N))` [F].
- **(a)** none. **(b)** B37, B1.

### PM — Physical model
- **Path:** scattering source → reflection Krein sign, ringdown rate, cavity rate or a count → RH.
- **Established:** S7.
- **(a)** A26, A54, A148. **(b)** B68, B71, B87; B147; B114, B117, B171; B178, B188. Visibility is proved, decay is not [F].

### PTR — Cosine source
- **Path:** no exceptional point of the cosine producers on the open depth band → RH.
- **Established:** RH ⇔ strict Laguerre sign at every `0<h<½`; the sign for `h≥½` and near the Vinogradov–Korobov boundary; ZAL gives finite nonreal defects at every positive shift [F].
- **(a)** none. **(b)** B29, B69.

### JAS — Joint ancestry
- **Path:** level-one dressed positivity on large primes; or subpower moving-window control → RH.
- **Established:** `JasDressedPSDAbove X σ`, `0≤σ≤1` ⇒ RH; RH ⇒ `JasDressedPSD σ` for `σ≥½`; `Θ≤b` ⇔ signal bounds at every `b′>b`; level-one constant-vector positivity on infinitely many dyadic prime shells ⇒ AAL [L*] (log §4.8, §4.13); under `Θ∞<Θ` the Gaussian Möbius and Liouville signals have top-residue asymptotics with leading coefficients related by `ζ(2ρ)` [F].
- **(a)** A118, A138. **(b)** B160, B161 (through B174, B185), B51. A `7/8` signal bound gives a strip, not level-one positivity [F].

### CTF — Chronological tail / Báez–Duarte
- **Path:** unit-bounded rows, BSY sign, cut-kernel mass, a uniform positive-proportion condition for `ζM_N−1` → RH. **Established:** the criteria; exact infimum `exp(2I(1))` of holomorphic mollifiers [F].
- **(a)** none. **(b)** B52, B66, B91.

### HCF — Heat trace
- **Path:** two prime-log heat grids nonnegative at every degree → RH. **Established:** two-grid criterion; every off-line zero gives a pole-annihilating negative test on `log 2` or `log 3` [F].
- **(a)** A1. **(b)** B30.

### XN — Newton discs
- **Path:** line-centred self-map discs covering every zero → RH. **Established:** coverage and closed-margin criteria [F].
- **(a)** none. **(b)** B32.

### BAG — Self-return
- **Path:** uniform head-target density → RH; transport → AAL.
- **Established:** strong recurrence ⇔ RH; fewer than `T^c` one-separated self-returns of some zero disc for `c>(30/13)(1−σ)` [F]; RH ⇔ relative compactness of the orbit [L*]; normalizations of translates at a finite layer tend to zero [L*] (log §4.10).
- **(a)** none. **(b)** B72, B83, B89, B97, B137, B145.

### EWU — Even sector
- **Path:** even blind minimum `≥0` at every aperture → RH. **Established:** blind minimum `≥1/20` for `a≤(log 2+1/50)/2`; sign-gauge balance iff `c≤log ρ`, `ρ³=ρ+1` [F].
- **(a)** A1–A3. **(b)** B4, B17, B44.

### GTA — Schur charge
- **Path:** cofinally small quartic charge → RH. **Established:** compactness criteria; late packets have charge `≤` stage Hilbert–Schmidt mass`/400` [F].
- **(a)** none. **(b)** B33.

### OWU — Odd sector
- **Path:** odd positivity with the polar hyperplane → RH. **Established:** odd criterion; unit-window floors; no sign gauge removes an acting negative prime antidiagonal [F].
- **(a)** A1–A3, A6. **(b)** B4, B17, B44.

### PBM — Regularized abscissa
- **Path:** convergence of the pole-regularized series right of `½` → RH. **Established:** exact equivalence [F].
- **(a)** none. **(b)** B53.

### RB — Robin / Nicolas
- **Path:** eventual extremal inequality → RH. **Established:** eventual criteria without a premise `Θ<1` [F].
- **(a)** none. **(b)** B54.

### SRT — Lag localization
- **Path:** the prime two-bump sign on a decisive sample → RH. **Established:** S3 [L*]; the two-prime form on windows of radius `r√T` [L*] (log §4.9); prime packet rungs from verified heights [F].
- **(a)** A9. **(b)** B130, B6, B101, B104. Every prescribed radius `o(log T)` admits a countermodel [L*] (log §4.10).

### ACT — Single shift
- **Path:** the variation inequality at one shift → RH. **Established:** receiver; `{2,3,4}` kicks below `991/1000` of the Lévy energy for `2c<log 5`; variance-free certificates fail for `c>273/400` [F].
- **(a)** A7, A140. **(b)** B44, B4.

### AIP — Incidence
- **Path:** global incidence allocation → RH. **Established:** exact allocation; signed cost bound of Vinogradov–Korobov shape; receiving modes with bounded charge and vanishing physical energy [F].
- **(a)** A9, A13. **(b)** B45, B101, B104.

### SC — Stokes / Witt–Krein
- **Path:** bounded Gaussian-damped coupling, or glued index `≤1` → RH. **Established:** bounded damped coupling ⇔ RH; glued index `=κ_ζ+1`; undamped coupling on a two-prime cone gives AAL [F].
- **(a)** none. **(b)** the damped bound; sublinear tensor loss (B39); ZAL for the undamped branch; B104.

### ACS — Castelnuovo–Severi on the degree points
- **Path:** the comb sign, the Hodge inequality on every window, subpolynomial critical-comb growth, or critical Abel integrability → RH.
- **Established:** S10; §0 (Hodge inequality form, certified ranges, gluing law and its rank law, weakened contacts, critical comb, Li tails).
- **(a)** A28, A41, A48, A141, A154.
- **(b)** B152, B192, B149, B169, B88, B87; B130; B28; B13. A fixed number of charges cannot close the induction on the ratio; a growing-rank construction or a signed comparison has to retain the binding of the true contacts [F]/[L*].

### ECP — Endpoint character positivity
- **Path:** endpoint jets → class functions → PSD character Grams at every rank ⇔ RH. **Established:** column projections nonnegative; Toeplitz minors through order 200; mixed shapes `(2,1)`, `(3,1)`, `(2,2)`, `(2,1,1)` paid [F].
- **(a)** none. **(b)** B86.

## 4. Candidates

Each needs its source-to-receiver step (B81). Dormant pending a source mechanism: SEC, CDC/BSH, APF, EWJ, RFHM, WBF [F].

| Candidate | Established | (a) | (b) |
|---|---|---|---|
| S3 | a strip excludes heavy identity returns; under `Θ<1` the transfer ⇔ RH [F] | none | B148: with `[X]` the transfer is RH |
| SEC | Fock boundedness at every strip parameter ⇔ `Re s=½` [F] | none | a ζ-selective bound from the Sonin source |
| CDC/BSH | marked prices agree iff `Re s=½` [F] | none | descent on actual zero fibres |
| APF | prime/grade trace reconstruction [F] | none | full-divisor exhaustion |
| EGC | zero-pair contour; explicit count error [F] | none | height-fibre isolation |
| EWJ | all-depth reporter [F] | none | faithful endpoint admission |
| FEL | KL accounting [F] | none | a predeclared history forcing the BSY sign |
| IRK | finite idempotent traces; a finite free resolution [F] | none | projective lift identifying trace with Chern charge |
| MSC | `L²` discrepancy; conormal transport [F] | none | Sonin/Weil sign landing |
| RFHM | support source; creation [F] | none | an RH-sufficient orientation law |
| W1C | index-one approximants or an index-one realization give RH [F] | none | B146, B171 |
| WBF | Gram recovers magnitudes and phase class [F] | none | arithmetic stream and Ξ landing |

## 5. Supporting programmes

| Programme | Established | (a) | (b) |
|---|---|---|---|
| AGZ | forced data; exact index for number rings, quotients and powers; Hodge inequality form of RH; certified ratio `≤103/50`, narrow windows positive definite, first blocks; uniform index bound at each ratio; index law in the aperture; charged crossings; gluing law, brackets, response matrices; rank law of the binding; weakened and twisted contacts; power and critical combs; Li coefficients as Laguerre tails [L*] | A154 | B104, B149, B169, B88, B87, B152, B192 |
| AHD / CACT / HTGeometry-HardyBoundary | thresholds; classification; the half-line energy branch and the critical state (uniqueness, concavity, derivative, stability, outer, cyclic, terminal mass); positivity below the eighth root; the universal strong-confinement floor, excess and width limits [L*] | A9, A13, A158 | B104, B123 |
| ALG | Metzler Hodge index theorem; trickle-down; twist-blind atomic hyperbolicity; Cayley ladder criterion [doc] | — | B192 (the hyperbolic regime with the true contacts) |
| HFP | mass floors on ratio windows; short windows do not see the contacts [L*] | — | B152 |
| WZC | two-sided edits; balance, parity, count floor; floor `≥13/30`; twin defects; the frontier dichotomy; the scenario table of world I [L*] | A155, A157 | B183, B191 |
| EFT / APD / SPAL | FE rigidity at any decay among unit multiplicities; arbitrarily slow defects among positive weights; Abel floors of real-weighted fakes; `T log T` defect energy; signed fake with bounded defect and its Euler weights; integer-norm fakes below one half [L*] | — | B191 |
| CRF | short columns, short Gram, average row, root numbers [L*] | A149 | B185, B187 |
| STCC | theta-square series: factorization over cube frequencies, double pole at `4/3`, rotated correlation, three-divisible layer [L*] | A148 | B180 |
| FCT | frame, coupled tower to `3/5`, zero transfer, barrier of `6r`-periodic pairings, budget vertex, signal exponent [L*] | A118, A138 | B161, B174, B187 |
| MMD | the half-plane `7/8` for ζ, the Dirichlet characters and the Hecke family over `ℚ(√−3)`: stated without hypotheses, with all four moment estimates and the summed continuation assembled in source [S] (log §4.14) | A33, A118 | — |
| GaloisTheoryOfZeros | zero field over the source field; prime trace and reflection fields; rational orbits; Jensen equations with full group or dependent moments; orderings of the squared-width field; the heat cover: branch times, Hermite sheets, transport, forward monodromy, local monodromies as group elements, conjugation as a monodromy [L*] | — | B190, B193 |
| RHTower/Artin | Brauer induction; induction and integer-relation invariance of Artin Euler products; abelian product form; cyclotomic reciprocity; Artin map onto; norm index and Herbrand quotients; norms at real places; second inequality for cyclic extensions; Artin map of the norm [L*] | A154 | — |
| FFA | floors; receivers and kills of the off-scale kinds; tangent data in world I [L*]/[F] | A144 | B170–B173 |
| SA | trivial aperture; ladder; exceptional heights; Liouville twist beyond the trivial aperture [L*] | A117 | B159, B156 |
| ELT | atoms; filters; growing-order reduction [F]; landing law criterion [L*] | — | B141, B145, B138, B13 |
| CTZ, IRP | no bounded or Wiener constituent; index semicontinuity [F] | — | B146 |
| MZF / CDG / AIF | twisted moments; positive proportion; centred cameras [L*]; bounded inner field [L*] | A18 | B62, B57, B59 |
| MatomakiRadziwill, LogarithmicChowla | short-interval mean squares of `λ` and `λχ`; logarithmic two-point Chowla [L*] | — | — |
| ShortIntervalPrimesInProgressions | primes in `(x,x+x^θ]` in every class [L*] | — | — |
| SignFreePurityMechanisms | Goss Riemann hypothesis [L*] | — | a norm for ξ |
| HAT | clock; tower; unbounded critical inverse [F]/[KR] | A54 | B88, B117 |
| BHR / AHMH / ASH / CTH | ringdown ⇔ strip; pulse rate = horocycle rate; Weyl order; `selberg_status`; Hecke pairs see every resonance [L*]; filters; hyperelliptic count [F] | A26, A41 | B68, B71, B87, B147, B178, B188 |
| TTPO / PTT / TAPO / CDGeo | returns; resonator means [F] | A24 | B46, B97, B137 |
| ALST / AAD / RAC / APR | Stepanov degrees; producer rates; cut kernel; parity blindness [F]/[KR] | A30 | B48, B55, B67 |
| VHR / TCS | height 67; rank 14; double-exponential window height with explicit `windowHeight` [L*] | A1–A5, A142 | — |
| Census (IGP, TTPC) | `0.67250071`; runs of four and five simple zeros; positivity cost [L*] | — | B150, B57, B27 |

## 6. Decisive wall per route

| Wall | Routes |
|---|---|
| The minimal face `P(p)≤A(p)+K` on logarithmic windows off power-thin exceptions; in two-prime form on windows of radius `r√T` | ACS, SRT, WL, HF, ZCG, HAT-C, PM (count) |
| Σ: the sign on every window = no crossing along the aperture = the Hodge inequality on positive packets without common blocks = feasible weights at every aperture | RW, EWU, OWU, ACT, CHMD, SZ, RN, AIP, SC, LI, TT (odd), HF, HAT-C, ACS |
| Σ: binding. The union of two windows holds one bound state only through the true contacts of the small primes; the binding has rank proportional to the block size; the first open case is ratio three (B192) | ACS, HF, RW |
| Σ: the critical half-line state: its existence is the failure of RH; its charge is B104 | HF, SRT, AIP, SC |
| Σ: continuation at small time: positive real branch times = nontrivial conjugation monodromy; theta heads | ZCG (heat), PTR, LA, GTA, XN, HCF, PA, TH |
| Π: square-root precision; long moments past the height | WL, MC, SQF, PBM, RB, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| One scale, one producer: `[X]` at `7/8`; the cubic probe's estimates reach `2/3` with square-root cancellation; every `6r`-periodic Gauss pairing has frame `≥3/5`; no other source | JAS; MC (signal); S3; ACS (tails); every graded receiver |
| Γ: reflection and count; the congruence mechanism is sharp at `3/16` in weight `½` | PM, ECP |
| The exceptional coordinate: world I needs the Euler product with unit multiplicities and the reflection up to a decaying error, or a count below half the real part of the layer; world II is the scale | BAG, ZCG, JAS shell, SC undamped, WL thick runs, LA finite support |
| The dark range: prime sums shorter than the Vinogradov length; polynomials longer than the height; window heights beyond every verified height | every route at all heights; BAG; WD; MC |
| Missing source landing | the twelve candidates |
