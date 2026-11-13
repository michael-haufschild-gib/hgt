# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: `fdc9cfc40f` (2026-11-13), working-tree sources included. Fact log: `logs/review-1311-status-quo-facts.md` (cited as "log §n").

**Evidence.** `[L*]` Lean statement read at its declaration for this report and recorded in the fact log; `[doc]` content of a module docstring whose theorem names were read but not every statement; `[F]`, `[KR]` stated by the frontier map and the scoped-obstruction ledger at the checkpoint; `[S]` module graded unfinished or unintegrated by the frontier map; `[D]` deduction made here from `[L*]` statements, not a Lean theorem; `[C]` classical mathematics quoted from memory, not in the corpus; `[A]` assessment; `[X]` the half-plane `7/8`, taken as proved: every Dirichlet `L`-function, ζ included, and every Hecke `L`-function of the family over `ℚ(√−3)` is zero-free in `Re s>7/8`. It is cached in the repository as an external theorem (OpenAI, 30 September 2026). In the Lean source it is stated without hypotheses (`riemannZeta_ne_zero_of_seven_eighths_lt_re`, `DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`, `riemannZeta_zero_mem_quasiRH_strip`, in `MetaplecticMobiusDescent/WeightedCubicResidualFourierTests.lean`; statements and final assembly read, log §4.14). The frontier map grades this source `[S]`: an unconditional statement in source, not a verified theorem; validating the complete producer and dependency chain is just work (A118). Consequences of `[X]` on receivers are `[D]`. Sections 2.3–2.21 are interpretation and ideation: every untagged statement there is a proposal.

**38 live formulations; 12 candidates** (SEC, CDC/BSH, S3, APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF). HJ is PA; PCS, DR, PW-B are retired labels.

**Notation.** As in [route-obstacles.md](route-obstacles.md). In addition: the **reach** of a producer is the least `σ₀` for which its implication gives `Θ≤σ₀`; a **pairing** `(c,k)` has local resonance norm `Q^{c−ks}` at a prime of norm `Q`, **uncoupled boundary** `(c+1)/k` and **coupled fixed point** `c/(k−1)`; the **defect energy** of a system at `T` is `∫‖g‖²e^{−|t|/T}dt`; the **floor tree** of `k` is the graph on the blocks that joins `b` to `⌊b/k⌋` (`floorGraph k`), in which every block has `k` children; the **Doob chain** of a window is the reversible Markov chain on its blocks with conductances `φ_aφ_b|N(a,b)|`, where `N` is the neutral part and `φ` the positive eigenvector of its least eigenvalue `−μ` [C: Perron–Frobenius].

## 1. Big picture

### 1.1 One object, five exact forms
- **One inequality per prime.** RH ⇔ `2Re S(log p)≥−K` at the primes of arbitrarily late logarithmic windows outside `Ce^{δT}` primes per window; equivalently the upper side alone, `ℕ`-counts on the surviving prime rays, or copositivity of the prime planes; `Θ<1` ⇔ the floor `−Kp^α` for some `α<½`. For two fixed primes `p≠q` and any `r>0`: RH ⇔ the trace is bounded below at the lags `k log p+l log q` within `r√T` of arbitrarily late `T` [L*] (log §4.8, §4.9, §4.10, §4.12).
- **One matrix at finite scale.** The Weil form on the step packets of a window is twice the product of its two charges plus the **neutral part**; the neutral part is a potential plus the Dirichlet form of a graph on the blocks whose weights are the jets and the contacts `Λ(k)/k` along the floor trees. Its off-diagonal entries are negative. RH ⇔ on every window `(R,R+J]`, `R≤J`, two disjointly supported nonnegative packets `x,y` with `N(x,x)<0` satisfy `N(x,x)N(y,y)≤N(x,y)²` ⇔ every eigenvector with negative eigenvalue has one sign. The supremum of the index of the neutral part is one plus the number of zeros right of the line [L*] (log §4.1, §4.7, §4.13).
- **One binding.** With the contact of 2 weighted in `[−4,0]` every window with `J≥2R` has two bound states; with the contacts of 2 and 3 weighted in `[−5/2,19/40]` every window with `J≥3R` has two; the Liouville twist gives two for `J≥2R`. The halves `(R,2R]`, `(2R,4R]` of a window glue through one pair of charges iff `R=1`; every model of their coupling of rank `r` with `600(r+1)≤H` leaves two negative squares [L*] (log §4.1, §4.9).
- **One path of Lagrangians.** The index of the restricted Weil form at an aperture is the sum of the nullities below it, the number of eigenvalues below the energy, and a Lagrangian intersection number; RH ⇔ every crossing number is zero [L*] (log §4.8, §4.10).
- **One cover.** RH ⇔ no branch time of the heat cover is real and positive ⇔ complex conjugation of the fibre over every positive real non-branch time, which is an element of the forward monodromy group, is the identity. Every forward branch time acts by a nontrivial monodromy; RH holds if every monodromy preserves every pair `{z,−z}` [L*] (log §4.4, §4.13, §4.14).

**In Poincaré form [D].** With `x_b=φ_bf_b` the ground-state transform (`sum_sum_mul_eq_doob` [L*]) gives `N(x,x)=−μ‖f‖²_φ+E(f)`, `E` the Dirichlet form of the Doob chain. So a window has at most one bound state iff the spectral gap of its Doob chain is at least `μ`: RH at finite scale is a Poincaré inequality whose constant is the binding energy of the window. The chain moves along the jets and along the floor trees.

### 1.2 One scale
Every graded receiver is an equivalence at each level of one scale [D]:

| Reading | Parameter | Depth it reaches | Evidence |
|---|---|---|---|
| saving of the contacts `n^{½+γ}` | `γ` | sign to rung `κ<1/(2γ)` | [L*] (`cancellation_and_depth_ladder`) |
| sign on a rung `κ` | `κ` | no isolated zero of depth `>1/(2κ)` | [L*] (`zeta_companion_of_rung`) |
| bounded dyadic Möbius moment at length `T^θ` | `θ>1` | depth `<1/(2θ)+ε` | [L*] (log §4.10) |
| exponent of the signal of the zeta kernel | `b∈[½,1)` | `Θ≤b` ⇔ `O(Z^{b′})` for all `b′>b` | [L*] (log §4.8) |
| growth exponent of the critical comb | `σ≥0` | strict growth `σ` ⇔ `w≤σ` | [L*] (`strictGrowth_criticalPowerCombTail_iff_zeroWidth`) |
| growth of a power tail | `σ` | a zero-free half-plane | [L*] (`powerCombTailGrowth_iff_zeroHalfPlane`) |
| ringdown rate; horocycle rate | `δ` | `Θ≤1−2δ` | [L*] (`zeroFreeStrip_iff_pulse_ringdown`, `pulse_ringdown_iff_horocycle_rate`) |
| heavy returns of the prime orbit | `y^{1−b}≤C log t` | `Θ≤b` | [L*] (`heavy_return_bound_of_halfPlane`) |

Sizes prove the scale to rung `1−o(1)`: the trivial aperture is `log log(mass)+o(1)` [L*] (`exists_abs_trivialAperture_sub_le`). The level `b=7/8` is `[X]`: the rung `κ<4/3`, heavy returns only for `log t≥c·y^{1/8}`, ringdown rate `1/16`, critical-comb growth `≤3/8` [D]. In the Lean source the half-plane is stated without hypotheses [S]; no receiver of the scale is stated with it inserted (A138).

### 1.3 Three structures; models; rigidity
ζ has an Euler product over the rational primes, the Riemann functional equation, and every integer with multiplicity one.

| Structures kept | Model | What fails | Evidence |
|---|---|---|---|
| the Riemann FE with Gamma factor, residue one, zero count within one | simple zeros off the line approaching it, no landing | Landing | [L*] (`exists_riemann_gamma_counting_model_without_landing`) |
| Euler product over the rational primes, multiplicities `0,1,2`, integer norms, a count rate above the top | two-sided edits: a non-real pair alone; every finite layer; zeros on and rising to a vertical line; sparse configurations; a finite layer of ζ edited away | AAL, B13, Landing, ZAL (sparse tails) | [L*] (log §4.10, §4.12) |
| the same, zeros symmetric about the line in a strip | quartet edits | the line | [L*] (`exists_isEdit_zeros_symmetric_in_a_strip`) |
| the same, with mean-square FE defect `≤C_εT^ε` | fake edits with a pair at any `½<β₀<3/2−Θ`, if `Θ<1` | AAL at `β₀` | [L*] (`frontier_dichotomy`) |
| positive real weights, Hamburger strip class, count `Ax+O(x^{4/5})`, FE defect below any prescribed `Φ→∞` | systems with prescribed off-line zeros `1−μ±iγ` | the line | [L*] (`exists_positiveWeighted_beurling_slow_defect`) |
| real integer weights, bounded FE defect | a signed system on the powers of 2 with the zero `¾+i` | a zero that ζ lacks | [L*] (`signedPoly_fake`) |
| unit multiplicities, Hamburger strip class, FE defect `O((1+\|t\|)^{−a})`, any `a>0` | none: the rational primes, with the same counting measure and a norm-preserving bijection of labels | — | [L*] (`beurlingSystem_rigidity_of_decaying_defect`) |
| real weights on the integers with a fake zero | none with a decaying defect: an Abel floor | — | [L*] (`fake_abelMass_floor`) |
| integer norms, count exponent `β≤½` | fakes of positive density that omit infinitely many primes; a prime-deletion fake has a real fake zero on top; an edit is balanced or has a real zero on top | a non-real top alone | [L*] (`integerNormFake_complete_solution`, `balance_or_real_top_of_fake`) |

**The FE axis [L*]; [D].** A fake two-sided edit has defect energy at least `(A²/(256πp₀))T log T`, with `p₀` its least deleted prime and `A` its density; its defect is not bounded and not `≤c√log|t|` for small `c`. If `Θ<1` fake edits with mean defect below `cT^{2α}` exist for every `α>0`. The least deleted prime can be arbitrarily large at a fixed fake zero (log §4.3). So the cost of a fake zero on the FE axis is the cost of the edit that carries it.

**The door [D].** Among unit multiplicities the reflection selects ζ at every rate of decay; among positive real weights no growth bound short of boundedness selects anything. A proof of AAL, B13 or Landing may use unit multiplicity together with the reflection up to a decaying error, or the count: a zero of an edit exponential above twice its count exponent (and above its continuation and summability exponents) has even order, and the greedy pair twin at `ρ` has count exponent at least `Re ρ/2` [L*] (`even_order_of_count`, `half_re_le_of_count_edit`). Every other combination of the three structures holds for a model with a layer.

### 1.4 Two worlds, three atoms
`Θ≤7/8` [X]; `Θ<1⇔Θ∞<1` [L*]. A failure of RH is world I (a finite isolated top layer at `β≤7/8`) or world II (a tail). RH ⇔ ZAL ∧ B13 ∧ Landing; B13 ⇔ the packet index is `0` or `∞`; AAL ⇔ at most one or infinitely many zeros right of every line [L*] (log §4.10). In world I `ψ(x)−x` attains `x^β` on every late window [F]; the Gaussian Möbius and Liouville signals have top-residue asymptotics with leading coefficients related by `ζ(2ρ)` [L*] (log §4.7).

**Receivers of AAL are recurrent [L*]; [D].** Level-one positivity of the constant vector on infinitely many dyadic prime shells `(N,2N]` gives AAL (`asymptoticAbscissaLaw_of_frequently_jasConstProductPositiveOn_shell`); under a maximal off-line zero that positivity fails eventually (`not_frequently_jasConstProductPositiveOn_shell_of_maximal_offLine`). Floors at every bounded length give AAL (`asymptoticAbscissaLaw_of_lengthDependent_floors`). Every exact form of RH quantifies over all windows and all vectors; AAL has receivers for one vector infinitely often.

### 1.5 Off the scale: each kind has a receiver and a kill
| Kind | Receiver | Kill | Evidence |
|---|---|---|---|
| homogeneous floor | a Green–Weil energy floor gives RH | the clock lies below Weil's form | [L*]/[F] |
| unit gap | an index-one approximant or realization gives RH | the tower quotient has a unit gap iff RH | [L*] |
| certificate | feasible weights at every aperture give RH | certificates converge to `Λ` | [L*] |
| amplification | one exponent for all even moments gives AAL | all orders are sup bounds | [F] |
| symmetrization | a functional decreasing under projection | monotonicity under every small split forces a concave gradient symbol | [L*] |
| replication | a bounded normalization of translates gives AAL | under a finite layer the normalization tends to zero | [L*] |
| the count as a power | — | fakes at every exponent above `½` | [L*] |
| the FE as a growth bound | decay forces the primes among unit multiplicities | slow defects among positive weights; a bounded defect among signed weights | [L*] |
| prime edits with a count rate | — | floor `≥13/30` | [L*] |
| a fixed number of charges | the gluing law | rank of the binding proportional to the block size | [L*] |
| sizes of the contacts | — | weakened contacts hold two bound states | [L*] |

### 1.6 The producer: a theorem at `7/8`, a reach of `2/3`, a frame of `3/5` at every period
`Θ≤7/8` [X]. Its mechanism: a completed sum of cubic Gauss-sum coefficients over the twists of ζ over `ℚ(ζ₃)` is bounded directly and compared with its signal; two estimates give a half-plane [L*] (`zetaZeroAbscissa_le_of_two_estimates`, `heckeHalfPlane_of_family_corrected_signal`).

**The frame [L*] (log §4.6, §4.8, §4.10).** The correction factors through a sextic Grössencharacter `L`-function at `6s−3`. A zero `ρ` of a Hecke `L`-function with estimates below `Re ρ` forces a zero of that `L`-function at `6ρ−3`. The continued correction has infinitely many zeros in `7/12≤Re s<2/3`. With estimates for the whole tower, `Θ≤max(σ₀,3/5)`; under GRH for the sextic Grössencharacters, down to `7/12`. Every `6r`-periodic Gauss pairing has coupled fixed point `(4r−1)/(6r−1)≥3/5`, with equality iff `r=1` (`gauss_pairing_6r_thresholds`). Completed estimates and unlimited iteration of the transfer do not pass `3/5` [F].

**The estimates [L*]/[KR].**

| Statement | Half-plane at twist order six |
|---|---|
| floor bin summed trivially | `13/15` |
| every Cauchy–Schwarz row sieve | `5/6` (`two_le_of_sieve_threshold`) |
| square-root cancellation across the rows | `2/3` (`signedGram_phase_endpoints`) |
| corner of the design with rows of conductor exponent two | `8/9` (`corner_two_six`) |
| binding bin at `7/8` | endpoint exponent `−7/30672`; positive if the boundary is `≤7/8−1/4000` |

Short columns are incoherent, the average row is target-free, the root number of a row is the theta phase times a square; the theta-square series on the cubic cover has a double pole at `4/3` and its rotated correlations read only the three-divisible layer [L*] (log §4.10).

**The half-plane in the Lean source [S] (log §4.14).** `ζ(s)≠0` for `Re s>7/8` (`riemannZeta_ne_zero_of_seven_eighths_lt_re`); `L(s,χ)≠0` there for every Dirichlet character (`DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`); every zero of ζ with `Re s>0` has real part in `[1/8,7/8]` (`riemannZeta_zero_mem_quasiRH_strip`). The assembly: certified detector bands from a capped width induction; the inverse, marked plain and unmarked plain moment batches; the common probe; `beta ≤ 7/8` for the Hecke family over `ℚ(√−3)`; norm base change to the Dirichlet characters. The statements carry no hypothesis. The frontier map grades the source as written, not verified: validation of the producer and dependency chain is work (A118).

### 1.7 Finite scale: index, bound states, binding
- Certified [L*]: exactly one bound state on every window with `R≤J`, `50J≤53R`, at every block size; none on narrow windows `16J≤R`, where the neutral part is positive definite and the block potential exceeds one; margins `1/20` on the first step packets of ratio four; at most `300000` negative squares of the block matrix at ratio four (log §4.7, §4.9, §4.10).
- Gluing [L*]: one bound state of two charge-coupled matrices iff the susceptibility product is `≥1`; brackets by lowered and raised potentials; response-matrix inertia for several charges; the sum of the indices of two windows raised by their mutual couplings is at most the index of the union. On positive definite windows the susceptibility criterion is satisfied by opposite-sign spike charges with arbitrary product and carries no information [L*]; [D] (log §4.9).
- Binding [L*]; [D]: on the half-constant plane at ratio four the neutral part is `−(Ds²+2(J+K_ω)st+2Dt²)`, `K_ω=ω(2)log 2+ω(3)(log 3)/3`. Numerically `D≈1.199`, `J≈1.182`, `K≈1.059`: the jets alone leave the antisymmetric combination bound (`−D+J/√2≈−0.36`), the contacts of 2 and 3 unbind it (`+0.39`); binding of that plane needs `ω>0.485` (log §5, §5.1). The contact of 2 joins every block of `(2R,4R]` to a block of `(R,2R]`: its rank is proportional to `R`.
- Regimes [doc]; [D]: the negative of the neutral part is a Metzler form. Narrow windows are its stability regime; windows of ratio `≥2` are its hyperbolic regime, in which one positive square ⇔ the trickle-down inequality ⇔ hyperbolic links. At small widths the atomic form is hyperbolic for every completely multiplicative sign twin (log §4.11).
- No unconditional sign theorem of the corpus uses a prime contact [D]: below ratio two the contacts vanish, the certified range ends at ratio `103/50`, and the first window whose sign needs the true contact of 2 is ratio three (log §5.1).
- Number rings and characters [L*]: the index counts the zeros off the line for Dedekind zeta functions of abelian rings, quotients, relative squares, powers and virtual configurations; every Artin Euler product is a product of integer powers of abelian Euler products; reciprocity holds for cyclotomic characters (log §4.5, §4.9, §4.10).

### 1.8 The critical half-line state
RH, or a finite critical ratio `W₀` with a critical state `F`; RH, or `R_polar<W₀`, or `∫F·polarSourceProfile=0` for every critical state [L*] (log §4.2). At every ratio `R>0` the unit-mass floor is attained, the minimizer is unique up to sign, its Laplace transform has no zero on `Re z>0`; the floor is strictly concave in `1/R` and the eighth-exponential mass of the minimizers is strictly decreasing. At `W₀`: the floor vanishes with derivative `−a(W₀)∫F²e^{−8u}/W₀`; the Laplace transform is nonzero on `Re z≥0`; the multiplier is outer; the causal translates are dense; every terminal interval carries mass; distance and polar pairing are stable along the branch; the polar residual is bounded by the critical energy. Strong confinement, `a=a(R)→∞`: `λ(R)−a−log a→μ`, the infimum of the logarithmic form with linear confinement; every rescaled minimizer approaches this floor, `a·δ_R→1`, and `a·∫(−u)F²→1/8`, uniformly over the minimizers [L*] (`universal_softLogarithmic_confinement_limit`; [paper proof and completed Lean audit](../../drafts/pipeline/3-formalized/universal-soft-logarithmic-confinement-limit.md)). All eighteen supporting modules pass plain source audits with only the standard three axioms and are integrated. Attainment of `μ` and convergence to a limiting profile remain open. Every one of these properties holds whether the state is charged or not: the polar pairing is undecided.

Every unit Rayleigh sublevel of the soft logarithmic trial domain has compact `L²` closure [L*] (`isCompact_closure_softLogarithmicRayleighSublevel`; [proof and Lean status](../../drafts/pipeline/1-in-progress/soft-logarithmic-profile-compactness-and-sign.md)). Uniform negative-logarithmic Fourier tails give coercivity; physical and positive logarithmic moments then control both cutoff errors. The final plain source audit passes with only the standard three axioms, and the module is integrated. Closed-domain recovery and sign rigidity remain open.

Further objects that exist exactly when RH fails [L*] (log §4.1, §4.4, §4.10): a sign-changing bound state of some window; a positive real branch time; an odd bound state; a defective hard-edge block; a point right of the line with `Re ξ′/ξ<0`; a negative definite Markov plane; an aperture with an empty feasible set.

### 1.9 The zero field and the heat cover
- **Field [L*] (log §4.4, §4.8, §4.10).** The centred zero field is algebraic and normal over the field of complete-fibre traces; `K_even⊆ℝ` ⇔ reflection field = prime trace field ⇔ RH; the action is not transitive; a zero with rational real part has the orbit `{ρ,ρ̄}`. The degree-`2n` centred Jensen equation has the full signed-permutation group `C₂≀S_n` over its coefficient field, or a nonzero rational polynomial relation holds among its normalized moments. Every ordering of the squared-width field induces complex conjugation iff every squared width is a sum of squares there.
- **Cover [L*] (log §4.4, §4.9, §4.11, §4.13, §4.14).** Every zero of the centre value `H_τ(0)` has `Re τ>0`; the central branch times are infinitely many and none is real; the turn around a central collision carries a zero `z` to `−z`, so the functional-equation reflection is its local monodromy. On a box `t₀≤Re τ`, `‖τ‖≤T₀` the far zeros are simple and the branch times finitely many; no zero escapes along a path of forward times; transport along branch-free forward paths is a bijection of fibres; the forward monodromy group commutes with `z↦−z` and is the same group at every base time; from every positive real non-branch time a forward path leads to the time `1/8`, at which all zeros are real.
- **Two involutions [L*]; [D].** The turn around a collision at a forward time transports the zero on each Hermite sheet to the zero on the opposite sheet and has order two. Every forward branch time gives an element `≠1` of the group at every base time; a centre time gives an element with `σp=−p≠p`; a collision away from the centre gives an element with `σp≠p`, `σp≠−p`; if every element preserves every pair `{z,−z}`, RH holds [L*] (`IsCollision.exists_transports_turn`, `exists_mem_forwardMonodromy_flip`, `exists_mem_forwardMonodromy_moving_pair`, `riemannHypothesis_of_forwardMonodromy_preserves_pairs`). A collision of order `m` has `⌊m/2⌋` transposed pairs of sheets, and before a real collision the local monodromy is conjugation [doc]. Conjugation over a real time fixes the real zeros and exchanges the two pairs of every nonreal quartet [D].
- **The time of ζ [L*].** `0` is a limit of real branch times, or along every short real segment across `0` infinitely many nonreal zeros escape. No statement controls transport as `τ→0` [F].

### 1.10 Verification
RH through `exp(exp(C·a))` gives the sign on `[−a,a]`; `C` is not explicit; the explicit `windowHeight` contains `exp(winE+2π)` and `48^{2n}`. RH is verified through height 67. The margin transfer from the first blocks to every block size at ratio four needs `log R≥2.5·10⁴` at the proved margin [L*]; [D] (log §4.7, §4.11, §5). Positivity at aperture `a` confines every zero with `T₀≤|γ|≤2πe^a` to depth `<exp(−c log³|γ|)` [L*].

### 1.11 Law and point
One pointwise theorem holds past the Vinogradov–Korobov region: no zero right of `7/8` [X]. Left of it every unconditional theorem on the zeros of ξ and on the Liouville function is in law [L*]: twisted moments below the square root and a positive proportion of critical zeros; `0.67250071` simple critical zeros in the objects of `Zeta23`; positive proportions of runs of four and of five consecutive simple critical zeros; adaptive clusters with complete exterior mass `≤¼`; short-interval mean squares of `λ` and `λχ`; `(log x)^{−1}Σ_{n≤x}λ(n)λ(n+h)/n→0` for every `h≥1`; a bounded inner field, equivalent to depth density `O(T)` (log §4.5, §4.8, §4.9, §4.10). Logarithmic correlation decay supplies no half-power rate [F].

### 1.12 Producers and receivers
| Mechanism | What the corpus proves |
|---|---|
| surfaces, sections, Riemann–Roch | identities; the square counts linearly |
| bounded-below heights | counts on prime rays ⇔ RH |
| families with monodromy | fixed parts; the heat cover with conjugation as a monodromy |
| Frobenius with zero derivative | `p^{11/12}` at one prime [F] |
| dominance in an ultrametric field | the Goss Riemann hypothesis |
| deformation, regulators | RH at every parameter; the count of the limit |
| recurrence | strong recurrence ⇔ RH; zero limits at a finite layer |
| sizes | the trivial aperture |
| the count as a power; prime edits | fakes at every exponent above `½` |
| the FE with the Euler product | rigidity at any decay among unit multiplicities; slow defects among positive weights |
| gluing of windows | the law; through finitely many charges it fails beyond block size one |
| binding by the contacts | necessary: weakened contacts fail; sufficient: open |
| critical compactness | a unique, outer, cyclic, stable critical state |
| congruence arithmetic of the horizon | `λ₁≥3/16`, attained by the theta function in weight `½` |
| mean values, correlations | in law |
| reciprocity families with two estimates | `Re s>7/8` [X]; reach `2/3`; frame `≥3/5` at every period |

**Consequence [D].** One mechanism has produced a pointwise theorem, and its class of `6r`-periodic Gauss pairings stops above `½`. Every other mechanism of the corpus is a receiver, a model or a rigidity theorem.

### 1.13 What is ruled out
| Mechanism | Verdict | Evidence |
|---|---|---|
| explicit formula, positivity, Euler products over integer norms or the rational primes with multiplicities `0,1,2` and a count rate, as a constraint on a finite layer, a tail, landing | realized by models | [L*] |
| the functional equation as a growth bound on the defect, among positive weights | systems with off-line zeros below every `Φ→∞` | [L*] |
| the functional equation up to an error of mean size `T^ε`, among edits | fake edits if `Θ<1` | [L*] |
| boundedness of the FE defect as a selector among signed weights | a signed fake with bounded defect | [L*] |
| induction on the ratio through one pair of charges, or through a model of the coupling of bounded rank | index `≥2` of the lowered model beyond block size one; rank `r` fails for `600(r+1)≤H` | [L*] |
| a sign of the windows of ratio three and four from the sizes of the contacts, or for a sign twin | weakened and Liouville-twisted contacts hold two bound states | [L*] |
| the susceptibility criterion on positive definite windows | satisfied with arbitrary product | [L*] |
| an exponent below `3/5` from the frame of a `6r`-periodic Gauss pairing, or below `2/3` without estimates beyond square root | the coupled tower; the uncoupled boundary | [L*]; [D] |
| a Cauchy–Schwarz row sieve below `5/6` | budget | [L*] |
| windows below the logarithmic radius; one-sided floors of one length | models | [L*]/[F] |
| regulators, paths, certificates, amplification, replication, symmetrization as sources | kills | [L*]/[F] |
| an improvement of `3/16` by an argument whose inputs hold in weight `½` | the theta function | [L*]; [doc] |
| a transitive Galois action on the zeros; group membership of conjugation as a constraint | not transitive; conjugation is a monodromy whether or not RH holds | [L*] |
| triviality of the whole forward monodromy group | at every base time a loop exchanges some zero `z≠0` with `−z` | [KR]; [L*] |
| half-power rates from logarithmic correlations | none | [F] |

### 1.14 The small primes [D]
The three cores meet at 2 and 3. On the sign side the contacts of 2 and 3 are the binding of every window of ratio three and four. On the precision side the producer is a sum of cubic and sextic Gauss sums over `ℚ(ζ₃)`. On the selection side the least deleted prime sets the constant of the defect energy of a fake. As receivers two primes suffice: two-prime lags decide RH, and every off-line zero gives a negative heat test on `log 2` or `log 3` [F]. As a producer the contact of 2 has rank proportional to the block size. Sampling by two primes is cheap; binding by two primes is the open sign.

## 2.1 Tasks that are just work

Difficulty is established where a known argument exists; `(unverified)` marks the rest. None of these decides RH.

### The half-plane `7/8`: validation, receivers, other fields
| # | Task | Routes | Basis |
|---|---|---|---|
| A118 | validation of the complete producer and dependency chain of the hypothesis-free `7/8` assembly | JAS, MC, S3 | `ProbeFinalAssemblyUnconditional.common_probe`, `riemannZeta_zero_mem_quasiRH_strip` [S]; [F] |
| A138 | the corollaries of `Θ≤7/8` on the receivers as Lean statements: rung `κ<4/3`, returns `y^{1/8}`, ringdown `1/16`, critical-comb growth `≤3/8`, fake edits with subpolynomial defect energy at every `½<β₀<5/8` | every scale route | `riemannZeta_zero_mem_quasiRH_strip`; §1.2; `frontier_dichotomy` |
| A141 | the half-plane for fields containing `ζ₃` and every ray class character (unverified) [C] | ACS, HF | frame for every Hecke character |

### Models and laws of world I
| # | Task | Routes | Basis |
|---|---|---|---|
| A155 | the order law at every multiple `k≥3` (unverified) | ZCG | `even_order_of_count` (`k=2`) |
| A157 | the count of the signed grouped edit by Perron's formula left of `½` (unverified) | ZCG, BAG | `sub_one_mul_zetaSeriesC_eq`, `differentiableOn_editCofactor` |
| A144 | the tangent data of `μ` and `λ` under additive twists (unverified) | ZCG, MC | tangent data under `Θ∞<Θ` [L*] |
| A120 | a finite nonempty stratum with both structures: Selberg zeta functions of surfaces with a small eigenvalue [C] | BAG, ZCG | — |

### The producer's estimates and its calibration
| # | Task | Routes | Basis |
|---|---|---|---|
| A148 | the layers `m=0,1` of the theta-square series and the target component of a twisted column [C] | MC, JAS, PM | `thetaSqDirichlet_double_pole`, `rotatedCorrelation_eq_three_layer` |
| A149 | the floor bin over `𝔽_q[T]`, `q≡1 mod 6`, with the long columns evaluated exactly (unverified) [C] | MC, JAS | CRF |

### Assemblies of proved pieces
| # | Task | Routes | Basis |
|---|---|---|---|
| A142 | an explicit constant in the verification rate `exp(exp(C·a))` | RW, SRT, TH, LI, HCF | `exists_doubleExp_windowPositive`, `windowPositiveAt_of_rhVerifiedThrough` |
| A154 | the reciprocity law for a general abelian extension: from the second inequality in unit form (in Lean for cyclic extensions) to ideal classes, Artin's lemma, triviality of the Artin map on a ray; with the abelian product form it gives the index of every Artin character [C] | ACS, HF | `exists_artinEulerProduct_eq_prod_zpow_abelian`; `card_dvd_index_norm_sup_congruence_sup_sUnits`; `map_artinMap_eq_artinMap_idealNormHom`; norm index and Herbrand quotients for cyclic extensions |
| A158 | attainment of the limiting infimum and convergence of the rescaled profiles remain open; compactness of unit Rayleigh sublevels and the strong-confinement energy, excess, and width limits are verified and integrated | HF | `isCompact_closure_softLogarithmicRayleighSublevel`, `universal_softLogarithmic_confinement_limit` [L*]; §1.8 |
| A140 | the sign on windows of half-width below `½log 5` (unverified) | RW, ACT, EWU, OWU | [F] |

### Finite verification and explicit constants
A1 certified `RHVerifiedThrough T` past 67; A2, A3 numeric heights and first-window membership; A4, A5 theta ranks 15 and beyond (unverified); A6, A7 cone widths, anti-diagonal certificates (unverified); A9, A13 eighth-root constants, near-gcd charges (unverified); A117 end points of the feasible interval of `w(2)`; A19 an explicit heat-horizon height; A48, A58 Hasse–Weil tests, effective gap iteration (unverified).

### Classical inputs to formalize
| # | Task | Basis |
|---|---|---|
| A18 | twisted second moments past the square root [C] | `θ<½` in Lean |
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | `weyl_law_order` |
| A33 | Fourier coefficients of the cubic residue at all heights [C] | [F] |
| A41 | count law for every curve, first plane quartics [C] | hyperelliptic case [F] |

Further: A16, A20, A24, A28, A30, A42, A46, A54 (unverified).

## 2.2 Open mathematical obstacles

`≥qRH`: implies a zero-free half-plane, Lindelöf or ZAL; with `[X]` open where it gives a half-plane below `7/8`.

### The common minimal face
| # | Problem | Strength | Routes |
|---|---|---|---|
| B130 | `P(p)≤A(p)+K` on the primes of late logarithmic windows; in two-prime form on windows of radius `r√T` | RH | ACS, SRT, WL, HF, ZCG, HAT-C |
| B159 | a rung `κ≥4/3` with a saving that fails for the Liouville twist | a half-plane below `7/8` | sign routes, BAG |
| B144 | separation of the deep off-line ordinates | sub | SRT, ACS |

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1, B152 | the sign on every window; the Hodge inequality on positive packets at every ratio and block size | RH | all sign routes; ACS, HF |
| B192 | the first selective sign: one bound state of `(R,3R]` and of `(R,4R]` at every block size, proved from the true contacts of 2 and 3 (§2.21) | sub at each ratio; method | ACS, HF, RW |
| B2, B4, B5 | no crossing along the aperture; outer predictors; kick admission | RH | RW, GWZ, WTZ |
| B6, B8, B101 | full-space sign at every critical multiple; head thresholds; polar payment | RH | HF, SRT, AIP |
| B104 | whether the critical half-line state is charged (§2.8) | method | HF, SRT, AIP, ACS, SC |
| B123, B156 | correlated pairings dominating the depleted kernel; cluster exclusion on a rung | method | HF; SA, RW |
| B160 | `JasDressedPSD 1` | RH | JAS |
| B9–B12, B14, B23 | zero mode; top stratum; exact SOS; index ceiling; interior width; `N_d` bounded (⇔ finite off-line support) | RH / ≥qRH | HF, SC, ACS, CHMD, LA |
| B16, B17, B3 | decay law of the margin; signed ground states; variation of `r` | sub / method | CHT, RW |
| B19–B22, B24, B25, B102 | theta ranks and heads; outer Jensen roots; collisions at small time; frequency below one | RH | TH, LA, ZCG |
| B27, B28, B47 | runs of simple critical zeros longer than five; local positivity at fixed `λ`; multiplicity | sub | ZCG, RW |
| B29–B45 | the single open estimates of PTR, HCF, PA, XN, GTA, TT, CHMD, RN, SZ, TG, SC, ACS, HF, FU/CFC/RP, LI, ACT, AIP | RH | as named |
| B124 | finite initial depth budgets of the heat divisor | ≥qRH to RH | ZCG, LA |
| B146, B171 | an independent family of bounded index; a form of signature `(1,∞)` | RH (producer) | W1C, PTR, IRP, PM |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B161 | a signal bound `O(Z^b)` for some `b<7/8` | a half-plane below `7/8` | JAS, MC |
| B174 | the row count of the binding bin | a half-plane in `[13/15,7/8)` | JAS, MC |
| B185 | the long columns: a power saving in the first moment of the root numbers against a dual column, uniformly in the column (§2.4) | a half-plane in `(2/3,13/15)` | JAS, MC |
| B187 | a Möbius-signed pairing outside the `6r`-periodic Gauss pairings with coupled fixed point below `3/5`, or with uncoupled boundary `½` (§2.5) | producer | JAS, MC, every scale route |
| B180 | the reflection of the completed theta row without Eisenstein series | method | JAS, MC |
| B48–B54 | the deciding input at square-root precision and its faces | RH | WL, MC, SQF, JAS, CTF, PBM, RB |
| B55, B67 | polynomial stencil rate; parity at power saving | ≥qRH to RH | WL, MC |
| B56 | `Θ<1⇒Θ=½`; with `[X]` it is RH | RH | whole programme |
| B57–B61 | depth density `o(T)`; `D_win`; pointwise prime cost of adaptive cameras; Green moments; a detector past the last scale | sub | WD, MC, ZCG |
| B62, B63, B66, B91 | cofinal long moment; collision charge; near-unit budgets; cut-kernel mass | RH | WD, CTF, AIF, RAC |
| B46, B97, B121, B137 | savings at length `(log X)^{2K}`; first return past VK; freezing; collective depth floor | sub | BAG, PTT, TAPO, TTPO |
| B106 | a correspondence on the orientation cover with bounded local indices | RH | MC, HAT |
| B110, B126, B127 | thick crude count; sampling set; lag recurrence | AAL | WL, ZCG, ACS, IWT |
| B145 | the prime-weighted centred type-II current at a growing isolated mode | AAL [D] | ZCG, BAG, ELT |
| B150 | arithmetic control beyond frequency one | sub | census |
| B173 | a two-sided subexponential bound of the trace on windows of one length | AAL | ZCG |

### Γ — selection, reflection, position
| # | Problem | Strength | Routes |
|---|---|---|---|
| B13, B138, B141 | finite stratum; landing; Deuring–Heilbronn for ζ | sub | whole programme |
| B83, B170 | AAL; non-attainment for ζ | sub / AAL | BAG, JAS, SC, ZCG, WL |
| B157 | what excludes a finite stratum when both structures are present | method | BAG, ZCG, ELT |
| B183 | a fake with count exponent `β<½` and a non-real pair alone on top; it must be balanced | method | WL, MC, BAG, ZCG |
| B191 | a unit-multiplicity fake with subpolynomial defect energy at `β₀≥3/2−Θ`; the order of the least defect energy between `T log T` and `T^{1+ε}`; whether a bounded defect forces the rational primes among unit multiplicities | method | ZCG, BAG |
| B190 | the orbit of a zero with irrational real part under the embeddings fixing the prime trace field | method | LA, ZCG |
| B193 | the forward monodromy group of the heat cover: a collision away from the centre at a forward time (it gives an element that moves a pair; a group without such elements gives RH [L*]); generators; transitivity on the pairs `{z,−z}`; control of transport as `τ→0` (§2.6, §2.19) | method | ZCG, LA |
| B89, B112, B128 | aligned returns; FE into vertical transport; replication | sub | BAG, ZCG, EFT |
| B68, B71, B178 | reflection Krein positivity; universal decay; a rate from the horizon | RH; producer | PM |
| B188 | a mechanism for the scattering resonances whose inputs fail in weight `½` (§2.7) | producer | PM |
| B69, B72–B76, B80, B81 | lossless stack; target mass; candidate landings; FE twins | RH / sub / producer | PTR, BAG, SEL, candidates |
| B86, B87, B88 | endpoint characters; a count defined without `Q`; the sign of the comb finite part | RH | ECP, ACS, HF, PM |
| B114, B117, B147 | partner involution; a regulator with a gap; Shimura nonvanishing | producer; indep. | PM |
| B149, B169 | Bézout from a property of the object; a doubling with a canonical height | RH (producer) | ACS, HF, AGZ |
| B172 | a functional decreasing under projection outside the finite-statistics class | producer | ZCG, HF |
| — | ZAL | ≥qRH | whole programme |

### Settled questions
| # | Question | Answer | Evidence |
|---|---|---|---|
| B189 | Do the halves of a window of ratio four glue through their charges? | only at block size one: for `R≥2` every admissible charge pair has susceptibility product `<1` and a lowered model of index `≥2`; rank two glues at `R=2`; rank `r` fails for `600(r+1)≤H` | [L*] (`halves_of_ratio_four_glue_iff_eq_one`, `two_le_hermNegIndex_lowered_model_of_rank`) |
| A156 | the susceptibilities of the certified windows | narrow windows are positive definite; the criterion is satisfied there with arbitrary product and is uninformative | [L*] (`exists_narrow_admissible_susceptibility_mul_ge`) |
| A146 | the index at ratio four at every block size by transfer or verification | the transfer threshold is `log R≥2.5·10⁴`; the window height is double exponential; the question is B192 | [L*]; [D] |
| A147 | logarithmic two-point Chowla | `(log x)^{−1}Σλ(n)λ(n+h)/n→0` for every `h≥1`; short-interval mean squares of `λ` | [L*] (`tendsto_logAvg_liouville_shift`) |
| A153 | FE rigidity of unit-multiplicity systems and slow defects of positive weights | rigidity at every decay exponent; arbitrarily slow defects with prescribed off-line zeros | [L*] (`beurlingSystem_rigidity_of_decaying_defect`, `exists_positiveWeighted_beurling_slow_defect`) |
| — | Which group do the zeros of the heat family generate along the flow? | over forward times transport is bijective and loops give a group of signed permutations of the pairs, the same at every base time; conjugation over a positive real time is an element; RH ⇔ it is trivial | [L*] (`forwardMonodromy`, `fibreConj_mem_forwardMonodromy`, `riemannHypothesis_iff_fibreConj_eq_one`, `nonempty_mulEquiv_forwardMonodromy`) |
| — | Is the forward monodromy group trivial, and what does a branch time contribute? | not trivial: every forward branch time gives an element `≠1`, a centre time an element exchanging some zero `z≠0` with `−z`; a group that preserves every pair gives RH; transport depends only on the homotopy class of the path | [L*]; [KR] (`forwardMonodromy_ne_bot`, `transports_of_homotopy`, `exists_mem_forwardMonodromy_ne_one_of_mem_branchTimes`, `riemannHypothesis_of_forwardMonodromy_preserves_pairs`) |
| — | The group of one Jensen equation | full signed-permutation group, or a rational relation among the normalized moments | [L*] (`jensenGal_full_or_exists_moment_relation`) |
| — | Is one bound state a Hodge index inequality? | yes: on positive packets without common blocks; equivalently one-sign bound states | [L*] |
| — | Do the sizes of the contacts bind a window? | no: weights in `[−5/2,19/40]` leave two bound states at ratio four | [L*] |
| — | Is `3/16` improvable by the congruence mechanism? | not by inputs valid in weight `½`: the theta function has eigenvalue `3/16` | [L*]; [doc] |
| B186, B184, B179, B175, B176, B182, A150, A151, A152 | cost of a fake zero; reach of the frame; Maslov index; signed cancellation in the floor bin; cost of a window; least count remainder; Brauer induction; twin defects; convergence of power combs | as stated in §1 and in the walls ledger | [L*] |

## 2.3 Frankenstein routes

**No assembly closes RH.** One assembly is a theorem (`[X]`). Every other assembly has an open input of RH or AAL strength, a half-plane input, or returns an identity.

| # | Parts | What the assembly gives | Missing input | Gain |
|---|---|---|---|---|
| F29 | **One scale** | every graded receiver is one number; the critical comb reads it on one sequence | a level below `7/8`; in Lean any level | a proposed estimate is placed before work starts |
| F30 | **Two estimates, fully evaluated.** Frame, coupled tower, barrier at every period, budget, coherence, theta-square poles | `[X]`; with square-root cancellation `2/3`; frame `≥3/5` for every `6r`-periodic pairing [L*]; [D] | A118; B174, B185; B187 | the exact reach of the only producer class |
| F31 | **Half-plane, then line** | rung `4/3`, returns `y^{1/8}` | a step from a strip to the line | none: every transfer is RH |
| F39 | **The index at three scales.** Finite-scale neutral part, index law in the aperture, verification rate | RH ⇔ no crossing ⇔ the Hodge inequality on every window; certified on ratio `≤103/50` and narrow windows [L*] | B152 | one exact finite object per window |
| F44 | **Gluing induction.** Certified windows, gluing law, brackets, response matrices | through one pair of charges the step exists only at block size one; through rank `r` it fails for `600(r+1)≤H` [L*] | a step of rank proportional to the block size (B192) | the induction on the ratio is not a recursion for finitely many numbers |
| F46 | **Binding along the floor trees.** Metzler dichotomy, weakened contacts, rank law, ground-state transform | one bound state ⇔ spectral gap of the Doob chain at least the binding energy [D]; false without the true contacts of 2 and 3 [L*] | B192 | the induction step as a Poincaré inequality on an explicit chain |
| F45 | **The critical object.** Thresholds, the critical state with its energy branch, index law, objects of a failure | a failure of RH has a unique, outer, cyclic, stable extremal function [L*] | B104 | the place where a contradiction on the Σ side has to act |
| F40 | **Models plus rigidity.** Two-sided edits, positive-weighted systems, signed weights, rigidity at any decay, Abel floors, count laws | the door of world I: unit multiplicity with the reflection up to a decaying error, or a count below half a layer [D] | B170, B145, B183, B191 | a proposed AAL argument is tested on the models before work starts |
| F41 | **World I off the scale.** Non-attainment, unit gap, filters, currents, tangent data, shell signs | AAL from any receiver form, among them one vector infinitely often [L*]/[F] | B170, B145 | — |
| F42 | **The lattice with a level.** Index law for number rings, quotients, powers; abelian product form; `[X]` | the index of an Artin Euler product counts zeros and poles of abelian `L`-functions in one strip [D] | A141, A154 | the index of every comb counts zeros in one strip |
| F47 | **The cover with a real structure.** Zero field, Jensen equations, heat cover, forward monodromy, conjugation | RH ⇔ one distinguished involution of a group of signed permutations is trivial; a group that preserves every pair `{z,−z}` gives RH [L*] | B193; a restriction on the group | a sign-free exact form |
| F37 | **Verification with a rate** | window sign from a double-exponential height | A142 | finite statements with stated sizes |
| F38 | **Mean values, correlations, cameras** | a positive proportion on the line; runs of simple zeros; logarithmic Chowla; short-interval mean squares; adaptive isolation of deep zeros [L*] | A18; B59 | the in-law half is native |
| F11 | **Construct, then identify** | an approximant with a gap gives RH | B146, B171 | regulators excluded |

**Closest to the open core:** F46 (the induction step of Σ in the form that survives the rank law), F30 (the producer's exact reach), F40 (the door of world I), F47 (the sign-free form).

### What a contradiction search may assume in world I
`Θ≤7/8` [X]; an attained isolated top `β≤7/8`; `ψ(x)−x` attains `x^β` on every late window [F]; top-residue asymptotics of the Möbius and Liouville signals with nonzero leading coefficients related by `ζ(2ρ)` [L*]; the level-one constant-vector sign fails on all late dyadic prime shells [L*]; normalizations of translates tend to zero [L*]; the packet index is finite and positive [L*]; a two-sided edit with a count rate above the top removes the layer [L*]; the critical half-line state exists, unique, outer and cyclic [L*]; a positive real branch time exists [L*]. No contradiction comes from identities alone, positivity, Euler products over integer norms or the rational primes with multiplicities `0,1,2`, a count rate, the FE with Gamma factor and count, the FE as a growth bound among positive weights, a regulator, or any statement in law [L*].

## Validation tests for 2.4–2.8 and 2.21

| Test | Requirement |
|---|---|
| T1 | implied by RH (or GRH for the family at hand) and implying neither RH nor AAL; or a method question implied by nothing about ζ's zeros. A half-plane below `7/8` satisfies T1 |
| T2 | answered by proving or refuting a stated inequality, identity, existence or implication |
| T3 | a named consequence for either answer |
| T4 | not decided by a finite rung |
| T5 | false on a corpus model, or calibrated on the models |
| T6 | names an input not refuted in Lean |
| T7 | moves a wall; not a shape answered in Lean |
| T8 | not a named long-standing problem in disguise; a first step in corpus objects with one named obstacle |

**No statement about the zeros of ζ below RH and AAL passes all tests as a door to the line.** The questions below were checked against the corpus by sentence queries (log §4.13, §5).

## 2.4 Breakthrough question below RH and below the half-plane `7/8`: the long columns (B185)

**Position.** The only producer of the corpus converts a law over a family of twists into a point by two estimates. Everything it does with squares stops at `13/15`, then at `5/6` (§1.6). Its floor bin is reduced in Lean to one object: the short columns cancel (`sum_pairColumn_eq_zero`), the short Gram is bounded (`norm_gramEntry_le`), the average row is target-free (`average_rowLocalSum`), the root number of a row is the theta phase times a square (`rowRootNumber_eq_thetaPhase_mul_sq`) [L*]. What is left are the long columns: first moments over the rows of the root numbers against a dual column [D]. Their untwisted main term is a theorem: the theta-square series has a double pole at `4/3` [L*] (log §4.7, §4.10). No declaration bounds a twisted long column (log §5).

**Question (B185).** *Is the first moment of the row root numbers over squarefree rows of norm up to `U`, twisted by a dual column `n` of norm up to the row scale, equal to its main term plus `O(N(n)^A U^{R₀+ε})` with some `R₀<1`, uniformly in `n`? What is the least such `R₀`?*

| Answer | Effect [D] |
|---|---|
| any `R₀<1` | a half-plane below `13/15`: the first estimate of the producer that is not a square |
| `R₀<5/6` | below the floor `5/6` of every Cauchy–Schwarz row sieve |
| `R₀=½` (square-root remainder) | `2/3`: the uncoupled boundary of every `6r`-periodic pairing, the end of the class |
| no saving uniformly in the column | the producer stops at `13/15` through its floor bin; every graded receiver keeps `[X]` as its only level |

Every receiver of the scale moves with the answer: the rung, the return bound, the ringdown rate, the tails, the critical-comb growth, the range `½<β₀<3/2−Θ` of the fake edits with subpolynomial defect energy.

**First step and obstacle.** A149 (the function-field floor bin [C]) and A148 (the layers `m=0,1` and the target component of a twisted column; the rotated correlation reads only the three-divisible layer [L*]). Named obstacle: uniformity in the column. The large sieve over the Eisenstein integers of the corpus is a square, and every Cauchy–Schwarz row sieve stops at `5/6` [L*] (`eisenstein_largeSieve`, `two_le_of_sieve_threshold`).

**Tests.** T1 passes (an estimate for Gauss sums; its consequence a half-plane below `7/8`). T2, T4, T6 pass. T3 named. T5 calibrated on the average row (target-free), the short columns (incoherent) and the untwisted main term (a double pole). T7 moves the Π walls of the floor bin. T8: the square-root form is a conjecture of Patterson type [C]; any power saving uniformly in the column is the question, with a first step in corpus objects.

**Limit.** `2/3`. The question does not lead to the line.

## 2.5 Breakthrough question for the search for a producer: a pairing whose frame reaches the line (B187)

**Position.** The class of the one producer is closed by two theorems. In the budget, square-root cancellation across rows of conductor exponent two gives the half-plane `1−2/n` at twist order `n` (`signedGram_phase_endpoints`), which is the line exactly at `n=4` [L*]; [D]. In the frame, every `6r`-periodic Gauss pairing has uncoupled boundary `2/3` and coupled fixed point `(4r−1)/(6r−1)≥3/5` (`gauss_pairing_6r_thresholds`) [L*]. Iterating the transfer does not pass `3/5` [F].

**Pairing coordinates [D].** A pairing with local resonance norm `Q^{c−ks}` has uncoupled boundary `(c+1)/k` and coupled map `b↦(c+b)/k` with fixed point `c/(k−1)`. The uncoupled boundary is the line iff `c=k/2−1`; the fixed point is the line iff `c=(k−1)/2`. The Gauss pairings have `c=(2/3)k−1`: the period changes `k` and leaves the ratio `c/k→2/3`. The Möbius sign comes from Gauss sums of odd order [L*] (`exists_gaussSum_pow_orderOf_eq_of_odd`).

**Question (B187).** *Is there an identity that writes the Möbius function through coefficients with a reflection whose local resonance norm `Q^{c−ks}` has `c/(k−1)<3/5` — in the best case `c≤(k−1)/2` — and whose rows have conductor exponent two with twist order four? Or does every Möbius-signed pairing of Gauss and Jacobi sums have `c/k≥2/3−1/k`, so that the class ends at `3/5`?*

| Answer | Effect |
|---|---|
| a pairing with fixed point `½` and a design with square-root endpoint `½` | a producer of the line by estimates: the remaining input is square-root cancellation in its bins |
| a pairing with fixed point in `(½,3/5)` | the frame moves below `3/5`; its estimates and its tower are the next object |
| `c/k≥2/3−1/k` for every Möbius-signed pairing | the Gauss-sum producers end at `3/5` (`2/3` by estimates of square-root size): RH needs a source of another kind |

**First step and obstacle.** Classify the Möbius-signed products of Gauss and Jacobi sums over cyclotomic rings by `(c,k)`: finite algebra in the objects of `exists_prod_jacobiSum_eq`, `exists_gaussSum_mul_gaussSum_eq` and `gauss_pairing_6r_thresholds`. Named obstacle: the theta coefficients of covers of degree four and higher are not known explicitly [C], so the source identity of a design has to be proved before its exponents mean anything.

**Tests.** T1: a producer question, implied by nothing about ζ's zeros. T2: an existence statement or a classification theorem. T3 named. T4 pass. T5 calibrated on the `6r` pairings (a theorem) and on even order (parity instead of sign). T6, T7 pass. T8 not a named problem; the first step is finite algebra in corpus objects.

**Limit.** The coordinates are an exponent model: a pairing that reaches `½` in them needs its source identity, its estimates and its tower.

## 2.6 If positivity, Weil positivity and spectral methods are excluded

"Spectral" covers spectral theory of operators in every form, automorphic spectral theory included; "positivity" covers nonnegativity of forms, kernels, counts, coefficients and averaging measures. Kept: Fourier analysis, exact identities of Gauss and Jacobi sums, reciprocity, mean values used as bounds, continuation and orders of zeros, covers and monodromy, Galois theory, dominance in ultrametric fields.

**What the constraint removes [A].** All of Σ in its matrix forms: the index, the bound states, the binding, the critical state. Landau's theorem and the balance law of edits; the proofs of FE rigidity and of the Abel floors; the large sieves; the Eisenstein reflection of the theta row. **What survives [L*].** RH ⇔ conjugation of the fibre of the heat cover is the trivial element of the forward monodromy group; the structure of the cover over forward times (isolated branch times, Hermite sheets, no escape, bijective transport); the Galois forms `K_even⊆ℝ` ⇔ reflection field = prime trace field ⇔ RH; the Jensen equations with full group or dependent moments; the Goss dominance; the order law of edits; the abelian product form of Artin Euler products and cyclotomic reciprocity; the receivers of the minimal face in absolute value.

**The sign-free exact form [L*]; [D].** Over a positive real time conjugation is an element of the forward monodromy group, trivial iff no positive real branch time exists [L*]; it is the word of the turns around the real branch times between that time and `1/8` [D]. Every element of the group commutes with `z↦−z`, so the group acts by signed permutations of the pairs `{z,−z}`. The centre times, which exist in infinite number and are never real, give elements that carry some zero `z≠0` to `−z` [L*]; the theorem does not say that such an element moves no other pair, and triviality of the whole group is refuted [KR]. Transport depends only on the homotopy class of the forward path [L*], so the group is a quotient of the fundamental group of the forward half-plane without the branch times [D]. An element that moves a pair comes from a collision away from the centre [L*], and no declaration asserts such a collision at a forward time (log §4.14). **If every element of the group preserves every pair, RH holds** [L*] (`riemannHypothesis_of_forwardMonodromy_preserves_pairs`): a failure of RH is a real collision at a positive time, and no real time is a centre time.

**Question (B193).** *Does the forward monodromy group of the heat cover contain an exchange of two pairs: is there a collision away from the centre at a forward time? If so: is the group transitive on the pairs `{z,−z}`, and is it the full restricted group of signed permutations?*

| Answer | Effect |
|---|---|
| no collision away from the centre at any forward time | RH: a failure of RH is a real collision at a positive time, and it is not at the centre [L*]. The statement is stronger than RH, which excludes such collisions on the positive real axis only. Not expected [A]: a collision is one complex equation in one complex time |
| exchanges exist and the group is transitive, or full | the heat cover is in the position of a generic curve over a finite field: a full group of signed permutations in which the Riemann hypothesis is the triviality of one involution [doc]; [C]. The remaining sign-free problem is to characterize the word of conjugation, not the group |
| exchanges exist and the group is intransitive | an invariant of the zeros that is constant along forward loops and defined without a sign: a partition of the pairs. It is the first candidate for a sign-free separation of zeros [A] |

**First step and obstacle.** One collision away from the centre at a forward time: what it gives is a theorem, an element that moves a pair at every base time [L*]. The polynomial heat flow is the calibration, where the cover is algebraic and the generic folded equation has the full group [doc]. Named obstacle: the central branch times are the zeros of one function of the time, the centre value [L*]; for the others the corpus has no such function (log §4.13).

**Tests.** T1: the existence of a collision away from the centre at a forward complex time is implied by nothing about ζ's zeros; its negation implies RH [L*]. T2, T3 pass. T4 pass: no verified height decides a statement at forward complex times. T5 calibrated on the polynomial heat flow and on the Jensen equations (full group or dependent moments). T6 pass. T7 moves Σ193, Σ194. T8: not a named problem; first step in corpus objects.

**The second half.** B145 is the sign-free question for world I: *does the prime-weighted centred type-II current at a growing isolated mode cancel below the recovered residue?* Under ¬AAL filters recover the top residues and the growing-order current reduces to centred cofactors [F]; no declaration bounds the restricted prime-weighted cofactor sum (log §5). It has AAL strength.

**Limit.** **Under the constraint no question below RH opens the path to the line.** B193 decides what kind of object the sign-free form is; B145 opens the half that world I is. The step from AAL to RH is ZAL, and the corpus has no sign-free source of half-planes: its one producer uses squares and an Eisenstein reflection.

## 2.7 If RH is a physical phenomenon in AdS with a modular horizon

**What is proved.** RH ⇔ every compact pulse rings down at the quarter rate; a strip `Re ρ≤1−2δ` ⇔ decay at rate `δ`; the pulse rate equals the horocycle rate [L*]. The unfiltered horocycle exponent is `1−Θ/2`, filtered `1−Θ∞/2`; AAL ⇔ no Euler filter accelerates [F]. The cusp spectrum has the Weyl order [L*]. `selberg_status` [L*]: no Maass cusp form with `0<λ<3/16` on any congruence subgroup; none in `(0,¼)` at the levels dividing `N²`, `N≤25`; `y^{1/4}θ` on `Γ₀(4)` with the theta multiplier is a square-integrable eigenfunction of the weight-`½` Laplacian with eigenvalue `3/16`. Every zero with `Re ρ>0` is seen by a pair of Hecke forms, and one form that sees all right zeros forces `ζ(ρ/2)≠0` [L*] (log §4.8, §4.9, §4.10). With `[X]`: the rate `1/16` [D].

**Readings [D].**
- *World I is ordinary ringdown and is removable*: a finite set of least-damped modes, removed by a filter of finite degree; a two-sided edit removes it from the primes [L*].
- *The one arithmetic gap of the horizon is saturated one weight away.* The bound `3/16=¼·¾` is the eigenvalue of a bound state of the weight-`½` field. Every argument whose inputs also hold in weight `½` stops there [doc].
- *The resonances are hidden behind the bound-state spectrum.* The resonances of the modular surface are at `ρ/2` [C], left of the line on which the cusp forms sit. An estimate on the Kloosterman side meets the cusp forms first.

**Question (B188).** *Is there an estimate for the Kloosterman sums of the trivial multiplier that fails for the theta multiplier, and does it bound the scattering resonances away from the unitary axis by a margin, without a family of twists?*

| Answer | Effect |
|---|---|
| such an estimate, with a resonance-free strip of width `δ>0` | a second producer of a half-plane, independent of the Gauss-sum class; `δ>1/16` is a half-plane below `7/8` |
| such an estimate exists and reaches the bound states only | Selberg's bound improves and the resonances stay invisible: the arithmetic of the horizon needs an average that annihilates the cusp forms before it sees a resonance (the Hecke pairs of AHMH are the corpus object) |
| every estimate of the trivial multiplier holds for the theta multiplier | the congruence arithmetic of the horizon is exhausted at `3/16`; the physical reading supplies receivers, and the source comes from elsewhere |

**What the corpus says about the candidates [KR].** Scattering Schur contractivity is blind to the position of zeros; halving pairs defeat a single Hecke form; no declaration bounds a resonance-free strip from Kloosterman sums (log §5).

**Tests.** T1 passes as a half-plane for `δ>1/16`. T2, T3 pass. T5 calibrated by `selberg_status`: the estimate must fail for the theta multiplier and is consistent with the levels `N≤25`. T6 pass. T7 moves Γ252. T8: the classical candidate, cancellation in sums of Kloosterman sums over the modulus, is a named conjecture [C]; the question asked is the weaker one, whether any input special to weight zero reaches a resonance. First step in corpus objects (`RHTower/SelbergThreeSixteenths`, `RHTower/SelbergConjectureStatus`).

**Limit.** A rate is a half-plane; the quarter rate is RH and is not reached by a principle with a margin.

## 2.8 If RH is a problem of topology or geometry

**What is proved [L*].** The Morse index of the sign problem is a Maslov index; below the polar ground energy every crossing is charged. At finite scale RH is a Hodge index inequality between positive packets without common blocks; the pieces of a window are bound by couplings of full rank. At the critical ratio a failure of RH is one function, unique up to sign, outer, cyclic, on a strictly concave energy branch. On the heat cover a failure is a nontrivial monodromy (§1.7–1.9).

**Readings [D].**
- *The sign problem has a two-dimensional shadow.* If the first crossing is charged, it is a crossing of the polar Lagrangian with the charge axis; a neutral null mode is invisible to the poles.
- *The failure has a shape and a motion.* The floor of the half-line energy moves with the wall at the rate `−a(W₀)∫F²e^{−8u}/W₀`: the motion of the wall is paid by the exponential mass of the state. This is a variation formula of Hadamard type, and it is nonzero.
- *The charge is not in the formula.* Uniqueness, outerness, cyclicity, concavity, stability and the strong-confinement asymptotics hold on both sides of the charge question; the transverse gap bounds the polar pairing of every variation and leaves the pairing of the state itself free.

**Question (B104).** *Is the critical half-line state charged: is `∫F·polarSourceProfile≠0`? In the form of a first step: is there an identity that expresses the derivative of the floor at the critical ratio through the boundary trace and the polar pairing of the state?*

| Answer | Effect |
|---|---|
| charged whenever it exists | the classification loses its third case: RH, or `R_polar<W₀`. The polar channel of HF, SRT, AIP, ACS (atomic) and SC sees a failure strictly before the window threshold; a proof of RH on these routes reduces to polar payment at every ratio (B101) |
| an identity that writes the derivative of the floor as a negative multiple of the squared polar pairing plus a remainder of one sign | the nonvanishing derivative decides the charge |
| a polar-orthogonal critical state on a configuration model with ζ's archimedean data | a neutral critical state is invisible to the poles: polar payment cannot certify the first crossing |

**First step and obstacle.** At finite scale the answer is yes on windows with `4J≤R` [L*] (`charges_mul_pos_of_blockMatrix_minimizer`). Named obstacle [F]: a Green or boundary-trace identity linking the motion of the wall to the charge is missing; the verified strong-confinement limit [L*] is the regime `R→0` and does not reach the sign at the critical ratio.

**Tests.** T1 passes (method; under RH the state does not exist). T2, T3, T4 pass. T5 calibrated on narrow windows and on short apertures. T6 pass. T7 moves Σ190, Σ191. T8 not a named problem.

**Limit.** The answer does not decide RH; it decides whether the polar shadow is a complete invariant of the first crossing.

## 2.9 New field for RH: mixing arithmetic of the floor trees

**Does RH need a new field?** The Σ core has an exact finite object, and three theorems fix what its induction step is: it has full rank (the rank law), it is selective (weakened contacts fail), and it is cooperative (the off-diagonal entries are negative). No programme has the object that these three describe: a positive dynamics on the blocks that moves along the floor trees. In Poincaré form (§1.1) RH at a window is a spectral gap of that dynamics, bounded below by its binding energy. AGZ has the decomposition and the certified windows, ALG the trickle-down criterion, SA the selective ladder; the chain itself — its bottlenecks, comparisons and limits — is not studied [A].

| Aspect | Content |
|---|---|
| What it is about | The Doob chains of the windows: reversible walks on the blocks that move by the jets and along the floor trees of the integers `k≤Q`; their spectral gaps against their binding energies; the bottlenecks between dyadic scales; the limit at infinite block size, where the floor tree of `k` is the dilation `x↦x/k` on `(1,Q]` |
| What it is like | Mixing theory of walks on trees and semigroups; local-to-global spectral gaps (trickle-down, high-dimensional expanders) [C]; Poincaré and Cheeger inequalities; Perron–Frobenius theory of positive operators |
| Established [L*] | the decomposition into charges, potential and Dirichlet form; the ground-state transform identity; negative off-diagonal entries; one bound state on ratio `≤103/50`, none on narrow windows; two with weakened or twisted contacts; the rank law; the contacts from a block `a` to the blocks below `4a` are those of 2 and 3; the Metzler dichotomy [doc] |
| Criteria | X1 a statement about the chain, proved without the zeros. X2 gap `≥` energy on the certified windows; gap `<` energy at ratio four with the weights of 2 and 3 in `[−5/2,19/40]`, and for the Liouville twist. X3 no bound through a bounded number of test functions across a dyadic cut. X4 stable under refinement of the blocks. X5 every inequality names the tree edges it uses: an argument that uses no edge of the tree of 2 proves nothing at ratio three. X6 it reproduces the curve case, in which the trickle-down inequality on Frobenius ladders is the one-sided point count [doc] |
| Questions it must answer | B192; which cut of a window of ratio three is the bottleneck of its chain; a comparison of the chain of `(R,3R]` with the chains of its parts through the tree of 2; a curvature bound for the floor trees with the weights `Λ(k)/k`; the gap of the dilation process on `(1,Q]`; whether the margin of gap over energy has a limit along the ratios |
| Tools | the ground-state transform; comparison of Dirichlet forms and canonical paths; trickle-down; Schur complements of rank proportional to the block size; the contact Mellin calculus |
| Objects | Doob chains, floor trees, cuts, bottlenecks, gaps, binding energies |
| Language | chain, conductance, bottleneck, gap, binding energy, selective edge |
| Mechanisms | Built on AGZ, ALG, HFP, SA. To discover: a quantity that is monotone along the tree of 2 and bounds the gap below by the energy |

**Main conjecture.** Every Doob chain has a gap at least its binding energy (RH). **Milestones.** M1 the Poincaré form as a Lean statement. M2 the half-constant cut at ratio three from the contact of 2. M3 B192 at ratio three. M4 a recursion along doublings. M5 every ratio (B152). **Limit [A].** The uniform statement is RH; the field supplies the first sign that comes from a prime.

## 2.10 New field for AAL: the arithmetic of recurrent signs

**Does AAL need a new field?** The receivers (FFA), the instruments (ELT), the model theory (WZC) and the selection of ζ (EFT) are built, and the door is fixed (§1.3). One feature separates AAL from every other target: its receivers are recurrent. One vector with a sign on infinitely many shells gives AAL [L*], whereas every exact form of RH quantifies over all windows and all vectors. A statement in law gives a recurrent statement: a quantity with a positive mean is positive infinitely often. Every native theorem on ζ left of `7/8` is in law (§1.11). No programme studies the means of the layer receivers [A].

| Aspect | Content |
|---|---|
| What it is about | Means, over shells and windows, of the one-vector statistics whose recurrent sign gives AAL: the level-one constant-vector product on the dyadic prime shells, the floors on windows of each bounded length, the normalized remainder at the top exponent; their values under an attained top, under a tail, and under RH |
| What it is like | Oscillation theory read backwards: Landau and Ingham derive oscillation from a singularity on the line of the abscissa [C]; here a mean excludes the singularity. Cramér's mean square as a diagonal sum over zeros [C]; logarithmic averaging; power sums for finitely many frequencies [C] |
| Established | shell signs give AAL; they fail on all late shells under a maximal off-line zero; under RH they hold on all late shells; floors at every bounded length give AAL; tangent data of `μ` and `λ` with `ζ(2ρ)` [L*]; attainment on every window in world I [F]; logarithmic Chowla and short-interval mean squares [L*]; even-moment exponents are sup bounds [F] |
| Criteria | R1 a statement for one vector, in the mean or infinitely often. R2 normalized at level one or at the top exponent; no value of `Θ` assumed. R3 false for a two-sided edit with a finite layer. R4 not an even-moment exponent and not a two-point correlation: logarithmic Chowla holds whatever the layer [D]. R5 it names its averaging. R6 its proof passes the door: unit multiplicity with the reflection, or the count |
| Questions it must answer | the logarithmic mean over `N` of the level-one constant-vector product on `(N,2N]`: its value under an attained top, from the tangent data; its value under RH; a formula for it as a diagonal sum over the zeros in which the top layer has one sign; B170; B145; a recurrent form of B183 on the count side |
| Tools | logarithmic averaging; Parseval on vertical lines; almost periodic functions and the Kronecker flow of a finite layer; power sums; the filters and currents of ELT |
| Objects | shells, means, recurrent signs, tangent data, top residues |
| Language | recurrent sign, mean sign, shell, attained top |
| Mechanisms | Built on FFA, ELT, the joint-ancestry modules of RHTower, LogarithmicChowla, MatomakiRadziwill. To discover: an unconditional identity for one mean whose sign an attained top reverses |

**Proof or falsification.** A proof is one mean with a sign that passes R1–R6. Each proposed mean is falsified on the edits. A falsification of AAL for ζ is a located finite layer, and the corpus has no mechanism that forces one (§2.20). **Milestones.** M1 the mean of the shell statistic under an attained top as a Lean statement. M2 the mean as a diagonal sum. M3 its sign on one edit with a finite layer. M4 AAL. **Limit [A].** A mean with a sign has AAL strength; the field moves the target from "for all" to "in the mean", where the corpus has methods.

## 2.11 New field for RH without positivity: Hurwitz arithmetic of the heat cover

**Does a positivity-free, non-spectral RH need a new field?** Under the constraint the exact form that survives is the triviality of conjugation as a monodromy (§2.6). GaloisTheoryOfZeros has the cover, the transport with its homotopy invariance, the group, the turn around each branch time and the element: the local theory. The field begins where that stops. No programme treats the branch divisor as a whole: where the branch times away from the centre are, whether the turns generate the group, and which relations hold among them [A].

| Aspect | Content |
|---|---|
| What it is about | The heat cover as a branched cover of the forward half-plane with infinitely many sheets: its branch divisor (central and other collisions with their orders), the local monodromies as generators of the forward monodromy group, the relations among them, the word of conjugation, and the boundary behaviour at the time of ζ |
| What it is like | Hurwitz theory and braid monodromy of discriminants [C], for a cover with infinitely many sheets; the curve case, where the roots have a group of signed permutations in which Frobenius is one element [C] |
| Established [L*] | isolated branch times, finitely many on boxes; Hermite sheets [doc]; the turn around a collision as a transport to the opposite sheet, of order two; every forward branch time a nontrivial element; from every centre time an element exchanging some `z≠0` with `−z`; a moving pair from a collision away from the centre; transport by homotopy class, none over convex branch-free sets; central branch times: infinitely many, nonreal, the zeros of the centre value; no escape and bijective transport over forward times; the group commutes with `z↦−z` and is the same at every base time; conjugation is an element; RH ⇔ it is trivial; pair-preserving group ⇒ RH; the generic folded equation has the full signed-permutation group [doc]; Jensen equations: full group or dependent moments |
| Criteria | H1 no inequality between a form and its squares; no operator. H2 statements about branch times, local monodromies, words and orbits. H3 it reproduces the polynomial heat flow. H4 a statement that forces the word of conjugation to be trivial fails for a heat family with a quartet. H5 statements at forward times; the time of ζ enters as a boundary point with its own hypothesis |
| Questions it must answer | B193; whether the turn around a simple central collision moves one pair only; a function of the time whose zeros are the branch times of a finite set of sheets away from the centre; the number and type of the branch times in a box; the branch times nearest to the positive real axis; whether conjugation is determined inside the group by its commutation relations; the extension of transport to the time of ζ |
| Tools | the implicit function theorem and Hermite blow-ups; the argument principle for discriminants of finite sets of sheets; saddle-point asymptotics of the half transform; wreath products |
| Objects | branch times, sheets, local monodromies, words, pairs, quartets |
| Language | branch divisor, central collision, sign flip, exchange, word of conjugation |
| Mechanisms | Built on GaloisTheoryOfZeros, ZCG (heat), NGF. To discover: a relation among the local monodromies that excludes an exchange on the real axis |

**Main conjecture [A].** The forward monodromy group is the full restricted group of signed permutations of the pairs, and the word of conjugation is trivial at every positive real time. The first half is a structure statement below RH; the second half is RH. **Milestones.** M1 a collision away from the centre at a forward time. M2 transitivity on pairs. M3 a discriminant for finitely many sheets. M4 a relation. **Limit [A].** A large group is compatible with RH and with its failure.

## 2.12 New field for RH as AdS physics: tree holography of the windows

**Does it need a new field?** The modular horizon has its receivers (BHR, AHMH, ASH, CTH) and one cover horizon (STCC). The finite-scale matrix has a geometry that no horizon programme uses: its contact part is a sum of weighted trees, one for each `k`, on the common vertex set of the blocks. In the physics of the assumption trees are the bulk geometry at a finite place, and the Hecke operator at `p` is the adjacency operator of the tree at `p` [C]. Under the assumption a window is a radial slab of a bulk whose archimedean part carries the jets and whose finite parts carry the contacts [A].

| Aspect | Content |
|---|---|
| What it is about | The blocks as bulk points with radial coordinate `log b`; the floor trees of the primes as the bulk at the finite places, the jets as the bulk at the archimedean place; a window as a radial slab; the cut between two dyadic scales and the edges that cross it; bound states as normalizable modes of a slab; the relation of the floor trees to the Hecke operators of the modular horizon on the Fourier modes at the cusp |
| What it is like | Holography on trees at a finite place; tensor networks on a scale tree; area laws for cuts [C] |
| Established [L*] | the floor tree of `k` with weight `Λ(k)/k` (`floorGraph`); the cut between `(R,2R]` and `(2R,4R]` is crossed by the whole tree of 2, with rank proportional to `R`; one pair of charges glues the halves only at `R=1`; without the true edges of 2 and 3 a slab of ratio three or four has a second bound state; narrow slabs have none; the contacts of a number ring are its point counts over the finite fields; `selberg_status`; Hecke pairs see every resonance |
| Criteria | K1 the bulk is built from places: trees and jets, not zeros. K2 the edges crossing a cut reproduce the rank law. K3 removing or twisting the tree of 2 produces a second normalizable mode. K4 moving the cutoff (refining the blocks) does not change the count of bound states. K5 a statement that holds with a sign field of nontrivial holonomy on the tree edges (the Liouville twist) is not a statement about ζ. K6 a rate with a margin is a half-plane; the quarter rate needs an equality case |
| Questions it must answer | is the neutral part of a window the restriction to the Fourier modes `b∈(R,QR]` of one quadratic form of the modular horizon in which the contact of `p` is the Hecke operator at `p`; what crosses a general cut and which cut is minimal; where in the radial coordinate the bound state of a slab sits; B192 as a statement on slabs of radial width `log 3`; B188 |
| Tools | Hecke operators on Fourier expansions; harmonic analysis on trees; Schur complements across cuts; the gluing brackets; the contact Mellin calculus |
| Objects | floor trees, slabs, cuts, crossing edges, normalizable modes |
| Language | bulk, slab, cut, crossing rank, twist field |
| Mechanisms | Built on AGZ, AHMH, BHR, STCC. To discover: the horizon form whose restriction to Fourier modes is the window matrix, or the proof that there is none |

**Main conjecture [A].** The window matrices are the restrictions to the Fourier modes at the cusp of one quadratic form of the modular horizon, with the contact of `p` the Hecke operator at `p`. **Milestones.** M1 the trees and the crossing ranks as Lean statements. M2 the contact of `p` against the Hecke operator at `p` on Fourier modes. M3 B192 on slabs. M4 a bulk reading of the binding energy. **Limit [A].** The dictionary gives the binding a geometry; it gives no sign.

## 2.13 New field for RH as topology or geometry: realization geometry of the windows

**Does it need a new field?** The index theory of the aperture (AGZ), the Lorentzian criteria (ALG) and the gluing law are built. At finite scale RH is the Hodge index inequality for classes without common components, and Weil's form on a window is the Castelnuovo–Severi defect `2d₁d₂−D²` with `D²=−N` [L*]; [D]. In geometry that inequality is a theorem as soon as the classes are classes of something: curves on a surface (the Hodge index theorem) or planar convex bodies (Minkowski's inequality for mixed areas) [C]. No programme asks for the things [A].

| Aspect | Content |
|---|---|
| What it is about | For each window a configuration — curves on a surface, or planar convex bodies — with one member for each block, whose pairing matrix is `−N`: positive pairings off the diagonal, self-pairings `−N(b,b)`, and two fixed classes whose pairings are the two charges; compatibility under refinement of the blocks and under enlarging the window |
| What it is like | The Hodge index theorem and Zariski decomposition on surfaces; Minkowski's inequality and its extensions; curve data over a finite field, where the window surface exists (`windowSurface` of ArithmeticCastelnuovoSeveri) [C]; [L*] |
| Established [L*] | Weil's form on step packets is twice the product of the charges plus `N`; the off-diagonal entries of `N` are negative; the Hodge inequality on positive packets ⇔ RH; narrow windows are positive definite (a negative definite configuration); ratio `≤103/50` has index one; with weakened or twisted contacts the index is two, so no realization exists [D] |
| Criteria | G1 built from the potential, the jets and the contacts, not from the zeros. G2 the pairing is `−N` at every block size, and refinement splits classes additively. G3 no realization when the contact of 2 or 3 is weakened or twisted. G4 negative definite on narrow windows. G5 the two charges are pairings with two fixed classes. G6 for curve data it is the product surface with the Frobenius graphs |
| Questions it must answer | are the couplings `−N(a,b)`, `a≠b`, of a dyadic window the mixed areas of planar convex bodies whose areas are at least `−N(a,a)` (lowering a self-pairing keeps at most one positive square [D]); which classes carry the contact of 2: is the floor tree of 2 the incidence of a doubling map; does a realization of `(R,2R]` and of `(2R,4R]` extend to `(R,4R]`; B192; B149, B169 |
| Tools | support functions and mixed areas; blow-ups, which lower a self-pairing; toric and tropical surfaces; Zariski decomposition; trickle-down as a test |
| Objects | configurations, classes, pairings, self-pairings, rulings |
| Language | realization, configuration, effective class, common component, self-pairing |
| Mechanisms | Built on AGZ, ALG, ArithmeticCastelnuovoSeveri. To discover: the configuration; or an obstruction class that vanishes exactly when the index is one |

**Main conjecture.** Every window matrix is realized (this gives RH). **Milestones.** M1 a realization on the certified dyadic windows. M2 non-realizability under weakened contacts as a geometric statement. M3 extension from the halves to ratio four. M4 compatibility along refinement. **Limit [A].** Realization on every window has RH strength; the field turns the inequality into an existence statement with a decidable first case.

## 2.14 A research programme to construct `𝔽₁`

**Goal.** A geometry in which Spec ℤ has a square and the inequality of Castelnuovo and Severi on it is a theorem. The programme is AGZ with HFP and ALG; SA, FFA and WZC are its test benches.

**What the corpus fixes [L*].**
| Item | Theorem |
|---|---|
| the pairing | Bézout for the comb ⇔ RH with the weights `Λ`; a shift of the constant is admissible only downward; the index is the number of right zeros |
| forced data | constant, scale and weights of the contacts; a contact altered and paid at its price is RH at every parameter |
| the square at finite scale | Weil's form on step packets is `2d₁d₂+N` with `d₁,d₂` the charges; `N` is a potential plus the Dirichlet form of the jets and the floor trees; distinct blocks pair negatively in `N` |
| the Hodge index | RH ⇔ `N(x,x)N(y,y)≤N(x,y)²` for positive packets without common blocks ⇔ one-sign bound states; certified at ratio `≤103/50`, on narrow windows, on the first blocks of ratio four |
| the binding | the halves of a window bind through the floor trees of 2 and 3 at their true weights; the coupling has rank proportional to the block size; one pair of charges suffices only at block size one |
| number rings | the index of every Dedekind zeta function of an abelian ring, of quotients, relative squares, powers and virtual configurations; the contacts of a number ring are its point counts over the finite fields |
| characters | Brauer induction; every Artin Euler product is a product of integer powers of abelian ones; reciprocity for cyclotomic characters |
| the aperture | Morse = Maslov index; the far end carries the zeros; the polar Lagrangian; a single simple null mode on a short aperture |
| tails | critical-comb growth = width; Abel integrability ⇔ RH; Laguerre tails = Li coefficients |
| sections | the count of sections in a box is its volume over the gluing index: the square counts linearly |
| models | a count rate above `½` identifies nothing; unit multiplicity with a decaying FE defect identifies the rational primes |

**What it would be like [D].** Spec ℤ over `𝔽₁` is a curve of infinite genus whose square is rigid and counts like a curve. At finite scale its Néron–Severi lattice is spanned by the blocks; two blocks meet positively; the correspondences are the graphs of the division maps `b↦⌊b/k⌋`, the transposes of the multiplication maps, with the weights `Λ(k)/k`; in the curve case their place is taken by the graphs of the Frobenius powers. Its Hodge index is a bound-state count. Its pieces are held together by the correspondences of 2 and 3, at full rank. Its index along the aperture is a Maslov index with a two-dimensional polar shadow. What distinguishes ℤ from its imitations is unit multiplicity with the reflection, and the exact count.

**State of the constructions.**
| Construction | Deliverable | State |
|---|---|---|
| I path | transport of the sign | closed: RH at every parameter [L*] |
| II glued fibre | the comb form as a glued form | refuted for invariant gluings [KR]; data forced |
| III Stepanov on the square | a small vanishing section | closed: an equality of ideals [F] |
| IV towers and characters | index per character | abelian rings, quotients, powers; abelian product form of Artin Euler products; cyclotomic reciprocity; the general reciprocity law is work (A154) |
| V count | quadratic count | linear [L*]; no definition without the form (B87) |
| VI finite scale | the inequality in finite rank | the Hodge inequality form; certified ranges; the first selective ratio open (B192) |
| VII index as topology | index from the path | closed as Morse = Maslov; the far end carries the zeros |
| VIII tails | the width on the comb | closed: one sequence |
| IX gluing | an induction on the ratio | the law is a theorem; through finitely many charges it fails; the step has full rank |
| X realization | a configuration whose pairing is `−N` | not attempted (§2.13) |

**Criteria.** C1 reproduces Weil and Stepanov for curves. C2 a count rate is not enough. C3 uses unit multiplicity with the reflection up to a decaying error. C4 uses the Euler product on the function. C5 sees the exact normalization. C6 infinite type. C7 the diagonal is the density of a comb. C8 positivity is derived. C9 selective exactly where a contact enters: blind below ratio two, false at ratio three for a weakened or twisted contact of 2. C10 additive over the constituents of a number ring, zeros and poles counted. C11 nothing below the trivial aperture beyond the dominated box. C12 at finite scale it is the Hodge inequality on positive packets. C13 a statement at the point. C14 a quadratic count. C15 treats neutral null modes. C16 its comb grows at the rate of the width. C17 its pieces bind at full rank; no finite number of charges replaces the binding.

**Questions.** 1 the first selective sign (B192). 2 a quadratic count (B87, B169). 3 Bézout from a property (B149). 4 a realization of the certified windows (§2.13). 5 the reciprocity law (A154). 6 the charge of the critical state (B104).

**Tools, objects, language.** The ground-state transform; trickle-down; Schur complements of full rank; the refinement tower; the index law for quotients and powers; the contact Mellin calculus; induction theorems for characters. Objects: degree points, blocks, jets, floor trees, charges, windows, configurations. Language: comb, Bézout, neutral part, bound state, binding, aperture.

**Order of work [A].** B192 at ratio three; a realization on the dyadic windows; A154.

**Decisive test [L*].** A construction whose inequality holds for an edit with a finite layer, for a fake, for the Liouville twist or a weakened contact of 2 at ratio three, for a wrong constant, or along a path of squares, is wrong.

## 2.15 A research programme to close the route WD

**Goal.** A bound `O_θ(T^K)` with one `K` and unbounded `θ` for the second moment of ζ times a Möbius mollifier of length `T^θ`, or the collision bound equivalent to it [F].

**What the corpus fixes.**
| Item | Statement | Evidence |
|---|---|---|
| receiver | RH ⇔ the mollified moment is subpolynomial; a cofinal bound with fixed `K` suffices | [F] |
| depth | dyadic boundedness at `θ>1` confines high zeros to depth `<1/(2θ)+ε` | [L*] |
| proved range | `θ<½` with displaced twisted moments; a positive proportion of critical zeros; the proved moment sits at `θ=13/50` | [L*]; [F] |
| necessary length | a mollifier that pays a relocation is longer than the height | [KR] (`KR-LLM`) |
| blindness | Type-II norms are sign-blind | [KR] |
| cameras | adaptive clusters with complete exterior mass `≤¼`; centred cameras with a prime mean square | [L*] |
| correlations | short-interval mean squares of `λ` and `λχ`; logarithmic two-point Chowla at every fixed shift | [L*] |
| what correlations give | no half-power rate | [F] |

**What it would be like [D].** A mean-value theory past the height, whose off-diagonal is a correlation of truncated Möbius divisor sums. On the scale a bounded dyadic moment at `θ` is the half-plane `½+1/(2θ)`: the route passes `7/8` at `θ=4/3` and reaches the line only cofinally. Below `3/5` the route competes with nothing: the frame of the producer ends there (§1.6).

**Criteria.** W1 fails for ζ times an Euler factor with a zero right of the line. W2 fails for a finite relocation. W3 not a Type-II norm bound. W4 keeps the pole and the diagonal. W5 `K` independent of `θ`. W6 at `θ<4/3` it gives nothing `[X]` does not. W7 it fails for a two-sided edit with a finite layer. W8 a correlation input states its rate: decay without a rate gives no exponent.

**Questions.** 1 A18. 2 the collision form at `θ≥1`. 3 a power saving at one `θ>4/3` (below `7/8`); at `θ>5` it is below `3/5`, past the frame of the producer. 4 fixed `K` along `θ→∞` (B62). 5 the converse of the depth theorem. 6 a rate in the logarithmic correlations at shifts growing with the length.

**Tools, objects, language.** Gallagher's transfer; shifted correlations of sieve weights; the ladder and Parseval of MatomakiRadziwill; the prime-dilate reduction of LogarithmicChowla. Objects: mollifiers, dyadic moments, collision charges, cameras. Language: length, depth, excess.

**Milestones.** M1 `θ<½` (Lean). M2 a proportion on the line (Lean). M3 logarithmic Chowla and short-interval mean squares (Lean). M4 A18. M5 the collision dictionary at `θ≥1`. M6 a saving at one `θ>4/3`. M7 the cofinal bound.

**Limit [A].** The cofinal bound is RH; every partial result is a level of the scale.

## 2.16 A research programme to close the route ACS

**Goal.** The Hodge inequality on positive packets of every window; equivalently the comb sign, a mass floor on every ratio window, or subpolynomial growth of the critical comb.

**What the corpus fixes.** The table of §2.14, and:
| Item | Statement | Evidence |
|---|---|---|
| the minimal face | one inequality per prime on logarithmic windows; two primes at radius `r√T` | [L*] |
| the regimes | no bound state for `16J≤R`; exactly one for `R≤J`, `50J≤53R`; at ratio four at most `300000` negative squares of the block matrix | [L*] |
| the binding | on the half-constant plane at ratio four `(J+K)²≈5.02>2D²≈2.87`; without the contacts `J²≈1.40<2D²` | [L*]; [D] |
| selectivity | two bound states for contact weights of 2 in `[−4,0]` (`J≥2R`), of 2 and 3 in `[−5/2,19/40]` (`J≥3R`), and for the Liouville twist | [L*] |
| the step | gluing law; brackets; response matrices; rank one only at block size one; rank `r` fails for `600(r+1)≤H` | [L*] |
| reach of finite procedures | transfer needs `log R≥2.5·10⁴`; window heights are double exponential | [L*]; [D] |
| tails | critical-comb growth = width; Abel integrable ⇔ RH; Li coefficients as Laguerre tails | [L*] |

**What it would be like [D].** Four tracks on one lattice. *Binding*: the neutral part as a cooperative system whose scales are tied by the floor trees; one bound state per window as a spectral gap of the Doob chain. *Index*: the aperture path and its polar shadow. *Tails*: the critical comb as the scale on one sequence. *Realization*: a configuration whose pairing is the neutral part.

**Criteria.** Those of §2.14, and: S1 nothing about the contacts below ratio two. S2 a margin at each ratio, none uniform. S3 nothing on the tails at `a<1/8` beyond `[X]`. S4 the certified windows are reproduced, not reproved. S5 an induction step has rank proportional to the block size. S6 the step fails when the contact of 2 is weakened.

**Questions.** 1 B192: ratio three, then four, at every block size. 2 the least contact weights for one bound state at ratio three and four: the interval of selectivity around the true weights. 3 B149, B87, B169. 4 B104. 5 A154, A141.

**Tools, objects, language.** As in §2.9, §2.13 and §2.14.

**Milestones.** M1 finite criteria and the Hodge inequality form (Lean). M2 ratio `≤103/50` and narrow windows (Lean). M3 the gluing law and its rank law (Lean). M4 necessity of the true contacts (Lean). M5 B192 at ratio three. M6 every ratio (B152).

**Limit [A].** Each ratio is a finite-height statement; the uniform statement is RH.

## 2.17 A research programme to close the route ZCG

**Goal.** No positive real branch time of the heat cover; or the floor on a decisive sequence of prime windows; or ZAL, B13 and Landing.

**What the corpus fixes.**
| Item | Statement | Evidence |
|---|---|---|
| worlds | world I or world II, top `≤7/8` | [X]; [L*] |
| world I receivers and instruments | unit gap, non-attainment, filters, currents, tangent data, shell signs | [L*]/[F] |
| world I models | every finite layer, a pair alone, zeros on and rising to a line, sparse tails, layer removal, symmetric quartets — over the rational primes with a count rate | [L*] |
| laws of the models | balance or real top; parity above twice the count exponent; count floor `13/30`; integer-norm fakes below one half | [L*] |
| the FE axis | unit multiplicities: any decay forces the rational primes; positive weights: arbitrarily slow defects; fake edits at `T log T`; mean defect `T^ε` under `Θ<1` | [L*] |
| the door | unit multiplicity with the reflection up to a decaying error, or the count below half the layer | [D] |
| the heat cover | RH ⇔ no positive real branch time ⇔ trivial conjugation monodromy; tame over forward times; central branch times never real; every forward branch time a nontrivial monodromy; pair-preserving group ⇒ RH | [L*] |
| the time of ζ | real branch times accumulate at `0`, or infinitely many nonreal zeros escape across `0`; no uniform control as `τ→0` | [L*]; [F] |
| cameras | adaptive clusters with complete exterior mass | [L*] |

**What it would be like [D].** World I is a finite-dimensional problem with complete receivers and a complete model theory: it closes by one statement that passes the door and fails on every model with a layer. World II is the scale and inherits the end of the producer. The heat side is a cover with a real structure: tame over forward times, with its difficulty concentrated at one boundary point, the time of ζ.

**Criteria.** Z1 a world-I statement fails on every edit with a finite layer, on the positive-weighted systems and on the signed fakes. Z2 two-sided, or at every length. Z3 nothing below the logarithmic radius. Z4 a world-II statement is placed on the scale. Z5 a camera statement names the cluster size and gap. Z6 nothing in law used as a point; a mean used for AAL names its averaging (§2.10). Z7 every statement states what it uses of the reflection: a growth bound on the defect is refuted among positive weights. Z8 a heat statement names its region of times: forward, positive real, or the time of ζ.

**Questions.** 1 B193. 2 B145 or B170. 3 B191. 4 B183. 5 B141. 6 B13 and Landing (B157, A120). 7 B59. 8 the half-planes of world II. 9 control of transport as `τ→0`.

**Tools, objects, language.** Filters, currents, tangent data; two-sided edits with prescribed factors; the balance and order laws; adaptive cameras; transport, local monodromies and Hermite sheets; the scale. Objects: layers, tails, edits, defects, branch times, sheets. Language: world, atom, layer, fake, defect, branch time, word of conjugation.

**Milestones.** M1 receivers, instruments, models (Lean). M2 the FE axis with rigidity at any decay (Lean). M3 the heat cover over forward times with the turns and conjugation as monodromies (Lean). M4 a collision away from the centre at a forward time. M5 the weighted current for one quartet. M6 AAL. M7 ZAL through the scale. M8 Landing and B13.

**Decisive test.** An argument for AAL that holds for a two-sided edit with a finite layer or for a positive-weighted system with off-line zeros is wrong. An argument on the heat cover that uses only group membership of conjugation proves nothing: conjugation is a monodromy whether or not RH holds.

**Limit [A].** AAL and ZAL together are RH; the corpus has a receiver for each and a producer for neither below `7/8`.

## 2.18 A research programme to close the route MC/JAS

**Goal.** The signal bound `O(Z^b)` for every `b>½`; equivalently level one of the dressed aggregate.

**What the corpus fixes.** §1.6 in full; producer rates are the Mertens level [L*]; bilinear norms are sign-blind [KR]; logarithmic two-point Chowla and short-interval mean squares of `λ` are native and give no half power [L*]; [F]; level-one signs of the constant vector on infinitely many dyadic shells give AAL [L*].

**What it would be like [D].**
| Stage | Half-plane | Input | Kind |
|---|---|---|---|
| 0 | `7/8` | the two estimates of the cubic probe, assembled in source without hypotheses; validation of the chain (A118) | just work |
| 1 | `7/8→13/15` | the row count of the binding bin (B174) | density estimate |
| 2 | `13/15→5/6→` below | the long columns with a power saving (B185) | an estimate that is not a square |
| 3 | `→2/3` | square-root remainder in the long columns | Patterson type [C] |
| 4 | `2/3→3/5` | estimates below square-root size on every level of the tower | beyond square root |
| 5 | below `3/5` | a pairing outside the `6r`-periodic Gauss pairings (B187) | — |

**Criteria.** J1 every estimate placed in the twist exponent. J2 a mean square containing the principal twists is not an input. J3 positive weights, even order, two row variables fail. J4 below `5/6` nothing is a square. J5 below `2/3` the family contains its corrections. J6 a source for the last stage has pairing coordinates with fixed point `½` and a design with square-root endpoint `½`. J7 a correlation theorem without a rate is no input on the scale.

**Questions.** B174, B185, B187, B180; the coupling map of every completed probe; level one directly (B160).

**Tools, objects, language.** The budget calculus; signed Gram forms; sieves over cyclotomic rings; the theta-square series; the scale as a ruler. Objects: rows, columns, bins, root numbers, pairings, towers. Language: design, corner, floor bin, frame, fixed point.

**Milestones.** M1 the half-plane `7/8` validated in Lean (A118). M2 a boundary below `7/8`. M3 B185 with any `R₀<1`. M4 below `5/6`. M5 B187.

**Decisive test.** An estimate that holds for matched phases, or for a family with its principal twists counted as input, proves no half-plane.

**Limit [A].** With every stage of the cubic probe completed the programme reaches `2/3` (`3/5` with estimates beyond square root), and no period of the Gauss pairings does better. It is the only programme that has produced a theorem about the zeros, and in its class it does not reach the line.

## 2.19 A research programme for a Galois theory of the zeros

**Goal.** Treat the zeros of ζ as the roots of equations over a field built from the primes, and as the sheets of a cover; determine the groups; classify the permutations of the zeros that they allow.

**What the corpus fixes [L*]** (GaloisTheoryOfZeros; log §4.4, §4.8, §4.9, §4.10, §4.11, §4.13).
| Item | Theorem |
|---|---|
| the equations | the centred zeros of each ordinate are the roots of a polynomial over the field `K` of complete-fibre traces; the zero field is algebraic and normal over `K` |
| the criterion | `K_even⊆ℝ` ⇔ RH; over the prime trace field `B` the reflection field `H` equals `B` ⇔ RH |
| the group over the fields | not transitive; a zero with rational real part has the orbit `{ρ,ρ̄}`; the reflection of the functional equation lifts iff every square relation among the reflection radicands has even cardinality; the zero field is the source field or a quadratic extension of the even width field |
| orderings | every ordering of the squared-width field induces complex conjugation iff every squared width is a sum of squares there; no ordering induces another automorphism iff every product of two radicands is a sum of squares |
| finite equations | Jensen discriminants are nonnegative; `N_d=4Q_d`; the degree-`2n` Jensen equation has the group `C₂≀S_n` or its normalized moments satisfy a rational polynomial relation |
| the cover | branch times; Hermite sheets; central branch times as the zeros of the centre value, none real; no escape and bijective transport over forward times; the forward monodromy group, commuting with `z↦−z`, the same at every base time; the turn around a collision: opposite sheets, order two; every forward branch time a nontrivial element; from every centre time an element exchanging some `z≠0` with `−z`; transport depends only on the homotopy class of the path |
| conjugation | over a positive real non-branch time it is an element of the forward monodromy group; RH ⇔ it is the identity ⇔ no positive real branch time; RH if every element preserves every pair `{z,−z}` |
| absent | an automorphism of the zero field other than conjugation; the orbit of a zero with irrational real part; a collision away from the centre at a forward time; generators and relations of the forward monodromy group; Frobenius or decomposition structure |

**What it would be like [D].** A theory of signed permutations with two marked involutions, in three tiers.
- *The model case [C].* The zeros of the zeta function of a curve of genus `g` over `𝔽_q` are the roots of one integer polynomial; the functional equation pairs them, so the group lies in `(ℤ/2)^g⋊S_g`, and for most curves it is the whole group. The Riemann hypothesis there says nothing about the size of the group: it says that two involutions of the roots agree, complex conjugation and `α↦q/α`.
- *Finite equations.* The Jensen equations have the full group unless the moments of `Φ` are dependent; the information is the cycle type of conjugation, `Q_d` double transpositions.
- *Fields.* Over the field of complete-fibre traces the group is a group of width reflections, trivial iff RH.
- *The cover.* The sign part of the group comes from the central collisions, where the functional equation is the local monodromy; the permutation part comes from the other collisions; conjugation is the word of the real ones. As existence statements the first two are theorems: a centre time gives an element exchanging some zero `z≠0` with `−z`, a collision away from the centre an element that moves a pair [L*]. That the turns generate the group is not proved.

**Criteria.** Q1 the base field is defined from the primes or from complete fibres, never from single zeros; the base of the cover is a region of times that is named. Q2 every statement names its base: over `K` the group is trivial iff RH, over a smaller field or on the cover a large group is compatible with RH. Q3 the classification names the classes of conjugation and of the reflection. Q4 it reproduces the curve case. Q5 a statement that forces the two involutions to agree fails for a configuration with a quartet. Q6 a transitive action on the zeros over `K` is excluded [L*].

**Questions it must answer.** 1 B193: a collision away from the centre at a forward time; generators; transitivity on pairs. 2 Are the normalized moments of `Φ` algebraically independent at each degree? This decides the group of every Jensen equation. 3 B190: the orbit of a zero with irrational real part under the embeddings fixing `B`. 4 Is the degree of the zero field over `K` one or infinite? A finite nontrivial degree is the Galois form of a finite stratum, so the statement contains B13. 5 Is every squared width a sum of squares in the squared-width field? 6 A restriction, from the prime traces or from the branch divisor, that forces the two involutions to agree.

**Tools, objects, language.** Kummer theory of the width classes; real fields and their orderings; transcendence of prime powers; specialization for the finite equations [C]; transport, Hermite blow-ups and words of local monodromies. Objects: source field, zero field, prime trace field, reflection field, fibres, widths, radicands, sheets, branch times. Language: orbit, width class, reflection kernel, sign flip, exchange, word.

**Milestones.** M1 the zero field and its criteria (Lean). M2 the Jensen dichotomy (Lean). M3 the forward monodromy group with the turns and conjugation as elements (Lean). M4 a collision away from the centre at a forward time. M5 independence of the moments at low degree. M6 the dichotomy for the degree over `K`.

**Limit [A].** Over the fields of the corpus the group is trivial exactly when RH holds, and on the cover conjugation is trivial exactly when RH holds. The theory supplies a language, criteria and one sign-free exact form; it supplies a route only through a restriction that the primes or the branch divisor impose on one element, and the corpus has none.

## 2.20 A research programme under the assumption that RH is false

**Goal.** (a) A proof that RH fails. (b) A concrete counterexample, found without computation at the height of the zero.

**What the corpus fixes.**
| Item | Statement | Evidence |
|---|---|---|
| where a failure lives | a zero with `½<Re ρ≤7/8`; world I or world II | [X]; [L*] |
| objects that exist iff RH fails | a window with a sign-changing bound state; a positive real branch time of the heat cover; the critical half-line state at a finite ratio; an odd bound state; a defective hard-edge block; a point right of the line with `Re ξ′/ξ<0`; a negative definite Markov plane; an aperture with an empty feasible set; a crossing along the aperture | [L*] |
| a failure repeats | negative paired Li indices in every window of some bounded length; in world I `ψ(x)−x` attains `x^β` on every late window; the level-one shell sign fails on all late shells under an attained top | [L*]; [F] |
| zero ⇒ certificate | for `2δκ>1`: a zero of depth `δ` at height `γ₀` with no other off-line zero within `m^κ`, `m=A₀log(\|γ₀\|+3)`, makes Weil's form negative on a test supported in `\|u\|≤κ log m` | [L*] (`zeta_companion_of_rung`) |
| certificate ⇒ zero | a negative test at aperture `a` gives an off-line zero below `exp(exp(Ca))`; `C` is not explicit | [L*] |
| returns | under `Θ≤b` a return of a heavy set of primes up to `y` at height `t` needs `log t≥c·y^{1−b}` | [L*] |
| counts | at ratio four the block matrix has at most `300000` negative squares at every block size; RH says none | [L*] |
| what is excluded | a failure below height 67; on windows of ratio `≤103/50`; on narrow windows; on the half-constant plane at ratio four; at a central collision; a failure visible to a statement in law | [F]; [L*]; [D] |
| models | every failure mode is realized over the rational primes with a count rate, and with slow FE defects among positive weights | [L*] |

**What it would be like [D].**
- *A failure is a return.* By the return bound with `b=½`, RH allows heavy returns of the primes up to `y` only at heights with `log t≥c√y`; with `b=7/8` the unconditional range is `log t≥c·y^{1/8}`. A disproof is an **anomalous return**: a height at which a heavy set of the primes up to `y` returns with `(log t)²≪y≪(log t)⁸`. The pigeonhole principle gives returns only for `y` of order `log t·log log t` [C].
- *A failure is a bound state that changes sign.* It lives on a window of ratio above `103/50`, off the half-constant plane, on packets on which the binding by the floor trees of 2 and 3 has a deficit. The weakened-contact theorems say how large that deficit is on one plane: the contacts would have to act with less than `0.485` of their weight.
- *A failure is one function.* The weak equation at the critical ratio is a linear equation with the actual primes; a unit solution on the half-line exists iff RH fails, and it is then unique, outer and cyclic.
- *A failure is a real collision.* A time `0<t<1/8` and a real point `x≠0` with `H_t(x)=H_t′(x)=0`.
- *A concrete counterexample* in this setting is a triple of a height, an aperture and a test, with the negativity of a finite sum over the prime powers below `e^{2a}`; or a window, a block size and a sign-changing vector of negative neutral energy; or a pair `(t,x)`. The first two have polylogarithmic size in the height of the zero, and the zero is then located only by a bound (A142). This is the form of Littlewood's theorem on `π(x)−li(x)` with Skewes' bound [C].

**Criteria.** N1 the argument fails for the zeta functions that satisfy their Riemann hypothesis: curves over finite fields [C], the Goss zeta function [L*], the certified windows [L*]. N2 it uses what ℤ has and those cases lack: the archimedean place, infinite type, the absence of a Frobenius. N3 it is consistent with `[X]`, with the verified height, with the positive proportion on the line and the runs of simple zeros, and it says which world it produces. N4 its certificate states an aperture and, through A142, a height. N5 no statement in law is used as a point. N6 an existence proof by return beats the pigeonhole range by a square. N7 a second bound state is exhibited with the true contacts: every second bound state of the corpus comes from a weakened or twisted contact.

**Questions it must answer.** 1 Is there a rung `κ∈(1,4]` and a sequence of heights with a heavy return of the primes up to `(log t)^{2κ}`? 2 Explicit constants: `c` in the return bound at `b=½`, `C` in the verification rate (A142). 3 On which packets of a window of ratio three is the Hodge inequality closest to failing? 4 Does the weak equation at a finite critical ratio have a solution (B104)? 5 Which world: is a failure of ζ necessarily a tail (AAL)?

**Tools, objects, language.** Diophantine approximation for the prime phases; Ω-theorems [C]; the ladder; the gluing brackets in both directions; compactness at the critical ratio; edits and positive-weighted systems as models of what a failure looks like in the primes. Objects: returns, certificates, failing apertures, critical states, sign-changing bound states, real collisions. Language: anomalous return, rung, certificate, height bound.

**Milestones.** M1 the explicit constants. M2 the extremal packets of the Hodge inequality at ratio three. M3 a return on a rung above one for a model system with the exact count, or the theorem that the exact count forbids it. M4 an anomalous return for the primes.

**Assessment [A].** The corpus contains no mechanism that forces a zero off the line. Every exact form of "RH fails" is an existence statement, and every model that realizes a failure gives up unit multiplicity or the reflection. The verified height, the certified windows, the binding numbers and the proved laws are all on the side of RH. The programme yields three things: the list of objects that a failure produces; the conversion between a zero and a certificate of polylogarithmic size; and a description of the event to look for. Part (b) is possible only in the Skewes form: a certificate with an explicit bound for the height, and not a located zero.

## 2.21 The one big question: the first selective sign (B192)

**Where the question sits.** At finite scale RH is the Hodge inequality on the positive packets of every window. It is a theorem where the window is narrow or close to dyadic. Each of these theorems holds for every sign twin and uses no prime: below ratio two the contacts vanish [L*]; [D]. At ratio three the statement is false for the Liouville twist and for every contact weight of 2 in `[−4,0]`; at ratio four it is false for contact weights of 2 and 3 in `[−5/2,19/40]` [L*]. With the true weights the index at ratio four lies between one (RH) and `300000` (proved). The two finite procedures of the corpus do not reach it: the transfer needs `log R≥2.5·10⁴`, the verification a double-exponential height [D]. The induction step through charges fails beyond block size one, and through every bounded rank at large block size [L*].

**What is in Lean [L*].**
- The two halves `(R,2R]` and `(2R,4R]` of a window of ratio four each have exactly one bound state at every block size (`hermNegIndex_neutralWindow_eq_one`).
- A window has two bound states iff it has a sign-changing bound state iff two positive packets without common blocks violate `N(x,x)N(y,y)≤N(x,y)²`.
- On the half-constant plane the inequality holds with the true contacts and fails without them (`bilin_neutralWindow_halves_pos`; §1.7).
- The sum of the indices of two windows raised by their mutual couplings is at most the index of the union; the union is bracketed by lowered and raised models.

**Question (B192).** *Does the window `(R,3R]` — and then `(R,4R]` — have exactly one bound state at every block size `R`, by an argument that uses the floor trees of 2 and 3 with their true weights? In the form of the step: for nonnegative packets `x` on `(R,2R]` and `y` on `(2R,4R]`, is `N(x,y)²≥N(x,x)N(y,y)` whenever `N(x,x)<0`?*

**Why this question.**
- It is below RH, AAL and every half-plane: the conclusion at a fixed ratio follows from RH.
- It is the first statement of the Σ core that is selective. A proof is the first sign theorem in which a prime enters, and it cannot be an argument about sizes, about sign twins, or about a bounded number of charges: each of these is refuted in Lean.
- Its two halves are certified, its first plane is computed, and its failure modes are theorems. The step that is missing is a lower bound for one bilinear form on a product of two positive cones.

**What an answer gives.**
| Answer | Effect |
|---|---|
| yes at ratio three, with a margin uniform in the block size, from the tree of 2 | the first selective sign. The same step applies to every doubling, and RH becomes the statement that the margin survives along the ratios: an induction whose step has full rank |
| yes at every block size, with a margin that tends to zero | the binding is critical in the limit of infinite block size; the limit object is the dilation form on `(1,3]`, and its null direction is the question of the critical state (B104) |
| yes, but only for weights in a neighbourhood of the true ones that shrinks with the ratio | selectivity sharpens along the ratios: the interval of admissible contact weights is the invariant to compute, and RH is the statement that the true weights stay inside |
| a sign-changing bound state at some block size | RH fails, with a zero beyond the verified height (§2.20) |

**First step and obstacle.** The half-constant plane at ratio three from the contact of 2, then all pairs of nonnegative packets supported on the two halves. Named obstacle: the positive cone is not a subspace. The inequality is a reverse Cauchy–Schwarz inequality for the coupling between the halves, in which the tree of 2 is a two-to-one matching of the blocks and the jets are a smooth kernel; the bound has to hold uniformly in the block size, where the rank of the coupling grows.

**Tests.** T1 passes: at each ratio the statement is implied by RH and implies neither RH nor AAL; as a method question it asks for a proof from the contacts. T2: an inequality on explicit matrices at every block size. T3: named for each answer. **T4 fails in the strict sense**: at each ratio the conclusion is decided by a finite verified height; the height is double exponential and no procedure of the corpus reaches it, and the question asks for the mechanism, which no height supplies. T5: calibrated — false for the Liouville twist and for weakened contacts, true on the half-constant plane and on the certified halves. T6: no declaration gives the index at ratio three with the true contacts (log §4.13). T7: moves Σ186, Σ188, Σ189. T8: not a named problem; the first step is in corpus objects with one named obstacle.

**Limit.** At each fixed ratio the conclusion is a finite-height statement, and uniformly over all ratios it is RH. **No question below RH, AAL and the half-plane passes all tests as a door to the line**; B192 is chosen because it is the place where the sign has to come from a prime for the first time, and because every easier form of its step is refuted.

### Alternatives considered
| Question | Effect | Verdict |
|---|---|---|
| The long columns (B185, §2.4) | the first non-square estimate; the half-plane moves toward `2/3` | the largest motion available on the scale; capped at `2/3` |
| A pairing whose frame reaches the line (B187, §2.5) | a producer for the line, or the end of the Gauss-sum class at `3/5` | the producer question; its first step is a classification |
| The charge of the critical state (B104, §2.8) | the polar shadow sees the first crossing | decides one channel of five routes; the limit case of B192 |
| An exchange in the forward monodromy group (B193, §2.6) | what kind of object the sign-free form is | a structure question; a large group decides nothing about conjugation |
| A mean with a sign on the shells (§2.10) | AAL from a statement in law | AAL strength |
| The defect gap and bounded defects (B191) | the last open part of the FE axis among unit multiplicities | a model question on an axis whose ends are theorems |
| A fake below `√x` with a non-real top (B183) | the count door for world I | a model question on the count axis |
| The row count of the binding bin (B174) | `[13/15,7/8)` | a one-sided density estimate |
| The weighted current (B145) | AAL without a sign | AAL strength |
| An input special to weight zero (B188, §2.7) | a second producer | the classical candidate is a named conjecture |
| The orbits of the zero field (B190, §2.19) | a nontrivial permutation of zeros, or none | no restriction from the primes in the corpus |
| An anomalous return (§2.20) | a disproof | no forcing mechanism |
| Validation of the `7/8` chain (A118) and its receivers (A138), the reciprocity law (A154), the explicit verification rate (A142) | the half-plane and the scale at `7/8`, the Artin index and the window heights as verified Lean statements | just work |
