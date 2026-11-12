# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: `dd55ee70d9` (2026-11-12). Fact log: `logs/review-1211-rev2-facts.md` (cited as "log §n").

**Evidence.** `[L*]` Lean statement read at the declaration for this report and recorded in the fact log; `[doc]` content of a module docstring whose theorem names were read but not every statement; `[F]`, `[KR]` stated by the frontier map and the scoped-obstruction ledger; `[S]` module graded unfinished by the frontier map; `[card]` proved on the pipeline card `docs/drafts/pipeline/2-fully-proven/b186-critical-line-fe-defect-of-fake-zeros.md`, no Lean declaration; `[D]` deduction made here from `[L*]` statements, not a Lean theorem; `[C]` classical mathematics quoted from memory, not in the corpus; `[A]` assessment; `[X]` the external theorem cached in the repository (OpenAI, 30 September 2026), taken as proved: every Dirichlet `L`-function, ζ included, and every finite-order Hecke `L`-function over `ℚ(√−3)` is zero-free in `Re s>7/8`. The Lean graph proves `zetaZeroAbscissa ≤ 1` unconditionally and `beta ≤ 7/8` from a uniform continuation margin; the native steps of `[X]` are just work (A118). Sections 2.3–2.21 are interpretation and ideation: every untagged statement there is a proposal.

**38 live formulations; 12 candidates** (SEC, CDC/BSH, S3, APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF). HJ is PA; PCS, DR, PW-B are retired labels.

**Notation.** As in [route-obstacles.md](route-obstacles.md). In addition: the **reach** of a producer is the least `σ₀` for which its implication gives `Θ≤σ₀`; a **design** `(κ,n)` is a probe whose rows have conductor exponent `κ` and principal frequencies of order `n`; a **pairing** `(c,k)` has local resonance norm `Q^{c−ks}` at a prime of norm `Q`, **uncoupled boundary** `(c+1)/k` and **coupled fixed point** `c/(k−1)`; the **defect energy** of a system at `T` is `∫‖g‖²e^{−|t|/T}dt`.

## 1. Big picture

### 1.1 One object, three exact forms
- **One inequality per prime.** RH ⇔ `2Re S(log p)≥−K` at the primes of arbitrarily late logarithmic windows outside `Ce^{δT}` primes per window; equivalently the upper side alone, `ℕ`-counts on the surviving prime rays, one growth exponent for all even local moments, or copositivity of the prime planes [L*] (log §15). `Θ<1` ⇔ the floor `−Kp^α` for some `α<½` [L*] (`quasiRH_iff_prime_logarithmic_power_windows`).
- **One matrix at finite scale.** On the blocks `(a,a+1]` the step-packet matrix is `d(a)+d(b)+δ_{ab}ϱ(a)−J(a,b)−C_Q(a,b)`. It is the product of the two charges plus a **neutral part**. RH ⇔ the neutral part has exactly one negative square on every window `(R,R+J]` with `R≤J` [L*]. The block matrix has `r` negative squares on some window iff ζ has at least `r` zeros right of the line; the neutral part iff at least `r−1`; on every window the two indices differ by at most one [L*] (log §8, §14, §22).
- **One path of Lagrangians.** The index of the restricted Weil form at aperture `b` is the sum of the nullities of the apertures below `b`, the number of eigenvalues below the energy, and a Lagrangian intersection number of the aperture conormals with the graph of Weil's operator. Its supremum at energy zero is the number of zeros right of the line [L*] (log §14).

**The induction step [L*].** Two matrices `A`, `B`, nonnegative on the kernels of charge vectors `u`, `v`, coupled by `−2(u·x)(v·y)`, have exactly one negative square iff the product of their susceptibilities is at least one, and exactly two if both susceptibilities are negative with product below one (`hermNegIndex_glued_eq_one`, `hermNegIndex_glued_eq_two`). The union of two adjacent windows has at most the bound states of this model with potentials lowered by the excess couplings (`hermNegIndex_neutralWindow_add_le_glued`).

### 1.2 One scale
Every graded receiver is an equivalence at each level of one scale [D]:

| Reading | Parameter | Depth it reaches | Evidence |
|---|---|---|---|
| saving of the contacts `n^{½+γ}` | `γ` | sign to rung `κ<1/(2γ)` | [L*] (`cancellation_and_depth_ladder`) |
| sign on a rung `κ` | `κ` | no isolated zero of depth `>1/(2κ)` | [L*] |
| bounded dyadic Möbius moment at length `T^θ` | `θ>1` | depth `<1/(2θ)+ε` | [L*] |
| level of the dressed aggregate | `σ` | from a signal bound `O(Z^b)`: level `b+½+ε` | [F] |
| exponent of the signal of the zeta kernel | `b∈[½,1)` | `Θ≤b` ⇔ `O(Z^{b′})` for all `b′>b` | [F] |
| twist exponent of a family | `θ` | `Θ≤½+(1−1/n)θ/2` | [F] |
| growth exponent of the critical comb | `σ≥0` | strict growth `σ` ⇔ `w≤σ` | [L*] (`strictGrowth_criticalPowerCombTail_iff_zeroWidth`) |
| growth of a power tail `F_a` | `σ` | a zero-free half-plane | [L*] (`powerCombTailGrowth_iff_zeroHalfPlane`) |
| horocycle exponent; ringdown rate | `α`; `δ` | `Θ≤2−2α`; `Θ≤1−2δ` | [L*]/[F] |
| heavy returns of the prime orbit | `y^{1−b}≤C log t` | `Θ≤b` | [L*] (`heavy_return_bound_of_halfPlane`) |

The critical comb reads the scale on one explicit sequence: its growth exponent is the zero width, it never converges, and RH is its subpolynomial growth or its absolute logarithmic Abel integrability; a subcritical comb at `a` converges exactly when every zero has `Re ρ<1−a` [L*]. Sizes prove the scale to rung `1−o(1)`: the trivial aperture is `log log(mass)+o(1)` [L*] (`exists_abs_trivialAperture_sub_le`). The level `b=7/8` is `[X]`: the rung `κ<4/3`, the level `11/8`, heavy returns only for `log t≥c·y^{1/8}`, ringdown rate `1/16` [D]. In Lean no rung above one is proved unconditionally in any aspect.

### 1.3 Three structures; models; rigidity
ζ has an Euler product over the rational primes, the Riemann functional equation, and every integer with multiplicity one.

| Structures kept | Model | What fails | Evidence |
|---|---|---|---|
| the Riemann FE with Gamma factor, residue one, zero count within one | simple zeros off the line approaching it, no landing | Landing | [L*] (`exists_riemann_gamma_counting_model_without_landing`) |
| Euler product over the rational primes, multiplicities `0,1,2`, integer norms, count `Ax+O(x^β)` above the top | two-sided edits: a non-real pair alone; every finite layer; an isolated pair above an infinite half-scale tail; zeros decreasing to the line; sparse configurations; a finite layer edited away | AAL, B13, Landing, ZAL (sparse tails) | [L*] (log §9, §18) |
| the same, zeros symmetric about the line in a strip | quartet edits | the line | [L*] (`exists_isEdit_zeros_symmetric_in_a_strip`) |
| the same, with FE defect `‖g(t)‖≤K_ε\|ζ(½+2it)\|(1+\|t\|)^ε` and mean square `≤C_εT^ε` | signed grouped edits with a pair at any `½<β₀<3/2−Θ`, if `Θ<1` | AAL at `β₀` | [L*] (`frontier_dichotomy`) |
| real integer weights, bounded count, bounded FE defect | `(1−2^{ρ−s})(1−2^{ρ̄−s})`, `ρ=¾+i` | a zero that ζ lacks | [L*] (`signedPoly_fake`) |
| Euler product with real weights, meromorphy, temperedness | the one-off pair above the frontier of ζ | AAL at that frontier | [doc] (log §10) |
| Euler product and an FE defect in `L¹`, or in `L²` of polynomial size | none: the rational primes | — | [L*] |
| a two-sided edit with a count rate and a decaying FE defect | none: every nontrivial coefficient difference gives an Abel floor | — | [L*] (`not_tendsto_zero_of_coeff_ne`) |
| an unweighted countable system with defect `O(\|t\|^{−½+ε})` | none: the rational primes | — | [card] (Theorem II.1) |
| a fake at count exponent `β≤½` | balanced edits only; a one-sided edit has a real zero on top | — | [L*] (`balance_or_real_top_of_fake`) |

**The FE axis is measured [L*]; [D].** A fake two-sided edit has defect energy at least `(A²/(256πp₀))T log T`, where `p₀` is its least deleted prime and `A` its density, and its defect is not `≤c√log|t|`. If `Θ<1` — which `[X]` gives — fakes with defect energy `≤C_εT^{1+ε}` exist. So the defect of a fake lies between `√log` and `T^ε` in mean. The lower bound comes from the deleted prime and not from the zero: a fake zero costs no more on the FE axis than the edit that carries it. The pair of the signed grouped edit is the image of the pole of ζ under `s↦s+1−ρ₀`, and the images of the zeros of ζ are poles of the model, which is why the construction needs `Θ+β₀<3/2` [card]; [doc].

**Consequence [D].** A proof of AAL, B13 or Landing may use the functional equation up to a decaying error — no fake survives that — and may not use it up to an error of mean size `T^ε`: such an argument holds for a fake. On the count side an odd zero of the edit exponential at `ρ` needs `Re ρ≤2max(β,c₀,θ/3)` [L*]: a count below half the real part of a layer, with the continuation and the summability of the edit below it as well, excludes an odd fake zero there.

### 1.4 Two worlds, three atoms
`Θ≤7/8` [X]; `Θ<1⇔Θ∞<1`, and `¬(Θ<1)` ⇔ both abscissas equal one [L*]. A failure of RH is world I (a finite isolated top layer at `β≤7/8`) or world II (a tail with `½<Θ=Θ∞≤7/8`). RH ⇔ ZAL ∧ B13 ∧ Landing; B13 ⇔ the packet index is `0` or `∞`; AAL ⇔ at most one or infinitely many zeros right of every line [L*] (log §15). In world I `ψ(x)−x` attains `x^β` on every late window; non-attainment on windows, at the primes, or one exponent for all even moments gives AAL; filters reduce the growing-order current to centred cofactors [F].

### 1.5 Off the scale: each kind has a receiver and a kill
| Kind | Receiver | Kill | Evidence |
|---|---|---|---|
| homogeneous floor | a Green–Weil energy floor gives RH | the clock lies below Weil's form | [L*]/[F] |
| unit gap | an index-one approximant or realization gives RH | `Λ(s)/Λ(s+N)` has a unit gap iff RH | [L*] |
| certificate | feasible weights at every aperture give RH | certificates converge to `Λ` | [L*] |
| amplification | one exponent for all even moments gives AAL | all orders are sup bounds | [F] |
| symmetrization | a functional decreasing under projection | linear statistics are not monotone under projection | [L*] |
| replication | a bounded normalization of translates gives AAL | under a finite layer the normalization tends to zero | [L*] |
| positivity of a prime density | excludes a layer on the line of the pole | a compensator below that line | [F] |
| the count as a power | a bounded error forces the primes | fakes at every exponent above the pair | [L*]/[F] |
| the FE as a bound | a decaying defect forces the primes among edits | fakes with defect of mean size `T^ε` | [L*] |
| prime edits with a count rate | — | floor `≥13/30` | [L*] |

### 1.6 The producer: a theorem at `7/8`, a reach of `2/3`, a frame of `3/5` at every period
`Θ≤7/8` [X]. Its mechanism: the cube of a composite cubic Gauss sum is the ideal Möbius value times a phase [F]; a completed sum over the twists of ζ over `K=ℚ(ζ₃)` is bounded directly and compared with its signal; two estimates give a half-plane [L*] (`zetaZeroAbscissa_le_of_two_estimates`, `heckeHalfPlane_of_family_corrected_signal`).

**The frame [L*] (log §6, §16).** The correction factors through a sextic Grössencharacter `L`-function at `6s−3`. A zero `ρ` of `L(s,η)` and estimates below `Re ρ` force a zero of that `L`-function at `6ρ−3`. The continued correction has infinitely many zeros in `7/12≤Re s<2/3`. With estimates for the whole tower, `Θ≤max(σ₀,3/5)`; with GRH for the sextic Grössencharacters, `Θ≤σ₀` down to `7/12`. For every `6r`-periodic Gauss pairing, with local resonance norm `Q^{(4r−1)−6rs}`, the uncoupled boundary is `2/3` and the coupled fixed point is `(4r−1)/(6r−1)`, which is `≥3/5` with equality iff `r=1` (`gauss_pairing_6r_thresholds`). Raising the period moves the frame away from the line.

**The estimates [L*]/[F].**

| Statement | Value at `n=6` |
|---|---|
| the room of the published geometry: the binding bin `δ=79/204` | `[13/15,7/8]` |
| floor bin summed trivially, `R₀=1` | `13/15` |
| every Cauchy–Schwarz row sieve | `5/6` |
| square-root cancellation across the rows, `R₀=½` | half-plane `1−2/n`: `2/3` |
| corners of the sign-carrying designs `(κ,n)` | `(2,6)`: `8/9`; `(3,4)`: `25/28`; `(4,3)`: `49/54` |

Short columns are incoherent; the average row is target-free; the Gram of two rows is a completed sum twisted by the root numbers; the root number of a row is `G(u)γ₂(u)²` [L*] (log §16). The untwisted main term of the long columns is a theorem: `Σ_I N(I)^{−w}τ(I)²` is `ζ_K(3w−1)` times a squarefree sum; `M(s)D(s)` has a double pole at `4/3` with leading coefficient `108π³r³`, the rotated correlation `54π³r³`, the twisted squarefree combination a simple pole; a rotation by a unit `ε≠±1` reads only the layers `m≥2` [L*] (log §6, §16, §22).

**The port [L*]/[F].** `beta ≤ 7/8` follows from a uniform continuation margin for every Hecke `L`-function. Centred exceptional rows, source-shell energies and the comparison of the long radial energy with shorter retained energies are proved with the retained energies as hypotheses. Open in the port: the retained-energy induction and the character-uniform signed and ramified detector saving.

**Reach [D].** With every bin at square-root size the probe reaches `2/3`, the uncoupled boundary of every `6r`-periodic pairing. A pairing `(c,k)` reaches the line uncoupled iff `c=k/2−1` and coupled iff `c=(k−1)/2`; the `6r`-periodic Gauss pairings have `c=4r−1`. The corpus contains no other source.

### 1.7 Finite scale, the index, bound states
- Certified [L*]: exactly one negative square of the neutral part on every window with `R≤J`, `50J≤53R`, at every block size (block-matrix margin `1/5000`); at most one on narrow windows `16J≤R`, from the potential `≥−½` and the couplings `≥1/(2J)` alone; margins `1/20` (three blocks) and `1/100` (six half blocks) on the first step packets of ratio four; nonnegativity on thin step packets at every ratio.
- Counts [L*]: with all couplings `≥λ` the index is at most one plus the number of blocks with potential below `−λJ`; at a fixed ratio `Q` the block matrix has at most `(Q−1)⌈e^{E_Q}⌉` negative squares at every block size, at most `300000` at ratio four; RH says zero.
- Transfer [L*]: a margin above one scale passes to every refinement (`packetForm_refined_ge_half_of_margin`).
- Charges [L*]: below the polar ground energy every crossing is charged and the rank is at most two; this holds for apertures `≤½(log 2+1/50)` and energies `<1/20`; on windows with `4J≤R` a ground vector of the block matrix has one sign and both charges nonzero of one sign.
- Number rings and quotients [L*]: the contacts of a number ring are its point counts over the finite fields; a virtual configuration has the index of its zeros and poles off the line; Dedekind's divisibility on the line is a no-negative-square condition; `ζ_{ℚ(∛2)}` has its Hodge index; `n` copies of a quotient have the index of the quotient. Brauer induction holds in the corpus (`brauer_induction`); the reciprocity law that turns it into the index of every Artin character does not (A154).
- Li coefficients [L*]: `combW(Icc 1 N)(laguerreTail n N)/N→Re xiLiPaired n`.

### 1.8 The critical half-line state
RH, or a finite `W₀=inf_A windowThreshold(A)` with a function `F`: unit norm, supported on `u<0`, zero full energy at `W₀`, mixed energy zero against the whole energy domain [L*] (`riemannHypothesis_or_exists_weak_criticalHalfLineGroundState`). Two such states agree up to sign; `∫F(u)e^{zu}du≠0` for `Re z>0`; a zero-energy profile with one positive real Laplace zero vanishes; the reflected state is a logarithmic convolution of one `L²` half-line source [L*] (log §1, §13, §22). RH, or `R_polar<W₀`, or `∫F·polarSourceProfile=0` [L*] (`criticalHalfLine_weakEquation_classification`). No statement excludes a Laplace zero on the imaginary axis or decides the polar pairing.

Further objects that exist exactly when RH fails [L*] (log §20): an odd bound state; a defective hard-edge block; a point right of the line with `Re ξ′/ξ<0`; a negative definite Markov plane; an aperture with an empty feasible set; negative paired Li indices in every window of some bounded length.

### 1.9 Constituents and the zero field
No bounded holomorphic Dirichlet constituent and no Wiener expansion of ξ has a zero [F]. The centered zero field `L` is algebraic and normal over the fibre source field `K`; conjugation is central; every orbit is finite; the action is not transitive; every critical zero is fixed by every automorphism; every source automorphism displaces a zero by less than one. Over the field of squared widths the group is the closed group of sign families annihilating the square-class relations of the radicands `−δ_q²`. The reflection `ρ↦1−ρ` lifts to the Gaussian extension iff `−1` is not a square in `L`. `K_even⊆ℝ` ⇔ RH. An embedding fixing the prime trace field `B` sends each zero to a zero with centered real part `±` the original; the reflection field `H` equals `B` iff RH; an orbit that meets the line lies on it; a zero with rational real part has the orbit `{ρ,ρ̄}`; `p^ρ` and `r^ρ` both algebraic force `Re ρ∈ℚ` [L*] (log §4, §21). No statement gives an automorphism other than conjugation, classifies an orbit with irrational real part, or forces `H=B`.

### 1.10 Verification
RH through `exp(exp(C·a))` gives the sign on `[−a,a]` [L*]; `C` is not explicit. RH is verified through height 67 [F]. Positivity at aperture `a` confines every zero with `T₀≤|γ|≤2πe^a` to depth `<exp(−c log³|γ|)` [L*].

### 1.11 Law and point
One pointwise theorem holds past the Vinogradov–Korobov region: no zero right of `7/8` [X]. Left of it every unconditional theorem on the zeros of ξ is in law: twisted moments below the square root and a positive proportion of critical zeros of odd multiplicity; `67.25%` simple critical zeros in the objects of `Zeta23` [L*]; the squared right-depth moment `o(V)` [KR]; adaptive clusters with complete exterior mass `≤¼` around every sufficiently high zero of depth `≥exp(−c log³(T/2π))` [L*]; short-interval mean squares of `λχ` for every nonprincipal `χ` [L*]. For the principal character the top-scale blocks are `≤(log X)^{−3}` on `(log X)^{19}≤2π|w|≤X` [L*]; the low frequencies carry the pole.

### 1.12 Producers and receivers
| Mechanism | What the corpus proves |
|---|---|
| surfaces, sections, Riemann–Roch | identities; the square counts linearly |
| bounded-below heights | counts on prime rays ⇔ RH; hyperelliptic count law |
| families with monodromy | fixed parts; all moment orders are sup bounds |
| Frobenius with zero derivative | `p^{11/12}` at one prime |
| dominant halves | index law; reflected halves are no Dirichlet series |
| dominance in an ultrametric field | the Goss Riemann hypothesis |
| deformation, regulators | RH at every parameter; the count of the limit |
| recurrence | strong recurrence ⇔ RH; zero limits at a finite layer |
| sizes | the trivial aperture |
| the count as a power; prime edits | fakes at every exponent above the pair |
| the FE with the Euler product | rigidity up to a decaying defect; fakes at mean size `T^ε` |
| gluing of windows | one bound state ⇔ susceptibility product `≥1`; certified ranges |
| critical compactness | a unique critical state with a zero-free Laplace transform |
| mean values | in law |
| reciprocity families with two estimates | `Re s>7/8` [X]; reach `2/3`; frame `≥3/5` at every period |

**Consequence [D].** One mechanism has produced a pointwise theorem, and its whole class of `6r`-periodic Gauss pairings stops above `½`. Every other mechanism of the corpus is a receiver, a model or a rigidity theorem.

### 1.13 What is ruled out
| Mechanism | Verdict | Evidence |
|---|---|---|
| explicit formula, positivity, Euler products over integer norms or the rational primes with a count rate, as a constraint on a finite layer, a tail, landing | realized by models | [L*] |
| the functional equation used up to an error of mean size `T^ε` (convexity bounds, zero counts, growth in the strip), as a constraint on a finite layer | holds for fake edits if `Θ<1` | [L*]; [D] |
| a lower bound for the FE defect that depends on the depth of a fake zero alone | the constants are those of the least deleted prime; a depth-only bound has to couple the defect with the count remainder | [card] (Corollary III.2) |
| boundedness of the FE defect as a selector among signed weights | a fake with a bounded defect | [L*] |
| an exponent below `3/5` reached by the frame of a `6r`-periodic Gauss pairing, or below `2/3` without estimates beyond square root | the coupled tower; the uncoupled boundary | [L*]; [D] |
| a Cauchy–Schwarz row sieve below `5/6`; geometry or row counts below `13/15` | budget | [L*]/[F] |
| windows below the logarithmic radius; one-sided floors of one length | models | [L*]/[F] |
| regulators, paths, certificates, amplification, replication, symmetrization as sources | kills | [L*]/[F] |
| bounded or Wiener constituents with a zero | none | [F] |
| the return transfer from a strip to the line | RH under a strip | [F] |
| positivity alone as a 70% census certificate | cost `>13/10` | [L*] |
| a transitive Galois action on the zeros; a real symmetry of the prime translations besides conjugation | none | [L*] |

## 2.1 Tasks that are just work

Difficulty is established where a known argument exists; `(unverified)` marks the rest. None of these decides RH.

### The half-plane `Re s>7/8` in Lean
| # | Task | Routes | Basis |
|---|---|---|---|
| A118 | the retained-energy induction; the character-uniform signed and ramified detector saving; the uniform continuation margin of the receiver | JAS, MC, S3 | `beta_le_seven_eighths_of_uniform_margin`, `actual_original_radial_comparison`, `actual_source_shell_subpower`, `exceptional_rectangle_estimate` |
| A138 | the corollaries of `Θ≤7/8` as unconditional statements: rung `κ<4/3`, level `11/8`, returns `y^{1/8}`, ringdown `1/16`, critical-comb growth `≤3/8`, fake edits with subpolynomial defect energy at every `½<β₀<5/8` | every scale route | §1.2; `frontier_dichotomy` |
| A141 | the half-plane for fields containing `ζ₃` and every ray class character (unverified) [C] | ACS, HF | frame for every Hecke character |

### The FE axis and the models
| # | Task | Routes | Basis |
|---|---|---|---|
| A153 | Lean statements for Theorem II.1 (a defect `O(\|t\|^{−½+ε})` forces the rational primes among unweighted countable systems), Theorem II.3 (positive real weights: a fake with defect below any unbounded nondecreasing `Φ`), Corollary III.2 and the prime weights of II.2(b) | ZCG, BAG | [card]; `HamburgerStripDefect` |
| A155 | the order law at every multiple: divisibility by `k` of the order of a zero of the edit exponential above `k` times the count exponent, for `k≥3` (unverified) | ZCG | `even_order_of_count` (`k=2`) |
| A157 | the count of the signed grouped edit by Perron's formula left of `½` (unverified) | ZCG, BAG | `sub_one_mul_zetaSeriesC_eq`, `differentiableOn_editCofactor` |
| A144 | the tangent data of `μ` and `λ` under additive twists (unverified) | ZCG, MC | [F] |

### The producer's estimates and its calibration
| # | Task | Routes | Basis |
|---|---|---|---|
| A148 | the layers `m=0,1` of the theta-square series and the target component of a twisted column [C] | MC, JAS, PM | `thetaSqDirichlet_double_pole`, `rotatedCorrelation_eq_three_layer` |
| A149 | the floor bin over `𝔽_q[T]`, `q≡1 mod 6`: Kubota series rational in `q^{−s}`; the long columns evaluated exactly (unverified) [C] | MC, JAS | CRF |

### Assemblies of proved pieces
| # | Task | Routes | Basis |
|---|---|---|---|
| A142 | an explicit constant in the verification rate `exp(exp(C·a))` | RW, SRT, TH, LI, HCF | `exists_doubleExp_windowPositive` |
| A146 | the sign of `𝔚_4` and `𝔚_7` at every block size: certified margins up to the transfer threshold, or A142 with a verified height (unverified) | ACS, HF, RW | `packetForm_stepPacket_ratioFour_ge`, `packetForm_refined_ge_half_of_margin` |
| A154 | the reciprocity law for induced one-dimensional characters; with `brauer_induction` it gives the index of every Artin character [C] | ACS, HF | `exists_le_negIndex_quotient_iff`, `exists_le_negIndex_power_iff` |
| A156 | the susceptibilities of the certified windows (ratio `≤103/50`, narrow windows) and the gluing criterion tested on unions that are themselves certified (unverified) | ACS, HF | `hermNegIndex_glued_eq_one`, `hermNegIndex_neutralWindow_eq_one` |
| A140 | the sign on windows of half-width below `½log 5` (unverified) | RW, ACT, EWU, OWU | [F] |

### Finite verification and explicit constants
A1 certified `RHVerifiedThrough T` past 67; A2, A3 numeric heights and first-window membership; A4, A5 theta ranks 15 and beyond (unverified); A6, A7 cone widths, anti-diagonal certificates (unverified); A9, A13 eighth-root constants, near-gcd charges (unverified); A117 end points of the feasible interval of `w(2)`; A19 an explicit heat-horizon height; A48, A58 Hasse–Weil tests, effective gap iteration (unverified).

### Classical inputs to formalize
| # | Task | Basis |
|---|---|---|
| A18 | twisted second moments past the square root [C] | `θ<½` in Lean |
| A147 | logarithmic two-point Chowla: for the principal character the low frequencies, the assembly of the ladder on a frequency set with Parseval, the transfer to `V(b/s,T)` [C] | `exists_short_sum_mean_square_twLiouville_le` (`χ≠1`), `exists_norm_blockQ_liouville_le`, `ladder_master_on`, `exists_scale_corr_close`, `exists_abs_avg_corr_le` |
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | `weyl_law_order` |
| A33 | Fourier coefficients of the cubic residue at all heights [C] | [F] |
| A41 | count law for every curve, first plane quartics [C] | hyperelliptic case [F] |
| A120 | a finite nonempty stratum with both structures: Selberg zeta functions of surfaces with a small eigenvalue [C] | — |

Further: A16, A20, A24, A28, A30, A42, A46, A54 (unverified).

## 2.2 Open mathematical obstacles

`≥qRH`: implies a zero-free half-plane, Lindelöf or ZAL; with `[X]` open where it gives a half-plane below `7/8`.

### The common minimal face
| # | Problem | Strength | Routes |
|---|---|---|---|
| B130 | `P(p)≤A(p)+K` on the primes of late logarithmic windows | RH | ACS, SRT, WL, HF, ZCG, HAT-C |
| B159 | a rung `κ≥4/3` with a saving that fails for the Liouville twist | a half-plane below `7/8` | sign routes, BAG |
| B144 | separation of the deep off-line ordinates | sub | SRT, ACS |

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1, B152 | the sign on every window; one negative square of the neutral part at every ratio and block size | RH | all sign routes; ACS, HF |
| B189 | the gluing law on actual windows: for adjacent windows with one bound state each, charge vectors below the couplings for which the lowered windows keep their sign on the kernels and the susceptibility product is `≥1`; first for `(R,2R]` and `(2R,4R]` at every block size (§2.21) | method; sub at each ratio | ACS, HF, RW |
| B2, B4, B5 | no crossing along the aperture; outer predictors; kick admission | RH | RW, GWZ, WTZ |
| B6, B8, B101 | full-space sign at every critical multiple; head thresholds; polar payment | RH | HF, SRT, AIP |
| B104 | whether the critical half-line state is charged; zeros of its Laplace transform on the imaginary axis (§2.8) | method | HF, SRT, AIP, ACS, SC |
| B123, B156 | correlated pairings dominating the depleted kernel; cluster exclusion on a rung | method | HF; SA, RW |
| B160 | `JasDressedPSD 1` | RH | JAS |
| B9–B12, B14, B23 | zero mode; top stratum; exact SOS; index ceiling; interior width; `N_d` bounded | RH / ≥qRH | HF, SC, ACS, CHMD, LA |
| B16, B17, B3 | decay law of the margin; signed ground states; variation of `r` | sub / method | CHT, RW |
| B19–B22, B24, B25, B102 | theta ranks and heads; outer Jensen roots; collisions; frequency below one | RH | TH, LA, ZCG |
| B27, B28, B47 | runs of simple critical zeros; local positivity at fixed `λ`; multiplicity | sub | ZCG, RW |
| B29–B45 | the single open estimates of PTR, HCF, PA, XN, GTA, TT, CHMD, RN, SZ, TG, SC, ACS, HF, FU/CFC/RP, LI, ACT, AIP | RH | as named |
| B124 | finite initial depth budgets of the heat divisor | ≥qRH to RH | ZCG, LA |
| B146, B171 | an independent family of bounded index; a form of signature `(1,∞)` | RH (producer) | W1C, PTR, IRP, PM |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B161 | a signal bound `O(Z^b)` for some `b<7/8` | a half-plane below `7/8` | JAS, MC |
| B174 | the row count of the binding bin `δ=79/204` | a half-plane in `[13/15,7/8)` | JAS, MC |
| B185 | the long columns: a power saving in the first moment of the root numbers `G(u)γ₂(u)²` against a dual column, uniformly in the column (§2.4) | a half-plane in `(2/3,13/15)` | JAS, MC |
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
| B145 | the prime-weighted centred type-II current at a growing isolated mode (§2.6) | AAL [D] | ZCG, BAG, ELT |
| B150 | arithmetic control beyond frequency one | sub | census |
| B173 | a two-sided subexponential bound of the trace on windows of one length | AAL | ZCG |

### Γ — selection, reflection, position
| # | Problem | Strength | Routes |
|---|---|---|---|
| B13, B138, B141 | finite stratum; landing; Deuring–Heilbronn for ζ | sub | whole programme |
| B83, B170 | AAL; non-attainment for ζ | sub / AAL | BAG, JAS, SC, ZCG, WL |
| B157 | what excludes a finite stratum when both structures are present | method | BAG, ZCG, ELT |
| B183 | a fake with count exponent `β<½` and a non-real pair alone on top; it must be balanced | method | WL, MC, BAG, ZCG |
| B191 | a fake with subpolynomial defect energy at `β₀≥3/2−Θ`; the order of the least defect energy of a fake between `T log T` and `T^{1+ε}` | method | ZCG, BAG |
| B190 | the orbit of a zero with irrational real part under the embeddings fixing the prime trace field; an automorphism of the zero field besides conjugation (§2.19) | method | LA, ZCG |
| B89, B112, B128 | aligned returns; FE into vertical transport; replication | sub | BAG, ZCG, EFT |
| B68, B71, B178, B188 | reflection Krein positivity; universal decay; a rate from the horizon; the congruence mechanism for resonances (§2.7) | RH; producer | PM |
| B69, B72–B76, B80, B81 | lossless stack; target mass; candidate landings; FE twins | RH / sub / producer | PTR, BAG, SEL, candidates |
| B86, B87, B88 | endpoint characters; a count defined without `Q`; the sign of the comb finite part | RH | ECP, ACS, HF, PM |
| B114, B117, B147 | partner involution; a regulator with a gap; Shimura nonvanishing | producer; indep. | PM |
| B149, B169 | Bézout from a property of the object; a doubling with a canonical height | RH (producer) | ACS, HF, AGZ |
| B172 | a functional decreasing under projection outside the finite-statistics class | producer | ZCG, HF |
| — | ZAL | ≥qRH | whole programme |

### Settled questions
| # | Question | Answer | Evidence |
|---|---|---|---|
| B186 | What does a fake zero cost in the functional equation? | no fake has a decaying defect; fake edits have defect energy `≥cT log T`, `c` from the least deleted prime; if `Θ<1`, fakes with defect energy `≤C_εT^{1+ε}` at every `½<β₀<3/2−Θ`; among signed weights a bounded defect has a fake; the zero adds no cost beyond the edit | [L*] (log §3, §12); II.1, II.3, III.2 [card] (A153) |
| A151 | the FE defect of the pair twin and of the quartet edits | `g=2iζ·Im M` with `M` the cofactor on the line; the quartet defect is unbounded with the `T log T` energy | [L*] (`pairTwin_stripDefect_eq`, `quartetTwin_defect`) |
| A150 | Brauer induction | the Brauer elementary monomial virtual characters generate the virtual characters | [L*] (`brauer_induction`) |
| B184 | How far does the frame of the producer reach? | zero transfer `ρ↦6ρ−3`; `max(σ₀,3/5)`; `7/12` under sextic GRH; every `6r`-periodic Gauss pairing has coupled fixed point `(4r−1)/(6r−1)≥3/5` | [L*] (log §16) |
| B104 (finite scale) | Is a ground vector of the block matrix charged? | yes on windows with `4J≤R`: one sign, both charges nonzero of one sign | [L*] (`charges_mul_pos_of_blockMatrix_minimizer`) |
| — | Is there a gluing lemma for windows? | one bound state iff the susceptibility product is `≥1`; two if both are negative with product `<1` | [L*] |
| — | Is the critical half-line state unique? | yes, up to sign; its Laplace transform has no zero on `Re z>0` | [L*] (log §1) |
| B179 | Is the index a Maslov index? | the crossing multiplicity is a Lagrangian intersection number; the far end carries the zeros | [L*] (log §14) |
| B175 | Signed cancellation across the rows of the floor bin | average row and short columns settled; untwisted main term a double pole at `4/3`; the twisted columns are B185 | [L*] (log §6, §16) |
| A143 | the sign of `𝔚_4` | margins at the first block sizes; every block size at ratio `≤103/50`; at most `300000` negative squares at ratio four; zero at every block size is A146 | [L*] |
| A152 | ordinary convergence of a power comb | converges ⇔ every zero has `Re ρ<1−a` | [L*] |
| A145 | Artin characters beyond the monomial case | index of quotients and of their powers; Brauer induction; the reciprocity law is A154 | [L*] |
| — | Does a count rate above `√x` force a real zero on top? | no | [L*] (`exists_isEdit_fake_with_zero_pair`) |
| — | Are the nullities along the aperture even? | no: a single simple null mode | [L*] |
| B176, A132 | the cost of a window | double exponential | [L*] |
| B182 | least count remainder of a fake | fakes at every exponent above the pair; the greedy pair twin has `β≥Re ρ/2` | [L*] |
| B177, B158, B169 (path half), B148 (strength), B94, B181, B156 (configurations), B117 (three regulators), B172 (first order), B153 | as recorded in the walls ledger | theorems; models; kills | [F]/[KR] |

## 2.3 Frankenstein routes

**No assembly closes RH.** One assembly is a theorem (`[X]`). Every other assembly has an open input of RH or AAL strength, a half-plane input, or returns an identity.

| # | Parts | What the assembly gives | Missing input | Gain |
|---|---|---|---|---|
| F29 | **One scale** | every graded receiver is one number; the critical comb reads it on one sequence | a level below `7/8`; in Lean any level | a proposed estimate is placed before work starts |
| F30 | **Two estimates, fully evaluated.** Frame, coupled tower, barrier at every period, budget, coherence, theta-square poles | `[X]`; with square-root cancellation `2/3`; frame `≥3/5` for every `6r`-periodic pairing [L*]; [D] | A118; B174, B185; B187 | the exact reach of the only producer class |
| F31 | **Half-plane, then line** | rung `4/3`, level `11/8`, returns `y^{1/8}` | a step from a strip to the line | none: every transfer is RH |
| F39 | **The index at three scales.** Finite-scale neutral part, index law in the aperture, verification rate | RH ⇔ no crossing ⇔ one bound state of every window; certified on ratio `≤103/50` and narrow windows [L*] | B152; A146 | one exact finite object per window |
| F44 | **Gluing induction.** Certified windows, the gluing law, lowered potentials, the sink count, charged ground vectors | a window of ratio four holds one bound state at every block size if the susceptibility product of its two dyadic halves, lowered, is `≥1` [D] | B189; A156 | an induction on the ratio whose step is one inequality between two numbers |
| F45 | **The critical object.** Thresholds, the critical half-line state, the index law, objects of a failure | a failure of RH has a unique extremal function with a zero-free Laplace transform; a contradiction at this object is RH [L*] | B104; a Laplace zero in the closed half-plane | the place where a proof by contradiction on the Σ side has to act |
| F40 | **Models plus rigidity.** Two-sided edits, signed grouped edits, signed weights, FE rigidity, Abel floors | the door of world I: the reflection up to a decaying error, or a count below half a layer [D] | B183, B191 | a proposed AAL argument is tested on the fakes before work starts |
| F41 | **World I off the scale.** Non-attainment, unit gap, filters, currents, tangent data | AAL from any receiver form [F] | B170, B145 | — |
| F42 | **The lattice with a level.** Index law for number rings, quotients, powers; Brauer induction; `[X]` | for `ζ_{ℚ(∛2)}` and the Artin character of `X³−2`: the index counts zeros in `(½,7/8]` [D] | A141, A154 | the index of every comb counts zeros in one strip |
| F43 | **Galois and continuation.** Zero field, prime trace field, Jensen quartets, heat counts | `K_even⊆ℝ` ⇔ `H=B` ⇔ RH; orbits in `{±δ}` [L*] | a restriction forcing `H=B`; B190 | none below RH |
| F37 | **Verification with a rate** | window sign from a double-exponential height | A142, A146 | finite statements with stated sizes |
| F38 | **Mean values and cameras** | a positive proportion on the line; adaptive isolation of deep zeros; short-interval Liouville mean squares for `χ≠1` | A18, A147; B59 | the in-law half is native |
| F11 | **Construct, then identify** | an approximant with a gap gives RH | B146, B171 | regulators excluded |

**Closest to the open core:** F44 (the induction step of Σ), F30 (the producer's exact reach), F40 (the door for world I).

### What a contradiction search may assume in world I
`Θ≤7/8` [X]; an attained isolated top `β≤7/8`; `ψ(x)−x` attains `x^β` on every late window and at the primes [F]; quantized multiplicities [F]; normalizations of translates tend to zero [L*]; a nonzero Euler filter accelerates the horocycle rate [F]; the packet index is finite and positive [L*]; a two-sided edit with a count rate above the top removes the layer [L*] (`exists_isEdit_zero_free_of_finite_layer`); the critical half-line state exists and is unique [L*]. No contradiction comes from identities alone, positivity, Euler products over integer norms or the rational primes with multiplicities `0,1,2`, a count rate, the FE with Gamma factor and count, the FE up to an error of mean size `T^ε`, a regulator, or any statement in law [L*].
