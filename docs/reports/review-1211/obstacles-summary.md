# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: `dd55ee70d9` (2026-11-12), working-tree sources included. Fact log: `logs/review-1211-rev2-facts.md` (cited as "log §n").

**Evidence.** `[L*]` Lean statement read at the declaration for this report and recorded in the fact log; `[doc]` content of a module docstring whose theorem names were read but not every statement; `[F]`, `[KR]` stated by the frontier map and the scoped-obstruction ledger; `[S]` module graded unfinished by the frontier map; `[card]` proved on the pipeline card `docs/drafts/pipeline/3-formalized/b186-critical-line-fe-defect-of-fake-zeros.md`, no Lean declaration; `[D]` deduction made here from `[L*]` statements, not a Lean theorem; `[C]` classical mathematics quoted from memory, not in the corpus; `[A]` assessment; `[X]` the external theorem cached in the repository (OpenAI, 30 September 2026), taken as proved: every Dirichlet `L`-function, ζ included, and every finite-order Hecke `L`-function over `ℚ(√−3)` is zero-free in `Re s>7/8`. The Lean graph proves `zetaZeroAbscissa ≤ 1` unconditionally and `beta ≤ 7/8` from a uniform continuation margin; the native steps of `[X]` are just work (A118). Sections 2.3–2.21 are interpretation and ideation: every untagged statement there is a proposal.

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
RH, or a finite `W₀=inf_A windowThreshold(A)` with a function `F`: unit norm, supported on `u<0`, zero full energy at `W₀`, mixed energy zero against the whole energy domain [L*] (`riemannHypothesis_or_exists_weak_criticalHalfLineGroundState`). Two such states agree up to sign; `∫F(u)e^{zu}du≠0` for `Re z>0`; a zero-energy profile with one positive real Laplace zero vanishes; the reflected state is a logarithmic convolution of one `L²` half-line source [L*] (log §1, §13, §22). RH, or `R_polar<W₀`, or `∫F·polarSourceProfile=0` [L*] (`criticalHalfLine_weakEquation_classification`). The polar pairing remains open.

**Post-checkpoint Lean update.** Imaginary-axis zeros are also excluded: `criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero` proves nonvanishing for `Re z≥0`. Testing the weak equation against the real undamped resolvent cancels its arithmetic and polar mixed terms, leaving strictly positive weighted mass. The unconditional RH-or-state theorem passed its transitive axiom audit. [Proof and declarations](../../drafts/pipeline/3-formalized/critical-half-line-boundary-laplace-exclusion.md).

The state also has positive square mass in every terminal interval `(-d,0)`, `d>0`: a support gap would allow a right translate with strictly negative critical energy. `criticalHalfLineGroundState_endpoint_mass_pos` and its unconditional RH-or-state dichotomy are Lean verified. [Proof and declarations](../../drafts/pipeline/3-formalized/critical-half-line-terminal-support.md). Together with boundary nonvanishing, this excludes the singular inner delay and proves its [Cayley Laplace multiplier outer](../../drafts/pipeline/3-formalized/critical-half-line-laplace-outerness.md). Its reflected profile is [cyclic for causal translations in half-line L²](../../drafts/pipeline/3-formalized/critical-half-line-ground-state-outerness.md). The polar pairing remains open.

Its finite causal sums have an [exact positive tail-square energy formula](../../drafts/pipeline/3-formalized/critical-causal-energy-factorization.md), without a one-sign assumption on the state. Distinct positive delays give strictly positive energy matrices; delay zero adds exactly the critical-state null direction. At a terminal wall `-h`, the sharp energy floor in the eighth-exponential norm is `criticalAliasCoefficient W₀·(1-exp(-8h))`; its extremizers are precisely scalar multiples of `F(·+h)`, modulo null sets. All statements have Lean-verified unconditional RH-or-state specializations. Density in the energy norm and the polar pairing remain open.

The critical-state line has a [positive transverse exponential gap](../../drafts/pipeline/3-formalized/critical-half-line-transverse-energy-gap.md). If `N_F(G)=G-⟨F,G⟩F`, then `γ∫N_F(G)²exp(-8u)≤E(G)` for some `γ>0`, throughout the actual energy domain. Moreover `|P(G)-⟨F,G⟩P(F)|²≤C E(G)` for the literal polar pairing `P`. Smooth recovery, compactness, and uniqueness discharge the analytic inputs in Lean. The remaining polar uncertainty is `P(F)`.

The [actual ground-energy branch](../../drafts/pipeline/3-formalized/critical-half-line-ground-energy-branch.md) is attained at every positive ratio. Near a finite global threshold its normalized minimizing line is unique, and its derivative at `W₀` is `-a(W₀)W(F)/W₀`. A quantitative weighted bound controls both state variation up to sign and variation of its polar pairing. Gamma integrability of the limiting state is derived in Lean. The critical polar charge remains undecided.

[Global simplicity](../../drafts/pipeline/3-formalized/global-confining-half-line-ground-state.md) now holds at every positive ratio: the normalized minimizers form one line, with zero-free Laplace transform on the open right half-plane. Ordinary-mass preservation transfers the causal-reflection defect to the form shifted by its attained floor. This classification is independent of RH and of a finite threshold; it assumes no sign condition on the state.

The floor is [strictly concave in the reciprocal ratio](../../drafts/pipeline/3-formalized/strict-concavity-of-confining-half-line-energy.md). A normalized profile cannot minimize at two positive ratios: subtracting its weak equations would confine its support to one exponential level set. Its minimizing eighth-exponential mass strictly decreases as confinement strengthens. These global variation laws are Lean verified independently of RH.

[Strong confinement](../../drafts/pipeline/3-formalized/strong-confinement-logarithmic-excess.md) has the sharp logarithmic excess `λ(R)=a(R)+log a(R)+O(1)`, where `a(R)=criticalAliasCoefficient R`. Every normalized minimizer satisfies `c/a(R)≤W(F)-1≤C/a(R)` for fixed positive constants at sufficiently large strength. The actual-domain correlation deficit gives the lower cost, and normalized compact-source dilates give the upper cost. Both conclusions are Lean verified independently of RH.

Further objects that exist exactly when RH fails [L*] (log §20): an odd bound state; a defective hard-edge block; a point right of the line with `Re ξ′/ξ<0`; a negative definite Markov plane; an aperture with an empty feasible set; negative paired Li indices in every window of some bounded length.

### 1.9 Constituents and the zero field
No bounded holomorphic Dirichlet constituent and no Wiener expansion of ξ has a zero [F]. The centered zero field `L` is algebraic and normal over the fibre source field `K`; conjugation is central; every orbit is finite; the action is not transitive; every critical zero is fixed by every automorphism; every source automorphism displaces a zero by less than one. Over the field of squared widths the group is the closed group of sign families annihilating the square-class relations of the radicands `−δ_q²`. The reflection `ρ↦1−ρ` lifts to the Gaussian extension iff `−1` is not a square in `L`. `K_even⊆ℝ` ⇔ RH. An embedding fixing the prime trace field `B` sends each zero to a zero with centered real part `±` the original; the reflection field `H` equals `B` iff RH; an orbit that meets the line lies on it; a zero with rational real part has the orbit `{ρ,ρ̄}`; `p^ρ` and `r^ρ` both algebraic force `Re ρ∈ℚ` [L*] (log §4, §21). No statement gives an automorphism other than conjugation, classifies an orbit with irrational real part, or forces `H=B`.

### 1.10 Verification
RH through `exp(exp(C·a))` gives the sign on `[−a,a]` [L*]; `C` is not explicit. RH is verified through height 67 [F]. Positivity at aperture `a` confines every zero with `T₀≤|γ|≤2πe^a` to depth `<exp(−c log³|γ|)` [L*].

### 1.11 Law and point
One pointwise theorem holds past the Vinogradov–Korobov region: no zero right of `7/8` [X]. Left of it every unconditional theorem on the zeros of ξ is in law: twisted moments below the square root and a positive proportion of critical zeros of odd multiplicity; `67.25%` simple critical zeros in the objects of `Zeta23` [L*]; the squared right-depth moment `o(V)` [KR]; adaptive clusters with complete exterior mass `≤¼` around every sufficiently high zero of depth `≥exp(−c log³(T/2π))` [L*]; short-interval mean squares of `λχ` for every nonprincipal `χ` [L*]. For the principal character the top-scale blocks are `≤(log X)^{−3}` on `(log X)^{19}≤2π|w|≤X` [L*] and the twisted partial sums are `o(N)` for `2|τ|≤√N` [S]; the low-frequency mean square is not assembled.

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
| A153 | Lean statements for Theorem II.1 (a defect `O(\|t\|^{−½+ε})` forces the rational primes among unweighted countable systems), Theorem II.3 (positive real weights: a fake with defect below any unbounded nondecreasing `Φ`) and Corollary III.2; the Euler weights of II.2(b) are `hasProd_signedPoly` [S] | ZCG, BAG | [card]; `HamburgerStripDefect` |
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
| A147 | logarithmic two-point Chowla: for the principal character the low-frequency mean square with reciprocal weights, the assembly of the ladder on a frequency set with Parseval, the transfer to `V(b/s,T)` [C] | `exists_short_sum_mean_square_twLiouville_le` (`χ≠1`), `exists_norm_blockQ_liouville_le`, `ladder_master_on`, `exists_norm_sum_liouvilleTwist_le` [S], `exists_scale_corr_close`, `exists_abs_avg_corr_le` |
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
| B104 | whether the critical half-line state is charged (§2.8) | method | HF, SRT, AIP, ACS, SC |
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
| F45 | **The critical object.** Thresholds, the critical half-line state, the index law, objects of a failure | a failure of RH has a unique extremal function with a zero-free Laplace transform; a contradiction at this object is RH [L*] | B104 | the place where a proof by contradiction on the Σ side has to act |
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

**No statement about the zeros of ζ below RH and AAL passes all tests as a door to the line.** The questions below were checked against the corpus by sentence queries (log §13, §14, §18, §21, §22, §24).

## 2.4 Breakthrough question below RH and below the half-plane `7/8`: the long columns (B185)

**Position.** The only producer of the corpus converts a law over a family of twists into a point by two estimates. Everything it does with squares is mapped and stops at `13/15`, then `5/6` (§1.6). Its floor bin is reduced in Lean to one object: the short columns cancel (`sum_pairColumn_eq_zero`), the short Gram is bounded (`norm_gramEntry_le`), the average row is target-free (`average_rowLocalSum`), and what remains are the long columns: first moments over the rows of the root numbers `G(u)γ₂(u)²` (`rowRootNumber_eq_thetaPhase_mul_sq`) against a dual column [L*]. The untwisted main term of these moments is a theorem: `Σ_I N(I)^{−w}τ(I)²=C̄²ζ_K(3w−1)·(squarefree sum)`, `M·D` has a double pole at `4/3`, and the twisted squarefree combination a simple pole [L*] (log §6, §22).

**Question (B185).** *Is the first moment of `G(u)γ₂(u)²` over squarefree rows `u` of norm up to `U`, twisted by a dual column `n` of norm up to the row scale, equal to its main term plus `O(N(n)^A U^{R₀+ε})` with some `R₀<1`, uniformly in `n`? What is the least such `R₀`?*

| Answer | Effect [D]: the half-plane `1−2/(3(6R₀−1))` of the signed-Gram curve at `n=6` (log §24) |
|---|---|
| any `R₀<1` | a half-plane below `13/15`: the first estimate of the producer that is not a square |
| `R₀<5/6` | below the floor `5/6` of every Cauchy–Schwarz sieve |
| `R₀=2/3` | `7/9` |
| `R₀=½` (square-root remainder) | `2/3`: the uncoupled boundary of every `6r`-periodic pairing, the end of the class |
| no saving uniformly in the column | the producer stops at `13/15` through its floor bin; every graded receiver keeps `[X]` as its only level |

Every receiver of the scale moves with the answer: the rung, the level, the return bound, the ringdown rate, the tails, the critical-comb growth, the range `½<β₀<3/2−Θ` of the fakes with subpolynomial defect energy.

**First step and obstacle.** A149 (the function-field floor bin, where the Kubota series is rational [C]) and A148 (the layers `m=0,1` and the target component of a twisted column; the rotated correlation reads only `m≥2` [L*]). Named obstacle: uniformity in the column. The corpus has neither a sextic metaplectic Eisenstein series nor a sextic large sieve, and every Cauchy–Schwarz row sieve stops at `5/6` [L*] (`two_le_of_sieve_threshold`).

**Tests.** T1 passes (an estimate for Gauss sums; its consequence a half-plane below `7/8`). T2, T4, T6 pass. T3 named. T5 calibrated on the average row (target-free), on the short columns (incoherent) and on the untwisted main term (a double pole). T7 moves Π167, Π175. T8: the square-root form is a conjecture of Patterson type [C]; any power saving uniformly in the column is the question, with a first step in corpus objects.

**Limit.** `2/3`. The question does not lead to the line.

## 2.5 Breakthrough question for the search for a producer: a pairing whose frame reaches the line (B187)

**Position.** The class of the one producer is closed by two theorems. In the budget of rows of conductor exponent two, square-root cancellation gives the twist exponent `(n−4)/(n−1)`, the half-plane `1−2/n` (`signedGram_phase_endpoints`), which is the line exactly at twist order `n=4`. In the frame, every `6r`-periodic Gauss pairing has local resonance norm `Q^{(4r−1)−6rs}`, uncoupled boundary `2/3` and coupled fixed point `(4r−1)/(6r−1)≥3/5` (`gauss_pairing_6r_thresholds`) [L*].

**Pairing coordinates [D].** A pairing with local resonance norm `Q^{c−ks}` has uncoupled boundary `(c+1)/k` and coupled map `b↦(c+b)/k` with fixed point `c/(k−1)`. The uncoupled boundary is the line iff `c=k/2−1`; the fixed point is the line iff `c=(k−1)/2`. The Gauss pairings have `c=(2/3)k−1`: the period changes `k` and leaves the ratio `c/k→2/3`. The Möbius sign comes from Gauss sums of odd order [L*] (`exists_gaussSum_pow_orderOf_eq_of_odd`), and the sign-carrying designs of the corpus are `(κ,n)=(2,6),(3,4),(4,3)` with corners `8/9`, `25/28`, `49/54` [L*]/[F].

**Question (B187).** *Is there an identity that writes the Möbius function through coefficients with a reflection whose local resonance norm `Q^{c−ks}` has `c/(k−1)<3/5` — in the best case `c≤(k−1)/2` — and whose rows have conductor exponent two with principal frequencies of order four? Or does every Möbius-signed pairing of Gauss and Jacobi sums have `c/k≥2/3−1/k`, so that the class ends at `3/5`?*

| Answer | Effect |
|---|---|
| a pairing with fixed point `½` and a design with square-root endpoint `½` | a producer of the line by estimates: the remaining input is square-root cancellation in its bins |
| a pairing with fixed point in `(½,3/5)` | the frame moves below `3/5`; its estimates and its tower are the next object |
| `c/k≥2/3−1/k` for every Möbius-signed pairing | the Gauss-sum producers end at `3/5` (`2/3` by estimates of square-root size): RH needs a source of another kind |

**First step and obstacle.** Classify the Möbius-signed products of Gauss and Jacobi sums over cyclotomic rings by `(c,k)` and `(κ,n)`: finite algebra in the objects of `exists_prod_jacobiSum_eq`, `exists_gaussSum_mul_gaussSum_eq` and `gauss_pairing_6r_thresholds`. Second model class [C]: Rankin–Selberg and symmetric-power towers, whose coupling maps are not of Gauss type. Named obstacle: the theta coefficients of covers of degree four and higher are not known explicitly [C], so the source identity of a design has to be proved before its exponents mean anything.

**Tests.** T1: a producer question, implied by nothing about ζ's zeros. T2: an existence statement or a classification theorem. T3 named. T4 pass. T5 calibrated on the `6r` pairings (a theorem), on the three designs, on even order (parity instead of sign). T6, T7 (moves Π174, Π177) pass. T8 not a named problem; the first step is finite algebra in corpus objects.

**Limit.** The coordinates are an exponent model: a pairing that reaches `½` in them needs its source identity, its estimates and its tower.

## 2.6 If positivity, Weil positivity and spectral methods are excluded

"Spectral" covers spectral theory of operators in every form, automorphic spectral theory included; "positivity" covers nonnegativity of forms, kernels, counts, coefficients and averaging measures. Kept: Fourier analysis, Poisson summation, exact identities of Gauss and Jacobi sums, reciprocity, mean values used as bounds, exponential sums, continuation and orders of zeros, integrality, recurrence, Galois theory, dominance in ultrametric fields.

**What the constraint removes [A].** The positivity forms (all of Σ, with the index, the bound states and the critical state), Landau's theorem and with it the balance law of edits, the proofs of FE rigidity and of the Abel floors (positivity of Abel means), the large sieves, and the Eisenstein reflection of the theta row. **What survives [L*].** The receivers of the minimal face in absolute value; the Galois forms `L=K` ⇔ `H=B` ⇔ RH; the Goss dominance; the order law (a zero of an edit exponential above twice the count exponent has even order, `even_order_of_count`); the reciprocity identities of the probe; the filters and currents of world I [F].

**Two facts that shape the question [D].**
- `Σλ(n)Λ(n)n^{−s}=ζ′/ζ(s)−2ζ′/ζ(2s)` has in `Re s>½` the pole at `1` and poles exactly at the zeros of ζ: AAL is invariant under the Liouville twist, and the parity blindness of bilinear statements is no obstruction to AAL.
- A sign-free argument for AAL has to pass the door of §1.3: it may not tolerate an FE error of mean size `T^ε`. Arguments built on the integers with multiplicity one — Type-I sums, which are exact geometric sums — use the count with a bounded remainder and pass: no fake of the corpus has a count exponent below half the real part of its layer.

**Question (B145).** *Does the prime-weighted centred type-II current at a growing isolated mode, with both continuum corrections, cancel below the recovered residue?* Under ¬AAL filters recover the top residues, and the growing-order Gaussian current reduces to centred cofactors with a filtered error [F]; separated complete unweighted pairs decay faster than every power [F]. Open: the restricted prime-weighted cofactor sum; no declaration bounds it (log §22).

| Answer | Effect |
|---|---|
| yes | AAL without a sign and without an operator; RH ⇔ ZAL |
| a lower bound of the size of the residue | the Vaughan–Gaussian architecture does not exclude a finite layer: world I needs an input beyond exponential sums |

**Tests.** T1 fails (AAL strength). T2, T3 pass. T5: the argument has to fail for two-sided edits with a finite layer — it can, through the actual Möbius coefficients and the exact count. T7 moves Π149. T8: a Type-II sum in the dark range [A].

**Limit.** Under the constraint the step from AAL to RH is ZAL, a half-plane at every depth, and the corpus has no sign-free, non-spectral source of half-planes: its one producer uses squares and an Eisenstein reflection. **Under the constraint no question in the corpus opens the path to RH; B145 opens the half of it that world I is.**

## 2.7 If RH is a physical phenomenon in AdS with a modular horizon

**What is proved.** RH ⇔ every compact pulse rings down at the quarter rate; the pulse rate equals the horocycle rate [L*] (`riemannHypothesis_iff_pulse_ringdown`, `pulse_ringdown_iff_horocycle_rate`). The unfiltered horocycle exponent is `1−Θ/2`, filtered `1−Θ∞/2`; AAL ⇔ no Euler filter accelerates; every regulator has the count of its limit [F]. The cusp spectrum has the Weyl order `cΛ≤N(Λ)≤CΛ`; no Maass cusp form with `0<λ<3/16` exists on any congruence subgroup [L*] (`weyl_law_order`, `selberg_three_sixteenths_congruence`). The producer lives on a second horizon, the cubic cover of hyperbolic three-space: its theta-square series has a double pole at `4/3`, its corrections are Grössencharacter `L`-functions, and the coupling of the scalar channel to them is the map `b↦((4r−1)+b)/(6r)` [L*]. With `[X]`: the rate `1/16` [D].

**Readings [D].**
- *World I is ordinary ringdown and is removable*: a finite set of least-damped modes, removed by a filter of finite degree; a two-sided edit removes it from the primes [L*].
- *The producer is a scattering experiment on a cover horizon*: the scalar channel couples to a tower of spinning channels, and the coupling has its fixed point at `3/5` or above at every period.
- *The one arithmetic gap principle in Lean is for bound states*: Selberg's `3/16`, whose proof is arithmetic (Kloosterman sums and Weil's bound) [C].

**Question (B188).** *Does the mechanism that gives `λ₁≥3/16` on congruence groups — the Kuznetsov formula with Weil's bound for Kloosterman sums — bound the scattering resonances of `SL₂(ℤ)\ℍ` away from the unitary axis: a resonance-free strip of any width, from the Kloosterman side, without a family of twists?*

| Answer | Effect |
|---|---|
| a strip of width `δ>0` | a second producer of a half-plane, independent of the Gauss-sum class; `δ>1/16` is a half-plane below `7/8` |
| no: the Kloosterman side sees the bound states and not the resonances | the arithmetic of the horizon bounds discrete spectrum only; the physical reading supplies receivers and the source comes from elsewhere |

**What the corpus says about the candidates [KR].** Hölder dynamical realizations give a strip and the oscillation estimate fails on additive realizations; graph horizons with commuting Hecke operators and slow resonances exist; KMS positivity and modular conjugation do not select the line; scattering Schur contractivity is blind to the position of zeros. No declaration bounds a resonance-free strip from Kloosterman sums (log §22).

**Tests.** T1 passes as a half-plane for `δ>1/16`. T2, T3 pass. T5: must fail for non-congruence groups and graph horizons with slow resonances; the `3/16` theorem does. T7 moves Γ226. T8: not a named problem in this form; first step in corpus objects (`RHTower/SelbergThreeSixteenths`) with one obstacle: the Eisenstein contribution to the Kuznetsov formula is weighted on the unitary axis, where the resonances are not [C].

**Limit.** A rate is a half-plane; the quarter rate is RH and is not reached by a principle with a margin.

## 2.8 If RH is a problem of topology or geometry

**What is proved [L*].** The Morse index of the sign problem is a Maslov index: the crossing multiplicity along the aperture is a Lagrangian intersection number, the index is the number of crossings, the far end carries the zeros (log §14). The poles see a finite-dimensional part of the path, the polar Lagrangian; below the polar ground energy every crossing is charged. At finite scale the neutral part of a window is a potential plus a Dirichlet form on the blocks, RH is one bound state on every window, and two windows glue to one bound state iff the product of their susceptibilities is at least one (log §2). At the critical ratio a failure of RH is one function: the critical half-line state, unique up to sign, with a Laplace transform that has no zero in the open right half-plane (log §1).

**Readings [D].**
- *The sign problem has a two-dimensional shadow.* If the first crossing is charged, it is a crossing of the polar Lagrangian with the charge axis; a neutral null mode is invisible to the poles.
- *Bound states glue through charges.* The index of a union is not the sum of the indices: two wells with one bound state each merge into one well with one bound state exactly when both are shallow against their charge coupling.
- *The failure has a shape.* The critical state is unique up to sign; its Laplace transform is zero-free on the closed right half-plane and its [Cayley multiplier is outer](../../drafts/pipeline/3-formalized/critical-half-line-laplace-outerness.md). Positive endpoint mass excludes the singular inner delay, and its [causal translates span half-line L²](../../drafts/pipeline/3-formalized/critical-half-line-ground-state-outerness.md). This unweighted density does not decide the polar pairing.
- *Its causal energy has an exact positive representation.* [Weighted tail squares](../../drafts/pipeline/3-formalized/critical-causal-energy-factorization.md) compute every finite causal sum, and wall displacement has an explicit sharp weighted energy floor with a unique extremizer line. The [transverse exponential gap](../../drafts/pipeline/3-formalized/critical-half-line-transverse-energy-gap.md) controls every full-domain variation after removing its ground-state component; its polar pairing error is bounded by energy. The ground-state charge remains open.

- *The state lies on an actual variational branch.* [Attainment, differentiability, and stability](../../drafts/pipeline/3-formalized/critical-half-line-ground-energy-branch.md) give derivative `-a(W₀)W(F)/W₀`. [Global simplicity](../../drafts/pipeline/3-formalized/global-confining-half-line-ground-state.md) gives one minimizing line at every positive ratio, with zero-free open-right-half-plane Laplace transform. [Strict concavity](../../drafts/pipeline/3-formalized/strict-concavity-of-confining-half-line-energy.md) excludes a common minimizer at distinct ratios and strictly orders their exponential masses. Weighted convergence near the threshold controls the polar pairing continuously; it does not determine its value there.

- *Its strong-confinement scale is quantified.* The [ground energy is `a+log a+O(1)`](../../drafts/pipeline/3-formalized/strong-confinement-logarithmic-excess.md), and every normalized minimizer has `W-1` of order `1/a`. These bounds combine the full arithmetic form with a logarithmic correlation-deficit cost; no sign condition on the state is needed.

**Question (B104).** *Is the critical half-line state charged: is `∫F·polarSourceProfile≠0`? Equivalently for the classification: does its third case (`R_polar=W₀` finite with a polar-orthogonal state) occur?*

| Answer | Effect |
|---|---|
| charged whenever it exists | the classification loses its third case: RH, or `R_polar<W₀`. The polar channel of HF, SRT, AIP, ACS (atomic) and SC sees a failure strictly before the window threshold; a proof of RH on these routes reduces to polar payment at every ratio (B101) |
| a polar-orthogonal critical state on a configuration model with ζ's archimedean data | a neutral critical state is invisible to the poles: polar payment cannot certify the first crossing, and those routes need a non-polar input |

**First step and obstacle.** At finite scale the answer is yes on windows with `4J≤R`: a ground vector of the block matrix has one sign and both charges nonzero of one sign [L*] (`charges_mul_pos_of_blockMatrix_minimizer`). The step is the same statement on windows with `R≤J` and its passage to the half-line state through the refinement tower. The former imaginary-axis obstruction is resolved by the [undamped-resolvent weak-equation argument](../../drafts/pipeline/3-formalized/critical-half-line-boundary-laplace-exclusion.md). This does not decide the polar pairing.

**Tests.** T1 passes (method; not known to follow from RH, under which the state does not exist). T2, T3, T4 pass. T5 calibrated on narrow windows and on short apertures. T6 pass. T7 moves Σ135, Σ139, Σ181. T8 not a named problem.

**Limit.** The answer does not decide RH; it decides whether the polar shadow is a complete invariant of the first crossing.

## 2.9 New field for RH: reflection arithmetic

**Does RH need a new field?** The fields that the mechanism classes call for exist as programmes and end at theorems (§1.12). The three cores share one input that no programme treats as its object: the reflection `s↦1−s`, and the corpus measures it [D]:
- On the model side the reflection is the selector, and only as an identity up to a decaying error: fakes exist with defects of mean size `T^ε`, none with a decaying defect (§1.3).
- On the producer side the reflection of the theta row needs a completion, and the completion couples the target to a tower whose fixed point is `≥3/5` at every period (§1.6).
- On the sign side the archimedean term of every form is the Gamma factor of the reflection; the neutral part is the form of the zeros minus the poles [L*] (`exists_le_negIndex_sub_zeroGram_iff`).

So the analytic uses of the functional equation with a remainder — approximate functional equations, convexity, zero counts, mollified moments — cannot separate ζ from a fake at the level of a finite layer, and the exact uses are few. A field whose object is the exact reflection is missing [A].

| Aspect | Content |
|---|---|
| What it is about | Operations that keep the reflection exact (twisting, lifting, Rankin–Selberg, completion [C]) and operations that break it (truncation, mollification, sieving, editing), with the defect each one creates and the zeros that the defect admits |
| What it is like | A quantitative converse theory. Hamburger's theorem says that the exact reflection identifies ζ; the field asks what each size of defect identifies, and which arithmetic constructions stay at defect zero |
| Established [L*] | rigidity at `L¹`/`L²` defects; Abel floors for every coefficient difference; defect energy `≥cT log T` of fake edits; fakes at defect energy `T^{1+ε}` under `Θ<1`; bounded-defect fakes among signed weights; twin defects `2iζ·Im M`; the zero transfer `ρ↦6ρ−3`; the barrier of `6r`-periodic pairings. On the card: rigidity of unweighted systems at `O(\|t\|^{−½+ε})`; the fake pair as the image of the pole under `s↦s+1−ρ₀` |
| Criteria | R1 a statement holds for ζ and fails for every fake of §1.3. R2 it states its defect budget; a budget of mean size `T^ε` is refuted. R3 it distinguishes completion from reflection. R4 it reproduces the Goss and Weil cases at defect zero. R5 a lower bound for a defect names what it sees: the deleted prime, the coefficient difference, or the zero |
| Questions it must answer | B191 (the gap between `T log T` and `T^{1+ε}`; fakes at `β₀≥3/2−Θ`); a joint inequality between the count remainder and the defect that sees the depth (the card's Corollary III.2 shows that the defect alone does not); B187 (a pairing whose completion fixes the line); B180 (a reflection of the theta row without Eisenstein series) |
| Tools | defect Laplace transforms and Abel means; Mellin–Plancherel on rays; grouped selections of primes with small discrepancy at every frequency; transfer maps of towers and their fixed points |
| Objects | reflections, completions, defects, transfer maps, edits, twins |
| Language | defect, defect energy, Abel floor, completion offset, transfer, rigidity radius |
| Mechanisms | Built on EFT, APD, WZC, FCT, CRF. To discover: an operation on Möbius-signed families that reflects without completing, or the theorem that every reflection of such a family completes with fixed point above `½` |

**Main conjecture [A].** Every reflection of a Möbius-signed family costs a completion whose coupled fixed point lies above `½`. **Milestones.** M1 the FE axis of edits (Lean, with A153). M2 B191. M3 the pairing coordinates of every sign-carrying design (B187). M4 a joint count–defect inequality.

## 2.10 New field for AAL: the arithmetic of exceptional layers

**Does AAL need a new field?** The receivers (FFA), the instruments (ELT) and the model theory over the rational primes (WZC) are built. They say what an argument for AAL may use: the reflection up to a decaying error, or the count below half the layer (§1.3). The layer–defect calculus that would have been the natural field is answered and gives no inequality in the depth alone: the lower bounds for the defect of a fake are those of its least deleted prime [L*]; [card]. What is missing is a theory of the object itself: a finite isolated layer of exceptional zeros [A].

The nearest mathematics is the theory of exceptional eigenvalues [C]. A hyperbolic surface has finitely many eigenvalues below `¼`; they are a finite layer of off-line zeros of its Selberg zeta function, which has an Euler product and a functional equation. On general surfaces such layers exist; on congruence surfaces Selberg's conjecture says there are none, and what is proved (`3/16` in the corpus [L*]; better bounds by functorial lifts [C]) is proved by arithmetic: Kloosterman sums, Hecke operators, lifts. AAL is the statement of the same kind for ζ: no finite exceptional layer.

| Aspect | Content |
|---|---|
| What it is about | Finite exceptional layers of zeta functions with an Euler product and a reflection: where they exist (Selberg zeta functions of surfaces with small eigenvalues, two-sided edits), where they are excluded (congruence surfaces down to `3/16`), and which arithmetic excludes them |
| What it is like | The Selberg eigenvalue problem transported to ζ: gap principles that are all-or-nothing (no layer, or infinitely many zeros), proved by twisting and averaging over an arithmetic family and not by bounding one function |
| Established | the atoms and their models; receivers and instruments of world I; removal of a finite layer by an edit [L*]; `selberg_three_sixteenths_congruence` [L*]; the FE axis [L*]; an Euler product over integer norms with a decaying FE defect is ζ [L*] |
| Criteria | E1 false for a Selberg zeta function with a small eigenvalue and for every two-sided edit with a layer. E2 it uses the exact count or the reflection up to a decaying error. E3 it treats a layer with multiplicities. E4 its constants do not degenerate as the depth tends to zero. E5 it is a gap principle: its conclusion is "none or infinitely many" |
| Questions it must answer | B157 (which structure of ζ that a Selberg zeta function lacks excludes a finite stratum); A120 (the finite stratum of a Selberg zeta function as a corpus model); B128 (does a finite layer of ζ replicate under a twisting operation?); A144 (tangent data under additive twists); B145 or B170; B183 |
| Tools | Kloosterman sums and the Kuznetsov formula; additive and multiplicative twisting; Rankin–Selberg positivity on lifts [C]; filters and currents; edits as test objects |
| Objects | layers, strata, twists, gaps, exceptional sets |
| Language | exceptional layer, gap principle, replication, removal |
| Mechanisms | Built on ELT, FFA, WZC, `RHTower/SelbergThreeSixteenths`. To discover: a twisting operation under which a finite layer of ζ has to reappear with a multiplicity that the exact count forbids |

**Proof or falsification.** A proof is a gap principle that passes E1–E5. A falsification of AAL for ζ is a located finite layer; the corpus has no mechanism that forces one (§2.20). What can be falsified is each proposed principle, on the edits and on the surfaces with small eigenvalues. **Milestones.** M1 A120. M2 B157 as a theorem about one structure. M3 a replication law for one twist. M4 AAL.

## 2.11 New field for RH without positivity: order arithmetic

**Does a positivity-free, non-spectral RH need a new field?** Under the constraint (§2.6) the surviving mechanisms that act on zeros are orders and their parity, branch points of continuations, Galois actions on zeros, ultrametric dominance and exact evaluations of Gauss and Jacobi sums. Each exists in one programme; none is organized as a theory of zeros.

| Aspect | Content |
|---|---|
| What it is about | Zeros through the algebra of their orders: parity of orders of Euler-product exponentials above multiples of the count exponent, branch points at `ρ/2`, `ρ/3`, …, the group of the zero field over the source field, Newton polygons in non-archimedean completions |
| What it is like | The Goss proof as the model case: a Riemann hypothesis from dominance and simplicity of slopes, with no inequality between a sum and its terms |
| Established [L*] | the order law at the multiple two (`even_order_of_count`); `L=K` ⇔ `H=B` ⇔ `K_even⊆ℝ` ⇔ RH; orbits in `{±δ}`; rational real parts have the orbit `{ρ,ρ̄}`; the reflection lifts iff `−1` is not a square; the Goss Riemann hypothesis; the sign law of Gauss sums |
| Criteria | O1 no inequality between a form and its squares. O2 no operator spectrum. O3 a statement about orders, branchings or Galois actions. O4 it reproduces the Goss case. O5 it fails for every fake with an odd fake zero below twice its count exponent |
| Questions it must answer | A155 (the order law at every multiple); B190 (orbits of zeros with irrational real part; an automorphism besides conjugation); a restriction forcing `H=B` from the prime traces; a non-archimedean completion of the zero field with fibrewise distinct norms; B145 |
| Tools | Newton polygons over completions of the source field; parity and branching of continuations; Kummer theory of the width classes; exact Gauss-sum evaluations |
| Objects | orders, branch points, zero fields, width classes, slopes |
| Language | order, parity, branch, slope, descent |
| Mechanisms | Built on GaloisTheoryOfZeros, SignFreePurityMechanisms, WZC, CRF. To discover: a valuation on the zero field that separates the zeros of each fibre |

**Main conjecture [A].** The zero field of ζ carries a valuation, defined from the source traces, whose slopes separate every fibre. **Limit.** The conjecture is of RH strength; its first steps (the order law at higher multiples, slopes of single fibres) are below it.

## 2.12 New field for RH as AdS physics: arithmetic horizon towers

**Does it need a new field?** The modular horizon has its receivers (BHR, AHMH, HAT, CTH) and one cover horizon has its unfolding (STCC). The producer reads ζ through a tower of horizons: a cover, its theta, and the Grössencharacter channels coupled to the scalar. No programme treats a family of horizons and the maps between their resonance sets.

| Aspect | Content |
|---|---|
| What it is about | Families of arithmetic horizons (congruence quotients, metaplectic covers of every degree), their scalar and spinning channels, the coupling maps between their resonance sets, and the arithmetic gap principles that each satisfies |
| What it is like | Scattering theory of a tower: each horizon's resonances are the zeros of a family of `L`-functions, and completion couples the families by affine maps with computable fixed points |
| Established [L*] | ringdown ⇔ strip; pulse rate = horocycle rate; the Weyl order of the cusp spectrum; Selberg `3/16`; the theta-square series of the cubic cover with its poles; the coupling maps `b↦((4r−1)+b)/(6r)` and their fixed points |
| Criteria | H1 built from horizons and places, not from zeros. H2 false for non-arithmetic groups. H3 a rate with a margin is a half-plane; the quarter rate needs an equality case. H4 coupling maps are computed from completions, not postulated |
| Questions it must answer | B188; B178; A26; the coupling maps of covers of every degree in the coordinates `(c,k)` of §2.5; a horizon whose coupling fixes the critical line (B187) |
| Tools | Kuznetsov formula and Kloosterman sums; metaplectic Eisenstein series; Rankin–Selberg on covers; Euler filters |
| Objects | horizons, covers, channels, coupling maps, rates |
| Language | channel, coupling, fixed point, rate, gap |
| Mechanisms | Built on BHR, AHMH, STCC, FCT, `RHTower/SelbergThreeSixteenths`. To discover: an arithmetic gap principle for resonances |

**Main conjecture [A].** On congruence horizons the Kloosterman side bounds resonances as it bounds bound states. **Milestones.** M1 A148. M2 the coupling map of a second cover. M3 B188.

## 2.13 New field for RH as topology or geometry: the gluing theory of windows

**Does it need a new field?** The index theory of the aperture is built (Morse = Maslov, the polar Lagrangian). The finite object that RH is at finite scale has its first geometric theorems: the neutral part of a window is a potential plus a Dirichlet form, its bound states are counted by the sinks of a positive trial vector, and two windows glue through the product of their charges with an exact criterion [L*] (log §2). No programme treats the gluing itself: how the response of a union is computed from the responses of its parts, and what the primes contribute to it.

| Aspect | Content |
|---|---|
| What it is about | Windows as wells with a charge channel: their bound states, their susceptibilities `u·A^{−1}u`, the response of a union in terms of the responses of its parts, the loss from the couplings that are not of charge type, and the behaviour of all of these under refinement of the blocks |
| What it is like | Scattering by composition: Schur complements, inertia additivity and its failure (Wall's non-additivity of the signature [C]), capacity and Cheeger-type constants of weighted graphs, Bargmann-type counts of bound states [C] |
| Established [L*] | one bound state ⇔ susceptibility product `≥1`, two if both are negative with product `<1`; the union holds at most the bound states of the glued model with lowered potentials, and at least those of the model with raised potentials [D]; index `≤1+` the number of blocks with potential below `−λJ`; narrow windows; one-sign charged ground vectors; exactly one bound state on ratio `≤103/50` at every block size; refinement transfer of margins |
| Criteria | G1 counts bound states without the zeros. G2 the count is one on the certified windows. G3 a wrong contact weight, constant or tree length produces a second bound state. G4 the Liouville twist produces one above the trivial aperture. G5 stable under refinement. G6 the gluing criterion reproduces the certified unions |
| Questions it must answer | B189 (the susceptibility product of adjacent windows); a composition law for susceptibilities under gluing; the rank of the coupling that carries the binding of two adjacent windows; the first ratio at which a second bound state could appear |
| Tools | Schur complements along the charges; interlacing; M-matrix theory; the refinement tower; the contact Mellin calculus |
| Objects | windows, blocks, potentials, couplings, charges, susceptibilities, bound states |
| Language | well, bound state, susceptibility, gluing, excess coupling, refinement |
| Mechanisms | Built on AGZ, HFP. To discover: a quantity that composes under gluing and that the primes keep on the side of one bound state |

**Main conjecture.** Every window holds exactly one bound state (RH); in gluing form, the susceptibility product of the two halves of every window is at least one. **Milestones.** M1 A156. M2 B189 at ratio four. M3 a composition law. M4 every ratio (B152).

## 2.14 A research programme to construct `𝔽₁`

**Goal.** A geometry in which Spec ℤ has a square and the inequality of Castelnuovo and Severi on it is a theorem. The programme is AGZ with HFP; SA, FFA and WZC are its test benches.

**What the corpus fixes [L*].**
| Item | Theorem |
|---|---|
| the pairing | Bézout for the comb ⇔ RH with the weights `Λ`; a shift of the constant is admissible only downward; index = right zeros |
| forced data | constant, contacts at their price, tree lengths; a contact altered and paid at its price is RH at every parameter |
| number rings | ideals as degree points; index of every Dedekind zeta function; the neutral form has the index of the zeta function plus one; quotients count zeros and poles; `n` copies of a quotient have the index of the quotient; Dedekind's divisibility on the line as a no-negative-square condition |
| a non-abelian extension | `ℚ(∛2,ω)`: the Artin character of degree two and `ζ_{ℚ(∛2)}` have their Hodge index |
| characters | the Brauer elementary monomial characters generate the virtual characters of a finite group |
| finite scale | RH ⇔ one negative square of the neutral part on every window; ratio `≤103/50`, narrow windows, first blocks, thin packets certified; refinement transfer |
| gluing | two windows hold one bound state iff their susceptibilities multiply to at least one; unions are bounded by the glued model with lowered potentials |
| the aperture | Morse = Maslov index; far end = zeros; polar Lagrangian; a single simple null mode on a short aperture |
| tails | critical comb growth = width; Abel integrability ⇔ `a+w≤½`; convergence ⇔ every zero left of `1−a`; Laguerre tails = Li coefficients |
| sections, points | the square counts linearly; the contacts of a number ring are its point counts over the finite fields |
| counts of models | a count rate above the pair identifies nothing; an FE defect that decays identifies the rational primes |

**What it would be like [D].** Spec ℤ over `𝔽₁` is a curve of infinite genus whose square is rigid and counts like a curve. Its Néron–Severi lattice at finite scale is a potential plus a Dirichlet form, its Hodge index is a bound-state count, and its pieces glue through two charges, the two poles. Its index along the aperture is a Maslov index with a two-dimensional polar shadow. Its zero width is the growth of one comb. What distinguishes ℤ from its imitations is the reflection as an identity and the exact count.

**State of the constructions.**
| Construction | Deliverable | State |
|---|---|---|
| I path | transport of the sign | closed: RH at every parameter |
| II glued fibre | the comb form as a glued form | refuted for invariant gluings [KR]; data forced |
| III Stepanov on the square | a small vanishing section | closed: an equality of ideals [F] |
| IV towers and Galois extensions | index per character | Hecke characters, number rings, quotients and their powers, one non-abelian ring; Brauer induction proved; the reciprocity law open as work (A154) |
| V own comb | Bézout for an own system | closed: fails |
| VI count | quadratic count | linear; no definition without the form (B87) |
| VII finite scale | the inequality in finite rank | equivalence; ratio `≤103/50`, narrow windows, first blocks certified; ratio four at every block size open (A146) |
| VIII index as topology | index from the path | closed as Morse = Maslov; the far end carries the zeros |
| IX tails | the width on the comb | closed: one sequence; Li coefficients on the same sequence |
| X bound states | the Hodge index as a bound-state count | the gluing law, the sink count and the charged ground vector are theorems; the susceptibilities of actual windows are open (B189) |

**Criteria.** C1 reproduces Weil and Stepanov for curves. C2 a count rate is not enough. C3 uses the reflection as an identity, or up to a decaying error. C4 uses the Euler product on the function. C5 sees the exact normalization. C6 infinite type. C7 the diagonal is the density of a comb. C8 positivity is derived. C9 selective only where a contact enters. C10 additive over the constituents of a number ring, zeros and poles counted. C11 nothing below the trivial aperture beyond the dominated box. C12 at finite scale it is the neutral-part index. C13 a statement at the point. C14 a quadratic count. C15 treats neutral null modes. C16 its comb grows at the rate of the width. C17 its pieces glue by the susceptibility criterion.

**Questions.** 1 a quadratic count (B87, B169). 2 Bézout from a property (B149). 3 the gluing law on actual windows (B189). 4 the reciprocity law (A154). 5 the sign of `𝔚_4` at every block size (A146). 6 the charge of the critical state (B104).

**Tools, objects, language.** Schur complements along the charges; the refinement tower; the index law for quotients and powers; contact Mellin calculus; induction theorems for characters. Objects: degree points, contacts, jets, blocks, charges, windows. Language: comb, Bézout, neutral part, bound state, susceptibility, aperture.

**Order of work [A].** A156; B189 at ratio four; A154; A146.

**Decisive test.** A construction whose Bézout holds for an edit with a finite layer, for a fake, for the Liouville twist at rung one, for a wrong constant, or along a path of squares, is wrong [L*].

## 2.15 A research programme to close the route WD

**Goal.** A bound `O_θ(T^K)` with one `K` and unbounded `θ` for the second moment of ζ times a Möbius mollifier of length `T^θ`, or the collision bound equivalent to it [F].

**What the corpus fixes.**
| Item | Statement | Evidence |
|---|---|---|
| receiver | RH ⇔ the mollified moment is subpolynomial; a cofinal bound with fixed `K` suffices | [F] |
| depth | dyadic boundedness at `θ>1` confines high zeros to depth `<1/(2θ)+ε` | [L*] |
| proved range | `θ<½` with displaced twisted moments; a positive proportion of critical zeros of odd multiplicity | [L*] |
| necessary length | excess `K₀/log T` forces `log N≥log²T/(6K₀)−(4/3)log T` | [F]/[KR] |
| blindness | Type-II norms sign-blind; finite relocation invisible to quadratic tests of length `o(T²)` | [KR] |
| cameras | adaptive clusters with complete exterior mass `≤¼`; centred cameras with prime mean square `≤C·T·exp(−2b(y−c log T))` | [L*] |
| short intervals | mean squares of `λχ` in intervals of bounded length for `χ≠1`; for `χ=1` the top-scale blocks above polylogarithmic frequencies, the ladder on a frequency set, twisted partial sums `o(N)` for `2\|τ\|≤√N` [S] | [L*] |

**What it would be like [D].** A mean-value theory past the height, whose off-diagonal is a correlation of truncated Möbius divisor sums. On the scale a bounded dyadic moment at `θ` is the half-plane `½+1/(2θ)`: the route passes `7/8` at `θ=4/3` and reaches the line only cofinally. Below `3/5` the route competes with nothing: the frame of the producer ends there (§1.6).

**Criteria.** W1 fails for `ζ(s)(1−cp^{−s})`, `c>√p`. W2 fails for a finite relocation (needs length beyond `T²`). W3 not a Type-II norm bound. W4 keeps the pole and the Barban–Vehov diagonal. W5 `K` independent of `θ`. W6 at `θ<4/3` it gives nothing `[X]` does not. W7 it fails for a two-sided edit with a finite layer, which changes the Möbius coefficients at infinitely many primes.

**Questions.** 1 A18. 2 the collision form at `θ≥1`. 3 a power saving at one `θ>4/3` (below `7/8`); at `θ>5` it is below `3/5`, past the frame of the producer. 4 fixed `K` along `θ→∞` (B62). 5 the converse of the depth theorem. 6 A147, the correlation input.

**Tools, objects, language.** Gallagher's transfer; the Selberg-integral dictionary; shifted correlations of sieve weights; the Levinson gate; the ladder and Parseval of MatomakiRadziwill and the prime-shift reduction of LogarithmicChowla. Objects: mollifiers, dyadic moments, collision charges, cameras. Language: length, depth, excess.

**Milestones.** M1 `θ<½` (Lean). M2 a proportion on the line (Lean). M3 A18. M4 A147. M5 the collision dictionary at `θ≥1`. M6 a saving at one `θ>4/3`. M7 the cofinal bound.

**Limit [A].** The cofinal bound is RH; every partial result is a level of the scale.

## 2.16 A research programme to close the route ACS

**Goal.** One negative square of the neutral part on every window; equivalently the comb sign, a mass floor on every ratio window, or subpolynomial growth of the critical comb.

**What the corpus fixes.** The table of §2.14, and:
| Item | Statement | Evidence |
|---|---|---|
| the minimal face | one inequality per prime on logarithmic windows | [L*] |
| finite scale | neutral-part index ⇔ RH; uniform index bound `(Q−1)⌈e^{E_Q}⌉` at each ratio, `300000` at ratio four | [L*] |
| bound states | index `≤1+#{blocks with potential <−λJ}`; narrow windows `16J≤R` from the potential `≥−½` and the couplings `≥1/(2J)` | [L*] |
| gluing | exact criterion; lowered potentials | [L*] |
| transfer | margins above one scale pass to every refinement | [L*] |
| tails | critical comb growth = width; never convergent; Abel integrable ⇔ RH; Li coefficients as Laguerre tails | [L*] |

**What it would be like [D].** Three tracks on one lattice. *Matrices*: the neutral part as a well with a charge channel, one bound state per window, glued ratio by ratio. *Index*: the aperture path and its polar shadow. *Tails*: the critical comb as the scale on one sequence.

**Criteria.** Those of §2.14, and: S1 nothing about the contacts below ratio two. S2 a margin at each ratio, none uniform. S3 nothing on the tails at `a<1/8` beyond `[X]`. S4 the certified windows are reproduced, not reproved.

**Questions.** 1 A146: ratios 4 and 7 at every block size, where the index is between `0` (RH) and `300000` (proved). 2 B189: the susceptibility product of the halves. 3 B149, B87, B169. 4 B104. 5 A154, A141.

**Tools, objects, language.** As in §2.13 and §2.14.

**Milestones.** M1 finite criteria (Lean). M2 ratio `≤103/50` and narrow windows (Lean). M3 the gluing law (Lean). M4 A156. M5 B189 at ratio four. M6 every ratio (B152).

**Limit [A].** Each ratio is a finite-height statement; the uniform statement is RH.

## 2.17 A research programme to close the route ZCG

**Goal.** No positive-time collision of the heat flow; or the floor on a decisive sequence of prime windows; or ZAL, B13 and Landing.

**What the corpus fixes.**
| Item | Statement | Evidence |
|---|---|---|
| worlds | world I or world II, top `≤7/8` | [X]; [L*] |
| world I receivers and instruments | unit gap, non-attainment, moments, filters, currents, quanta | [L*]/[F] |
| world I models | every finite layer, the pair alone above the pair, an isolated pair above a tail, landing failure, sparse tails, layer removal, symmetric quartets — over the rational primes with a count rate | [L*] |
| laws of the models | balance or real top; parity above twice the count exponent; count floor `13/30` | [L*] |
| the FE axis | no fake with a decaying defect; fake edits at `T log T`; fakes at `T^{1+ε}` under `Θ<1`; the constants are those of the least deleted prime | [L*]; [card] |
| the door | the reflection up to a decaying error, or a count below half the layer | [D] |
| heat | RH ⇔ no collision; finitely many non-real zeros at positive times, infinitely many at negative times | [L*] |
| cameras | adaptive clusters with complete exterior mass | [L*] |

**What it would be like [D].** World I is a finite-dimensional problem with complete receivers and a complete model theory over the rational primes: it closes by one statement that uses the reflection to a decaying error, or the exact count, and that fails on every edit. World II is the scale and inherits the end of the producer.

**Criteria.** Z1 a world-I statement fails on every edit with a finite layer and on the fakes. Z2 two-sided, or at every length. Z3 nothing below the logarithmic radius. Z4 a world-II statement is placed on the scale. Z5 a camera statement names the cluster size and gap. Z6 nothing in law used as a point. Z7 every statement states its FE defect budget; a budget of mean size `T^ε` is refuted by the fakes if `Θ<1`.

**Questions.** 1 B145 or B170. 2 B191. 3 B183. 4 B141: not from an Euler product over the rational primes with a count rate (the isolated pair above a tail) [L*]. 5 B13 and Landing (B157, A120). 6 B59. 7 the half-planes of world II.

**Tools, objects, language.** Filters, currents, quanta; two-sided and signed grouped edits with prescribed factors; the balance and order laws; defect Laplace transforms; adaptive cameras; the scale. Objects: layers, tails, edits, twins, defects. Language: world, atom, layer, fake, defect.

**Milestones.** M1 receivers, instruments, models (Lean). M2 the FE axis (Lean; A153). M3 the weighted current for one quartet. M4 AAL. M5 ZAL through the scale. M6 Landing and B13.

**Decisive test.** An argument for AAL that holds for a two-sided edit with a finite layer or for a fake is wrong.

**Limit [A].** AAL and ZAL together are RH; the corpus has a receiver for each and a producer for neither below `7/8`.

## 2.18 A research programme to close the route MC/JAS

**Goal.** The signal bound `O(Z^b)` for every `b>½`; equivalently level one of the dressed aggregate.

**What the corpus fixes.** §1.6 in full; producer rates are the Mertens level [L*]; bilinear norms are sign-blind [KR]; the prime kernel off the major arcs, short-interval mean squares of `λχ` and the reduction of logarithmic correlations to prime dilates [L*]; these give no half power [F].

**What it would be like [D].**
| Stage | Half-plane | Input | Kind |
|---|---|---|---|
| 0 | `7/8` native | A118 | just work |
| 1 | `7/8→13/15` | row count of the binding bin (B174) | density estimate |
| 2 | `13/15→5/6→7/9` | the long columns with a power saving (B185) | an estimate that is not a square |
| 3 | `7/9→2/3` | square-root remainder in the long columns | Patterson type [C] |
| 4 | `2/3→3/5` | estimates below square-root size on every level of the tower | beyond square root |
| 5 | below `3/5` | a pairing outside the `6r`-periodic Gauss pairings (B187) | — |

**Criteria.** J1 every estimate placed in the twist exponent. J2 a mean square containing the principal twists is not an input. J3 positive weights, even order, two row variables fail. J4 below `5/6` nothing is a square. J5 below `2/3` the family contains its corrections. J6 a source for the last stage has pairing coordinates with fixed point `½` and a design with square-root endpoint `½`.

**Questions.** B174, B185, B187, B180; the coupling map of every completed probe; level one directly (B160).

**Tools, objects, language.** The budget calculus; signed Gram forms; Poisson coefficients; sieves over cyclotomic rings; the theta-square series; the scale as a ruler. Objects: rows, columns, bins, root numbers, pairings, towers. Language: design, corner, floor bin, frame, fixed point.

**Milestones.** M1 the native `7/8`. M2 a boundary below `7/8`. M3 B185 with any `R₀<1`. M4 below `5/6`. M5 B187.

**Decisive test.** An estimate that holds for matched phases, or for a family with its principal twists counted as input, proves no half-plane.

**Limit [A].** With every stage of the cubic probe completed the programme reaches `2/3` (`3/5` with estimates beyond square root), and no period of the Gauss pairings does better. It is the only programme that has produced a theorem about the zeros, and in its class it does not reach the line.

## 2.19 A research programme for a Galois theory of the zeros

**Goal.** Treat the zeros of ζ as the roots of equations over a field built from the primes, determine the group of these equations, and classify the permutations of the zeros that the group allows.

**What the corpus fixes [L*]** (GaloisTheoryOfZeros, log §4, §21, §24).
| Item | Theorem |
|---|---|
| the equations | for each ordinate the polynomial of the centred zeros with that ordinate has coefficients in the fibre source field `K`; the zero field `L` is algebraic and normal over `K` |
| the criterion | `K` equals the field generated by the zeros iff RH; `K_even⊆ℝ` iff RH; over the prime trace field `B` the reflection field `H` equals `B` iff RH |
| the group | conjugation is central; every orbit is finite; the action is not transitive; every critical zero is fixed; a source automorphism displaces a zero by less than one |
| its shape | over the field of squared widths the group is the closed group of sign families that annihilate the square-class relations of the radicands `−δ_q²`: each element reflects the widths of a set of fibres |
| the reflection | `ρ↦1−ρ` lifts to the Gaussian extension iff `−1` is not a square in `L` |
| over the prime traces | an embedding fixing `B` sends a zero to a zero with centred real part `±` the original; an orbit meeting the line lies on it; a zero with rational real part has the orbit `{ρ,ρ̄}` |
| transcendence | `p^ρ` and `r^ρ` both algebraic force `Re ρ∈ℚ`; `B` contains a transcendental element |
| symmetries of the translations | maps commuting with the translations at 2 and 3 are diagonal; the only nonidentity pointed real symmetry is conjugation |
| finite equations | Jensen discriminants are nonnegative; the folded nonreal census exhausts the off-line divisor; the generic centred polynomial of degree `d` has the full symmetric group |
| absent | an automorphism other than conjugation; the orbit of a zero with irrational real part; the group of one Jensen polynomial of ξ; a monodromy group of the zeros along the heat flow; Frobenius or decomposition structure |

**What it would be like [D].** A theory of signed permutations with two marked involutions.
- *The model case [C].* The zeros of the zeta function of a curve of genus `g` over `𝔽_q` are the roots of one polynomial with integer coefficients. The functional equation pairs the roots, so the group lies in the group of signed permutations `(ℤ/2)^g⋊S_g`; for most curves it is the whole group. The Riemann hypothesis there is not a statement about the size of the group. It says that two involutions of the roots agree: complex conjugation and the reflection `α↦q/α`.
- *For ζ.* The same two involutions act on the zeros: conjugation `c: ρ↦ρ̄` and the reflection `r: ρ↦1−ρ`. RH ⇔ `c=r` on the zeros ⇔ the involution `cr: ρ↦1−ρ̄`, which fixes the ordinate and reflects the width, is the identity. The corpus has built the sign part of the signed-permutation group: over `K` the group is a group of width reflections, and it is trivial iff RH. The permutation part is removed by the choice of the base field, which contains the ordinates.
- *Three tiers of equations.* (1) Finite: Jensen polynomials, whose group is expected to be the full symmetric group and carries no information; the information is the cycle type of conjugation, `N_d/2` transpositions. (2) The zero field over `K`, `D`, `B`: an elementary abelian 2-group dual to the group of square classes of the radicands. (3) Monodromy: the zeros as functions of a complex parameter (heat time, a twist), with branch points at collisions and transpositions as local monodromy.

**Criteria.** T1g the base field is defined from the primes or from complete fibres, never from single zeros. T2g every statement names its base field: over `K` the group is trivial iff RH, over a smaller field a large group is compatible with RH. T3g the classification names the classes of conjugation and of the reflection. T4g it reproduces the function-field case with its signed-permutation group. T5g a statement that forces `c=r` fails for the zero set of a two-sided edit with a fake pair, to which every construction of the theory applies as well. T6g a transitive action is excluded [L*]; nothing may assume one.

**Questions it must answer.** 1 B190: the orbit of a zero with irrational real part under the embeddings fixing `B`; an automorphism of `L` besides conjugation. 2 Is `[L:K]` equal to one or infinite? A finite nontrivial degree is the Galois form of a finite stratum, so the statement contains B13. 3 Which square-class relations hold among the radicands `−δ_q²`: is the group, if nontrivial, the full product of signs? 4 The group of one Jensen polynomial of ξ over the field of its coefficients, and the class of conjugation in it. 5 The monodromy of the zeros of the heat family around a collision time, and the group it generates; RH ⇔ no multiple zero at a positive time [L*] (`riemannHypothesis_iff_forall_zeros_simple`). 6 A restriction, from the prime traces alone, that forces `H=B`.

**Tools, objects, language.** Kummer theory of the width classes; the Artin–Schreier theory of real fields [C]; transcendence of prime powers; specialization and Hilbert irreducibility for the finite equations [C]; monodromy of analytic covers. Objects: source field, zero field, prime trace field, reflection field, fibres, widths, radicands, sign families. Language: orbit, width class, reflection kernel, lift.

**Milestones.** M1 the zero field and its criteria (Lean). M2 the group of the Jensen polynomials of low degree. M3 the square-class relations of two fibres. M4 the monodromy group of the heat family near one collision. M5 the dichotomy `[L:K]∈{1,∞}`.

**Limit [A].** Over the fields of the corpus the group is trivial exactly when RH holds, so determining the group is RH and classifying its permutations is classifying the failures of RH. The theory supplies a language and criteria; it supplies a route only through a restriction that the primes impose on the group, and the corpus has none.

## 2.20 A research programme under the assumption that RH is false

**Goal.** (a) A proof that RH fails. (b) A concrete counterexample, found without computation at the height of the zero.

**What the corpus fixes.**
| Item | Statement | Evidence |
|---|---|---|
| where a failure lives | a zero with `½<Re ρ≤7/8`; world I (a finite isolated top layer) or world II (a tail) | [X]; [L*] |
| objects that exist iff RH fails | the critical half-line state at a finite `W₀`, unique up to sign, with the weak equation; an odd bound state; a defective hard-edge block; a point right of the line with `Re ξ′/ξ<0`; a negative definite Markov plane; an aperture with an empty feasible set; a window whose neutral part has two negative squares; a crossing along the aperture; a multiple zero of some `H_t`, `t>0` | [L*] (log §1, §14, §20) |
| a failure repeats | negative paired Li indices in every window of some bounded length; in world I `ψ(x)−x` attains `x^β` on every late window and at the primes | [L*]; [F] |
| zero ⇒ certificate | a zero of depth `δ` at height `γ₀` with no other off-line zero within `(A log γ₀)^κ`, `κ>1/(2δ)`, makes Weil's form negative on tests supported in `\|u\|≤κ log(A log γ₀)`; a zero within `1/V` of the top makes `μ(A)<0` for `A≥V/2+w` | [L*] (log §24) |
| certificate ⇒ zero | a negative test at aperture `a` gives an off-line zero below `exp(exp(Ca))`; `C` is not explicit | [L*] |
| returns | under `Θ≤b` a return of a heavy set of primes up to `y` at height `t` needs `log t≥c·y^{1−b}`; a system aligned with a height fails at every aperture above `log log T+log 2` | [L*] |
| counts | at ratio four the block matrix has at most `300000` negative squares at every block size; RH says none | [L*] |
| what is excluded | a failure below height 67; a failure on windows of ratio `≤103/50` or on narrow windows; a failure visible to a statement in law | [F]; [L*] |
| models | every failure mode (a pair alone, a finite layer, a tail, no landing) is realized over the rational primes with a count rate, and under `Θ<1` with an FE defect of mean size `T^ε` | [L*] |

**What it would be like [D].**
- *A failure is a return.* An isolated off-line zero of depth `δ` at height `t` is visible in the primes up to `(A log t)^{2κ}`, `κ>1/(2δ)`: Weil's form at that height is negative on a test supported in `|u|≤κ log(A log t)`, and the prime side of that test reads prime powers up to `e^{2a}`. With `δ≤3/8` the rung is `κ>4/3`. By the return bound with `b=½`, RH allows heavy returns of the primes up to `y` only at heights with `log t≥c√y`; with `b=7/8` the unconditional range is `log t≥c·y^{1/8}`. So a disproof is an **anomalous return**: a height `t` at which a heavy set of the primes up to `y` returns although `log t<c√y`. The window for it is `(log t)^2≪y≪(log t)^8`. The pigeonhole principle gives returns only for `y` of order `log t·log log t` [C].
- *A failure is a second bound state.* Two adjacent windows with one bound state each whose raised models have negative susceptibilities with product below one hold two bound states together (log §24), which RH forbids on windows with `R≤J`.
- *A failure is one function.* The weak equation at the critical ratio is a linear equation with the actual primes; a unit solution on the half-line with nonpositive truncated forms exists iff RH fails.
- *A concrete counterexample* in this setting is a triple: a height, an aperture and a test, with the negativity of a finite sum over the prime powers below `e^{2a}`; or a window, a block size and a vector. Its size is polylogarithmic in the height of the zero. The zero itself is then located only by a bound: below `exp(exp(Ca))` (A142). This is the form of Littlewood's theorem on `π(x)−li(x)` with Skewes' bound [C].

**Criteria.** N1 the argument fails for the zeta functions that satisfy their Riemann hypothesis: curves over finite fields [C], the Goss zeta function [L*], the certified windows [L*]. N2 it uses what ℤ has and those cases lack: the archimedean place, infinite type, the absence of a Frobenius. N3 it is consistent with `[X]`, with the verified height, with the positive proportion on the line, and it says which world it produces. N4 its certificate states an aperture and, through A142, a height. N5 no statement in law is used as a point. N6 an existence proof by return has to beat the pigeonhole range by a square: it uses arithmetic relations among the `log p`, and the only relations are those of the integers.

**Questions it must answer.** 1 Is there a rung `κ∈(1,4]` and a sequence of heights with a heavy return of the primes up to `(log t)^{2κ}`? 2 Explicit constants: `c` in the return bound at `b=½`, `C` in the verification rate (A142). 3 The raised-potential side of the gluing comparison as a Lean statement, and the susceptibilities of the first uncertified windows (A156). 4 Does the weak equation at a finite `W₀` have a solution; what do uniqueness and the zero-free Laplace transform force on it (B104)? 5 Which world: is a failure of ζ necessarily a tail (AAL), which would make every counterexample non-isolated and remove the ladder's certificate?

**Tools, objects, language.** Diophantine approximation and the geometry of numbers for the prime phases; Ω-theorems [C]; the ladder; the gluing comparison in both directions; compactness at the critical ratio; edits as models of what a failure looks like in the primes. Objects: returns, certificates, failing apertures, critical states, second bound states. Language: anomalous return, rung, certificate, height bound.

**Milestones.** M1 the explicit constants (A142 and the return bound). M2 the two-sided gluing comparison. M3 a return on a rung above one for a model system with the exact count, or the theorem that the exact count forbids it. M4 an anomalous return for the primes.

**Assessment [A].** The corpus contains no mechanism that forces a zero off the line. Every exact form of "RH fails" is an existence statement, and every model that realizes a failure gives up the exact reflection. The verified height, the certified windows and the proved laws are all on the side of RH. The programme therefore yields, as it stands, three things: the list of objects that a failure would have to produce; the conversion between a zero and a certificate of polylogarithmic size; and a sharp description of the event to look for, a return of the primes beyond the pigeonhole range. Part (b) is possible only in the Skewes form: a certificate with an explicit bound for the height, and not a located zero.

## 2.21 The one big question: do adjacent windows glue through their charges? (B189)

**Where the question sits.** At finite scale RH is a count: the neutral part of every window `(R,R+J]`, `R≤J`, has one negative square. The count is certified where the window is close to dyadic (ratio between `2` and `103/50`, every block size) and where it is narrow (`16J≤R`). At ratio four the block matrix has between zero (RH) and `300000` (proved) negative squares at every block size [L*]. The induction step from a window to a larger one exists as linear algebra, and it reduces to two numbers: the susceptibilities of the two pieces [L*]. No statement gives these numbers for an actual window (log §14, §22).

**What is in Lean [L*].**
- Two symmetric matrices `A`, `B`, nonnegative on the kernels of charge vectors `u`, `v`, with `Aa=u`, `Bb=v`, `α=u·a`, `β=v·b<0`: the glued form `A(x)+B(y)−2(u·x)(v·y)` has exactly one negative square if `αβ≥1`, and exactly two if `α<0` and `αβ<1`.
- For adjacent windows and charge vectors with `u_iv_j` at most the coupling of the blocks `i` and `j`, the neutral part of the union has at most the negative squares of the glued model whose potentials are lowered by the excess couplings.
- A window whose couplings are all `≥λ` has at most one bound state more than its number of blocks with potential below `−λJ`; a window with `4J≤R` has a ground vector of one sign with both charges nonzero.

**What follows [D].** With the potentials raised by the excess couplings the same comparison holds in the other direction (log §24). So the index of a union lies between the indices of two glued models, and each of those is decided by a susceptibility product: at most one bound state if the lowered product is `≥1`, at least two if the raised product is `<1` with both susceptibilities negative.

**Question (B189).** *For the two halves `(R,2R]` and `(2R,4R]` of a window of ratio four, at every block size: are there charge vectors `u`, `v` below the couplings for which the lowered halves are nonnegative on the kernels of `u` and `v` and their susceptibilities multiply to at least one? In general: what is the largest susceptibility product of two adjacent certified windows over the admissible charge vectors, as a function of the ratio and the block size?*

**Why this question.**
- It is below RH, AAL and every half-plane. The conclusion at a fixed ratio — one bound state at ratio four — follows from RH and already from a finite verified height (A142). The question is whether the gluing mechanism proves it, and that is implied by nothing about the zeros.
- It is the induction step of the Σ core in its smallest form: one inequality between two numbers per gluing, with every other part of the step proved.
- Its first step (A156) is a computation in corpus objects on windows whose answer is known.

**What an answer gives.**
| Answer | Effect |
|---|---|
| yes at ratio four, with a margin uniform in the block size | the first finite-scale index outside the certified range that is proved from the potential and the couplings and not from the zeros. The same step applies to the next gluing, and RH becomes the statement that the margin does not close along the ratios: a recursion for one quantity |
| yes at every block size, with a margin that tends to zero | the charge channel binds at finite resolution only: the limit of the step is the question of the charge of the critical state (B104) |
| no for the lowered model, yes for the raised one | the bracket is not tight: the binding of the halves is carried by couplings beyond the product of the charges. The gluing law has to be extended from numbers to response matrices, and the rank of the coupling that carries the binding is the invariant to compute |
| the raised product is below one with both susceptibilities negative, at some block size | two bound states at ratio four: RH fails, with a zero beyond the verified height (§2.20) |

**First step and obstacle.** A156: the susceptibilities of the certified windows, and the criterion tested on unions whose index is known — two narrow windows whose union is narrow, and a dyadic window extended to ratio `103/50`. Named obstacle: the excess couplings. The contacts along the floor maps are not of product form, the lowering by the excess can destroy nonnegativity on the kernel, and the loss has to be bounded uniformly in the block size.

**Tests.** T1: a method question; the fixed-ratio conclusion is implied by RH and is below it. T2: an inequality between two computable numbers for each window and block size. T3: named for each answer. T4: the lowered criterion is not decided by a verified height. T5: calibrated on the certified unions; the criterion has to fail where a second bound state exists (the Liouville twist above the trivial aperture, a wrong constant), and `hermNegIndex_glued_eq_two` says exactly when it does. T6: no bound for the susceptibility of an actual window or of a union is in the corpus. T7: moves Σ178, Σ176 and A146. T8: not a named problem; the first step is in corpus objects with one named obstacle.

**Limit.** At each fixed ratio the conclusion is a finite-height statement, and uniformly over all ratios it is RH. One negative square of the neutral part on a window does not by itself give the sign of the block matrix on that window: the two indices differ by at most one [L*]. The question decides whether the induction on the ratio has a step of rank one.

### Alternatives considered
| Question | Effect | Verdict |
|---|---|---|
| The long columns (B185, §2.4) | the first non-square estimate; the half-plane moves toward `2/3` | the largest motion available on the scale; capped at `2/3` |
| A pairing whose frame reaches the line (B187, §2.5) | a producer for the line, or the end of the Gauss-sum class at `3/5` | the producer question; its first step is a classification |
| The charge of the critical state (B104, §2.8) | the polar shadow sees the first crossing | decides one channel of five routes; the limit case of B189 |
| The defect gap (B191) | the exact order of the least defect energy of a fake | a model question on an axis whose two ends are theorems |
| A fake below `√x` with a non-real top (B183) | the count door for world I | balanced edits only; a model question on the count axis |
| The row count of the binding bin (B174) | `[13/15,7/8)` | a one-sided density estimate |
| The weighted current (B145, §2.6) | AAL without a sign | AAL strength |
| The congruence mechanism for resonances (B188, §2.7) | a second producer | no first step past the dictionary |
| The orbits of the zero field (B190, §2.19) | a nontrivial permutation of zeros, or none | no restriction from the primes in the corpus |
| An anomalous return (§2.20) | a disproof | no forcing mechanism |
| The steps of `[X]` (A118), the reciprocity law (A154), the explicit verification rate (A142) | the half-plane, the Artin index and the window heights in the native graph | just work |
