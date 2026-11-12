# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: `5920325719` with its working tree (2026-11-12). Fact log: `logs/review-1211-status-quo-facts.md` (identifiers `FC-T*`, `CR*`, `ST*`, `AG-L*`, `AG-F*`, `AG-V*`, `PC*`, `WZ*`, `GZ1`, `CAM1`, `D1–D8`; §6 lists the baseline declarations re-read for this report).

**Evidence.** `[L*]` Lean statement read at the declaration for this report; `[doc]` content of a module docstring whose theorem names were read but not every statement; `[F]`, `[KR]` stated by the frontier map and the scoped-obstruction ledger, both read in full; `[S]` module graded unfinished by the frontier map; `[D]` deduction made here from `[L*]` statements, not a Lean theorem; `[C]` classical mathematics quoted from memory, not in the corpus; `[A]` assessment; `[X]` the external theorem cached in the repository (OpenAI, 30 September 2026), taken as proved: every Dirichlet `L`-function, ζ included, and every finite-order Hecke `L`-function over `ℚ(√−3)` is zero-free in `Re s>7/8`. The Lean graph proves `zetaZeroAbscissa ≤ 1` and no smaller bound unconditionally; the native steps of `[X]` are just work (A118). Sections 2.3–2.18 and 3 are interpretation and ideation: every untagged statement there is a proposal.

**38 live formulations; 12 candidates** (SEC, CDC/BSH, S3, APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF). HJ is PA; PCS, DR, PW-B are retired labels.

**Notation.** As in [route-obstacles.md](route-obstacles.md). In addition: the **reach** of a producer is the least `σ₀` for which its implication gives `Θ≤σ₀`; the **square-root endpoint** of the probe is its reach when every bin cancels at square-root size; a **design** `(κ,n)` is a probe whose rows have conductor exponent `κ` and principal frequencies of order `n`; the **FE defect** of a system is its uncompleted critical-line functional-equation defect `g` (`E(s)−E(1−s)` on `Re s=½` in the normalization of `EulerFETransportTheory`).

## 1. Big picture

### 1.1 One object, three exact forms
- **One inequality per prime.** RH ⇔ `2Re S(log p)≥−K` at the primes of arbitrarily late logarithmic windows outside `Ce^{δT}` primes per window; equivalently the upper side alone, `ℕ`-counts on the surviving prime rays with quadratic limit the plane defect, one growth exponent for all even local moments, or the limit of the two-bump comb form [L*] (§6 minimal face). `Θ<1` ⇔ the floor `−Kp^α` for some `α<½` [L*] (`quasiRH_iff_prime_logarithmic_power_windows`).
- **One matrix at finite scale.** On the blocks `(a,a+1]` the step-packet matrix of `𝔚_Q` is `d(a)+d(b)+δ_{ab}ϱ(a)−J(a,b)−C_Q(a,b)`: degrees, density, jets of `n log n`, contacts along the floor maps. It is twice the product of the two charges plus a **neutral part**, and the neutral part is a potential plus the Dirichlet form of a weighted graph whose weights (jets and contacts) are positive [doc] (AG-F4). RH ⇔ the neutral part has exactly one negative square on every window `(R,R+J]` with `R≤J` [L*] (AG-F1). The block matrix has `r` negative squares on some window iff ζ has at least `r` zeros right of the line; the neutral part iff at least `r−1` [L*] (AG-F2).
- **One path of Lagrangians.** The index of the restricted Weil form at aperture `b` is the sum of the nullities of the resonant apertures below `b`, the number of eigenvalues below the energy, and the number of crossings of the path of aperture conormals — Lagrangian, increasing, independent of the primes — with the graph of Weil's operator, the one place where primes and poles enter. Its supremum at energy zero is the number of zeros right of the line. RH ⇔ no crossing [L*] (AG-L1–AG-L4).

### 1.2 One scale
Every graded receiver is an equivalence at each level of one scale [D]:

| Reading | Parameter | Depth it reaches | Evidence |
|---|---|---|---|
| saving of the contacts `n^{½+γ}` | `γ` | sign to rung `κ<1/(2γ)` | [L*] (`cancellation_and_depth_ladder`) |
| sign on a rung `κ` | `κ` | no isolated zero of depth `>1/(2κ)` | [L*] |
| bounded dyadic Möbius moment at length `T^θ` | `θ>1` | depth `<1/(2θ)+ε` | [L*] |
| level of the dressed aggregate | `σ` | from a signal bound `O(Z^b)`: level `b+½+ε` | [L*] |
| exponent of the signal of the zeta kernel | `b∈[½,1)` | `Θ≤b` ⇔ `O(Z^{b′})` for all `b′>b` | [L*] |
| twist exponent of a family | `θ` | `Θ≤½+(1−1/n)θ/2`; least `θ` is `(n/(n−1))(2Θ−1)` | [L*]/[F] |
| growth exponent of the critical comb | `σ≥0` | strict growth `σ` ⇔ `w≤σ` | [L*] (PC1) |
| growth of a power tail `F_a` | `σ` | `Θ≤1−a+σ` | [L*]/[F] |
| moment of order `2k` with exponent `A` | `A/2k` | the abscissa law at depths `≥A/2k` | [L*] |
| horocycle exponent; ringdown rate | `α`; `δ` | `Θ≤2−2α`; `Θ≤1−2δ` | [L*] |

The critical comb reads the scale on one explicit sequence: its growth exponent is the zero width, it never converges, and RH is its subpolynomial growth or its absolute logarithmic Abel integrability [L*] (PC1–PC3); a subcritical comb at `a` converges exactly when every zero has `Re ρ<1−a` [L*] (`powerCombTailConverges_iff_forall_zero_re_lt`). Sizes prove the scale to rung `1−o(1)`: every dominated system is positive below the trivial aperture `log log(mass)`, the Liouville twist fails just above it, and at height `t` a dominated system fails at `log log t+log(π/2)+η` [L*]. The level `b=7/8` is `[X]`: the rung `κ<4/3`, the level `11/8`, heavy returns only for `log t≥c·y^{1/8}`, power tails convergent for `a<1/8`, ringdown rate `1/16` [D]. In Lean no rung above one is proved in any aspect.

### 1.3 Three structures; every two have a model; one pair is rigid
ζ has an Euler product over the rational primes, the Riemann functional equation, and every integer with multiplicity one.

| Structures kept | Model | What fails | Evidence |
|---|---|---|---|
| reflection symmetry, temperedness | every tangent datum as the top layer of a symmetric configuration | AAL, B13 | [L*] |
| the Riemann FE with Gamma factor, residue one, order one, zero count within one | simple zeros off the line approaching it, no landing | Landing | [L*] (`exists_riemann_gamma_counting_model_without_landing`) |
| positive prime density with a simple pole | any finite layer at any `Θ<1` | AAL | [L*] |
| Euler product over natural norms, natural coefficients, linear counting | any finite divisor with multiplicities; landing failure | AAL, B13, Landing | [L*] |
| Euler product over the rational primes, multiplicities `0,1,2`, integer norms, count `Ax+O(x^β)` above the top | two-sided edits: a non-real pair alone; every finite layer; an isolated pair above an infinite half-scale tail; every configuration approaching the line; every sparse configuration; a finite layer edited away | AAL, B13, Landing, ZAL (sparse tails) | [L*] (WZ1, WZ5–WZ7) |
| the same, zeros symmetric about the line in `c<Re s<1−c`, `c≥1/3` | quartet edits at every depth below `½−c` | the line | [L*] (WZ4) |
| the same, count below the deletion exponent | balanced edits only; a one-sided edit has a real zero on top | — | [L*] (WZ2) |
| Euler product over the rational primes with real weights in `[0,2]`, meromorphy, polynomial bounds | one pair above the frontier of ζ | AAL at that frontier | [L*] |
| Euler product and the FE with an `L¹` defect, or an `L²` defect of polynomial size | none: the system is the rational primes | — | [L*] |
| integer norms and a bounded count error | none: the rational primes | — | [L*] |

**Consequence [D] (D5).** A proof of AAL, ZAL, B13 or Landing has to use the Euler product together with the functional equation as an identity (up to an integrable defect), or the Euler product together with a count below the floor of the edits; each weaker set has a model. A fake that continues to the critical line has a non-integrable FE defect.

### 1.4 Two worlds, three atoms
`Θ≤7/8` [X]; `Θ<1⇔Θ∞<1`, and `¬(Θ<1)` ⇔ `Θ=Θ∞=1 ∧ AAL` [L*], so the edge world is excluded. A failure of RH is world I (a finite isolated top layer at `β≤7/8`) or world II (a tail with `½<Θ=Θ∞≤7/8`). RH ⇔ ZAL ∧ B13 ∧ Landing; B13 ⇔ the supremal negative index on real packets is `0` or `∞` [L*]. AAL ⇔ at most one or infinitely many zeros right of every line [L*]. In world I `ψ(x)−x` attains `x^β` on every late window [L*]; non-attainment on windows, at the primes, or one exponent for all even moments gives AAL [L*]; filters reduce the growing-order current to centred cofactors [L*].

### 1.5 Off the scale: each kind has a receiver and a kill
| Kind | Receiver | Kill | Evidence |
|---|---|---|---|
| homogeneous floor | a floor of the clock at one cutoff per aperture gives RH | the clock lies below Weil's form | [L*] |
| unit gap | an index-one approximant or realization gives RH | `Λ(s)/Λ(s+N)` has a unit gap iff RH; the heat flow has the count of its limit | [L*] |
| certificate | feasible weights at every aperture give RH | certificates converge to `Λ`; reflected halves are no Dirichlet series | [L*] |
| amplification | one exponent for all even moments gives AAL | all orders are sup bounds | [L*] |
| symmetrization | a functional decreasing under projection | linear statistics and differentiable functions of finitely many fail | [L*] |
| replication | a bounded normalization of translates at every right zero gives AAL | under a finite layer the limit is zero | [L*] |
| positivity of a prime density | excludes a layer on the line of the pole | a compensator below that line | [L*] |
| the count as a power | a bounded error forces the primes | fakes at every exponent above `½` (deletions with a real top, two-sided edits with a non-real pair) | [L*] |
| prime edits with a count rate | — | floor `≥13/30` right of the line, `≥1/6` on the strip `c=1/3` | [L*] (WZ4) |

### 1.6 The producer: a theorem at `7/8`, a reach of `2/3`, a frame of `3/5`
`Θ≤7/8` [X]. Its mechanism: the cube of a composite cubic Gauss sum is the ideal Möbius value times a phase [L*]; a completed sum over the twists of ζ over `K=ℚ(ζ₃)` is bounded directly and compared with the signal of `exp((s−c)²)H_η(s)/L(s,η)`; two estimates give a half-plane [L*] (`zetaZeroAbscissa_le_of_two_estimates`, `heckeHalfPlane_of_family_corrected_signal`).

**The frame [L*] (FC-T1–FC-T3, CR7, CR8).** `H_η(s)=L^S(6s−3,ψ₆η⁶)·E(s)` with `E` holomorphic and nonvanishing on `Re s>½` for every finite `S`; the frame premise at `½<σ≤2/3` is a zero-free half-plane of the phase `L`-function at `6σ−3`. A zero `ρ` of `L(s,η)` and estimates below `Re ρ` force `L(6ρ−3,ψ₆χ_{𝔣(η⁶)})=0` (zero transfer). The continued correction is nonvanishing on `Re s≥2/3`, has infinitely many zeros in `7/12≤Re s<2/3`, and has no nonvanishing continuation below `7/12`. With estimates for the whole tower of weights `k↦6k+1`, `Θ≤max(σ₀,3/5)`; with GRH for the weight-one sextic Grössencharacters, `Θ≤σ₀` down to `7/12`. The uncompleted (cube-free) correction has no wall; every wall term is a joint sixth power of the completed index and the frequency. The transfer `w=6ρ−3` maps the critical line to the edge `Re w=0` of the strip of the Grössencharacter [D] (D3).

**The estimates [L*] (budget; CR1–CR6).**

| Statement | Value at `n=6` |
|---|---|
| the room of the published geometry: the row count of the binding bin `δ=79/204` | `[13/15,7/8]` |
| floor bin summed trivially, `R₀=1` | `13/15` |
| every Cauchy–Schwarz row sieve, `R₀=5/6` | `5/6` |
| bifurcation of the signed-Gram curve, `R₀=½+1/n` | `θ=n/(n+3)`: `7/9` |
| square-root cancellation across the rows, `R₀=½` | `θ=(n−4)/(n−1)`, half-plane `1−2/n`: `2/3` |
| corners of the sign-carrying designs `(κ,n)` with squares | `(2,6)`: `8/9`; `(3,4)`: `25/28`; `(4,3)`: `49/54` |

Short columns of conductor below the row scale are incoherent to every order; the short sextic Gram is diagonal; the average row over `μ₆` is target-free (saturation along the principal twists does not read the target); the Gram of two rows is a completed sum twisted by the root numbers of the rows; the root number of a row is `G(u)γ₂(u)²` with `γ₂(u)³=μ(u)u/|u|`, a normalized sextic Gauss sum. The long columns are first moments of these root numbers; their main term sits at the Kubota exponent `½+1/6`, the bifurcation point `R₀=2/3` [C]/[doc].

**Reach [D] (D1, D2).** With every bin at square-root size the probe reaches `2/3`, exactly its uncoupled wall. The tower's `3/5` requires estimates below the square-root endpoint on every tower level. In the budget of rows of conductor exponent two the square-root endpoint is `1−2/n`, which is `½` only for `n=4`; the only sign-carrying design with `κ=2` has `n=6` (the sign law gives the Möbius sign at odd order of the Gauss sums and the parity `χ(−1)` at even order [L*]). The corpus contains no other source.

### 1.7 Finite scale and the index
- Certified: the neutral part of every window of ratio `≤103/50` has exactly one negative square at every block size, with the margin `1/5000` of the block matrix; the first step packets of ratio four (three blocks, `1/20`; six half blocks, `1/100`) and ratio seven (six blocks, `1/100`) have margins and Lorentzian neutral parts; every ratio is nonnegative on thin step packets [L*] (AG-F5–AG-F8).
- Transfer: a margin `μ₀` above one scale `R` with `log R≥E_Q+2C_Q²/μ₀+μ₀` is a margin `μ₀/2` on every refinement [L*]; at ratio four with `μ₀=1/20` this needs `log R` of order `2.5·10⁴` [D] (D4). At a fixed ratio `Q` the block matrix has at most `(Q−1)⌈e^{E_Q}⌉` negative squares at every block size; at ratio four at most `300000` [L*] (`hermNegIndex_blockWindow_le_uniform`, `hermNegIndex_blockWindow_ratioFour_le`); RH says zero.
- Polar Lagrangian: below the charge-free floor `μ₀(a)` every null mode is charged, the index is at most two and is the crossing number of a path of Lagrangian planes in `ℂ²×ℂ²` that splits into an even and an odd line; below the ground energy the polar Lagrangian is a positive increasing graph; ground modes are all charged iff `μ(a)<μ₀(a)`; unconditional on apertures `≤½(log 2+1/50)` [L*] (AG-L5–AG-L8).
- Number rings and quotients: the contacts of a number ring are its point counts over the finite fields, `idealContact K (p^m)=#Hom(𝓞_K,𝔽_{p^m})·log p` [L*]; a virtual configuration has the index of its zeros and poles off the line; `W_{ζ_L}−W_{ζ_K}` has no negative square iff the two have the same right zeros and on the line Dedekind's divisibility holds; the neutral form of a number ring has the index of its zeta function plus one; `ζ_{ℚ(∛2)}` has its Hodge index [L*] (AG-V1–AG-V3).

### 1.8 Paths, squares, sections
Constant, contacts and tree lengths are forced; a contact altered by `t` and paid at its price is RH at every parameter [L*]. The sections of the first `N` graphs in aligned boxes number the volume over `N!`: the square counts linearly [L*]. Every one-parameter family through ζ in the corpus has the count of its limit or is RH at every parameter [D].

### 1.9 Constituents and the zero field
No bounded holomorphic Dirichlet constituent and no Wiener expansion of ξ has a zero [L*]. The centered zero field `L` is algebraic and normal over the complete-fibre source field `K`; `L=K` ⇔ RH [F]; identity and conjugation are exactly the Euclidean-continuous source automorphisms, and every source automorphism moves each centered zero by less than one; over the field of squared widths the Galois group is the group of sign families annihilating every square-class relation of the radicands, with conjugation the uniform sign reversal [doc] (GZ1, GZ2). No restriction forcing `L=K` is known.

### 1.10 Verification
RH through `exp(exp(C·a))` gives the sign on `[−a,a]` [L*]; `C` is not explicit. RH is verified through height 67 [F]. Positivity at aperture `a` confines every zero with `T₀≤|γ|≤2πe^a` to depth `<exp(−c log³|γ|)` [L*].

### 1.11 Law and point
One pointwise theorem holds past the Vinogradov–Korobov region: no zero right of `7/8` [X]. Left of it every unconditional theorem on the zeros of ξ is in law: twisted moments below the square root and a positive proportion of critical zeros of odd multiplicity [L*]; `67.25%` simple critical zeros in the objects of `Zeta23` [L*]; the squared right-depth moment `o(V)` [KR]; visibility of a near-top cluster with a fixed depth deficit or a deep companion, by box cameras [doc] (CAM1).

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
| positivity of a prime density | the line of the pole |
| the count as a power; prime edits | fakes at every exponent above `½` |
| the FE with the Euler product | rigidity: the rational primes |
| mean values | in law |
| reciprocity families with two estimates | `Re s>7/8` [X]; reach `2/3` with square-root cancellation; frame `3/5` |

**Consequence [D].** One mechanism has produced a pointwise theorem, and its whole class stops above `½`. Every other mechanism of the corpus is a receiver, a model or a rigidity theorem.

### 1.13 What is ruled out
| Mechanism | Verdict | Evidence |
|---|---|---|
| explicit formula, positivity, Euler products over integer norms or rational primes (with multiplicities `0,1,2` and a count rate), linear counting, as a constraint on a finite layer, a tail, landing | realized by models | [L*] |
| a count rate above `√x` forcing a real zero on top | false: two-sided edits with a non-real pair alone | [L*] (WZ1) |
| an exponent `>3/5` reached by the cubic probe's frame, or `>2/3` without estimates beyond square root | the coupled tower; the signed-Gram endpoint | [L*]; [D] |
| a nonvanishing continuation of the probe's correction below `7/12` | none | [L*] |
| the uncompleted correction with a reflection | completion is what the reflection needs and what creates the wall | [doc] (CR7) |
| a Cauchy–Schwarz row sieve below `5/6`; geometry or row counts below `13/15` | budget | [L*] |
| windows below the logarithmic radius; one-sided floors of one length | models | [L*] |
| regulators, paths, certificates, amplification, replication, symmetrization as sources | kills | [L*] |
| bounded or Wiener constituents with a zero | none | [L*] |
| the return transfer from a strip to the line | RH under a strip | [L*] |
| positivity alone as a 70% census certificate | cost `>13/10` | [L*] |

## 2.1 Tasks that are just work

Difficulty is established where a known argument exists; `(unverified)` marks the rest. None of these decides RH.

### The half-plane `Re s>7/8` in Lean
| # | Task | Routes | Basis |
|---|---|---|---|
| A118a | the full arithmetic Poisson series of the probe, its continuation, removal of the cube sum in the comparison | JAS, MC, S3 | `zetaZeroAbscissa_le_of_two_estimates`; the local factors; `fullResidualCorrection` (FC-T3) |
| A118c | the comparison saving uniformly in the ray class character | — | `heckeHalfPlane_of_family_corrected_signal` |
| A118d | the direct bound: reflection of the completed theta row, the sextic large sieve, the zero detector | — | `sieveNorm_sharp`; STCC unfolding (ST2) |
| A118-I | a first native half-plane: the balanced design at `11/12` [D] | — | budget |
| A138 | the corollaries of `Θ≤7/8` as unconditional statements: rung `κ<4/3`, level `11/8`, returns `y^{1/8}`, ringdown `1/16`, tails `a<1/8`, critical-comb growth `≤3/8`, the Artin index of `X³−2` in `(½,7/8]` | every scale route | §1.2 |
| A141 | the half-plane for fields containing `ζ₃` and every ray class character (unverified) [C] | ACS, HF | frame for every number field |

### The producer's last estimates and its calibration
| # | Task | Routes | Basis |
|---|---|---|---|
| A148 | global continuation of the cubic Eisenstein series; the regularized Rankin–Selberg of `θ²` with its double pole at `4/3` [C] | MC, JAS, PM | ST1–ST3; the Hecke bound and the Mellin transform of the nonconstant part of `θ²` are in Lean (ST5, ST6) |
| A149 | the floor bin over `𝔽_q[T]`, `q≡1 mod 6`: Kubota series rational in `q^{−s}`, theta coefficients explicit; evaluate the long columns exactly and test the bifurcation `½+1/n` (unverified) [C] | MC, JAS | CR5; CRF Q8 |

### Assemblies of proved pieces
| # | Task | Routes | Basis |
|---|---|---|---|
| A142 | an explicit constant in the verification rate `exp(exp(C·a))` | RW, SRT, TH, LI, HCF | `exists_doubleExp_windowPositive`, `spreadHeight_le` |
| A146 | the sign of `𝔚_4` and `𝔚_7` at every block size: certified margins between the first block sizes and the transfer threshold, or a sharper transfer (unverified) | ACS, HF, RW | AG-F6, AG-F9 |
| A150 | Brauer induction, extending the index of a quotient of `L`-functions to every Artin character [C] | ACS, HF | `exists_le_negIndex_quotient_iff` |
| A151 | the critical-line FE defect of the pair twin and of the quartet edits as functions of the height: the first step of B186 (unverified) | ZCG, BAG | WZ1, WZ4; EFT normalization |
| A140 | the sign on windows of half-width below `½log 5` (unverified) | RW, ACT, EWU, OWU | edge cost [F] |
| A144 | the tangent data of `μ` and `λ` under additive twists (unverified) | ZCG, MC | [F] |

### Finite verification and explicit constants
A1 certified `RHVerifiedThrough T` past 67; A2, A3 numeric heights and first-window membership; A4, A5 theta ranks 15 and beyond (unverified); A6, A7 cone widths, anti-diagonal certificates (unverified); A9, A13 eighth-root constants, near-gcd charges (unverified); A117 end points of the feasible interval of `w(2)`; A19 an explicit heat-horizon height; A48, A58 Hasse–Weil tests, effective gap iteration (unverified).

### Classical inputs to formalize
| # | Task | Basis |
|---|---|---|
| A18 | twisted second moments past the square root [C] | `θ<½` in Lean |
| A147 | logarithmic two-point Chowla: Matomäki–Radziwiłł for `λχ` and the final assembly [C] | entropy decrement, circle method, the prime kernel off the major arcs, VK region for Dirichlet `L`, prime-block bounds, ladder mean values, Ramaré's identity [L*]/[doc] |
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | order `Λ` [F] |
| A33 | Fourier coefficients of the cubic residue at all heights [C] | `Re s>2` [F] |
| A41 | count law for every curve, first plane quartics [C] | hyperelliptic case [L*] |
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
| B1, B152 | the sign on every window; the neutral part with one negative square at every ratio and block size | RH | all sign routes; ACS, HF |
| B2, B4, B5 | no crossing of the aperture path; outer predictors; kick admission | RH | RW, GWZ, WTZ |
| B6, B8, B101 | full-space sign at every critical multiple; head thresholds; polar payment | RH | HF, SRT, AIP |
| B104 | whether `μ(a)=μ₀(a)` can occur: a charge-free ground state solving the unforced equation, at the critical aperture in particular (§2.8) | method | HF, SRT, AIP, ACS, SC |
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
| B187 | a Möbius-signed source whose square-root endpoint is the line, or a theorem that none exists among Gauss-sum designs (§2.5) | producer | JAS, MC, every scale route |
| B180 | the reflection of the completed theta row without Eisenstein series | method | JAS, MC |
| B48–B54 | the deciding input at square-root precision and its faces | RH | WL, MC, SQF, JAS, CTF, PBM, RB |
| B55, B67 | polynomial stencil rate; parity at power saving | ≥qRH to RH | WL, MC |
| B56 | `Θ<1⇒Θ=½`; with `[X]` it is RH | RH | whole programme |
| B57–B61 | depth density `o(T)`; `D_win`; cluster wall; Green moments; a detector past the last scale | sub | WD, MC, ZCG |
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
| B186 | the FE axis: the least size of the critical-line FE defect of a fake (§3) | method | ZCG, BAG, ELT, JAS, LA, SC, WL |
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
| B184 | How far does the frame of the producer reach? | a coupled tower: zero transfer `ρ↦6ρ−3`; `max(σ₀,3/5)` with all estimates; `7/12` under sextic GRH; correction zeros in `7/12≤Re s<2/3` | [L*] (FC-T1, FC-T2) |
| B179 | Is the index a Maslov index? | yes: the crossing number of the conormal path with the graph of Weil's operator; the far end carries the zeros | [L*] (AG-L2, AG-L3) |
| B175 | Signed cancellation across the rows of the floor bin | reduced: average row and short columns settled; the long columns are B185 | [L*] (CR1–CR6) |
| A139 | the correction as a Grössencharacter `L`-function | `H_η=L^S(6s−3,ψ₆η⁶)E`, `E` nonvanishing on `Re s>½` | [L*] (FC-T3, CR8) |
| A143 | the sign of `𝔚_4`, `𝔚_7` | margins at the first block sizes; every block size at ratio `≤103/50`; every ratio on thin packets; at most `300000` negative squares at ratio four for every block size; zero at every block size is A146 | [L*] (AG-F5–AG-F8, AG-F11) |
| A152 | ordinary convergence of a power comb at an unattained boundary | converges ⇔ every zero has `Re ρ<1−a` | [L*] (`powerCombTailConverges_iff_forall_zero_re_lt`) |
| A145 | Artin characters beyond the monomial case | the index of quotients of products of configurations; the rest is Brauer induction (A150) | [L*] (AG-V2) |
| — | Does a count rate above `√x` force a real zero on top? | no | [L*] (WZ1) |
| — | Are the nullities of the aperture path even? | no: a simple ground mode | [L*] (AG-L9) |
| B176, A132 | the cost of a window | double exponential | [L*] |
| B177 | least twist exponent with a generic mean square | `(n/(n−1))(2Θ−1)`; Jacobi family generic at every `θ` iff RH and GRH for the quadratic twists | [L*] |
| B182 | least count remainder of a fake | fakes at every `β>½`, below `½` from a half-plane; infimum in `[0,½]` | [L*] |
| B158 | the boundary of the order-`n` probe | the budget tables | [L*] |
| B169 (path half) | a Lefschetz path at an odd prime | the price path is RH at every parameter | [L*] |
| B148 (strength), B94, B181, quasi-RH | the return transfer; theta identification; the comparison at `7/8`; `Θ<1` | RH under a strip; `[X]` | [L*]; [X] |
| B156 (configurations), B117 (three regulators), B172 (first order), B153 | as recorded | models; kills | [L*] |
| A59, A89, A115, A133–A135, A137, A118b, A80, A82, A94, A102–A105, A108, A109, A112–A114, A116, A119, A121, A123–A131 | as recorded in the walls ledger | theorems | [L*] |

## 2.3 Frankenstein routes

**No assembly closes RH.** One assembly is a theorem (`[X]`). Every other assembly has an open input of RH or AAL strength, a half-plane input, or returns an identity.

| # | Parts | What the assembly gives | Missing input | Gain |
|---|---|---|---|---|
| F29 | **One scale** | every graded receiver is one number; the critical comb reads it on one sequence | a level below `7/8`; in Lean any level | a proposed estimate is placed before work starts |
| F30 | **Two estimates, fully evaluated.** Frame, coupled tower, budget, coherence (short columns, average row, root numbers) | `[X]`; with square-root cancellation `2/3`; with estimates beyond it on the tower `3/5` [D] | A118; B174, B185 | the exact reach of the only producer |
| F31 | **Half-plane, then line** | rung `4/3`, level `11/8`, returns `y^{1/8}` | a step from a strip to the line | none: every transfer is RH |
| F39 | **The index at three scales.** Finite-scale neutral part (short windows, first blocks, thin packets), Morse = Maslov index, verification rate | RH ⇔ no crossing ⇔ one negative square of every neutral window; certified on short windows at every block size [L*] | B152 at ratio `>103/50`; A146 | one exact finite object per window with certified transfer |
| F40 | **Models plus rigidity.** Two-sided edits, deletions, the firewall, FE rigidity with `L¹`/`L²` defects | the inputs a proof of AAL cannot be built from; the door: Euler product with the FE as an identity [D] | B186; B183 | a proposed AAL argument is tested on the models before work starts |
| F41 | **World I off the scale.** Non-attainment, unit gap, quantum, four sectors, filters, currents, tangent data | AAL from any receiver form [L*] | B170, B145 | — |
| F42 | **The lattice with a level.** Index law for Hecke characters, number rings, quotients; `[X]`; base change | for `ζ_{ℚ(∛2)}` and the Artin character of `X³−2`: index counts zeros in `(½,7/8]` [D] | A141, A150 | the index of every comb counts zeros in one strip |
| F43 | **Galois and continuation.** Zero field, Jensen quartets, heat counts | `L=K` ⇔ RH; quartet exhaustion of the off-line divisor [L*/F] | a restriction forcing `L=K` | none below RH |
| F37 | **Verification with a rate** | window sign from a double-exponential height; certified matrix margins transfer | A142, A146 | finite statements with stated sizes |
| F38 | **Mean values and cameras** | a positive proportion on the line; near-top clusters with a depth deficit visible | A18; B59 | the in-law half is native |
| F11 | **Construct, then identify** | an approximant with a gap gives RH | B146, B171 | regulators excluded |

**Closest to the open core:** F30 (the producer's exact reach), F40 (the door for world I), F39 (the finite object of Σ).

### What a contradiction search may assume in world I
`Θ≤7/8` [X]; an attained isolated top `β≤7/8`; `M(x)=O(x^{β′})`, `β′<1` [F]; `ψ(x)−x` attains `x^β` on every late window and at the primes [L*]; Gaussian window sums of `μ` and `λ` equal their top residues with numerators related by `ζ(2ρ)` [F]; quantized multiplicities [L*]; zero limits of normalized translates [L*]; a nonzero Euler filter accelerates the horocycle rate [L*]; the packet index is finite and positive [L*]; a two-sided edit with a count rate above the top removes the layer [L*] (WZ6). No contradiction comes from identities alone, positivity, Euler products over integer norms or the rational primes with multiplicities `0,1,2`, a count rate, the FE with Gamma factor and count, a regulator, or any statement in law [L*].

## Validation tests for 2.4–2.8 and 3

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

**No statement about the zeros of ζ below RH and AAL passes all tests as a door to the line.** The questions below were checked against the corpus by sentence queries (log §9).

## 2.4 Breakthrough question below RH: the long columns (B185)

**Position.** The only producer of the corpus converts a law over a family of twists into a point by two estimates. Everything it does with squares is mapped and stops at `13/15`, then `5/6` (§1.6). Its floor bin is reduced in Lean to one object: the short columns cancel to every order, the short sextic Gram is diagonal, the average row is target-free, and what remains are the long columns, first moments over the rows of the root numbers `G(u)γ₂(u)²` (normalized sextic Gauss sums times a phase of bounded conductor) against a dual column [L*] (CR1–CR6). The coherent main term of these moments sits at the Kubota exponent `½+1/6` [C].

**Question (B185).** *Is the first moment of `G(u)γ₂(u)²` over squarefree rows `u` of norm up to `U`, twisted by a dual column `n` of norm up to the row scale, equal to its Kubota main term plus `O(N(n)^A U^{R₀+ε})` with some `R₀<1`, uniformly in `n`? What is the least such `R₀`?*

| Answer | Effect [D] (signed-Gram curve at `n=6`) |
|---|---|
| any `R₀<1` | a half-plane below `13/15`: the first estimate of the producer that is not a square |
| `R₀<5/6` | below the floor `5/6` of every Cauchy–Schwarz sieve |
| `R₀=2/3` with the main term evaluated | `7/9` |
| `R₀=½` (square-root remainder) | `2/3`: the wall of the frame, the end of the class |
| no saving uniformly in the column | the producer stops at `13/15` through its floor bin; every graded receiver keeps `[X]` as its only level |

Every receiver of the scale moves with the answer: the rung, the level, the return bound, the ringdown rate, the tails, the critical-comb growth, the fake exponent.

**First step and obstacle.** A149 (the function-field floor bin, where the Kubota series is rational) and A148 (the main term through the regularized Rankin–Selberg of `θ²`, whose double pole at `4/3` makes the squarefree part coherent at `2/3`). Named obstacle: uniformity in the column; the corpus has neither the sextic metaplectic Eisenstein series nor a sextic large sieve, and Heath-Brown's cubic large sieve gives `5/6` and no more [doc].

**Tests.** T1 passes (an estimate for Gauss sums; its consequence a half-plane below `7/8`). T2, T4, T6 pass. T3 named. T5 calibrated on matched phases (saturation), on `μ²` (not generic), on the average row (target-free). T7 moves Π167 and Π175. T8: the square-root form is a conjecture of Patterson type [C]; any power saving uniformly in the column is the question, with a first step in corpus objects.

**Limit.** `2/3`. The question does not lead to the line.

## 2.5 Breakthrough question for the search for a producer: a source whose square-root endpoint is the line (B187)

**Position.** The producer class is mapped to its end (§1.6): with square-root cancellation everywhere the cubic probe reaches `2/3`; its frame stops at `3/5`. The reason is arithmetic, not analytic [D] (D2): in the budget of rows of conductor exponent two the square-root endpoint is `1−2/n` [L*] (`signedGram_phase_endpoints`), which is the line exactly at twist order `n=4`; the Möbius sign comes only from Gauss sums of odd order [L*]; and the three sign-carrying designs of the corpus are `(κ,n)=(2,6),(3,4),(4,3)` — `κn=12` in each — with square corners `8/9`, `25/28`, `49/54` [L*]. The design `(3,4)` has twist order four and carries the sign through one Jacobi sum (`g(χ)²=J(χ,χ)g(χ²)`, `J≡−1`) [L*], but its rows have conductor exponent three.

**Question (B187).** *Is there an identity that writes the Möbius function through coefficients with a reflection — Gauss or Jacobi sums of a metaplectic cover, or another family with a functional equation — whose rows have conductor exponent two and principal frequencies of order four (`κn=8`), or more generally whose budget has the square-root endpoint `½`? Or does every sign-carrying design satisfy `κn≥12`, so that the class ends at `2/3`?*

| Answer | Effect |
|---|---|
| a design with square-root endpoint `½` and a correction without a wall above `½` | a producer of the line by estimates: the remaining input is square-root cancellation in its bins |
| such a design whose correction has a wall | the frame decides; the transfer map of its tower and its fixed point become the question (§1.6, D3) |
| `κn≥12` for every sign-carrying design | the Gauss-sum producers end at `2/3`: RH needs a source of another kind |

**First step and obstacle.** Classify the products of Gauss and Jacobi sums over cyclotomic rings that carry the Möbius sign by `(κ,n)` — finite algebra in the objects of `TheOddPowerOfAGaussSumCarriesTheMoebiusSign` and `TwoGaussSumsWithAQuadraticProductCarryTheMoebiusSign` — and run each through `lowBoundaryGenOrder` and the signed-Gram curve with the conductor penalty of `lowUnslotted`. Named obstacle: the theta coefficients of covers of degree four and higher are not known explicitly [C], so the source identity of a new design has to be proved before its budget means anything.

**Tests.** T1: a producer question, implied by nothing about ζ's zeros. T2: an existence statement or a classification theorem. T3 named. T4 pass. T5 calibrated on the three designs in Lean, on even order (parity instead of sign), on the uncompleted correction (no wall, no reflection). T6, T7 (moves Π174) pass. T8 not a named problem; the first step is finite algebra in corpus objects.

**Limit.** The budget is an exponent model; a design that reaches `½` in it needs its estimates and its frame as well.

## 2.6 If positivity, Weil positivity and spectral methods are excluded

"Spectral" covers spectral theory of operators in every form, automorphic spectral theory included; "positivity" covers nonnegativity of forms, kernels, counts, coefficients and averaging measures. Kept: Fourier analysis, Poisson summation, exact identities of Gauss and Jacobi sums, reciprocity, mean values used as bounds, exponential sums, continuation and orders of zeros, integrality, recurrence, Galois theory, dominance in ultrametric fields.

**What the constraint removes [A].** The positivity forms (all of Σ), Landau's theorem (positive coefficients) and with it the balance law of edits, the proofs of FE rigidity (positivity of Abel means), the large sieves (squares), and the Eisenstein reflection of the theta row with the Kubota main term (spectral). What survives: the receivers of the minimal face in absolute value; the Galois form `L=K` ⇔ RH; the Goss dominance; the parity law of squares (an odd zero of an edit exponential at `ρ` is a branch point of `ζ_B` at `ρ/2`) [L*] (WZ3); the reciprocity identities of the probe [L*]; the Vaughan–Gaussian reduction of world I [L*].

**An observation that frees one tool [D].** `Σλ(n)Λ(n)n^{−s}=ζ′/ζ(s)−2ζ′/ζ(2s)` has in `Re s>½` the pole at `1` and poles exactly at the zeros of ζ: AAL is invariant under the Liouville twist, and the parity blindness of bilinear statements is no obstruction to AAL.

**Question (B145).** *Does the prime-weighted centred type-II current at a growing isolated mode, with both continuum corrections, cancel below the recovered residue?* In Lean: under ¬AAL filters recover the top residues; the growing-order Gaussian current reduces to centred cofactors `≤3t^{71}` with filtered error `≤2h^d exp(−at/8)` [L*]; separated complete unweighted pairs decay faster than every power and the normalized near-diagonal row is bounded [F]. Open: the restricted prime-weighted cofactor sum.

| Answer | Effect |
|---|---|
| yes | AAL without a sign and without an operator; RH ⇔ ZAL |
| a lower bound of the size of the residue | the Vaughan–Gaussian architecture does not exclude a finite layer: world I needs an input beyond exponential sums |

**Tests.** T1 fails (AAL strength). T2, T3 pass. T5: the argument has to fail for two-sided edits with a finite layer — it can, through the actual Möbius coefficients, which edits change at infinitely many primes. T7 moves Π149. T8: a Type-II sum in the dark range [A].

**Limit.** Under the constraint the step from AAL to RH is ZAL, a half-plane at every depth, and the corpus has no sign-free, non-spectral source of half-planes: its one producer uses squares and an Eisenstein reflection, and with both it ends at `2/3`. **Under the constraint no question in the corpus opens the path to RH; B145 opens the half of it that world I is.**

## 2.7 If RH is a physical phenomenon in AdS with a modular horizon

**What is proved [L*].** The resonances of the modular horizon are the zeros of `ξ(2s)`; a rate `δ` for compact pulses is the strip `Re ρ≤1−2δ`, and the pulse rate equals the horocycle rate; RH is the quarter rate; the unfiltered horocycle exponent is `1−Θ/2`, filtered `1−Θ∞/2`; AAL ⇔ no Euler filter accelerates; every regulator has the count of its limit; no Maass cusp form with `0<λ<3/16` exists on any congruence subgroup (`selberg_three_sixteenths_congruence`); the producer itself lives on a second horizon, the cubic cover of hyperbolic three-space, where `θ` is the residue of the Eisenstein series at `4/3`, its square unfolds against Eisenstein series, and the corrections are Grössencharacter `L`-functions of the angular characters `ψ₆^k` (harmonic weights `6k`) [doc] (ST1–ST3, FC-T4). With `[X]`: the rate `1/16`.

**Readings [D].**
- *World I is ordinary ringdown and is removable*: a finite set of least-damped modes, removed by a differential filter of finite degree.
- *The producer is a scattering experiment on a cover horizon*: the scalar channel (ζ) couples to a tower of spinning channels (`ψ₆^k`), and the coupling `w=6ρ−3` maps the scalar's critical line to the edge of the spinning channel's strip. The wall `2/3` is the resonance set of the first spinning channel.
- *The one arithmetic gap principle in Lean is for bound states*: Selberg's `3/16` holds on every congruence group and fails on non-arithmetic groups [C]; its proof is arithmetic (Kloosterman sums and Weil's bound) [C].

**Question (B188).** *Does the mechanism that gives `λ₁≥3/16` on congruence groups — the Kuznetsov formula with Weil's bound for Kloosterman sums — bound the scattering resonances of `SL₂(ℤ)\ℍ` away from the unitary axis: a resonance-free strip of any width, from the Kloosterman side, without a family of twists?*

| Answer | Effect |
|---|---|
| a strip of width `δ>0` | a second producer of a half-plane, independent of the Gauss-sum class; `δ>1/16` is a half-plane below `7/8` |
| no: the Kloosterman side sees the bound states and not the resonances | the arithmetic of the horizon bounds discrete spectrum only; the physical reading supplies receivers and the source must come from elsewhere |

**What the corpus says about the candidates.** Hölder dynamical realizations give a strip and the oscillation estimate fails on additive realizations [KR]; graph horizons with commuting Hecke operators and slow resonances exist [KR]; KMS positivity and modular conjugation do not select the line [KR]; scattering Schur contractivity is blind to the position of zeros [KR].

**Tests.** T1 passes as a half-plane for `δ>1/16`. T2, T3 pass. T5: must fail for non-congruence groups and graph horizons with slow resonances; the `3/16` theorem itself does. T7 moves Γ226. T8: a zero-free strip from Kloosterman sums is not a named problem in this form; first step in corpus objects (`RHTower/SelbergThreeSixteenths`, the Kuznetsov large sieve of the corpus) with one obstacle: the Eisenstein contribution to Kuznetsov is weighted on the unitary axis, where the resonances are not [C].

**Limit.** A rate is a half-plane; the quarter rate is RH and is not reached by a principle with a margin.

## 2.8 If RH is a problem of topology or geometry

**What is proved [L*].** The Morse index of the sign problem is a Maslov index: the conormals of the apertures form an increasing path of Lagrangian subspaces that ends at the horizontal Lagrangian; its crossings with the graph of Weil's operator are the null modes; the index is their number; the far end carries the zeros; RH ⇔ no crossing (AG-L1–AG-L3). The poles see a finite-dimensional part of this path: the polar Lagrangian in `ℂ²×ℂ²`, an even line and an odd line, positive and increasing below the ground energy, meeting the charge axis exactly at the charged null modes (AG-L5–AG-L8). At finite scale the neutral part of the step-packet matrix is a Dirichlet form on a weighted graph plus a potential, and RH is its Hodge index on every window (AG-F1, AG-F4).

**Readings [D].**
- *The sign problem has a finite-dimensional shadow.* If every null mode is charged, the index is the crossing number of two curves in two projective lines; a neutral null mode is invisible to them.
- *The finite-scale form is a bound-state count.* The neutral part is `Σ V_jσ_j² + ½Σ w_{jl}(σ_j−σ_l)²` with `w>0`: a discrete Schrödinger operator on the graph of the floor maps; RH says that its well holds exactly one bound state on every window [D] (from AG-F1, AG-F4).

**Question (B104, exact form).** *Can the ground state of the restricted Weil form at an aperture be charge-free — can `μ(a)=μ₀(a)` hold, at the first conjugate aperture in particular?*

| Answer | Effect |
|---|---|
| never | ground null modes are charged; the critical-curve classification loses its third case (RH or `R_polar<W`); the polar channel of HF, SRT, AIP, ACS (atomic) and SC sees the first crossing |
| it can, on a configuration model with ζ's archimedean data | a neutral null mode is invisible to the poles: polar payment cannot certify the first crossing, and those routes need a non-polar input |

**First step and obstacle.** The finite-scale analogue: at every block size, is the ground vector of the full block matrix (with the product of the charges) charged? The neutral part's ground vector has one sign and is charged because jets and contacts attract [doc] (AG-F4); the full matrix adds `2c₀c₁`, which favours charges of opposite sign. Then transfer to the continuum through the refinement tower. Named obstacle: the continuum form is frustrated (no positivity-improving property: Markov stability fails on long intervals [KR]), so the one-sign argument does not pass to the limit as it stands.

**Tests.** T1 passes (method; not known to follow from RH). T2, T3 pass. T4 pass. T5 calibrated on the finite-scale neutral part and on short apertures. T6 pass. T7 moves Σ135, Σ139, Σ177. T8 not a named problem.

**Limit.** The answer does not decide RH; it decides whether the finite-dimensional polar path is a complete invariant of the first crossing.

## 2.9 New field for RH: reflection arithmetic

**Does RH need a new field?** The fields that the mechanism classes call for exist as programmes and end at theorems (§1.12). What the three cores share is one input that no programme treats as its object [D] (D6): the reflection `s↦1−s`.
- On the producer side, the reflection of the theta row needs the completed index, and the completion is what puts the phase `L`-function into the correction: the wall (CR7, FC-T1).
- On the model side, the reflection is the one structure no model of world I has; the Euler product with the FE as an identity is rigid (§1.3).
- On the sign side, the archimedean term of every form is the Gamma factor of the reflection; the neutral part is the form of the zeros minus the poles (AG-F3).

| Field | Programme | Where it ends |
|---|---|---|
| reciprocity sources, family continuation, coherence | FCT, MMD, CRF, STCC | `[X]`; reach `2/3`; frame `3/5` |
| models of world I | WZC, FFA, SPAL, APD | every structure set weaker than Euler + FE identity has a model |
| FE rigidity | EFT, APD | `L¹`/`L²` defects force the rational primes |
| index and finite scale | AGZ, HFP | RH as a Maslov index and as a finite-scale Hodge index |

| Aspect | Content |
|---|---|
| What it is about | What the functional equation costs and what it buys, measured in one currency: the defect. The FE defect of a system (rigidity, B186); the completion defect of a family (the wall, the transfer map `ρ↦kρ−c` of its tower); the Gamma defect of a form (the archimedean term); and how each moves zeros |
| What it is like | A defect calculus: every construction is assigned its FE defect, its completion offset and its count remainder, and a statement about zeros is placed on the defect axes before work starts, as estimates are placed on the scale |
| Established | Rigidity at `L¹`/`L²`; quantitative small-defect identification of the primes; the uncompleted correction without a wall; the zero-transfer law; the classification of the models by structure set; the neutral part as zeros minus poles [L*] |
| Criteria | R1 a statement must hold for ζ and fail for every model that lacks the reflection. R2 it states its defect budget. R3 it distinguishes completion from reflection. R4 it reproduces the Goss and Weil cases as defect zero. R5 it does not use positivity of Abel means where the defect is not integrable |
| Questions it must answer | B186 (the FE axis); B187 (a source with square-root endpoint `½`); B180 (a reflection of the theta row without Eisenstein series); is there a completed family whose transfer map fixes the critical line (D3)? |
| Tools | defect Laplace transforms (the EFT method); Poisson summation on covers; transfer maps and their fixed points; edit constructions with prescribed symmetric factors |
| Objects | reflections, completions, defects, transfer maps, walls, edits |
| Language | defect, completion offset, transfer, wall, rigidity radius |
| Mechanisms | Built on EFT, CRF, WZC, AGZ. To discover: a reflection that does not complete, or a theorem that it must |

**Main conjecture [A].** Every reflection of a Möbius-signed family costs a completion whose transfer map sends the critical line to the edge of a strip. **Milestones.** M1 A151. M2 B186. M3 the transfer maps of every sign-carrying design (B187). M4 a reflection without completion, or the theorem that none exists.

## 2.10 New field for AAL: defect arithmetic of finite layers

**Does AAL need a new field?** The receivers (FFA), the instruments (ELT) and the model theory over the rational primes (WZC) are built, and they meet at one conclusion (D5): an argument for AAL uses the Euler product with the FE as an identity, or with a count below the floor. Both are rigidity inputs. What is missing is rigidity **with a layer**: a quantitative form of "the Euler product with the FE identifies ζ" that sees a finite top layer.

| Aspect | Content |
|---|---|
| What it is about | Systems with an Euler product, a count remainder `r` and an FE defect `g`, and the finite top layers they can carry: the least `(r,g)` for a layer of depth `h` and multiplicity `m`. ζ is the case `r=O(1)`, `g=0`; AAL is the statement that this case carries no layer |
| What it is like | Hamburger's theorem made quantitative and given a layer. Its model case is the one-off continuous system with a pair and a defect trade-off [KR]; its first discrete case is the two-sided edit |
| Established | layers realized at every count exponent above the top; balance and parity laws below it; the count floor; rigidity at `L¹`/`L²` FE defects; tangent data of `μ` and `λ`; four sectors of the trace [L*] |
| Criteria | Q1 every layer statement is a statement about `(r,g)`. Q2 the case `g=0`, `r=O(1)` is ζ. Q3 the bounds hold for every edit and every continuous system. Q4 no positivity of a prime density inside the strip. Q5 constants do not degenerate as the depth tends to zero |
| Questions it must answer | B186; B183 (layers below `√x`); a layer–defect inequality `‖g‖≥F(h,m)` on every discrete Euler product with a count rate; does it pass to `g=0`? |
| Tools | greedy two-sided rounding with prescribed factors; Perron analysis of edit counts; the Laplace method of FE rigidity with a layer term; filters and currents |
| Objects | edits, layers, defects, count remainders, tangent data |
| Language | layer, defect, remainder, balance, parity, rigidity radius |
| Mechanisms | Built on WZC, EFT, FFA, ELT. To discover: one inequality between the FE defect and a finite layer |

**Main conjecture.** AAL, as the `g=0` case of a layer–defect inequality. **Milestones.** M1 A151. M2 B186. M3 the inequality on edits. M4 on Beurling systems with real weights. M5 the passage to `g=0`.

## 2.11 New field for RH without positivity: order arithmetic

**Does a positivity-free, non-spectral RH need a new field?** Under the constraint (§2.6) the surviving mechanisms that act on zeros are orders and their parity, branch points of continuations, Galois actions on zeros, ultrametric dominance and exact evaluations of Gauss and Jacobi sums. Each exists in one programme; none is organized as a theory of zeros.

| Aspect | Content |
|---|---|
| What it is about | Zeros through the algebra of their orders: parity of orders of squares and of Euler-product exponentials, branch points at `ρ/2`, `ρ/3`, …, the Galois group of the zero field over the source field, Newton polygons in non-archimedean completions |
| What it is like | The Goss proof as the model case: a Riemann hypothesis from dominance and simplicity of slopes, with no inequality between a sum and its terms |
| Established | the parity law of squares (WZ3); `L=K` ⇔ RH and the Euclidean topology of the zero field (GZ1); separation forces rationality [F]; the Goss Riemann hypothesis [L*]; the sign law of Gauss sums [L*]; the uncompleted correction (CR7) |
| Criteria | O1 no inequality between a form and its squares. O2 no operator spectrum. O3 a statement about orders, branchings or Galois actions. O4 it reproduces the Goss case. O5 it fails for every fake with an odd fake zero below twice its count exponent (WZ3) |
| Questions it must answer | B145; a restriction forcing `L=K` from the source traces; a non-archimedean completion of the zero field with fibrewise distinct norms; the branch points of `λ`-type series at the half-scale points of a top layer |
| Tools | Newton polygons over completions of the source field; parity and branching of continuations; Galois descent of width classes; exact Gauss-sum evaluations |
| Objects | orders, branch points, zero fields, width classes, slopes |
| Language | order, parity, branch, slope, descent |
| Mechanisms | Built on GaloisTheoryOfZeros, SignFreePurityMechanisms, WZC, CRF. To discover: a valuation on the zero field that separates the zeros of each fibre |

**Main conjecture [A].** The zero field of ζ carries a valuation, defined from the source traces, whose slopes separate every fibre; separation then forces `L=K` [F]. **Limit.** The conjecture is RH-strength; its first steps (valuations on `K`, slopes of single fibres) are below it.

## 2.12 New field for RH as AdS physics: arithmetic horizon towers

**Does it need a new field?** The modular horizon has its receivers (BHR, AHMH, HAT, CTH) and one cover horizon has its unfolding (STCC). The producer reads ζ through a horizon tower: a cover, its theta, and the spinning Grössencharacter channels coupled to the scalar by `w=6ρ−3` (§2.7). No programme treats a family of horizons and the maps between their resonance sets.

| Aspect | Content |
|---|---|
| What it is about | Families of arithmetic horizons (congruence quotients, metaplectic covers of every degree), their scalar and spinning channels, the coupling maps between their resonance sets, and the arithmetic gap principles (Selberg's `3/16`) that each satisfies |
| What it is like | Scattering theory of a tower: each horizon's resonances are the zeros of a family of `L`-functions, and completion couples the families by affine maps |
| Established | ringdown ⇔ strip; horocycle exponents; filters; Selberg `3/16` on congruence groups; the cubic cover's Eisenstein series, residue, unfolding and cube frequencies; Grössencharacter continuation for harmonic weights `6k`; the coupled tower [L*]/[doc] |
| Criteria | H1 built from horizons and places, not from zeros. H2 false for non-arithmetic groups. H3 a rate with a margin is a half-plane; the quarter rate needs an equality case. H4 coupling maps are computed from completions, not postulated |
| Questions it must answer | B188; B178; the coupling maps of covers of every degree and their fixed points; a horizon whose coupling fixes the critical line |
| Tools | Kuznetsov and Kloosterman sums; metaplectic Eisenstein series; Rankin–Selberg on covers; Euler filters |
| Objects | horizons, covers, channels, spins, coupling maps, rates |
| Language | channel, spin, coupling, rate, gap |
| Mechanisms | Built on BHR, AHMH, STCC, FCT, `RHTower/SelbergThreeSixteenths`. To discover: an arithmetic gap principle for resonances |

**Main conjecture [A].** On congruence horizons the Kloosterman side bounds resonances as it bounds bound states. **Milestones.** M1 A148. M2 the coupling map of a second cover. M3 B188.

## 2.13 New field for RH as topology or geometry: potential theory of the floor-map graph

**Does it need a new field?** The index theory of the aperture is built (AGZ: Morse = Maslov, polar Lagrangian); the zero field has its Galois topology (GaloisTheoryOfZeros). What no programme contains is the geometry of the finite object that RH is at finite scale: the neutral part of a window is a Dirichlet form on a weighted graph — vertices the blocks, edges the jets (every pair) and the contacts (the graphs of the floor maps `b↦⌊b/k⌋`, weighted by `Λ(k)/k`) — plus a potential, and RH says it has exactly one negative eigenvalue on every window [D] (AG-F1, AG-F4).

| Aspect | Content |
|---|---|
| What it is about | Bound states of discrete Schrödinger operators on the floor-map graphs of windows: their number, their ground state (one sign, charged), their behaviour under refinement (translation by `log m`), gluing of windows, and growth of the ratio |
| What it is like | Potential theory and spectral geometry of weighted graphs: Cheeger and isoperimetric constants, Bargmann- and Cwikel–Lieb–Rozenblum-type counts of bound states, Agmon decay [C] |
| Established | the decomposition charges + potential + Dirichlet form with positive weights; one-sign charged ground vector of the neutral part; one negative square on windows of ratio `≤103/50` at every block size and on the first blocks of ratios 4 and 7; the refinement tower; the cross term of a block and a far window is minus the product of their charges [L*]/[doc] |
| Criteria | G1 counts bound states without the zeros. G2 the count is one on the certified windows. G3 a wrong contact weight, constant or tree length produces a second bound state. G4 the Liouville twist produces one above the trivial aperture. G5 stable under refinement |
| Questions it must answer | a bound-state count for the floor-map graph in terms of its potential and its edge weights; gluing two one-bound-state windows along the rank-one charge coupling; the first window where a second bound state could appear |
| Tools | Bargmann and CLR bounds on graphs; Schur complements along the charges; interlacing; M-matrix theory |
| Objects | windows, blocks, floor-map graphs, potentials, bound states |
| Language | well, bound state, gluing, refinement, charge coupling |
| Mechanisms | Built on AGZ, HFP. To discover: a bound-state inequality whose right-hand side the primes keep below two |

**Main conjecture.** Every window's floor-map graph holds exactly one bound state. **Milestones.** M1 A146. M2 a gluing lemma for two windows. M3 a Bargmann-type count with explicit constants on the certified ratios.

## 2.14 A research programme to construct `𝔽₁`

**Goal.** A geometry in which Spec ℤ has a square and the inequality of Castelnuovo and Severi on it is a theorem. The programme is AGZ with HFP; SA, FFA and WZC are its test benches.

**What the corpus fixes [L*].**
| Item | Theorem |
|---|---|
| the pairing | limit `2d₁d₂−Z(f)`; Bézout ⇔ RH; index = right zeros |
| forced data | constant, contacts at their price, tree lengths |
| number rings | ideals as degree points; index of every Dedekind zeta function; the neutral form has index of the zeta function plus one; quotients of `L`-functions count zeros and poles; Dedekind's divisibility on the line as a no-negative-square condition |
| a non-abelian extension | `ℚ(∛2,ω)`: the Artin character of degree two and `ζ_{ℚ(∛2)}` have their Hodge index |
| finite scale | the step-packet matrix; RH ⇔ one negative square of the neutral part on every window; certified short windows, first blocks, thin packets; refinement tower; coarse-block transfer |
| the aperture | Morse = Maslov index; far end = zeros; polar Lagrangian; simple ground mode |
| tails | critical comb growth = width; Abel integrability ⇔ `a+w≤½`; ordinary convergence ⇔ every zero left of `1−a` |
| sections | the square counts linearly |
| points | the contacts of a number ring are its point counts over `𝔽_{p^m}` |
| deformations | price paths are RH at every parameter |
| counts of models | a bounded count error identifies the rational primes; a count rate does not |

**What it would be like [D].** Spec ℤ over `𝔽₁` is a curve of infinite genus whose square is rigid and counts like a curve. Its Néron–Severi lattice at finite scale is a weighted graph with a potential, and its Hodge index is a bound-state count. Its index along the aperture is a Maslov index with a two-dimensional polar shadow. Its zero width is the growth of one comb. What distinguishes ℤ from its imitations is the functional equation as an identity and the exact count.

**State of the constructions.**
| Construction | Deliverable | State |
|---|---|---|
| I path | transport of the sign | closed: RH at every parameter |
| II glued fibre | the comb form as a glued form | refuted for invariant gluings; data forced |
| III Stepanov on the square | a small vanishing section | closed: an equality of ideals |
| IV towers and Galois extensions | index per character | Hecke characters, number rings, quotients, one non-abelian ring; general Artin via Brauer (A150) |
| V own comb | Bézout for an own system | closed: fails |
| VI count | quadratic count | linear; no definition without the form (B87) |
| VII finite scale | the inequality in finite rank | equivalence; short windows and first blocks certified; all blocks at ratio 4 open (A146) |
| VIII index as topology | index from the path | closed as Morse = Maslov; the far end carries the zeros |
| IX tails | the width on the comb | closed: one sequence |
| X bound states | the Hodge index as a bound-state count | proposed (§2.13) |

**Criteria.** C1 reproduces Weil and Stepanov for curves. C2 a count rate is not enough. C3 uses the functional equation as an identity. C4 uses the Euler product on the function. C5 sees the exact normalization. C6 infinite type. C7 the diagonal is the density of a comb. C8 positivity is derived. C9 selective only where a contact enters. C10 additive over the constituents of a number ring, zeros and poles counted. C11 nothing below the trivial aperture beyond the dominated box. C12 at finite scale it is the neutral-part index. C13 a statement at the point. C14 a quadratic count. C15 treats neutral null modes. C16 its comb grows at the rate of the width.

**Questions.** 1 a quadratic count (B87, B169). 2 Bézout from a property (B149). 3 the bound-state count of the floor-map graph (§2.13). 4 Brauer induction (A150). 5 the sign of `𝔚_4` at every block size (A146). 6 charged ground states (B104). **Order of work [A].** A146; A150; a gluing lemma for windows; B104 at finite scale.

**Decisive test.** A construction whose Bézout holds for an edit with a finite layer, for a fake, for the Liouville twist at rung one, for a wrong constant, or along a path of squares, is wrong [L*].

## 2.15 A research programme to close the route WD

**Goal.** A bound `O_θ(T^K)` with one `K` and unbounded `θ` for the second moment of ζ times a Möbius mollifier of length `T^θ`, or the collision bound equivalent to it [F].

**What the corpus fixes.**
| Item | Statement | Evidence |
|---|---|---|
| receiver | RH ⇔ the mollified moment is subpolynomial; a cofinal bound with fixed `K` suffices | [F] |
| depth | dyadic boundedness at `θ>1` confines high zeros to depth `<1/(2θ)+ε` | [L*] |
| proved range | `θ<½` with main terms and a power saving | [L*] |
| on the line | a positive proportion of critical zeros of odd multiplicity at `θ=13/50` | [L*] |
| necessary length | excess `K₀/log T` forces `log N≥log²T/(6K₀)−(4/3)log T` | [F]/[KR] |
| blindness | Type-II norms sign-blind; finite relocation invisible to quadratic tests of length `o(T²)`; impure factors pass every upper bound up to a constant | [KR] |
| cameras | box cameras with geometric exterior loss and order-uniform prime cost | [doc] |

**What it would be like [D].** A mean-value theory past the height, whose off-diagonal is a correlation of truncated Möbius divisor sums. On the scale a bounded dyadic moment at `θ` is the half-plane `½+1/(2θ)`: the route passes `7/8` at `θ=4/3` and reaches the line only cofinally. Below `2/3` the route competes with nothing: the producer ends there (§1.6).

**Criteria.** W1 fails for `ζ(s)(1−cp^{−s})`, `c>√p`. W2 fails for a finite relocation (needs length beyond `T²`). W3 not a Type-II norm bound. W4 keeps the pole and the Barban–Vehov diagonal. W5 `K` independent of `θ`. W6 at `θ<4/3` it gives nothing `[X]` does not. W7 it fails for a two-sided edit with a finite layer, which changes the Möbius coefficients at infinitely many primes.

**Questions.** 1 A18. 2 the collision form at `θ≥1`. 3 a power saving at one `θ>4/3` (below `7/8`); at `θ>3/2` it is below `2/3`, past the producer's reach. 4 fixed `K` along `θ→∞` (B62). 5 the converse of the depth theorem.

**Tools.** Gallagher's transfer; the Selberg-integral dictionary; shifted correlations of sieve weights; the Levinson gate; the entropy decrement and the circle method of LogarithmicChowla as the correlation inputs in Lean.

**Milestones.** M1 `θ<½` (Lean). M2 a proportion on the line (Lean). M3 A18. M4 the collision dictionary at `θ≥1`. M5 a saving at one `θ>4/3`. M6 the cofinal bound.

**Limit [A].** The cofinal bound is RH; every partial result is a level of the scale, and below `2/3` this route is the only one of the corpus that the producer's end does not cap.

## 2.16 A research programme to close the route ACS

**Goal.** One negative square of the neutral part on every window; equivalently the comb sign, a mass floor on every ratio window, or subpolynomial growth of the critical comb.

**What the corpus fixes.** The table of §2.14, and:
| Item | Statement | Evidence |
|---|---|---|
| the minimal face | one inequality per prime as the limit of two-bump comb forms | [L*] |
| finite scale | neutral-part index ⇔ RH; short windows, first blocks, thin packets certified; uniform index bound `(Q−1)⌈e^{E_Q}⌉` at each ratio | [L*] |
| transfer | margins above one scale transfer to every refinement past `log R≥E_Q+2C_Q²/μ₀+μ₀` | [L*] |
| tails | critical comb growth = width; never convergent; Abel integrable ⇔ RH; subcritical convergence ⇔ every zero left of the boundary | [L*] |
| right trace | the prime error keeps its complete right-substrip zero trace with a global power remainder | [doc] |

**What it would be like [D].** Three tracks on one lattice. *Matrices*: the neutral part as a graph Schrödinger operator, one bound state per window, ratio by ratio. *Index*: the aperture path and its polar shadow. *Tails*: the critical comb as the scale on one sequence.

**Criteria.** Those of §2.14, and: S1 nothing about the contacts below ratio two. S2 a margin at each ratio, none uniform. S3 nothing on the tails at `a<1/8` beyond `[X]`. S4 the certified windows are reproduced, not reproved.

**Questions.** 1 A146: ratios 4 and 7 at every block size, where the index is between `0` (RH) and `300000` (proved). 2 a gluing lemma: two windows with one bound state each, coupled through the product of their charges. 3 B149, B87, B169. 4 B104. 5 A150, A141.

**Tools.** Schur complements against the charges; the refinement tower; the coarse-block transfer; Bargmann/CLR counts on graphs; the contact Mellin calculus; the index law for quotients.

**Milestones.** M1 finite criteria (Lean). M2 short windows (Lean). M3 A146. M4 a gluing lemma. M5 every ratio (B152).

**Limit [A].** Each ratio is a finite-height statement; the uniform statement is RH.

## 2.17 A research programme to close the route ZCG

**Goal.** No positive-time collision of the heat flow; or the floor on a decisive sequence of prime windows; or ZAL, B13 and Landing.

**What the corpus fixes.**
| Item | Statement | Evidence |
|---|---|---|
| worlds | world I or world II, top `≤7/8` | [X]; [L*] |
| world I receivers and instruments | unit gap, non-attainment, moments, four sectors, filters, currents, quanta | [L*] |
| world I models | every finite layer, the pair alone above `√x`, an isolated pair above a tail, landing failure, sparse tails, layer removal — all over the rational primes with a count rate | [L*] (WZC) |
| laws of the models | balance or real top below a fake zero; parity above twice the count exponent; additions paid in full; count floor | [L*] |
| the door | Euler product with the FE as an identity, or with a count below the floor | [D] (D5) |
| heat | RH ⇔ no collision; `N(t)≥2` at small times unless RH | [L*] |
| cameras | box cameras; complete exterior mass of adaptive clusters | [doc]/[F] |

**What it would be like [D].** World I is a finite-dimensional problem with complete receivers and a complete model theory over the rational primes: it closes by one inequality that uses the FE as an identity and fails on every edit. World II is the scale and inherits the producer's end at `2/3`.

**Criteria.** Z1 a world-I statement fails on every edit with a finite layer, on the firewall and on the fakes. Z2 two-sided, or at every length. Z3 nothing below the logarithmic radius. Z4 a world-II statement is placed on the scale. Z5 a camera statement names the cluster size and gap. Z6 nothing in law used as a point. Z7 every statement states its FE defect budget (B186).

**Questions.** 1 B145 or B170. 2 B186. 3 B183. 4 B141: not from an Euler product over the rational primes with a count rate (the isolated pair above a tail) [L*]. 5 B13 and Landing (B157, A120). 6 B59. 7 the half-planes of world II.

**Tools.** Filters, currents, quanta; two-sided edits with prescribed factors; the balance and parity laws; box cameras; the scale.

**Milestones.** M1 receivers, instruments, models (Lean). M2 A151, then B186. M3 the weighted current for one quartet. M4 AAL. M5 ZAL through the scale. M6 Landing and B13.

**Decisive test.** An argument for AAL that holds for a two-sided edit with a finite layer, for the firewall or for a fake, is wrong.

**Limit [A].** AAL and ZAL together are RH; the corpus has a receiver for each and a producer for neither below `7/8`.

## 2.18 A research programme to close the route MC/JAS

**Goal.** The signal bound `O(Z^b)` for every `b>½`; equivalently level one of the dressed aggregate.

**What the corpus fixes.** §1.6 in full; the signal is a smoothed Möbius sum whose exponent is the abscissa [L*]; the centred cover count is `M(N)` [L*]; producer rates are the Mertens level [L*]; bilinear norms are sign-blind [KR]; the prime kernel off the major arcs and the VK region for Dirichlet `L` [L*]/[doc].

**What it would be like [D].**
| Stage | Half-plane | Input | Kind |
|---|---|---|---|
| 0 | `7/8` native | A118, first `11/12` | just work |
| 1 | `7/8→13/15` | row count of the binding bin (B174) | density estimate |
| 2 | `13/15→5/6→7/9` | the long columns with a power saving (B185) | an estimate that is not a square |
| 3 | `7/9→2/3` | square-root remainder in the long columns | Patterson-type [C] |
| 4 | `2/3→3/5` | estimates below the square-root endpoint on every tower level | beyond square root |
| 5 | below `3/5` | a source outside the class (B187) | — |

**Criteria.** J1 every estimate placed in the twist exponent. J2 a mean square containing the principal twists is not an input. J3 positive weights, even order, two row variables fail. J4 below `5/6` nothing is a square. J5 below `2/3` the family contains its corrections. J6 a source for the last stage has square-root endpoint `½` and a frame without a wall above `½`.

**Questions.** B174, B185, B187, B180; the transfer map of every completed probe; level one directly (B160).

**Tools.** The budget calculus; signed Gram forms; Poisson coefficients; sieves over cyclotomic rings; the scale as a ruler; `μ²` and matched phases as calibrations.

**Milestones.** M1 the native `11/12`, then `7/8`. M2 a boundary below `7/8`. M3 B185 with any `R₀<1`. M4 below `5/6`. M5 B187.

**Decisive test.** An estimate that holds for `μ²`, for matched phases, or for a family with its principal twists counted as input, proves no half-plane.

**Limit [A].** With every stage of the cubic probe completed the programme reaches `2/3` (`3/5` with estimates beyond square root). It is the only programme that has produced a theorem about the zeros, and in its present class it does not reach the line.

## 3. The one big question: what does a fake zero cost in the functional equation? (B186)

**Where the question sits.** The three cores meet at one input [D] (D6). The producer stops above `½` because the reflection of its theta row needs a completion, and the completion couples the target to a second family (Π). World I has a model for every structure set that is weaker than the Euler product with the functional equation as an identity, and with the identity the system is the rational primes (Γ). The archimedean side of every sign form is the reflection's Gamma factor (Σ). So every remaining route to AAL uses the reflection, and nobody knows how exactly: as an identity, up to an integrable defect, or up to a defect that grows.

**What is in Lean [L*].**
- A countable Beurling system whose critical-line FE defect `g` is in `L¹`, or in `L²` with polynomial growth, is the rational primes (`IntegrableFunctionalEquationsDetermineThePrimes`, `beurlingSystem_rigidity_of_finiteEnergy_theta_defect`); a prime of the system at distance `>δ` from every rational prime below `N` forces `∫|g|≥min(1/(400N²),2δ²/(3πN²))` (`critical_line_defect_ge_of_prime_dist_gt`); by the formalized card `integrable-fe-defect-gap`, `6400‖g‖₁≤1` already forces the integers (`SmallIntegrableDefectsForceTheRationalPrimes`).
- Two-sided edits of the rational primes with a count rate carry a non-real pair alone on top, any finite layer, tails and landing failure; their zeta functions continue past the line (pair twins to `Re s>Re ρ/2`) (WZ1, WZ5–WZ7).
- Quartet edits keep the zero set symmetric under `s↦1−s̄` on `c<Re s<1−c`, `c≥1/3` (WZ4).
- Continuous positive prime measures with an integrable FE defect keep the zeros of ζ [KR].

**What follows [D] (D5).** Every fake that continues to the critical line has an FE defect outside `L¹` and outside polynomially bounded `L²`. The pair factor `(s−ρ)(s−ρ̄)` alone contributes a defect of order `|t|·|½−Re ρ|` times `|ζ(½+it)|` on the line; whether the edit exponential can compensate it is open.

**Question (B186).** *For a two-sided edit of the rational primes (an Euler product with multiplicities `0,1,2`, integer norms and a count rate) whose zeta function continues to the critical line and has a zero right of the line that ζ lacks: what is the least growth of its critical-line FE defect `g(t)`? Is there one with `g=O(|t|^{−½+ε})`, with `g` bounded, or must `g` grow like a power of `|t|`? The same question for countable Beurling systems with real weights.*

**Why this question.**
- It is below RH and AAL: a question about models and rigidity, answerable by a construction or by a lower bound in the method of the rigidity theorems.
- It measures the one input that every remaining route to AAL has to use, and the input whose cost limits the producer.
- It costs little: its first step (A151) is a computation in the objects of two Lean programmes.

**What an answer gives.**
| Answer | Effect |
|---|---|
| fakes with `g` just outside `L²` (of size `|t|^{−½}` up to logarithms) | rigidity is sharp at square integrability. Every argument that uses the reflection approximately — the approximate functional equation, Gamma-factor asymptotics, zero counts, an FE with an error of size `|t|^{−¼}` — is consistent with a fake zero: AAL, B13 and Landing need the reflection to `L²` precision. Kills the approximate-FE strategies of ZCG, BAG, ELT, JAS (shell), LA (finite support), SC (undamped), WL (thick runs) |
| fakes only with bounded or polynomially growing `g` | a gap between rigidity and the models: the triple "Euler product over the rational primes, count rate, FE up to `o(|t|^α)`" has no model with a fake zero, and a proof of AAL may use the reflection approximately. Opens a defect calculus for world I (§2.10) and fixes the first exponent of a layer–defect inequality |
| a lower bound `‖g‖≥F(depth)` on every edit with a fake zero, uniform in the depth | the first quantitative form of "the Euler product with the reflection identifies ζ" that sees a zero; its `g=0` case for ζ is AAL, so the bound is the place where a proof of AAL by rigidity would start |

**First step and obstacle.** A151: the defect of the pair twin `(s−1)ζ_B=(s−1)ζ·C(s−ρ)(s−ρ̄)e^{H}` and of a quartet edit on the line, as a function of the height, through the prescribed-factor identity and the edit series. Named obstacle: the edit exponential `e^{H}` on the line is controlled only through the discrepancy of the greedy rounding at frequency zero; a symmetric factor needs a two-sided selection of primes with small discrepancy at every frequency (the WZC open topic).

**Tests.** T1: method, implied by nothing about ζ's zeros. T2: a construction with a stated defect, or a lower bound. T3: named for each answer. T4: pass. T5: calibrated on the rigidity theorems (no fake with an integrable defect), on the continuous models (defect integrable, no fake zero), on the quartet edits (symmetric in a strip, defect open). T6: pass. T7: sets the defect axis Γ239; moves Γ15, Γ231. T8: not a named problem; the first step is in corpus objects with one named obstacle.

**Limit.** The question concerns models. It does not decide RH; it decides how much of the functional equation a proof of the abscissa law has to carry, and with that which of the remaining world-I strategies can succeed.

### Alternatives considered
| Question | Effect | Verdict |
|---|---|---|
| The long columns (B185, §2.4) | the first non-square estimate; the half-plane moves toward `2/3` | the largest motion available; capped at `2/3` |
| A source with square-root endpoint `½` (B187, §2.5) | a producer for the line, or the end of the Gauss-sum class | the producer question; its first step is a classification |
| Charged ground states (B104, §2.8) | the polar shadow sees the first crossing | decides one channel of five routes |
| A fake below `√x` with a non-real top (B183) | the count door for world I | balanced edits only; a model question on the count axis |
| The row count of the binding bin (B174) | `[13/15,7/8)` | one-sided density estimate |
| The weighted current (B145, §2.6) | AAL without a sign | AAL strength |
| The congruence mechanism for resonances (B188, §2.7) | a second producer | no first step past the dictionary |
| The steps of `[X]` (A118) | the half-plane in the native graph | just work |
| A bound-state count for the floor-map graph (§2.13) | RH | RH strength |
| Brauer induction, the sign of `𝔚_4` at every block size | index for Artin characters; ratio 4 | just work / sub |
